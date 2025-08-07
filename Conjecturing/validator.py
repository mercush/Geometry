"""Validates conjecture output by LLM.

Must do three things.
1. Check that algebraic_euclid proves the statement
2. Check that the hypotheses do not prove False
3. Use a Gemini API call to check that the statement is not
identical to one of the inputs.
"""
import asyncio
from dotenv import load_dotenv
from google import genai
from lean_interact import LeanREPLConfig, AutoLeanServer, Command, LocalProject
from lean_interact.interface import LeanError, CommandResponse
from LeanPotential import lean_parse

TIMEOUT = 20

class Validator:
    def __init__(self, lean_version, project_dir, lean_preamble):
        self.lean_config = LeanREPLConfig(verbose=True, project=LocalProject(directory=project_dir), memory_hard_limit_mb=4000)
        self.lean_server = AutoLeanServer(self.lean_config)
        self.lean_preamble = lean_preamble
        response = self.lean_server.run(Command(cmd=lean_preamble))
        self.environment = response.env
        load_dotenv()
        self.client = genai.Client()

    async def run_lean_check(self, lean_code):
        """Run a Lean check and return True if there are no errors."""
        try:
            response = await self.lean_server.async_run(
                Command(cmd=lean_code, env=0), timeout=TIMEOUT
            )
            match response:
                case CommandResponse():
                    messages = response.messages
                    errors = [m for m in messages if m.severity == "error"]
                    if errors:
                        print(f"❌ Lean check failed: {errors[0].data}")
                        return False
                    else:
                        print("✅ Lean check passed")
                        return True
                case LeanError(message):
                    print(f"❌❌ Lean error: {message}")
                    return False
        except asyncio.TimeoutError:
            print(f"⏰ Lean timed out (> {TIMEOUT}s)")
            return False

    async def check_proves(self, conjecture):
        """Check that algebraic_euclid proves the statement.
        
        Args:
            conjecture: The conjecture to check.
            
        Returns:
            True if the conjecture is provable, False otherwise.
        """
        parsed_expr = lean_parse.parse_lean(conjecture)[0]
        parsed_expr.proof = 'algebraic_euclid'
        reconstructed = parsed_expr.complete_str()
        return await self.run_lean_check(reconstructed)

    async def check_non_trivial(self, conjecture):
        """Check that the hypotheses of the conjecture do not prove False.
        
        Args:
            conjecture: The conjecture.
            
        Returns:
            True if the hypotheses are non-trivial, False otherwise.
        """
        parsed_expr = lean_parse.parse_lean(conjecture)[0]
        parsed_expr.typ = "False"
        reconstructed = parsed_expr.complete_str()
        return not await self.run_lean_check(reconstructed)

    def check_not_identical(self, conjecture, examples):
        """Use a Gemini API call to check that the statement is not
        identical to one of the inputs.
        
        Args:
            conjecture: The conjecture to check.
            examples: The list of input theorems.
            
        Returns:
            True if the conjecture is not identical to any of the examples, False otherwise.
        """
        prompt = f"Is the following conjecture an original thought, or is it identical to one of the provided examples? Please only respond with 'Original' or 'Identical'.\n\nConjecture:\n{conjecture}\n\nExamples:\n"
        for i, example in enumerate(examples):
            prompt += f"Example {i+1}:\n{example}\n\n"
            
        response = self.client.models.generate_content(
                model='gemini2.0-flash', contents=prompt)
        
        return "Original" in response.text

    async def validate_conjecture(self, conjecture, examples):
        """Validate the conjecture.
        
        Args:
            conjecture: The conjecture to validate.
            examples: The list of input theorems.
            
        Returns:
            A string indicating the result of the validation.
        """
        if not await self.check_proves(conjecture):
            return "Failed: Does not prove"
        
        if not await self.check_non_trivial(conjecture):
            return "Failed: Trivial hypotheses"
            
        if not self.check_not_identical(conjecture, examples):
            return "Failed: Identical to an example"
            
        return "Success"

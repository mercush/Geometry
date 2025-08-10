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
from Geometry.Conjecturing.prompts import validator_system_prompt, validator_user_prompt

TIMEOUT = 60

class Validator:
    def __init__(self, project_dir, lean_preamble):
        self.project_dir = project_dir
        self.lean_preamble = lean_preamble
        load_dotenv()
        self.client = genai.Client()
        self._init_lean_server()
    
    def _init_lean_server(self):
        """Initialize or reinitialize the Lean server and environment."""
        self.lean_config = LeanREPLConfig(verbose=True, project=LocalProject(directory=self.project_dir), memory_hard_limit_mb=4000)
        self.lean_server = AutoLeanServer(self.lean_config)
        response = self.lean_server.run(Command(cmd=self.lean_preamble))
        self.environment = response.env

    async def run_lean_check(self, lean_code):
        """Run a Lean check and return True if there are no errors."""
        try:
            response = await self.lean_server.async_run(
                Command(cmd=lean_code, env=self.environment), timeout=TIMEOUT
            )
            match response:
                case CommandResponse():
                    messages = response.messages
                    errors = [m for m in messages if m.severity == "error"]
                    print(errors)
                    if errors:
                        return False
                    else:
                        return True
                case LeanError():
                    if response.message == 'Unknown environment.':
                        self._init_lean_server()
                        # Retry once with fresh environment
                        response = await self.lean_server.async_run(
                            Command(cmd=lean_code, env=self.environment), timeout=TIMEOUT
                        )
                        match response:
                            case CommandResponse():
                                messages = response.messages
                                errors = [m for m in messages if m.severity == "error"]
                                print(errors)
                                return len(errors) == 0
                            case LeanError():
                                print(response.message)
                                return False
                    else:
                        print(response.message)
                        return False
        except asyncio.TimeoutError:
            print("Lean check timed out.")
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
        parsed_expr.proof = "algebraic_euclid"
        reconstructed = parsed_expr.complete_str()
        return not await self.run_lean_check(reconstructed)

    async def check_conclusion_non_trivial(self, conjecture):
        """Check that the conclusion of the conjecture is not provable without hypotheses.
        
        Args:
            conjecture: The conjecture.
            
        Returns:
            True if the conclusion is non-trivial, False otherwise.
        """
        parsed_expr = lean_parse.parse_lean(conjecture)[0]
        
        # Create a new theorem with no hypotheses
        conclusion_only_expr = type(parsed_expr)(
            name=parsed_expr.name + "_conclusion_only",
            params=[], # No hypotheses
            typ=parsed_expr.typ,
            proof="algebraic_euclid"
        )
        
        reconstructed = conclusion_only_expr.complete_str()
        
        # If it proves, then the conclusion is trivial
        return not await self.run_lean_check(reconstructed)

    async def check_materially_different(self, conjecture, examples):
        """Use a Gemini API call to check that the statement is not
        materially different to one of the inputs. This is done in batches.
        
        Args:
            conjecture: The conjecture to check.
            examples: The list of input theorems.
            
        Returns:
            True if the conjecture is not identical to any of the examples, False otherwise.
        """
        batch_size = 10
        num_batches = (len(examples) + batch_size - 1) // batch_size
        
        yes_count = 0
        no_count = 0
        
        for i in range(num_batches):
            batch = examples[i*batch_size:(i+1)*batch_size]
            user_prompt_str = validator_user_prompt(conjecture, batch)
            
            response = self.client.models.generate_content(
                    model='models/gemini-1.5-flash', 
                    contents=[validator_system_prompt, user_prompt_str]
            )
            
            if "Yes" in response.text:
                yes_count += 1
            elif "No" in response.text:
                no_count += 1
        
        return yes_count > no_count

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
            
        if not await self.check_conclusion_non_trivial(conjecture):
            return "Failed: Trivial conclusion"
            
        if not await self.check_materially_different(conjecture, examples):
            return "Failed: Not materially different"
            
        return "Success"

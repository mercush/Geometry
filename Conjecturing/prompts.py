"""Prompts."""

system_prompt = """You are a Lean4 conjecturer. Your goal is to make novel conjectures
for a geometry DSL written in Lean4. You will be given some example theorems as 
inspiration. You must be creative to make conjectures that are 
1. True
2. Non-trivial (hypotheses can't be used to prove False)
3. Not identical to the inspiration problems"""

def user_prompt(examples):
    """Create the user prompt.    Args:
        examples: A list of theorems.        Returns:
        A string that will be the user prompt.
    """
    prompt = "Here are some example theorems:\n\n"
    for i, example in enumerate(examples):
        prompt += f"Example {i+1}:\n{example}\n\n"
    prompt += "Please make a conjecture based on these examples."
    return prompt
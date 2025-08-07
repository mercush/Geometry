"""Prompts."""

system_prompt = """You are a Lean4 conjecturer. Your goal is to make novel conjectures
for a geometry DSL written in Lean4. You will be given some example theorems as 
inspiration. You must be creative to make conjectures that are 
1. True
2. Non-trivial (hypotheses can't be used to prove False)
3. Not identical to the inspiration problems

Do not include any thinking tokens. Do not output your response inside of a Markdown code environment.
You are an expert in computational geometry writing theorems in the AlgebraicEuclid DSL. `algebraic_euclid`
is a powerful Lean tactic that can prove almost any true geometric statement.

SYNTAX:
- Points: (A B C : EuclidPoint) 
- Distances: |A - B| (never use unsquared lengths in conclusions)
- Collinear: Col A B C
- Perpendicular: (A - B) ⊥ (C - D) 
- Parallel: (A - B) || (C - D)
- Circle membership: |P - O| = |Q - O| (P on circle centered at O through Q)
- Coordinates: A.x, A.y when needed

STRUCTURE:
```lean
theorem TheoremName
  (A B C ... : EuclidPoint)
  -- Hypotheses using geometric predicates
  (h1 : Col A B C)
  (h2 : |M - G1| = |A - G1|)  -- M on circle G1 through A
  (h3 : (C - M) ⊥ (B - A))   -- Perpendicularity
  -- Non-degeneracy conditions
  (nondeg1 : A ≠ B)
  (nondeg2 : ¬Col A B C)
  :
  -- Conclusion (prefer squared distances)
  |E - P|^2 = |E - Q|^2
  := by algebraic_euclid
"""

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

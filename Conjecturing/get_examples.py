"""Get examples that will be passed into the conjecturing LM.

Need to parse Basic.lean to create list of all the theorems. Then, sample n distinct
theorems from this list.
"""
import random
import re

def get_theorems(file_path):
    """Parse the Lean file to get a list of theorems.
    
    Args:
        file_path: The path to the Lean file.
        
    Returns:
        A list of theorems.
    """
    with open(file_path, 'r') as f:
        content = f.read()
    
    # This is a simple way to parse the file. It might not be robust.
    theorems = content.split('theorem')
    
    # The first element is the import statements, so we discard it.
    theorems = theorems[1:]
    
    # Clean up the theorems
    cleaned_theorems = []
    for theorem in theorems:
        # Remove the proof
        theorem_statement = theorem.split(':= by')[0]
        # Strip leading/trailing whitespace
        cleaned_theorems.append(theorem_statement.strip())
        
    return cleaned_theorems

def sample_theorems(theorems, n):
    """Sample n distinct theorems from the list of theorems.
    
    Args:
        theorems: A list of theorems.
        n: The number of theorems to sample.
        
    Returns:
        A list of n distinct theorems.
    """
    return random.sample(theorems, n)
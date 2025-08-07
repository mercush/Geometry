"""Evaluate the performance of LMs on conjecturing.

For n trials, sample k theorems from Basic.lean, pass these into the user prompt,
query the LM to conjecture a theorem, then pass into validate.
"""
import asyncio
from Geometry.Conjecturing.get_examples import get_theorems, sample_theorems
from Geometry.Conjecturing.prompts import system_prompt, user_prompt
from Geometry.Conjecturing import validator 
from LeanPotential.lean_potential import *
import argparse
from collections import Counter

def query_lm(user_prompt, system_prompt_arg, model_name, lean_version, project_dir, tensor_parallel_size):
    """Query the language model to make a conjecture.
    
    Args:
        user_prompt: The user prompt.
        system_prompt_arg: The system prompt.
        
    Returns:
        The conjecture from the LM.
    """
    model = GenLMModel(
            model_name, 
            "import Geometry",
            lean_version, 
            project_dir, # assuming run with the run.sh script 
            tensor_parallel_size)
    model.add_message("system", system_prompt_arg)
    model.add_message("user", user_prompt)
    response = model.retry_response()
    return response

async def run_evaluation(n_trials, k_examples, tensor_parallel_size, model_name, lean_version, project_dir):
    """Run the evaluation. 
    
    Args:
        n_trials: The number of trials to run.
        k_examples: The number of examples to use in each trial.
    """
    val = validator.Validator(lean_version, project_dir, "import Geometry")
    theorems = get_theorems('Geometry/Basic.lean')
    
    results = []
    for i in range(n_trials):
        print(f"--- Trial {i+1}/{n_trials} ---")
        
        # Sample k theorems
        examples = sample_theorems(theorems, k_examples)
        
        # Create the prompt
        prompt = user_prompt(examples)
        
        # Query the LM
        conjecture = await query_lm(prompt, system_prompt, model_name, lean_version, project_dir, tensor_parallel_size)
        print(f"Conjecture: {conjecture}")
        
        # Validate the conjecture
        result = await val.validate_conjecture(conjecture, examples)
        print(f"Validation Result: {result}")
        results.append(result)
            
    print("\n--- Evaluation Summary ---")
    result_counts = Counter(results)
    for result_type, count in result_counts.items():
        print(f"{result_type}: {count}/{n_trials} ({(count/n_trials)*100:.2f}%)")

if __name__ == '__main__':
    # These are placeholder values. You can change them.
    parser = argparse.ArgumentParser()
    parser.add_argument('-n', '--n_trials', type=int)
    parser.add_argument('-k', '--k_examples', type=int)
    parser.add_argument('-t', '--tensor_parallel_size', type=int)
    parser.add_argument('-m', '--model_name')
    parser.add_argument('-v', '--lean_version')
    parser.add_argument('-p', '--project_dir')
    args = parser.parse_args()
    
    asyncio.run(run_evaluation(
        args.n_trials, 
        args.k_examples, 
        args.tensor_parallel_size, 
        args.model_name, 
        args.lean_version, 
        args.project_dir))

"""Evaluate the performance of LMs on conjecturing.

For n trials, sample k theorems from Basic.lean, pass these into the user prompt,
query the LM to conjecture a theorem, then pass into validate.
"""
import asyncio
import json
import os
from pathlib import Path
from Geometry.Conjecturing.get_examples import get_theorems, sample_theorems
from Geometry.Conjecturing.prompts import system_prompt, user_prompt, preamble
from Geometry.Conjecturing import validator 
from LeanPotential.lean_potential import BaseLMModel, GenLMModel, GeminiModel
import argparse
from collections import Counter

async def query_lm(user_prompt, system_prompt_arg, model_name, project_dir, tensor_parallel_size, model_type):
    """Query the language model to make a conjecture.
    
    Args:
        user_prompt: The user prompt.
        system_prompt_arg: The system prompt.
        model_name: The name of the model to use.
        project_dir: The project directory.
        tensor_parallel_size: The tensor parallel size.
        model_type: The type of model to use ('genlm', 'base', or 'gemini').
        
    Returns:
        The conjecture from the LM.
    """
    if model_type.lower() == 'genlm':
        model = GenLMModel(
                model_name, 
                preamble, 
                project_dir, # assuming run with the run.sh script 
                tensor_parallel_size)
    elif model_type.lower() == 'base':
        model = BaseLMModel(
                model_name=model_name,
                temperature=1.0,
                max_tokens=2000,
                n_particles=20)
    elif model_type.lower() == 'gemini':
        model = GeminiModel(
                model=model_name,
                temperature=0.2,
                max_tokens=300)
    else:
        raise ValueError(f"Unknown model_type: {model_type}. Choose from 'genlm', 'base', or 'gemini'.")
    
    model.add_message("system", system_prompt_arg)
    model.add_message("user", user_prompt)
    
    if model_type.lower() == 'genlm':
        response = await model.retry_response()
    else:
        response = await model.get_response()
    
    return response

async def run_evaluation(n_trials, tensor_parallel_size, model_name, project_dir, model_type):
    """Run the evaluation. 
    
    Args:
        n_trials: The number of trials to run.
        tensor_parallel_size: The tensor parallel size.
        model_name: The name of the model to use.
        project_dir: The project directory.
        model_type: The type of model to use ('genlm', 'base', or 'gemini').
    """
    val = validator.Validator(project_dir, preamble)
    theorems = get_theorems('Geometry/Basic.lean')
    
    # Create output directory structure
    # Clean model name for filesystem (replace problematic characters)
    clean_model_name = model_name.replace("/", "_").replace(":", "_")
    output_dir = Path(f"results/{model_type}/{clean_model_name}/all_theorems")
    output_dir.mkdir(parents=True, exist_ok=True)
    
    results = []
    for i in range(n_trials):
        print(f"--- Trial {i+1}/{n_trials} ---")
        
        # Use all theorems as examples
        examples = theorems
        
        # Create the prompt
        prompt = "Based on the following theorems, please conjecture a new, materially different theorem.\n\n" + "\n\n".join(examples)
        
        # Query the LM
        conjecture = await query_lm(prompt, system_prompt, model_name, project_dir, tensor_parallel_size, model_type)
        print(f"Conjecture: {conjecture}")
        
        # Validate the conjecture
        result = await val.validate_conjecture(conjecture, examples)
        print(f"Validation Result: {result}")
        
        # Determine if valid (Success means valid)
        is_valid = result == "Success"
        
        if is_valid:
            print("New valid theorem found! Adding to Basic.lean.")
            basic_lean_path = 'Geometry/Basic.lean'
            with open(basic_lean_path, 'a') as f:
                f.write(f"\n\n{conjecture}")
            theorems.append(conjecture)
        
        # Save to JSON
        output_data = {
            "conjecture": conjecture,
            "valid": is_valid
        }
        
        # Add failure reason if conjecture failed
        if not is_valid:
            output_data["failure_reason"] = result
        
        output_file = output_dir / f"{i}.json"
        with open(output_file, 'w') as f:
            json.dump(output_data, f, indent=2)
        
        results.append(result)
            
    print("\n--- Evaluation Summary ---")
    result_counts = Counter(results)
    for result_type, count in result_counts.items():
        print(f"{result_type}: {count}/{n_trials} ({(count/n_trials)*100:.2f}%)")
    
    # Save summary
    summary_data = {
        "model_type": model_type,
        "model_name": model_name,
        "n_trials": n_trials,
        "results_summary": dict(result_counts),
        "success_rate": result_counts.get("Success", 0) / n_trials
    }
    
    summary_file = output_dir / "summary.json"
    with open(summary_file, 'w') as f:
        json.dump(summary_data, f, indent=2)
    
    print(f"\nResults saved to: {output_dir}")
    print(f"Summary saved to: {summary_file}")

if __name__ == '__main__':
    # These are placeholder values. You can change them.
    parser = argparse.ArgumentParser()
    parser.add_argument('-n', '--n_trials', type=int)
    parser.add_argument('-t', '--tensor_parallel_size', type=int)
    parser.add_argument('-m', '--model_name')
    parser.add_argument('-p', '--project_dir')
    parser.add_argument('--model_type', choices=['genlm', 'base', 'gemini'], default='genlm', 
                        help='Type of model to use: genlm (GenLMModel), base (BaseLMModel), or gemini (GeminiModel)')
    args = parser.parse_args()
    
    asyncio.run(run_evaluation(
        args.n_trials, 
        args.tensor_parallel_size, 
        args.model_name, 
        args.project_dir,
        args.model_type))


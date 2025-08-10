import pytest
from Geometry.Conjecturing.prompts import preamble
from LeanPotential import lean_potential
from Geometry.Conjecturing import get_examples
from Geometry.Conjecturing import validator
from genlm.control import PromptedLLM

@pytest.mark.asyncio
async def test_examples():
    potential = lean_potential.LeanPotential(
        PromptedLLM.from_name("openai-community/gpt2"), 
        preamble,
        ".")
    theorems = get_examples.get_theorems("Geometry/Basic.lean")
    for t in theorems:
        assert await potential.is_valid_lean(t)

@pytest.mark.asyncio
async def test_validator_run_lean_check():
    val = validator.Validator(".", preamble)
    theorems = get_examples.get_theorems("Geometry/Basic.lean")
    for i, t in enumerate(theorems):
        result = await val.run_lean_check(t)
        assert result

@pytest.mark.asyncio
async def test_validator():
    val = validator.Validator(".", preamble)
    theorems = get_examples.get_theorems("Geometry/Basic.lean")
    for i, t in enumerate(theorems):
        result = await val.check_proves(t)
        if not result: 
            print(i, t)
        assert result

@pytest.mark.asyncio
async def test_validator_2():
    val = validator.Validator(".", preamble)
    result = await val.check_proves("""theorem IsoscelesTriangleAltitudeMedian
  (h1 : |A - B| = |A - C|)
  (h2 : Col B D C)
  (h3 : (A - D) ⊥ (B - C))
  (h4 : Noncol A B C)
  : isMidpoint D (B - C) := by algebraic_euclid""")
    assert result

@pytest.mark.asyncio
async def test_validator_3():
    val = validator.Validator(".", preamble)
    result = await val.check_proves("""theorem CircleMidpointChordPerpendicular
  (h1 : |O - A| = |O - B|)
  (h2 : isMidpoint M (A - B))
  (h3 : |A - B| ≠ 0)
  : (O - M) ⊥ (A - B) := by algebraic_euclid""")
    assert result

@pytest.mark.asyncio
async def test_validator_non_trivial():
    val = validator.Validator(".", preamble)
    theorems = get_examples.get_theorems("Geometry/Basic.lean")
    for t in theorems:
        assert await val.check_non_trivial(t)

@pytest.mark.asyncio
async def test_validator_trivial():
    val = validator.Validator(".", preamble)
    bad_conjecture = "theorem test (A B C : EuclidPoint) (h : Col A B C) (h2 : Noncol A B C) : (A - B) || (B - C) := by sorry"
    result = await val.check_non_trivial(bad_conjecture)
    assert not result

@pytest.mark.asyncio
async def test_potential_proof_irrelevance_1():
    potential = lean_potential.LeanPotential(
        PromptedLLM.from_name("openai-community/gpt2"), 
        preamble, ".")
    # Test with invalid proof - should be ignored and replaced with sorry
    theorem_with_bad_proof = "theorem test_theorem (A B : EuclidPoint) : A = A := by invalid_tactic_that_doesnt_exist"
    result = await potential.is_valid_lean(theorem_with_bad_proof)
    assert result

@pytest.mark.asyncio
async def test_potential_proof_irrelevance_2():
    potential = lean_potential.LeanPotential(
        PromptedLLM.from_name("openai-community/gpt2"), 
        preamble, ".")
    # Test with garbage in proof - should be ignored
    theorem_with_garbage = "theorem test_theorem2 (A B : EuclidPoint) : A = A := by garbage nonsense invalid_stuff"
    result = await potential.is_valid_lean(theorem_with_garbage)
    assert result

@pytest.mark.asyncio
async def test_potential_proof_irrelevance_3():
    potential = lean_potential.LeanPotential(
        PromptedLLM.from_name("openai-community/gpt2"), 
        preamble, ".")
    # Test with extremely long invalid proof - should be truncated and replaced
    theorem_with_long_proof = "theorem test_theorem3 (A B : EuclidPoint) : A = A := by very_long_invalid_proof_that_goes_on_and_on_with_many_words_and_tactics_that_dont_exist_at_all"
    result = await potential.is_valid_lean(theorem_with_long_proof)
    assert result

@pytest.mark.asyncio
async def test_validator_not_identical_1():
    val = validator.Validator(".", preamble)
    original_theorem = "theorem new_theorem (A B : EuclidPoint) : A = A := by rfl"
    examples = ["theorem old_theorem (A B : EuclidPoint) : A = A := by rfl"]
    result = await val.check_materially_different(original_theorem, examples)
    assert not result  # Should be original/not identical

@pytest.mark.asyncio
async def test_validator_not_identical_2():
    val = validator.Validator(".", preamble)
    original_theorem = "theorem new_theorem (A B : EuclidPoint) : A = A := by rfl"
    examples = ["theorem old_theorem (X Y : EuclidPoint) :=X^2 - Y = 2 by sorry"]
    result = await val.check_materially_different(original_theorem, examples)
    assert result  # Should be original/not identical


@pytest.mark.asyncio
async def test_validator_not_identical_2():
    val = validator.Validator(".", preamble)
    original_theorem = """theorem  CevaTheoremSquaredDistances
  (h1 : Col D B C)
  (h2 : Col E C A)
  (h3 : Col F A B)
  (h4 : Col A G D)
  (h5 : Col B G E)
  (h6 : Col C G F)
  (h7 : Noncol A B C)
  :
  |A - F|^2 * |B - D|^2 * |C - E|^2 = |F - B|^2 * |D - C|^2 * |E - A|^2
  := by
  algebraic_euclid"""
    examples = ["""theorem CevaTheorem
  (h1 : Col D B C)
  (h2 : Col E C A)
  (h3 : Col F A B)
  (h4 : Col A G D)
  (h5 : Col B G E)
  (h6 : Col C G F)
  (h7 : Noncol A B C)
  :
  |A - F|^2 * |B - D|^ 2 * |C - E| ^ 2 = |F - B| ^ 2 * |D - C| ^ 2 * |E - A| ^ 2
  := by
  algebraic_euclid"""]
    result = not await val.check_materially_different(original_theorem, examples)
    assert result  # Should be identical.

@pytest.mark.asyncio
async def test_potential_malformed_syntax():
    potential = lean_potential.LeanPotential(
        PromptedLLM.from_name("openai-community/gpt2"), 
        preamble, ".")
    # Test with missing colon, wrong syntax, etc.
    malformed = "theorem bad_syntax A B EuclidPoint A = B"
    result = await potential.is_valid_lean(malformed)
    assert not result

@pytest.mark.asyncio
async def test_validator_timeout_recovery():
    val = validator.Validator(".", preamble)
    # Create a theorem that might cause timeout and test recovery
    complex_theorem = "theorem timeout_test (A B C D E F G H I J : EuclidPoint) : A = A := by rfl"
    result = await val.run_lean_check(complex_theorem)
    assert result

@pytest.mark.asyncio
async def test_validator_conclusion_non_trivial():
    val = validator.Validator(".", preamble)
    good_conjecture = """theorem CircleMidpointChordPerpendicular
  (h1 : |O - A| = |O - B|)
  (h2 : isMidpoint M (A - B))
  (h3 : |A - B| ≠ 0)
  : (O - M) ⊥ (A - B) := by algebraic_euclid"""
    result = await val.check_conclusion_non_trivial(good_conjecture)
    assert result

@pytest.mark.asyncio
async def test_validator_conclusion_trivial():
    val = validator.Validator(".", preamble)
    bad_conjecture = "theorem trivial_conclusion (A B C : EuclidPoint) : (A - B) || (A - B) := by algebraic_euclid"
    result = await val.check_conclusion_non_trivial(bad_conjecture)
    assert not result

import json
import fractions
import sys

def float_to_lean_rat(f_val):
    """
    Converts a float to a Lean Rational string representation.
    E.g., 0.5 -> "(1 : Rat)/2" or just "1/2" if we manage coercion.
    Safest is explicit construction or just division of integers.
    Lean `Rat` is often constructed via division of integers. 
    We will output `(num : Rat) / den`.
    """
    # Create an exact fraction from the float
    frac = fractions.Fraction(f_val).limit_denominator(1000000000)
    
    # We construct it as (numerator : Rat) / denominator
    return f"({frac.numerator} : Rat) / {frac.denominator}"

def generate_lean_rat(json_path, output_path):
    with open(json_path, 'r') as f:
        data = json.load(f)

    basis_s = data['basisS']
    centers = data['centers']
    coeffs_a = data['a'] 
    constraints = data['constraints']
    active_indices = data['activeIndices']

    with open(output_path, 'w') as f:
        f.write("import Mathlib.Data.Rat.Defs\n")
        f.write("import Mathlib.Data.Rat.Cast.Defs\n\n")
        f.write("/- \n")
        f.write("  AQEI_Generated_Data_Rat.lean\n")
        f.write("  Auto-generated from Phase 2 Optimization.\n")
        f.write("  Converted to exact Rationals for rigorous verification.\n")
        f.write("-/\n\n")
        
        f.write("namespace AQEIGeneratedRat\n\n")

        # 1. Coefficients (Vertex)
        f.write("/-- Vertex coefficients 'a' as Rationals -/\n")
        f.write("def coefficients : List Rat := [\n")
        for a in coeffs_a:
            f.write(f"  {float_to_lean_rat(a)},\n")
        f.write("]\n\n")

        # 2. Active Constraint Normals (L)
        f.write("/-- The normal vectors L for the active constraints (Rational approximation) -/\n")
        f.write("def active_L : List (List Rat) := [\n")
        for c in constraints:
            L_vec = c['L']
            f.write("  [\n")
            for val in L_vec:
                f.write(f"    {float_to_lean_rat(val)},\n")
            f.write("  ],\n")
        f.write("]\n\n")

        # 3. Active Constraint Bounds (B)
        f.write("/-- The bounds B for the active constraints (Rational approximation) -/\n")
        f.write("def active_B : List Rat := [\n")
        for c in constraints:
            B_val = c['B']
            f.write(f"  {float_to_lean_rat(B_val)},\n")
        f.write("]\n\n")
        
        f.write("end AQEIGeneratedRat\n\n")
        
        # Add axiom checks
        f.write("#print axioms AQEIGeneratedRat.coefficients\n")
        f.write("#print axioms AQEIGeneratedRat.active_L\n")
        f.write("#print axioms AQEIGeneratedRat.active_B\n")

    print(f"Generated {output_path}")

if __name__ == "__main__":
    json_path = "mathematica/results/vertex.json"
    output_path = "lean/src/AQEI_Generated_Data_Rat.lean"
    if len(sys.argv) > 1:
        json_path = sys.argv[1]
    if len(sys.argv) > 2:
        output_path = sys.argv[2]
        
    generate_lean_rat(json_path, output_path)

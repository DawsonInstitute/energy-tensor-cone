import AQEI_Generated_Data_Rat

namespace Phase2Rat

open AQEIGeneratedRat

/--
  VertexVerificationRat.lean

  Formal verification of the vertex property using Exact Rational Arithmetic.
-/

-- Simple Matrix Utilities for Rat
section LinearAlgebra

abbrev Row := List Rat
abbrev Matrix := List Row

-- Subtract projection of pivot from row
-- row <- row - (row[col] / pivot[col]) * pivot
def eliminate (pivot : Row) (row : Row) (col_idx : Nat) : Row :=
  match pivot.get? col_idx, row.get? col_idx with
  | some p_val, some r_val =>
    if p_val == 0 then row
    else
      let factor := r_val / p_val
      List.zipWith (fun r p => r - factor * p) row pivot
  | _, _ => row

-- Exact Gaussian elimination to compute rank
def compute_rank (m : Matrix) : Nat :=
  let n_rows := m.length
  let n_cols := match m.head? with | some r => r.length | none => 0

  let rec reduce (rows : Matrix) (c : Nat) (rank_acc : Nat) : Nat :=
    if c >= n_cols || rows.isEmpty then rank_acc
    else
      -- Find pivot in current column `c` (First non-zero)
      let pivot_idx_opt := rows.findIdx? (fun r => match r.get? c with | some v => v != 0 | none => false)

      match pivot_idx_opt with
      | none =>
        -- No pivot in this column, move to next
        reduce rows (c + 1) rank_acc
      | some pivot_idx =>
        -- Move pivot to top
        let pivot := rows.get! pivot_idx
        let other_rows := rows.eraseIdx pivot_idx

        -- Eliminate this column from other rows
        let new_rows := other_rows.map (fun r => eliminate pivot r c)

        -- Continue
        reduce new_rows (c + 1) (rank_acc + 1)

  reduce m 0 0

end LinearAlgebra

/--
  The Rational verification matrix.
  Rows 1..3: from `active_L` (AQEI constraints).
  Rows 4..6: from Box constraints.

  Indices (0-based) for Box Constraints from previous analysis:
  x1 (idx 1), x2 (idx 2), x5 (idx 5) were active at 100.
-/
def box_rows : Matrix := [
  [0, 1, 0, 0, 0, 0],
  [0, 0, 1, 0, 0, 0],
  [0, 0, 0, 0, 0, 1]
]

def verification_matrix : Matrix :=
  active_L ++ box_rows

def computed_rank : Nat := compute_rank verification_matrix

-- Verify rank is 6
#eval computed_rank

/--
  Rigorous Statement:
  There exists a system of 6 Rational linear constraints (approximating equation verified)
  which are linearly independent. Intersection of these hyperplanes defines a unique point.
-/
theorem active_constraints_full_rank_rat : computed_rank = 6 := by
  rfl

end Phase2Rat

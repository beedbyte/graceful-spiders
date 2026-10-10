import K30Seed
open GracefulBoundary GracefulBoundary.EvenSeedFamily
example : ∃ j, j≤0 ∧ (25=30+24*0-(3+2*0+2*j) ∨
                     25=30+24*0-(3+2*0+2*j+1)) :=
  window_arithmetic 30 3 0 25 (by decide) (by decide) (by decide)

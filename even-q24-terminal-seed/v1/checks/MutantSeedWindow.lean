import K30Seed
open GracefulBoundary GracefulBoundary.EvenSeedFamily
set_option maxRecDepth 8192 in
example : Seed 30 5 seed30 := by constructor; constructor <;> decide; decide

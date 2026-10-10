import K30Seed
open GracefulBoundary GracefulBoundary.EvenSeedFamily
set_option maxRecDepth 8192 in
example : (EvenQ24Rooted.rootWord 30 seed30)[3]?=some 0 := by decide

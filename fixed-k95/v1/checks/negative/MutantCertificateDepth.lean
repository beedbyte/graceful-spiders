import K95Catalog0
import FiniteAlphaTransfer
open GracefulBoundary
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
example : FiniteAlpha.Certificate 46 3 1 K95Catalog.path0 := by unfold FiniteAlpha.Certificate GenericPathCertificate; decide

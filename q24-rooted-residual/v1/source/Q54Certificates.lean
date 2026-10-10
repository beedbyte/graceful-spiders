import Q54Arrays
import FiniteAlphaTransfer
namespace GracefulBoundary.Q54

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem core9_labels : A9.Perm (List.range 54) := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem core9_differences : (edgeDiffs A9).Perm (List.range' 1 53) := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem core6_labels : A6.Perm (List.range 54) := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem core6_differences : (edgeDiffs A6).Perm (List.range' 1 53) := by decide

theorem core9_anchors : A9[0]?=some 9 ∧ A9[36]?=some 53 := by decide
theorem core6_anchors : A6[0]?=some 6 ∧ A6[36]?=some 53 := by decide
theorem core_bridges :
    A9[35]?=some 1 ∧ A9[37]?=some 0 ∧
    A6[35]?=some 0 ∧ A6[37]?=some 1 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem append_C8 : append source_C8 A9=output_C8 := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem append_C7 : append source_C7 A9=output_C7 := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem append_older : append source_older A6=output_older := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem generic_C8 : GenericPathCertificate 34 (coreLabels 142 output_C8) := by
  exact WholeTagged.whole_path_certificate 34 output_C8
    (by decide) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem generic_C7 : GenericPathCertificate 34 (coreLabels 142 output_C7) := by
  exact WholeTagged.whole_path_certificate 34 output_C7
    (by decide) (by decide) (by decide) (by decide) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem generic_older : GenericPathCertificate 34 (coreLabels 142 output_older) := by
  exact WholeTagged.whole_path_certificate 34 output_older
    (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem packet_C8 : FiniteAlpha.Certificate 34 66 65 (coreLabels 142 output_C8) := by
  exact ⟨by decide,by decide,by decide,by decide,generic_C8,by decide,by decide⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem packet_C7 : FiniteAlpha.Certificate 34 66 67 (coreLabels 142 output_C7) := by
  exact ⟨by decide,by decide,by decide,by decide,generic_C7,by decide,by decide⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem packet_older : FiniteAlpha.Certificate 34 68 69 (coreLabels 142 output_older) := by
  exact ⟨by decide,by decide,by decide,by decide,generic_older,by decide,by decide⟩

end GracefulBoundary.Q54

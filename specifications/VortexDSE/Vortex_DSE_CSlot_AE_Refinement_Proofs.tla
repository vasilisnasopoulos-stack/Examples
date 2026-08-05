---------------- MODULE Vortex_DSE_CSlot_AE_Refinement_Proofs ----------------
(***************************************************************************)
(* The agreement layer refines the core, under the identity mapping on the  *)
(* core's variables.                                                        *)
(***************************************************************************)

EXTENDS Vortex_DSE_CSlot_AE_Refinement, TLAPS

THEOREM Refinement == Spec => C!Spec
<1>1. Init => C!Init
  BY DEF Init, C!Init
<1>2. [Next]_vars => [C!Next]_C!vars
  <2> SUFFICES ASSUME Next
               PROVE  [C!Next]_coreVars
    BY DEF vars, coreVars, C!vars
  <2>1. CASE \E id \in MsgIDs : Submit(id)
    BY <2>1 DEF Submit, C!Next
  <2>2. CASE \E n \in Nodes, m \in network : Process(n, m)
    BY <2>2 DEF Process, C!Next
  <2>3. CASE \E n \in Nodes : Freeze(n)
    BY <2>3 DEF Freeze, coreVars, C!vars
  <2>4. CASE Reconcile
    BY <2>4 DEF Reconcile, coreVars, C!vars
  <2>5. CASE \E id \in MsgIDs, k \in Nat : DuplicateInject(id, k)
    BY <2>5 DEF DuplicateInject, C!Next
  <2>6. CASE NextCslot
    BY <2>6 DEF NextCslot, C!Next
  <2>. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next
<1>. QED
  BY <1>1, <1>2, PTL DEF Spec, C!Spec

=============================================================================

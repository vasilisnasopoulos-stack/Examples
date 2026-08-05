---- MODULE MC_Vortex_DSE_CSlot_AE_Refinement ----
(***************************************************************************)
(* TLC harness. The horizon lives here, inside MCNextCslot, for the reason  *)
(* recorded in MC_Vortex_DSE_CSlot.                                         *)
(***************************************************************************)
EXTENDS Vortex_DSE_CSlot_AE_Refinement

CONSTANT MaxSlot

ASSUME MaxSlotAssumption == MaxSlot \in Nat

Slots == 0..MaxSlot

MCNextCslot ==
    /\ current_slot < MaxSlot
    /\ NextCslot

MCNext ==
    \/ \E id \in MsgIDs : Submit(id)
    \/ \E n \in Nodes, m \in network : Process(n, m)
    \/ \E n \in Nodes : Freeze(n)
    \/ Reconcile
    \/ \E id \in MsgIDs, k \in Slots : DuplicateInject(id, k)
    \/ MCNextCslot

MCSpec == Init /\ [][MCNext]_vars

MCTypeInvariant ==
    /\ current_slot \in Slots
    /\ network      \subseteq [id: MsgIDs, cslot: Slots]
    /\ processed    \in [Nodes -> SUBSET MsgIDs]
    /\ persisted    \in [Nodes -> SUBSET MsgIDs]
    /\ node_state   \in [Nodes -> {C!Up, C!Down}]
    /\ phase        \in [Nodes -> {Open, Frozen, Committed}]
    /\ committed    \in [Nodes -> SUBSET MsgIDs]

\* Refinement, checked by TLC as a temporal property. The core's own Next
\* quantifies the forged slot over Nat, which TLC cannot enumerate, so the
\* proxy below is the core's next-state relation with that one quantifier
\* bounded by the same horizon. Nothing else about the core is changed.
MCCoreNext ==
    \/ \E id \in MsgIDs : C!Submit(id)
    \/ \E n \in Nodes, m \in network : C!Process(n, m)
    \/ \E n \in Nodes : C!Crash(n)
    \/ \E n \in Nodes : C!Rejoin(n)
    \/ \E id \in MsgIDs, k \in Slots : C!DuplicateInject(id, k)
    \/ C!Tick

MCRefinement == C!Init /\ [][MCCoreNext]_coreVars

====

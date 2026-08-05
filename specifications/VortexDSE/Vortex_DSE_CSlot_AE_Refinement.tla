------------------- MODULE Vortex_DSE_CSlot_AE_Refinement -------------------
(***************************************************************************)
(* Vortex DSE — the agreement layer as a refinement of the core.           *)
(*                                                                          *)
(* Vortex_DSE_CSlot_AE specifies the Freeze / Reconcile / Commit cycle as   *)
(* a standalone state machine, and is deliberately not a refinement of      *)
(* anything: its NextCslot clears processed for every node at a slot        *)
(* boundary, which no action of Vortex_DSE_CSlot can do, and it models no   *)
(* crash. Presenting it as a layer on top of the core was therefore an      *)
(* overstatement.                                                           *)
(*                                                                          *)
(* This module is the layer. It carries the core's variables unchanged and  *)
(* adds the two the agreement phase needs, and every action either is a     *)
(* core action or leaves the core's variables alone:                        *)
(*                                                                          *)
(*   Submit, DuplicateInject   are the core's                               *)
(*   Process                   is the core's, additionally gated on Open    *)
(*   NextCslot                 is the core's Tick                           *)
(*   Freeze, Reconcile         change only phase and committed              *)
(*                                                                          *)
(* processed accumulates, as in the core; the per-slot input set lives in   *)
(* committed instead of being recovered by wiping processed.                *)
(*                                                                          *)
(* Crash and Rejoin are absent. That costs nothing here: refinement asks    *)
(* that every behaviour of this module be a behaviour of the core, not the  *)
(* reverse, so a layer may exercise fewer of the core's actions than the    *)
(* core allows.                                                             *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, MsgIDs

ASSUME NodesAssumption  == IsFiniteSet(Nodes)  /\ Nodes  # {}
ASSUME MsgIDsAssumption == IsFiniteSet(MsgIDs)

Open      == "open"
Frozen    == "frozen"
Committed == "committed"

VARIABLES
    current_slot,    \* core: global slot counter
    network,         \* core: in-flight messages
    processed,       \* core: ids admitted by each node, cumulative
    persisted,       \* core: crash snapshot; constant here
    node_state,      \* core: liveness; constant here
    phase,           \* phase[n] \in {Open, Frozen, Committed}
    committed        \* committed[n] = agreed input set after Reconcile

coreVars == <<current_slot, network, processed, persisted, node_state>>
vars     == <<current_slot, network, processed, persisted, node_state,
              phase, committed>>

\* The core, over the same variable names.
C == INSTANCE Vortex_DSE_CSlot

MsgRecord == [id: MsgIDs, cslot: Nat]

-------------------------------------------------------------------------------
(*                              INITIAL STATE                               *)

Init ==
    /\ current_slot = 0
    /\ network      = {}
    /\ processed    = [n \in Nodes |-> {}]
    /\ persisted    = [n \in Nodes |-> {}]
    /\ node_state   = [n \in Nodes |-> C!Up]
    /\ phase        = [n \in Nodes |-> Open]
    /\ committed    = [n \in Nodes |-> {}]

-------------------------------------------------------------------------------
(*                                ACTIONS                                   *)

\* Core actions, with the agreement variables left alone.

Submit(id) ==
    /\ C!Submit(id)
    /\ UNCHANGED <<phase, committed>>

DuplicateInject(id, fake_cslot) ==
    /\ C!DuplicateInject(id, fake_cslot)
    /\ UNCHANGED <<phase, committed>>

\* Admission, additionally closed once the node has frozen. The core admits
\* on m.cslot <= current_slot; here the gate is equality, which is stronger,
\* so every step of this action is still a step of the core's.
Process(n, m) ==
    /\ phase[n] = Open
    /\ m.cslot = current_slot
    /\ C!Process(n, m)
    /\ UNCHANGED <<phase, committed>>

\* Advancing the slot is exactly the core's Tick: processed is carried over
\* rather than cleared.
NextCslot ==
    /\ \A n \in Nodes : phase[n] = Committed
    /\ C!Tick
    /\ phase'     = [n \in Nodes |-> Open]
    /\ UNCHANGED committed

-------------------------------------------------------------------------------
\* Agreement actions. These touch none of the core's variables, so they are
\* stuttering steps of the core.

Freeze(n) ==
    /\ n \in Nodes
    /\ phase[n] = Open
    /\ phase' = [phase EXCEPT ![n] = Frozen]
    /\ UNCHANGED <<coreVars, committed>>

Reconcile ==
    /\ \A n \in Nodes : phase[n] = Frozen
    /\ LET union_view == UNION { processed[n] : n \in Nodes }
       IN committed' = [n \in Nodes |-> union_view]
    /\ phase' = [n \in Nodes |-> Committed]
    /\ UNCHANGED coreVars

-------------------------------------------------------------------------------

Next ==
    \/ \E id \in MsgIDs : Submit(id)
    \/ \E n \in Nodes, m \in network : Process(n, m)
    \/ \E n \in Nodes : Freeze(n)
    \/ Reconcile
    \/ \E id \in MsgIDs, k \in Nat : DuplicateInject(id, k)
    \/ NextCslot

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------
(*                               INVARIANTS                                 *)

TypeInvariant ==
    /\ current_slot \in Nat
    /\ network      \subseteq MsgRecord
    /\ processed    \in [Nodes -> SUBSET MsgIDs]
    /\ persisted    \in [Nodes -> SUBSET MsgIDs]
    /\ node_state   \in [Nodes -> {C!Up, C!Down}]
    /\ phase        \in [Nodes -> {Open, Frozen, Committed}]
    /\ committed    \in [Nodes -> SUBSET MsgIDs]

\* Nodes that have committed hold the same set.
MerkleAgreement ==
    \A a, b \in Nodes :
        (phase[a] = Committed /\ phase[b] = Committed) =>
            committed[a] = committed[b]

\* Committing never drops what a node admitted locally.
CommittedSupersetsProcessed ==
    \A n \in Nodes :
        phase[n] = Committed => processed[n] \subseteq committed[n]

\* Nothing is committed that was never in the network.
NoPhantomInCommitted ==
    \A n \in Nodes :
        \A id \in committed[n] : \E m \in network : m.id = id

\* Nodes move Open -> Frozen -> Committed and reopen only on a slot change,
\* so no node is ever behind a peer by more than one phase in a way that
\* would let Reconcile run on a mixed view.
PhaseProgressionValid ==
    (\E n \in Nodes : phase[n] = Committed) =>
        (\A n \in Nodes : phase[n] # Open)

-------------------------------------------------------------------------------
(*                              REFINEMENT                                  *)
(*                                                                          *)
(* Every behaviour of this module is a behaviour of Vortex_DSE_CSlot, under *)
(* the identity mapping on the core's variables. Stated and proved in       *)
(* Vortex_DSE_CSlot_AE_Refinement_Proofs.                                   *)

=============================================================================

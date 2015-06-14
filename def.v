(** Definitions pour le display calcul *)

Require Import List.
Require Import ZArith.
(*Require Import Znumtheory.
Require Import Bool.
Require Import Psatz.*)
SearchAbout (nat -> nat -> bool).
(*NPeano.Nat.eqb: nat -> nat -> bool*)


(* Connecteurs *)
Definition connector := (nat * nat)%type.

Definition arity (c : connector) := snd c.

(* The set str_con_adj gives the couple of adjoints
(c1, c2) is the couple s.t. c1 -| c2 *)
Parameter str_con_adj : (connector * connector)%type.


(*Definition is_adjoint :  (c1 : connector) (c2 : connector)
 : bool :=
if (c1,c2) in str_con_adj then true else false.*)


(*Fixpoint is_adjoint ( c1 c2 : connector ) : bool :=
if (c1, c2) : str_con_adj then true else false.
*)


(* Signature, formules, structures *)
Record SequentSystemSignature := mkSequentSystemSignature {
  logical_connectors      : list connector;
  structural_connectors : list connector
}.


Inductive formula : Set :=
| Var : nat -> formula 
| App : connector -> list formula -> formula.

Inductive structure : Set :=
| Atomic : formula -> structure
| FHole : nat -> structure
| SHole : nat -> structure
| SApp : connector -> list structure -> structure.

Inductive wf_formula (S : SequentSystemSignature) : formula -> Prop :=
| wfVar : forall x, wf_formula S (Var x)
| wfApp : 
  forall c, In c (logical_connectors S) ->
  forall fs, List.length fs = arity c ->
  (forall f, In f fs -> wf_formula S f) ->
  wf_formula S (App c fs).

Inductive wf_structure (S : SequentSystemSignature) : structure -> Prop :=
| wfAtomic : forall f : formula , wf_formula S f -> wf_structure  S ( Atomic f )
| wfFHole : forall hf, wf_structure S (FHole hf) 
| wfSHole : forall hs, wf_structure S (SHole hs)
| wfSApp : forall c, In c (structural_connectors S) ->
  forall ss, List.length ss = arity c ->
  (forall X, In X ss -> wf_structure S X) ->
  wf_structure S (SApp c ss).

(* Sequents *)
Definition sequent : Set := (structure * structure)%type.

Definition wf_sequent (S : SequentSystemSignature) (seq : sequent) : Prop :=
 wf_structure S ( fst seq ) /\ wf_structure S ( snd seq ).

(* Rules : axioms, strustural rules, display rules *)
Inductive rule : Set :=
| RAxiom : sequent -> rule
| RStructural : nat -> list sequent -> sequent -> rule
| RDisplay : sequent -> sequent -> rule.

Inductive wf_rule (S : SequentSystemSignature) : rule -> Prop :=
| wfRAxiom : forall seq, wf_sequent S seq ->  wf_rule S ( RAxiom seq )
| wfRStructural : forall x, forall lseq, forall seq_ccl,
List.length lseq = x -> 
(forall seq_premise, In seq_premise lseq -> wf_sequent S seq_premise ) ->
wf_sequent S seq_ccl ->
wf_rule S ( RStructural x lseq seq_ccl )
| wfRDisplay_LR : forall seq1 seq2, 
wf_sequent S seq1 ->
wf_sequent S seq2 -> 
(* seq1 = o X |- Y *)
(* seq2 = X |- o' Y *)
(* (o,o') are adjoints *)  
wf_rule S ( RDisplay seq1 seq2 ).

Print formula.

Inductive eq_f (f1 f2 : formula) : bool :=

if f1 = f2 then true else false.

eq_var : forall x, eq_f ( Var x ) ( Var x ) -> true
.


Definition str_is_subformula (S : SequentSystemSignature) 
(f : formula) (s : structure) : bool :=
match s with
| Atomic(f1) =>  f = f1 -> true
| _ => true
end.



(** /!\ Faut-il définir précisément 
qu'une règle de display parle de 2 connecteurs liés 
par adjonction ou résiduation *)


(** Definition of the C1, ... C8 conditions *)

(** C1 : Preservation of formulas *)












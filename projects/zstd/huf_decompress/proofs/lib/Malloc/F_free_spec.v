(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (4 recorded proofs replaced by written proofs (lb_remove_lbrm, NoDup_map_perm, lbrm_perm and 1 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free MallocTree MallocBlocks MallocHINV MallocFacts_B MallocFacts_B_reach Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf F_free_K F_free.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_free_spec () := "C35stdpp4base6LookupC59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapI46Stdlib7Sorting;Permutation;Permutation00C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib6Malloc6F_free@NoDup_map_inj_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc6F_free=filter_ext_inC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation>Permutation_inC45stdpp>list_relations4list9NoDup_nilC59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib6Malloc<MallocBlocks6blk_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<Malloc_iface8bptr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool7Is_trueC59OSSVerify5KrLib6Malloc<MallocBlocks8blk_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C35stdpp9decidable;Is_true_decC59OSSVerify5KrLib6MallocAMallocFacts_Bpres>aptr_eqb_spec'C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic3and01C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z8eqb_reflC47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc<Malloc_iface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc6F_free4lbrmC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C46Stdlib7Sorting;Permutation?Permutation_mapC46Stdlib7Sorting;PermutationAPermutation_NoDupC45stdpp>list_relations4listBfilter_Permutationc59OSSVerify5KrLib6Malloc;F_free_spec9lbrm_permC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma lb_remove_lbrm LB (p : bptr) A n : List.NoDup (map blk_slot LB) -> In (p, A, n) LB ->
  lb_remove p LB = lbrm LB (p, A, n).
Proof.
  intros ND Hin. unfold lb_remove, lbrm. apply filter_ext_in. intros x Hx.
  unfold bptr_eqb, blk_id, blk_slot. cbn [fst snd].
  destruct (aptr_eqb_spec' (fst (fst (fst x))) (fst p)) as [E|NE]; cbn [andb negb].
  - pose proof (NoDup_map_inj_in blk_slot LB ND x (p, A, n) Hx Hin E) as ->. cbn. rewrite Z.eqb_refl. cbn. tauto.
  - tauto.
Qed.

Lemma NoDup_map_perm {A B} (f : A -> B) (l l' : list A) : Permutation l l' -> List.NoDup (map f l) -> List.NoDup (map f l').
Proof. intros P ND. eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND]. Qed.

Lemma lbrm_perm LB LB' blk : Permutation LB LB' -> Permutation (lbrm LB blk) (lbrm LB' blk).
Proof. intros P. unfold lbrm. apply filter_Permutation. exact P. Qed.

Lemma In_lbrm_perm LB LB' blk b : Permutation LB LB' -> In b (lbrm LB blk) -> In b (lbrm LB' blk).
Proof. intros P H. eapply Permutation_in; [apply lbrm_perm; exact P| exact H]. Qed.

(* [comment removed for export] *)
Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis LO : ATOP <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.

Let FPT := fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 107900 <= a < 107904.
End FP.

End CANSEC1.

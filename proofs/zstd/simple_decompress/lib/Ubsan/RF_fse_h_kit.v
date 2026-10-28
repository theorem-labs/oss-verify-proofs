(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg StdioFiles.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio Malloc Harness Prog.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition hideP (P : Prop) : Prop := P.

(* [comment removed for export] *)
Lemma implM_post_evt : forall {St A} (c : Monad.M St A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
  implM usegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt usegs (Q' a s') ms') ->
  implM usegs c s Q' ms.
Proof.
  intros St A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt'; [exact H|].
  intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact I| apply HQ; exact H'].
Qed.

(* [comment removed for export] *)
Lemma errno_lit : bv_unsigned (Z_to_bv 64 RATP) + -164 = RERRNO.
Proof. unfold RATP, RERRNO. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rheap_pres_of_munch : forall LB SP W m m',
  munch W m m' -> wmono usegs m m' ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a) ->
  rheap_pres LB SP m m'.
Proof.
  intros LB SP W m m' MU WM OUT a Ha Hc. split.
  - apply MU. unfold wa. rewrite unsigned_lit by lia. apply OUT; assumption.
  - intros Hv. apply WM. exact Hv.
Qed.

(* [comment removed for export] *)
Lemma RHEAP_stack_frame : forall s LB m m' W,
  RHEAP s LB m -> munch W m m' -> wmono usegs m m' ->
  Forall (fun iv => ATOP <= fst iv) W -> RHEAP s LB m'.
Proof.
  intros s LB m m' W HP MU WM FW. eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
  eapply Forall_impl; [| exact FW]. intros iv H. left. exact H.
Qed.

Lemma rauxv_ok_stack_frame : forall m m' B W,
  rauxv_ok m B -> munch W m m' -> wmono usegs m m' ->
  Forall (fun iv => ATOP <= fst iv /\ snd iv <= B) W -> rauxv_ok m' B.
Proof.
  intros m m' B W AUX MU WM FW. eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
  eapply Forall_impl; [| exact FW]. intros [lo hi] [H1 H2]. cbn [fst snd] in *. unfold RAUXV_CELL in *. atop_facts. lia.
Qed.

(* [comment removed for export] *)
Lemma RHEAP_disjoint_head : forall s p P n LB m b,
  RHEAP s ((p, P, n) :: LB) m -> In b LB -> P + n <= blk_addr b \/ blk_addr b + blk_size b <= P.
Proof.
  intros s p P n LB m b HP Hb.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP) as ND.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (p, P, n) b HP ltac:(left; reflexivity) ltac:(right; exact Hb)) as D.
  cbn [blk_id blk_addr blk_size fst snd] in D. apply D. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst.
  intros E. apply NI. rewrite E. apply in_map_iff. exists b. split; [reflexivity| exact Hb].
Qed.

Lemma blocks_distinct_disjoint : forall s LBX LB m b b',
  RHEAP s (LBX ++ LB) m -> In b LBX -> In b' LB ->
  blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b.
Proof.
  intros s LBX LB m b b' HP Hb Hb'.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP) as ND. rewrite map_app in ND.
  apply (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ b b' HP); [apply in_app_iff; left; exact Hb| apply in_app_iff; right; exact Hb'|].
  intros E. destruct (in_split _ _ Hb') as (l1 & l2 & ->). rewrite map_app in ND. cbn [map] in ND. rewrite app_assoc in ND.
  apply List.NoDup_remove_2 in ND. apply ND. apply in_app_iff. left. apply in_app_iff. left. rewrite <- E. apply in_map_iff. exists b; auto.
Qed.

Lemma outside_of_forall : forall W x, (forall iv, In iv W -> ~ (fst iv <= x < snd iv)) -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn; [exact I|]. split.
  - exact (H (lo, hi) ltac:(left; reflexivity)).
  - apply IH. intros iv Hiv. apply H. right; exact Hiv.
Qed.

Lemma disjoint_from_of_forall : forall W a n, (forall iv, In iv W -> a + n <= fst iv \/ snd iv <= a) -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; cbn; [exact I|]. split.
  - exact (H (lo, hi) ltac:(left; reflexivity)).
  - apply IH. intros iv Hiv. apply H. right; exact Hiv.
Qed.

(* [comment removed for export] *)
Definition fh_fp_ok (LBX : list block) (SPC : Z) (iv : Z * Z) : Prop :=
  (ATOP <= fst iv /\ snd iv <= SPC)
  \/ (exists b, In b LBX /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Lemma fh_transport : forall s LBX LB m m' W AB SPC,
  RHEAP s (LBX ++ LB) m -> munch W m m' -> wmono usegs m m' ->
  Forall (fh_fp_ok LBX SPC) W -> ATOP <= SPC <= AB ->
  RHEAP s (LBX ++ LB) m'
  /\ (rauxv_ok m AB -> rauxv_ok m' AB)
  /\ (forall errv, rw_cells usegs m RERRNO [C4 errv] -> rw_cells usegs m' RERRNO [C4 errv])
  /\ rheap_pres LB SPC m m'.
Proof.
  intros s LBX LB m m' W AB SPC HP MU WM FW HS.
  assert (BLK : forall b, In b LBX -> rblock_range (blk_addr b) (blk_size b)).
  { intros b Hb. eapply RMalloc_ifaceP.RHEAP_block_range_proof; [exact HP| apply in_app_iff; left; exact Hb]. }
  assert (OUT : forall a, (SPC <= a \/ (0x10000 <= a < 0x69000) \/ in_block LB a) -> outside W a).
  { intros a Ha. apply outside_of_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as [[F1 F2]|(b & Hb & F1 & F2)].
    - destruct Ha as [Ha|[Ha|(b' & Hb' & R1 & R2)]]; [lia| atop_facts; lia|].
      pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP ltac:(apply in_app_iff; right; exact Hb')) as (_ & _ & _ & R4 & _). lia.
    - pose proof (BLK b Hb) as (B1 & B2 & B3 & B4 & B5).
      destruct Ha as [Ha|[Ha|(b' & Hb' & R1 & R2)]]; [atop_facts; lia| lia|].
      pose proof (blocks_distinct_disjoint _ _ _ _ b b' HP Hb Hb'). lia. }
  split; [| split; [| split]].
  - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros iv [[F1 F2]|(b & Hb & F1 & F2)]; [left; exact F1|].
    right; right. exists b. split; [apply in_app_iff; left; exact Hb| lia].
  - intros AUX.
    eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros iv [[F1 F2]|(b & Hb & F1 & F2)]; [unfold RAUXV_CELL in *; atop_facts; lia|].
    pose proof (BLK b Hb) as (B1 & B2 & B3 & B4 & B5). unfold RAUXV_CELL in *. atop_facts. lia.
  - intros errv ERR. eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
    apply disjoint_from_of_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as [[F1 F2]|(b & Hb & F1 & F2)].
    + unfold RERRNO in *. atop_facts. lia.
    + pose proof (BLK b Hb) as (B1 & B2 & B3 & B4 & B5). unfold RERRNO in *. lia.
  - eapply rheap_pres_of_munch; [exact MU| exact WM|]. intros a Ha Hc. apply OUT.
    destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc| right; left; lia| right; right; exact Hc].
Qed.

End CANSEC1.

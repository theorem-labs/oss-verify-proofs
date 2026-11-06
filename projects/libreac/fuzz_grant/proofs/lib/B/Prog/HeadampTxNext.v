(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contract of reac_headamp_tx_next for fuzz_grant.asan; tnext_kept and tnext_post adapted from proofs/cgif/cgif_file_fuzzer/lib/YC20.v (tlzw_kept, tlzw_post). *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/HeadampTxNext.v at a working branch afd75724b5b (blob 95ee256830c, the blob the walk was ported from), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; the shared definitions, model bridge and six cut statements of the walk; frame 96 and NX_STK = STK_reac_headamp_tx_next because image B calls reac_headamp_tx_effective at 0x863dc where image A inlines it; past the prologue the table is in s0 (atom 8) and the value pointer in s1 (atom 9); the shadow-base cell is object 35; atom facts are the fields' machine ranges because the contract gives thd_replay_ok, not I1; the .rodata divisor image B's scan reads is GrantBContracts.v's IMG_NEXT_DIV3 *)
(* reac_headamp_tx_next (image B 0x85efc, 465 instructions, 35 instrumented accesses, one call):
   what every segment of the walk shares.

   Image B differs from image A (0x850cc) in five ways the walk carries:
     - its frame is 96 bytes and it saves ra and s0..s10 (image A: 80 bytes, ra and s0..s8), and the
       window it needs below its entry sp reaches past that frame because it CALLS
       reac_headamp_tx_effective (0x863dc): NX_STK is GrantBContracts.STK_reac_headamp_tx_next;
     - the UBSan build adds 18 trap guards to the one `unimp` at 0x8644c;
     - the dirty scan divides by 3 with mulhu, not with the byte multiply image A uses;
     - image A inlines reac_headamp_tx_effective into the replay emit; image B calls it;
     - the contract gives only `thd_replay_ok T` about the table's fields, never image A's whole I1,
       so every atom fact below is the field's plain machine range, and the replay bound
       0 <= replay_idx enters in the segments that know the width is not 0.

   Image-B boundary rule: this file never uses off_img or a `*_imgP` lemma (image A's carry image A's top
   0x5fa000; on the integration tree off_img is lib/B/YCbq.v's, over image B's top 0x5fb000; the walk does not
   depend on which); it uses blk_off_imgB (lib/B/Prog/GrantPaLib.v:324) with
   IMG_LO_B_val / IMG_TOP_B_val (GrantTop.v:33, :35). The shadow-base cell is listing object 35 on
   image B (image A: 32). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* The model's branches are full of `j / 3`, `j mod 3` and the shadow's `a / 8`, and zify turns
   every one of them into a euclidean-division equation before lia runs, which is what makes a
   goal of this file take minutes instead of milliseconds. The unit's heavy walks switch it off the
   same way (lib/A/Prog/CtrlChecksumVerify.v:28, CtrlBuildGrantSweep.v:45): where a proof here
   really needs the division, it says `Z.div_mod_to_equations` itself. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The address-free table layout image A's leaf states; GrantBContracts names it the same way. *)
#[local] Notation TX_SIZE := ATx.TX_SIZE.
#[local] Notation LAY_TX := ATx.LAY_TX.
#[local] Notation tx_vals := ATx.tx_vals.
#[local] Notation tx_fbyte := ATx.tx_fbyte.

(* The addresses this call may change outside its own machine-stack window. *)
Definition nx_touch (tx chp parp valp a : Z) : Prop :=
  (tx <= a < tx + TX_SIZE) \/ a = chp \/ a = parp \/ a = valp.

(* Image B's own frame, and the window it needs below its entry sp (its frame plus the one
   callee's window). *)
Definition NX_FRAME : Z := 96.
Definition NX_STK : Z := STK_reac_headamp_tx_next.

Lemma nx_stk_val : NX_STK = 4208.
Proof. reflexivity. Qed.

Lemma nx_frame_val : NX_FRAME = 96.
Proof. reflexivity. Qed.

Lemma nx_frame_le : NX_FRAME <= NX_STK.
Proof. rewrite nx_stk_val. unfold NX_FRAME. lia. Qed.

(* ---- the model's answer, and the table invariant the contract carries ---------------------- *)
Definition nxT (res : nres) : list byte := snd res.

Lemma fd_range : forall n T i0 i, first_dirty_from T i0 n = Some i -> i0 <= i < i0 + Z.of_nat n.
Proof.
  induction n as [|n IH]; intros T i0 i H; cbn [first_dirty_from] in H; [discriminate|].
  destruct (tb T (288 + i0) =? 0) eqn:Hz.
  - pose proof (IH T (i0 + 1) i H). lia.
  - injection H as <-. lia.
Qed.

Lemma fd_none : forall n T i0,
  (forall l, i0 <= l < i0 + Z.of_nat n -> tb T (288 + l) = 0) -> first_dirty_from T i0 n = None.
Proof.
  induction n as [|n IH]; intros T i0 H; [reflexivity|].
  cbn [first_dirty_from]. rewrite (proj2 (Z.eqb_eq _ 0) (H i0 ltac:(lia))).
  apply IH. intros l Hl. apply H. lia.
Qed.

Lemma fd_some : forall n T i0 i,
  i0 <= i < i0 + Z.of_nat n ->
  (forall l, i0 <= l < i -> tb T (288 + l) = 0) -> tb T (288 + i) <> 0 ->
  first_dirty_from T i0 n = Some i.
Proof.
  induction n as [|n IH]; intros T i0 i Hr Hz Hnz; [lia|].
  cbn [first_dirty_from].
  destruct (Z.eqb_spec (tb T (288 + i0)) 0) as [E|E].
  - apply (IH T (i0 + 1) i); [|intros l Hl; apply Hz; lia | exact Hnz].
    assert (i <> i0) by (intros Heq; rewrite Heq in Hnz; exact (Hnz E)). lia.
  - assert (i = i0) as ->; [|reflexivity].
    destruct (Z.eq_dec i i0) as [Heq|Hne]; [exact Heq|].
    exfalso. apply E. apply Hz. lia.
Qed.

Lemma u32_agree : forall T1 T2 k, tb T1 k = tb T2 k -> tb T1 (k + 1) = tb T2 (k + 1) ->
  tb T1 (k + 2) = tb T2 (k + 2) -> tb T1 (k + 3) = tb T2 (k + 3) -> u32 T1 k = u32 T2 k.
Proof. intros T1 T2 k H0 H1 H2 H3. unfold u32. rewrite H0, H1, H2, H3. reflexivity. Qed.

Lemma s32_agree : forall T1 T2 k, u32 T1 k = u32 T2 k -> s32 T1 k = s32 T2 k.
Proof. intros T1 T2 k H. unfold s32. rewrite H. reflexivity. Qed.

Lemma thd_ok_set4_out : forall T k v,
  length T = 460%nat -> 0 <= k -> k + 4 <= 460 -> (k + 4 <= 437 \/ 443 < k) ->
  thd_replay_ok T -> thd_replay_ok (set4 T k v).
Proof.
  intros T k v HL Hk0 Hk4 Hout H. unfold thd_replay_ok in *.
  rewrite (tb_set4_out T k v 437) by lia.
  assert (HU : u32 (set4 T k v) 440 = u32 T 440)
    by (apply u32_agree; apply tb_set4_out; first [exact HL | lia]).
  rewrite (s32_agree _ _ _ HU). exact H.
Qed.

Lemma thd_ok_setb_out : forall T k v,
  length T = 460%nat -> 0 <= k < 460 -> k <> 437 -> (k < 440 \/ 443 < k) ->
  thd_replay_ok T -> thd_replay_ok (setb T k v).
Proof.
  intros T k v HL Hk Hne Hout H. unfold thd_replay_ok in *.
  rewrite (tb_setb_out T k v 437) by lia.
  assert (HU : u32 (setb T k v) 440 = u32 T 440)
    by (apply u32_agree; apply tb_setb_out; first [exact HL | lia]).
  rewrite (s32_agree _ _ _ HU). exact H.
Qed.

(* One byte of a one-byte write, read back. *)
Lemma le1_bytes : forall u, 0 <= u < 2 ^ 64 -> le1 (Z_to_bv 64 u) = [Z_to_bv 8 u].
Proof.
  intros u Hu. unfold le1. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite (Z.mod_small u) by (change (2 ^ Z.of_N 64) with 18446744073709551616; lia).
  reflexivity.
Qed.

Lemma tb_setb_in : forall T k v, length T = 460%nat -> 0 <= k < 460 -> 0 <= v < 256 ->
  tb (setb T k v) k = v.
Proof.
  intros T k v HL Hk Hv. unfold tb, setb. rewrite nth_as_error.
  rewrite upd_bytes_nth by (rewrite ?length_le1; lia).
  rewrite length_le1.
  replace (Nat.leb (Z.to_nat k) (Z.to_nat k) && Nat.ltb (Z.to_nat k) (Z.to_nat k + 1))%bool with true
    by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
  replace (Z.to_nat k - Z.to_nat k)%nat with 0%nat by lia.
  rewrite le1_bytes by lia. cbn [nth_error].
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_small. lia.
Qed.

Lemma thd_ok_w0 : forall T, length T = 460%nat -> thd_replay_ok (setb T 437 0).
Proof.
  intros T HL. unfold thd_replay_ok. intros Hne. exfalso. apply Hne.
  apply tb_setb_in; [exact HL | lia | lia].
Qed.

Lemma thd_ok_idx : forall T v,
  length T = 460%nat -> 0 <= v < 2147483648 -> thd_replay_ok (set4 T 440 v).
Proof.
  intros T v HL Hv. unfold thd_replay_ok. intros _.
  rewrite (s32_set4 T 440 v) by lia. lia.
Qed.

(* lia does not evaluate `2 ^ 64`, and the walk's address bounds are all stated against it. *)
Ltac lia64 := change (2 ^ 64) with 18446744073709551616 in *; lia.

(* Peel a tower of set4 / setb down to the table it was built from. *)
Ltac lentac := repeat first [ apply len_set4 | apply len_setb | eassumption | lia ].

Lemma len_resweep : forall T, length T = 460%nat -> length (nxT (resweep T)) = 460%nat.
Proof.
  intros T HL. unfold nxT, resweep.
  destruct (u32 T 452 =? 0); [exact HL|].
  destruct (tb T 450 =? 0); [exact HL|].
  destruct (u32 T 452 <=? (u32 T 456 + 1) mod 4294967296); cbn [snd silent];
    repeat first [ apply len_set4 | apply len_setb | exact HL | lia ].
Qed.

Lemma thd_ok_resweep : forall T,
  length T = 460%nat -> thd_replay_ok T -> thd_replay_ok (nxT (resweep T)).
Proof.
  intros T HL H. unfold nxT, resweep.
  destruct (u32 T 452 =? 0); [exact H|].
  destruct (tb T 450 =? 0); [exact H|].
  destruct (u32 T 452 <=? (u32 T 456 + 1) mod 4294967296); cbn [snd silent].
  - (* the re-arm: the cursor is stored as 0, so the invariant holds of the new table *)
    apply thd_ok_set4_out; [lentac | lia | lia | right; lia |].
    apply thd_ok_idx; [lentac | lia].
  - (* only the silence counter moved *)
    apply thd_ok_set4_out; [exact HL | lia | lia | right; lia | exact H].
Qed.

Lemma thd_ok_walk : forall n T t bs o total j,
  length T = 460%nat -> 0 <= j < total -> total <= 765 -> thd_replay_ok T ->
  thd_replay_ok (nxT (walk T t bs o total j n)).
Proof.
  induction n as [|n IH]; intros T t bs o total j HL Hj Htot H.
  - cbn [walk]. unfold nxT, silent. cbn [snd]. exact H.
  - rewrite walk_step. cbv zeta.
    set (T1 := set4 T 440 (j + 1)).
    assert (HL1 : length T1 = 460%nat) by (unfold T1; apply len_set4; [exact HL | lia | lia]).
    assert (H1 : thd_replay_ok T1) by (unfold T1; apply thd_ok_idx; [exact HL | lia]).
    destruct (carried T1 bs o j) eqn:Hc.
    + unfold emit_res, nxT. cbn [snd].
      destruct (j + 1 <? total) eqn:Hlt.
      * apply thd_ok_set4_out; [apply len_set4; [exact HL1 | lia | lia] | lia | lia | right; lia |].
        apply thd_ok_set4_out; [exact HL1 | lia | lia | right; lia | exact H1].
      * apply thd_ok_set4_out; [apply len_setb; [exact HL1 | lia] | lia | lia | right; lia |].
        apply thd_ok_w0. exact HL1.
    + destruct (j + 1 =? total) eqn:He.
      * apply thd_ok_resweep; [apply len_setb; [exact HL1 | lia]|]. apply thd_ok_w0. exact HL1.
      * apply Z.eqb_neq in He. apply IH; [exact HL1 | lia | lia | exact H1].
Qed.

Lemma thd_ok_after : forall T t,
  length T = 460%nat -> thd_replay_ok T -> thd_replay_ok (nxT (after_scan T t)).
Proof.
  intros T t HL H. unfold after_scan.
  destruct (tb T 437 =? 0) eqn:Hw.
  - apply thd_ok_resweep; [exact HL | exact H].
  - apply Z.eqb_neq in Hw.
    destruct (0 <? s32 T 444) eqn:Hwt.
    + unfold nxT, silent. cbn [snd].
      apply thd_ok_set4_out; [exact HL | lia | lia | right; lia | exact H].
    + destruct (3 * tb T 437 <=? s32 T 440) eqn:Hdone.
      * apply thd_ok_resweep; [apply len_setb; [exact HL | lia]|]. apply thd_ok_w0. exact HL.
      * apply Z.leb_gt in Hdone.
        pose proof (tb_range T 437) as Hr.
        apply thd_ok_walk; [exact HL | split; [exact (H Hw) | exact Hdone] | lia | exact H].
Qed.

(* The contract's table invariant is kept by the model, from the invariant alone. *)
Lemma thd_ok_next : forall T tx,
  length T = 460%nat -> thd_replay_ok T -> thd_replay_ok (nxT (next_model T tx)).
Proof.
  intros T tx HL H. unfold next_model.
  destruct ((u32 T 432 =? 0) && (tb T 437 =? 0))%bool; [exact H|].
  destruct (first_dirty_from T 0 144) as [i|] eqn:Hfd.
  - pose proof (fd_range 144%nat T 0 i Hfd) as Hi. cbn [Z.of_nat] in Hi.
    unfold edge_res, nxT. cbn [snd].
    apply thd_ok_set4_out; [apply len_setb; [exact HL | lia] | lia | lia | right; lia |].
    apply thd_ok_setb_out; [exact HL | lia | lia | left; lia | exact H].
  - apply thd_ok_after; [exact HL | exact H].
Qed.

(* The model's length is 460 at every answer: the three return sites need it for the table. *)
Lemma len_walk : forall n T t bs o total j,
  length T = 460%nat -> length (nxT (walk T t bs o total j n)) = 460%nat.
Proof.
  induction n as [|n IH]; intros T t bs o total j HL; [exact HL|].
  rewrite walk_step. cbv zeta.
  set (T1 := set4 T 440 (j + 1)).
  assert (HL1 : length T1 = 460%nat) by (unfold T1; apply len_set4; [exact HL | lia | lia]).
  destruct (carried T1 bs o j).
  - unfold emit_res, nxT. cbn [snd].
    destruct (j + 1 <? total);
      repeat first [ apply len_set4 | apply len_setb | exact HL1 | lia ].
  - destruct (j + 1 =? total).
    + apply len_resweep. repeat first [ apply len_setb | exact HL1 | lia ].
    + apply IH. exact HL1.
Qed.

Lemma len_after : forall T t, length T = 460%nat -> length (nxT (after_scan T t)) = 460%nat.
Proof.
  intros T t HL. unfold after_scan.
  destruct (tb T 437 =? 0); [apply len_resweep; exact HL|].
  destruct (0 <? s32 T 444).
  - unfold nxT, silent. cbn [snd]. repeat first [ apply len_set4 | exact HL | lia ].
  - destruct (3 * tb T 437 <=? s32 T 440).
    + apply len_resweep. repeat first [ apply len_setb | exact HL | lia ].
    + apply len_walk. exact HL.
Qed.

Lemma len_next : forall T tx, length T = 460%nat -> length (nxT (next_model T tx)) = 460%nat.
Proof.
  intros T tx HL. unfold next_model.
  destruct ((u32 T 432 =? 0) && (tb T 437 =? 0))%bool; [exact HL|].
  destruct (first_dirty_from T 0 144) as [i|] eqn:Hfd.
  - pose proof (fd_range 144%nat T 0 i Hfd) as Hi. cbn [Z.of_nat] in Hi.
    unfold edge_res, nxT. cbn [snd].
    repeat first [ apply len_set4 | apply len_setb | exact HL | lia ].
  - apply len_after. exact HL.
Qed.

(* Which case of the model the machine takes, from the branches the walk has settled. *)
Lemma u32at_u32 : forall T k, u32at T k = u32 T k. Proof. reflexivity. Qed.
Lemma s32at_s32 : forall T k, s32at T k = s32 T k. Proof. reflexivity. Qed.

Lemma nx_model_silent : forall T t, u32 T 432 = 0 -> tb T 437 = 0 -> next_model T t = silent T.
Proof.
  intros T t H1 H2. unfold next_model.
  rewrite (proj2 (Z.eqb_eq _ 0) H1), (proj2 (Z.eqb_eq _ 0) H2). reflexivity.
Qed.

Lemma nx_live : forall T, ~ (u32 T 432 = 0 /\ tb T 437 = 0) ->
  ((u32 T 432 =? 0) && (tb T 437 =? 0))%bool = false.
Proof.
  intros T Hact. apply andb_false_iff.
  destruct (Z.eqb_spec (u32 T 432) 0) as [E1|E1]; [|left; reflexivity].
  destruct (Z.eqb_spec (tb T 437) 0) as [E2|E2]; [exfalso; exact (Hact (conj E1 E2)) | right; reflexivity].
Qed.

Lemma nx_model_edge : forall T t i,
  ~ (u32 T 432 = 0 /\ tb T 437 = 0) -> 0 <= i < 144 ->
  (forall l, 0 <= l < i -> tb T (288 + l) = 0) -> tb T (288 + i) <> 0 ->
  next_model T t = edge_res T i.
Proof.
  intros T t i Hact Hi Hz Hnz. unfold next_model. rewrite (nx_live T Hact).
  rewrite (fd_some 144%nat T 0 i ltac:(cbn; lia) Hz Hnz). reflexivity.
Qed.

Lemma nx_model_after : forall T t,
  ~ (u32 T 432 = 0 /\ tb T 437 = 0) ->
  (forall l, 0 <= l < 144 -> tb T (288 + l) = 0) -> next_model T t = after_scan T t.
Proof.
  intros T t Hact Hz. unfold next_model. rewrite (nx_live T Hact).
  rewrite (fd_none 144%nat T 0); [reflexivity|]. intros l Hl. apply Hz. cbn in Hl. lia.
Qed.

Lemma nx_after_w0 : forall T t, tb T 437 = 0 -> after_scan T t = resweep T.
Proof. intros T t H. unfold after_scan. rewrite (proj2 (Z.eqb_eq _ 0) H). reflexivity. Qed.

Lemma nx_after_wait : forall T t, tb T 437 <> 0 -> 0 < s32 T 444 ->
  after_scan T t = silent (set4 T 444 (s32 T 444 - 1)).
Proof.
  intros T t H1 H2. unfold after_scan.
  rewrite (proj2 (Z.eqb_neq _ 0) H1), (proj2 (Z.ltb_lt 0 _) H2). reflexivity.
Qed.

Lemma nx_after_done : forall T t, tb T 437 <> 0 -> s32 T 444 <= 0 ->
  3 * tb T 437 <= s32 T 440 -> after_scan T t = resweep (setb T 437 0).
Proof.
  intros T t H1 H2 H3. unfold after_scan.
  rewrite (proj2 (Z.eqb_neq _ 0) H1), (proj2 (Z.ltb_ge 0 _) H2), (proj2 (Z.leb_le _ _) H3).
  reflexivity.
Qed.

Lemma nx_after_walk : forall T t, tb T 437 <> 0 -> s32 T 444 <= 0 -> s32 T 440 < 3 * tb T 437 ->
  after_scan T t =
    walk T t (tb T 436) (tb T 448) (3 * tb T 437) (s32 T 440) (Z.to_nat (3 * tb T 437 - s32 T 440)).
Proof.
  intros T t H1 H2 H3. unfold after_scan.
  rewrite (proj2 (Z.eqb_neq _ 0) H1), (proj2 (Z.ltb_ge 0 _) H2), (proj2 (Z.leb_gt _ _) H3).
  reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition A_reac_headamp_tx_nextP : Z := BASE + AF_reac_headamp_tx_next.
Definition SB_NX : Z := 0x7fff8000.
Definition BxN : sv := SOff 32 0.
(* At a cut the shadow base is the register s5 = x21 of that cut's own file, so a mid-function
   state says `sh_ok` with this one; BxN is right only for the entry state, where the base is
   still an extra atom of nx_extra. *)
Definition BxC : sv := SOff 21 0.
Definition BspanN : Z * Z := (SB_NX, SB_NX + 2 ^ 44 - 1).

(* The six slots the walk is cut at, as offsets from the listing's base (listing base 0x80a3c):
   LOOPD 0x85fb8 the head of the edge scan over the 144 cells, AFTR 0x86100 where that scan found
   none, LOOPR 0x861cc the head of the replay scan over the cursor, RSWP 0x8626c the re-assert
   tail, REARM 0x86304 its re-arm, EMIT 0x863a0 the replay scan's emit block. *)
Definition LOOPD : Z := AF_reac_headamp_tx_next + 0xbc.
Definition AFTR : Z := AF_reac_headamp_tx_next + 0x204.
Definition LOOPR : Z := AF_reac_headamp_tx_next + 0x2d0.
Definition RSWP : Z := AF_reac_headamp_tx_next + 0x370.
Definition REARM : Z := AF_reac_headamp_tx_next + 0x408.
Definition EMIT : Z := AF_reac_headamp_tx_next + 0x4a4.

(* The listing's atoms this walk adds to the 32 registers: 32 the shadow base, 33..42 the table's
   ten scalar fields as their plain unsigned machine values, 46 the dirty-scan index, 47 the
   address of its dirty byte, 48 the address of its value byte, 49 and 50 those two bytes, 51 the
   replay cursor, 52..55 the replay scan's cell addresses and bytes. *)
Definition nx_extra (tx : Z) (T : list byte) : list word :=
  map (Z_to_bv 64)
    [ SB_NX; u32at T 432; tb T 436; tb T 437; u32at T 440; u32at T 444;
      tb T 448; tb T 449; tb T 450; u32at T 452; u32at T 456;
      0; 0; 0; 0; tx + 432; tx; 0; 0; 0; tx + 144; 0; tx; 0 ].

Definition TXS : YP09.region := YP09.mkRegion (Some 10%nat) 432 460 432 460
  [ YP09.mkChunk 432 (CVal 4 (SOff 33 0)); YP09.mkChunk 436 (CVal 1 (SOff 34 0));
    YP09.mkChunk 437 (CVal 1 (SOff 35 0)); YP09.mkChunk 440 (CVal 4 (SOff 36 0));
    YP09.mkChunk 444 (CVal 4 (SOff 37 0)); YP09.mkChunk 448 (CVal 1 (SOff 38 0));
    YP09.mkChunk 449 (CVal 1 (SOff 39 0)); YP09.mkChunk 450 (CVal 1 (SOff 40 0));
    YP09.mkChunk 452 (CVal 4 (SOff 41 0)); YP09.mkChunk 456 (CVal 4 (SOff 42 0)) ].
(* The table's ten scalar fields, read-only: the state the entry segment is seated with. *)
Definition TXSro : YP09.region := YP09.mkRegion (Some 10%nat) 432 460 432 432 (YP09.r_chunks TXS).
Definition OUTC : YP09.region := YP09.mkRegion (Some 11%nat) 0 1 0 1 [].
Definition OUTP : YP09.region := YP09.mkRegion (Some 12%nat) 0 1 0 1 [].
Definition OUTV : YP09.region := YP09.mkRegion (Some 13%nat) 0 1 0 1 [].

Definition PTRN (al : Z) : afact := mkAF 4096 140737479966720 al.
(* A caller's byte: its shadow byte must lie in the shadow span, so below 2^47. *)
Definition OUTF : afact := mkAF 4096 (2 ^ 47 - 1) 0.

(* The contract bounds no field beyond its machine width, so neither does this. *)
Definition nx_atoms : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTRN 4); (11%nat, OUTF); (12%nat, OUTF); (13%nat, OUTF);
    (32%nat, mkAF SB_NX SB_NX 0);
    (33%nat, mkAF 0 4294967295 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0);
    (36%nat, mkAF 0 4294967295 0); (37%nat, mkAF 0 4294967295 0); (38%nat, mkAF 0 255 0);
    (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0); (41%nat, mkAF 0 4294967295 0);
    (42%nat, mkAF 0 4294967295 0) ].

Definition nx_SH : list shent := [ mkSHE 10 0 460; mkSHE 11 0 1; mkSHE 12 0 1; mkSHE 13 0 1 ].

(* The entry segment's regions: its own machine-stack window, the two image words the shadow base
   is read through, and the table's ten scalar fields, read-only. The three bytes the caller holds
   are NOT seated here, so no region of a caller byte ever has to be told apart from an image word:
   image B's contract places those bytes by `~ in_img`, not by a numeric bound. *)
Definition nx_regs_ro : list YP09.region :=
  [ stack_region NX_FRAME; got_regionP; bcell_regionP 32; TXSro ].
Definition ss_ro : sstate :=
  mkSS AF_reac_headamp_tx_next sr_atoms nx_regs_ro None (mkFacts nx_atoms [] []).

(* The regions the two scans add: the dirty byte the edge clears (atom 47, written), the value byte
   it reads (atom 48), and the replay scan's set and value bytes (atoms 52 and 54), read only. *)
Definition DREG : YP09.region := YP09.mkRegion (Some 47%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 49 0))].
Definition VREG : YP09.region := YP09.mkRegion (Some 48%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 50 0))].
Definition SREG : YP09.region := YP09.mkRegion (Some 52%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 53 0))].
Definition RVREG : YP09.region := YP09.mkRegion (Some 54%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 55 0))].

(* Past the prologue image B holds the table in s0 (atom 8), the value pointer in s1 (atom 9),
   and still the channel and parameter pointers in a1 and a2 (atoms 11 and 12): a0 and a3 are
   scratch from 0x85f34 on. So a region seated at a cut keys the table to atom 8 and the value
   byte to atom 9, NOT to image A's a0 / a3. The shadow base is an atom by then (s5), so neither
   image word is among these. *)
Definition TXS8 : YP09.region := YP09.mkRegion (Some 8%nat) 432 460 432 460 (YP09.r_chunks TXS).
(* The frame, seen from a CUT: the env of a cut is built from that cut's register file, so atom 2
   is the cut's own sp (the entry sp less the 96 the prologue took), and the frame runs UP from it.
   The entry state is the one seated before `addi sp,sp,-96`, so it keeps `stack_region NX_FRAME`,
   which runs DOWN from the entry sp. *)
Definition STKC : YP09.region := YP09.mkRegion (Some 2%nat) 0 NX_FRAME 0 NX_FRAME [].
Definition OUTV8 : YP09.region := YP09.mkRegion (Some 9%nat) 0 1 0 1 [].

(* The regions a segment that WRITES the three caller bytes may be seated with. *)
Definition nx_regs_all : list YP09.region :=
  [ STKC; TXS8; OUTC; OUTP; OUTV8; DREG; VREG; SREG; RVREG ].

(* The regions a segment that writes NO caller byte may be seated with. A run over these keeps
   nx_outq, which is what the contract's `r = 0` clause needs. *)
Definition nx_regs_q : list YP09.region :=
  [ STKC; TXS8; DREG; VREG; SREG; RVREG ].

(* The bytes this walk may write: its own machine-stack window, the table's ten scalar fields, the
   three bytes the caller holds, and the one array byte the edge clears. *)
Definition nx_touch2 (tx chp parp valp d a : Z) : Prop :=
  (tx + 432 <= a < tx + 460) \/ a = chp \/ a = parp \/ a = valp \/ a = d.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.

(* The post is the contract's own, so the closing file has nothing to translate. *)
#[local] Notation tnext_post := (tb_reac_headamp_tx_next_post B).

(* The one image byte range the walk reads: image B's dirty scan divides by 3 with mulhu and reads
   the multiplier 0xAAAAAAAAAAAAAAAB from .rodata object 34 at 0x10320 (slot 5466 of the listing,
   `PLdHi t4 a0 67 (A_OBJ 34) 0 SZ8`); image A divides with the immediate 171. GrantBContracts.v
   states that word as IMG_NEXT_DIV3, a conjunct of hyps_reac_headamp_tx_next: NextEntry.v's nx_walk
   takes it as a premise, and HeadampTxNextClose.v destructs it from hyps_. *)

(* The caller's right to write a byte it holds, as the contract's twr_ok gives it. *)
Definition nx_may_write (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (lyc : alayout) (Sc : astate) (own : list (Z * Z)) (a : Z) : Prop :=
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a.

Lemma nx_may_write_of_twr : forall STK sp0 FP ly S lyc Sc own W memc sp q n a,
  twr_ok B STK sp0 FP ly S lyc Sc own W memc sp q n -> q <= a < q + n ->
  nx_may_write STK sp0 FP ly S lyc Sc own a.
Proof. intros ? ? ? ? ? ? ? ? ? ? ? ? ? a H Ha. exact (proj1 (H a Ha)). Qed.

Lemma nx_present_of_twr : forall STK sp0 FP ly S lyc Sc own W memc sp q n a,
  twr_ok B STK sp0 FP ly S lyc Sc own W memc sp q n -> q <= a < q + n ->
  apresent (w_H W) memc a.
Proof. intros ? ? ? ? ? ? ? ? ? ? ? ? ? a H Ha. exact (proj1 (proj2 (H a Ha))). Qed.

(* What the walk has changed so far: nothing outside the window it owns below sp and the bytes of
   nx_touch2. The window is NX_STK, not the frame: the one call writes below the frame. *)
Definition nx_same (W : world SEGS) (memc m : word -> option byte)
  (sp tx chp parp valp d : Z) : Prop :=
  forall x : word, ~ (sp - NX_STK <= bv_unsigned x < sp) ->
    ~ nx_touch2 tx chp parp valp d (bv_unsigned x) ->
    mrestrict (w_H W) m x = mrestrict (w_H W) memc x.

Lemma nx_same_refl : forall W memc sp tx chp parp valp d,
  nx_same W memc memc sp tx chp parp valp d.
Proof. intros. intros x _ _. reflexivity. Qed.

(* The three bytes the caller holds still read as they did at the call: what a silent path keeps,
   and what the contract's `r = 0` clause asks for. *)
Definition nx_outq (W : world SEGS) (memc m : word -> option byte) (chp parp valp : Z) : Prop :=
  aview SEGS (w_H W) m chp = aview SEGS (w_H W) memc chp /\
  aview SEGS (w_H W) m parp = aview SEGS (w_H W) memc parp /\
  aview SEGS (w_H W) m valp = aview SEGS (w_H W) memc valp.

Lemma nx_outq_refl : forall W memc chp parp valp, nx_outq W memc memc chp parp valp.
Proof. intros. repeat split; reflexivity. Qed.

(* The entry segment writes only the twelve saved registers, into its own frame: its state has the
   table read-only and no caller byte at all, and at the entry the table is still in a0 (atom 10),
   not yet in s0. *)
Lemma nx_wrange_ro : forall (E : env) (rs : smem) (sp a : Z),
  (forall r, In r rs -> In (skel r) (skeleton nx_regs_ro)) ->
  bv_unsigned (ew E 2) = sp -> in_wrange E rs a -> sp - NX_FRAME <= a < sp.
Proof.
  intros E rs sp a Hsk E2 (r & Hin & Ha).
  pose proof (Hsk r Hin) as Hs.
  unfold nx_regs_ro, stack_region, got_regionP, bcell_regionP, TXSro, skeleton in Hs.
  cbn [map skel YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hs.
  unfold NX_FRAME in *.
  destruct Hs as [Hs|[Hs|[Hs|[Hs|Hs]]]]; try (exfalso; exact Hs);
    symmetry in Hs; unfold skel in Hs;
    injection Hs as H1 H2 H3 H4 H5;
    rewrite ?H1, ?H2, ?H3, ?H4, ?H5 in Ha; cbn [base_val] in Ha;
    pose proof nx_frame_val as HNF.
  - rewrite E2 in Ha. lia.
  - lia.
  - lia.
  - lia.
Qed.

(* A segment that writes no caller byte keeps nx_outq as well as nx_same. *)
Lemma nx_wrange_q : forall (E : env) (rs : smem) (sp tx d a : Z),
  (forall r, In r rs -> In (skel r) (skeleton nx_regs_q)) ->
  bv_unsigned (ew E 2) = sp - NX_FRAME -> bv_unsigned (ew E 8) = tx -> bv_unsigned (ew E 47) = d ->
  in_wrange E rs a -> (sp - NX_FRAME <= a < sp) \/ (tx + 432 <= a < tx + 460) \/ a = d.
Proof.
  intros E rs sp tx d a Hsk E2 E8 E47 (r & Hin & Ha).
  pose proof (Hsk r Hin) as Hs.
  unfold nx_regs_q, STKC, TXS8, TXS, DREG, VREG, SREG, RVREG, skeleton in Hs.
  cbn [map skel YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hs.
  unfold NX_FRAME in *.
  destruct Hs as [Hs|[Hs|[Hs|[Hs|[Hs|[Hs|Hs]]]]]]; try (exfalso; exact Hs);
    symmetry in Hs; unfold skel in Hs;
    injection Hs as H1 H2 H3 H4 H5;
    rewrite ?H1, ?H2, ?H3, ?H4, ?H5 in Ha; cbn [base_val] in Ha;
    pose proof nx_frame_val as HNF.
  - rewrite E2 in Ha. left. lia.
  - rewrite E8 in Ha. right. left. lia.
  - rewrite E47 in Ha. right. right. lia.
  - lia.
  - lia.
  - lia.
Qed.

(* Only the windows of the regions above are written, so every byte outside them is kept. *)
Lemma nx_wrange : forall (E : env) (rs : smem) (sp tx chp parp valp d a : Z),
  (forall r, In r rs -> In (skel r) (skeleton nx_regs_all)) ->
  bv_unsigned (ew E 2) = sp - NX_FRAME -> bv_unsigned (ew E 8) = tx ->
  bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 9) = valp -> bv_unsigned (ew E 47) = d ->
  in_wrange E rs a -> (sp - NX_FRAME <= a < sp) \/ nx_touch2 tx chp parp valp d a.
Proof.
  intros E rs sp tx chp parp valp d a Hsk E2 E8 E11 E12 E9 E47 (r & Hin & Ha).
  pose proof (Hsk r Hin) as Hs.
  unfold nx_regs_all, STKC, TXS8, TXS, OUTC, OUTP, OUTV8, DREG, VREG, SREG, RVREG, skeleton in Hs.
  cbn [map skel YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hs.
  unfold nx_touch2, NX_FRAME.
  destruct Hs as [Hs|[Hs|[Hs|[Hs|[Hs|[Hs|[Hs|[Hs|[Hs|Hs]]]]]]]]];
    try (exfalso; exact Hs);
    symmetry in Hs; unfold skel in Hs;
    injection Hs as H1 H2 H3 H4 H5;
    rewrite ?H1, ?H2, ?H3, ?H4, ?H5 in Ha; cbn [base_val] in Ha;
    pose proof nx_frame_val as HNF.
  - rewrite E2 in Ha. left. lia.
  - rewrite E8 in Ha. right. left. lia.
  - rewrite E11 in Ha. right. right. left. lia.
  - rewrite E12 in Ha. right. right. right. left. lia.
  - rewrite E9 in Ha. right. right. right. right. left. lia.
  - rewrite E47 in Ha. right. right. right. right. right. lia.
  - lia.
  - lia.
  - lia.
Qed.

Lemma nx_same_step : forall (E : env) (rs : smem) W memc m1 m2 (sp tx chp parp valp d : Z),
  (forall r, In r rs -> In (skel r) (skeleton nx_regs_all)) ->
  bv_unsigned (ew E 2) = sp - NX_FRAME -> bv_unsigned (ew E 8) = tx ->
  bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 9) = valp -> bv_unsigned (ew E 47) = d ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  nx_same W memc m1 sp tx chp parp valp d ->
  nx_same W memc m2 sp tx chp parp valp d.
Proof.
  intros E rs W memc m1 m2 sp tx chp parp valp d Hsk E2 E8 E11 E12 E9 E47 HF HS x Hst Htc.
  rewrite (HF x); [apply HS; assumption|].
  intros Hw. destruct (nx_wrange E rs sp tx chp parp valp d (bv_unsigned x)
    Hsk E2 E8 E11 E12 E9 E47 Hw) as [H|H]; [|exact (Htc H)].
  apply Hst. pose proof nx_frame_le. unfold NX_FRAME in *. lia.
Qed.

(* A run of the entry segment, and a run of a segment that writes no caller byte: each keeps both
   what the walk has left untouched and the three bytes the caller holds. *)
Lemma nx_same_step_ro : forall (E : env) (rs : smem) W memc m1 m2 (sp tx chp parp valp d : Z),
  (forall r, In r rs -> In (skel r) (skeleton nx_regs_ro)) ->
  bv_unsigned (ew E 2) = sp ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  nx_same W memc m1 sp tx chp parp valp d ->
  nx_same W memc m2 sp tx chp parp valp d.
Proof.
  intros E rs W memc m1 m2 sp tx chp parp valp d Hsk E2 HF HS x Hst Htc.
  rewrite (HF x); [apply HS; assumption|].
  intros Hw. apply Hst. pose proof nx_frame_le.
  pose proof (nx_wrange_ro E rs sp (bv_unsigned x) Hsk E2 Hw). unfold NX_FRAME in *. lia.
Qed.

Lemma nx_same_step_q : forall (E : env) (rs : smem) W memc m1 m2 (sp tx chp parp valp d : Z),
  (forall r, In r rs -> In (skel r) (skeleton nx_regs_q)) ->
  bv_unsigned (ew E 2) = sp - NX_FRAME -> bv_unsigned (ew E 8) = tx -> bv_unsigned (ew E 47) = d ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  nx_same W memc m1 sp tx chp parp valp d ->
  nx_same W memc m2 sp tx chp parp valp d.
Proof.
  intros E rs W memc m1 m2 sp tx chp parp valp d Hsk E2 E8 E47 HF HS x Hst Htc.
  rewrite (HF x); [apply HS; assumption|].
  intros Hw. destruct (nx_wrange_q E rs sp tx d (bv_unsigned x) Hsk E2 E8 E47 Hw) as [H|[H|H]].
  - apply Hst. pose proof nx_frame_le. unfold NX_FRAME in *. lia.
  - apply Htc. unfold nx_touch2. left. exact H.
  - apply Htc. unfold nx_touch2. right. right. right. right. exact H.
Qed.

(* The three bytes the caller holds lie outside both the frame and the table, so a run over either
   of those two region sets leaves them as they were. *)
Lemma nx_outq_step_ro : forall (E : env) (rs : smem) W memc m1 m2 (sp tx chp parp valp : Z),
  (forall r, In r rs -> In (skel r) (skeleton nx_regs_ro)) ->
  bv_unsigned (ew E 2) = sp ->
  thd_out_ok sp tx chp -> thd_out_ok sp tx parp -> thd_out_ok sp tx valp ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  nx_outq W memc m1 chp parp valp -> nx_outq W memc m2 chp parp valp.
Proof.
  intros E rs W memc m1 m2 sp tx chp parp valp Hsk E2 Hc Hp Hv HF (Q1 & Q2 & Q3).
  assert (K : forall q, thd_out_ok sp tx q ->
    aview SEGS (w_H W) m2 q = aview SEGS (w_H W) m1 q).
  { intros q (Hq0 & Hq1 & Hq2 & Hq3 & Hq4 & Hq5).
    unfold aview, YP09.mbyte. rewrite (HF (Z_to_bv 64 q)); [reflexivity|].
    intros Hw. pose proof (nx_wrange_ro E rs sp (bv_unsigned (Z_to_bv 64 q)) Hsk E2 Hw) as Hr.
    rewrite unsigned_lit_small in Hr by lia.
    pose proof nx_frame_le. unfold NX_FRAME, NX_STK in *. lia. }
  split; [|split].
  - rewrite (K chp Hc). exact Q1.
  - rewrite (K parp Hp). exact Q2.
  - rewrite (K valp Hv). exact Q3.
Qed.

Lemma nx_outq_step_q : forall (E : env) (rs : smem) W memc m1 m2 (sp tx chp parp valp d : Z),
  (forall r, In r rs -> In (skel r) (skeleton nx_regs_q)) ->
  bv_unsigned (ew E 2) = sp - NX_FRAME -> bv_unsigned (ew E 8) = tx -> bv_unsigned (ew E 47) = d ->
  tx <= d < tx + TX_SIZE ->
  thd_out_ok sp tx chp -> thd_out_ok sp tx parp -> thd_out_ok sp tx valp ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  nx_outq W memc m1 chp parp valp -> nx_outq W memc m2 chp parp valp.
Proof.
  intros E rs W memc m1 m2 sp tx chp parp valp d Hsk E2 E8 E47 Hd Hc Hp Hv HF (Q1 & Q2 & Q3).
  assert (K : forall q, thd_out_ok sp tx q ->
    aview SEGS (w_H W) m2 q = aview SEGS (w_H W) m1 q).
  { intros q (Hq0 & Hq1 & Hq2 & Hq3 & Hq4 & Hq5).
    unfold aview, YP09.mbyte. rewrite (HF (Z_to_bv 64 q)); [reflexivity|].
    intros Hw.
    destruct (nx_wrange_q E rs sp tx d (bv_unsigned (Z_to_bv 64 q)) Hsk E2 E8 E47 Hw) as [H|[H|H]];
      rewrite unsigned_lit_small in H by lia;
      [ pose proof nx_frame_le; unfold NX_FRAME, NX_STK in *; lia
      | unfold TX_SIZE, ATx.TX_SIZE in Hq2; lia
      | unfold TX_SIZE, ATx.TX_SIZE in Hq2, Hd; lia ]. }
  split; [|split].
  - rewrite (K chp Hc). exact Q1.
  - rewrite (K parp Hp). exact Q2.
  - rewrite (K valp Hv). exact Q3.
Qed.

(* The awr obligation of a run: its own window, the table and the three bytes. *)
Lemma nx_awr : forall (E : env) STK sp0 FP ly S lyc Sc own (rs : smem)
    (sp tx chp parp valp d : Z),
  (forall r, In r rs -> In (skel r) (skeleton nx_regs_all)) ->
  bv_unsigned (ew E 2) = sp - NX_FRAME -> bv_unsigned (ew E 8) = tx ->
  bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 9) = valp -> bv_unsigned (ew E 47) = d ->
  sp0 - STK <= sp - NX_STK -> sp <= sp0 -> tx <= d < tx + TX_SIZE ->
  (forall a, tx <= a < tx + TX_SIZE -> nx_may_write STK sp0 FP ly S lyc Sc own a) ->
  nx_may_write STK sp0 FP ly S lyc Sc own chp ->
  nx_may_write STK sp0 FP ly S lyc Sc own parp ->
  nx_may_write STK sp0 FP ly S lyc Sc own valp ->
  awr_ok E rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
  intros E STK sp0 FP ly S lyc Sc own rs sp tx chp parp valp d
    Hsk E2 E8 E11 E12 E9 E47 Hlo Hhi Hd Htab Hc Hp Hv a Hw.
  destruct (nx_wrange E rs sp tx chp parp valp d a Hsk E2 E8 E11 E12 E9 E47 Hw)
    as [Hst | [Htb | [-> | [-> | [-> | ->]]]]].
  - left. pose proof nx_frame_le. unfold NX_FRAME in *. lia.
  - apply Htab. unfold TX_SIZE, ATx.TX_SIZE in *. lia.
  - exact Hc.
  - exact Hp.
  - exact Hv.
  - apply Htab. exact Hd.
Qed.

(* The facts about the call that hold at every slot of the walk. *)
Definition nx_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
    (lyc : alayout) (Sc : astate) (own : list (Z * Z)) (W : world SEGS)
    (memc : word -> option byte) (mdc : Model) (regs : bvmap 5 word)
    (tx chp parp valp : Z) (T : list byte) : Prop :=
  AR SEGS B lyc Sc W memc mdc /\
  In (tx, TX_SIZE) (ablocks B lyc Sc) /\
  thd_out_ok (spZ regs) tx chp /\ thd_out_ok (spZ regs) tx parp /\ thd_out_ok (spZ regs) tx valp /\
  chp <> parp /\ chp <> valp /\ parp <> valp /\
  apresent (w_H W) memc chp /\ apresent (w_H W) memc parp /\ apresent (w_H W) memc valp /\
  byte_ok W memc chp /\ byte_ok W memc parp /\ byte_ok W memc valp /\
  bytes_ok W memc (tx + 456) 4 /\
  2 ^ 46 <= spZ regs <= 2 ^ 47 /\ alloc_ceiling <= spZ regs - NX_STK /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - NX_STK /\ spZ regs <= sp0 /\
  (forall a, tx <= a < tx + TX_SIZE -> nx_may_write STK sp0 FP ly S lyc Sc own a) /\
  nx_may_write STK sp0 FP ly S lyc Sc own chp /\
  nx_may_write STK sp0 FP ly S lyc Sc own parp /\
  nx_may_write STK sp0 FP ly S lyc Sc own valp /\
  YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 10 = w64 tx /\ getr regs 11 = w64 chp /\
  getr regs 12 = w64 parp /\ getr regs 13 = w64 valp /\
  length T = 460%nat /\ thd_replay_ok T /\
  obj_at SEGS (mrestrict (w_H W) memc) tx LAY_TX (tx_vals T) /\
  (forall a, spZ regs - NX_STK <= a < spZ regs -> apresent (w_H W) memc a).

(* What the walk carries from one slot to the next. The flag q says the three bytes the caller
   holds still read as they did at the call, which a silent return needs. *)
Definition nx_mid (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
    (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (memj : word -> option byte) (mdj : Model)
    (tx chp parp valp d : Z) (q : bool) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memj mdj k /\
  nx_same W memc memj (spZ regs) tx chp parp valp d /\
  (forall a, spZ regs - NX_STK <= a < spZ regs -> apresent (w_H W) memj a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memj a) /\
  (if q then nx_outq W memc memj chp parp valp else True).

Lemma nx_mid_drop : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj
    tx chp parp valp d q,
  nx_mid STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp d q ->
  nx_mid STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp d false.
Proof. intros. destruct H as (H1 & H2 & H3 & H4 & _). repeat (split; [assumption|]). exact I. Qed.

(* The twelve callee-saved registers the prologue put on the machine stack: a cut in the middle of
   the function has clobbered the registers themselves, and the epilogue reads them back. *)
Definition nx_saved (W : world SEGS) (m : word -> option byte) (regs : bvmap 5 word)
    (sp : Z) : Prop :=
  val_mem SEGS (mrestrict (w_H W) m) (sp - 8) 8 (bv_unsigned (getr regs 1)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 24) 8 (bv_unsigned (getr regs 9)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 32) 8 (bv_unsigned (getr regs 18)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 40) 8 (bv_unsigned (getr regs 19)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 48) 8 (bv_unsigned (getr regs 20)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 56) 8 (bv_unsigned (getr regs 21)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 64) 8 (bv_unsigned (getr regs 22)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 72) 8 (bv_unsigned (getr regs 23)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 80) 8 (bv_unsigned (getr regs 24)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 88) 8 (bv_unsigned (getr regs 25)) /\
  val_mem SEGS (mrestrict (w_H W) m) (sp - 96) 8 (bv_unsigned (getr regs 26)).

Lemma nx_same_aview : forall W memc m (sp tx chp parp valp d a : Z),
  nx_same W memc m sp tx chp parp valp d -> 0 <= a < 2 ^ 64 ->
  tx <= d < tx + TX_SIZE ->
  ~ (sp - NX_STK <= a < sp) -> ~ nx_touch tx chp parp valp a ->
  aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a.
Proof.
  intros W memc m sp tx chp parp valp d a HS Ha Hd Hst Htc.
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha).
  assert (Htc2 : ~ nx_touch2 tx chp parp valp d a).
  { unfold nx_touch2. unfold nx_touch, TX_SIZE, ATx.TX_SIZE in Htc, Hd.
    intros [H|[H|[H|[H|H]]]]; apply Htc; unfold nx_touch, TX_SIZE, ATx.TX_SIZE; lia. }
  unfold aview, mbyte. rewrite (HS (Z_to_bv 64 a) ltac:(rewrite Hu; exact Hst)
    ltac:(rewrite Hu; exact Htc2)).
  reflexivity.
Qed.

(* Every return site of the walk ends the same way. *)
Lemma nx_finish : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs regs2 : bvmap 5 word) mem2 md2 (tx chp parp valp d : Z) (T T' : list byte) (r c p v : Z),
  tx <= d < tx + TX_SIZE ->
  AR SEGS B lyc Sc W memc mdc ->
  In (tx, TX_SIZE) (ablocks B lyc Sc) ->
  thd_out_ok (spZ regs) tx chp -> thd_out_ok (spZ regs) tx parp -> thd_out_ok (spZ regs) tx valp ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> alloc_ceiling <= spZ regs - NX_STK ->
  next_model T tx = (r, (c, p, v), T') ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  aregs_preserved regs regs2 ->
  nx_same W memc mem2 (spZ regs) tx chp parp valp d ->
  (forall a, spZ regs - NX_STK <= a < spZ regs -> apresent (w_H W) mem2 a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  getr regs2 10 = w64 r ->
  obj_at SEGS (mrestrict (w_H W) mem2) tx LAY_TX (tx_vals T') ->
  thd_replay_ok T' ->
  (r = 1 -> aview SEGS (w_H W) mem2 chp = Some c
            /\ aview SEGS (w_H W) mem2 parp = Some p
            /\ aview SEGS (w_H W) mem2 valp = Some v) ->
  (r = 0 -> nx_outq W memc mem2 chp parp valp) ->
  tnext_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2
    tx chp parp valp d T T' r c p v Hd HAR Hg Hoc Hop Hov Hspr Hac Hmodel HJ2 HP HSAME
    HpresS HpresK H10 Hobj Hrok Hr1 Hr0.
  destruct Hoc as (Hc0 & Hc1 & Hc2 & Hc3 & Hc4 & Hc5).
  destruct Hop as (Hp0 & Hp1 & Hp2 & Hp3 & Hp4 & Hp5).
  destruct Hov as (Hv0 & Hv1 & Hv2 & Hv3 & Hv4 & Hv5).
  pose proof (blk_off_imgB B lyc Sc W memc mdc tx TX_SIZE HAR Hg) as Hgimg.
  change (req_size TX_SIZE) with 460 in Hgimg.
  rewrite IMG_LO_B_val, IMG_TOP_B_val in Hgimg.
  unfold TX_SIZE, ATx.TX_SIZE in Hc2, Hp2, Hv2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold tb_reac_headamp_tx_next_post. split; [reflexivity|].
  exists regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
  split.
  { unfold tcj_kept. split; [|split; [|split; [|split; [|split]]]].
    - intros a Ha Hst Htc. apply (nx_same_aview W memc mem2 (spZ regs) tx chp parp valp d a);
        [exact HSAME | lia64 | exact Hd | | exact Htc].
      unfold NX_STK in *. lia.
    - intros b m i Hb Hi Htc.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hb4096 & Hbceil & _ & _ & _).
      apply (nx_same_aview W memc mem2 (spZ regs) tx chp parp valp d (b + i));
        [exact HSAME | lia64 | exact Hd | unfold NX_STK in *; lia | exact Htc].
    - intros a Hi Ho He.
      pose proof (pa_img_range a Hi) as Hir. rewrite IMG_LO_B_val, IMG_TOP_B_val in Hir.
      apply (nx_same_aview W memc mem2 (spZ regs) tx chp parp valp d a);
        [exact HSAME | lia64 | exact Hd | unfold NX_STK in *; lia |].
      unfold nx_touch, TX_SIZE, ATx.TX_SIZE.
      intros [Hx | [Hx | [Hx | Hx]]]; [lia | | |];
        subst a; [exact (Hc4 Hi) | exact (Hp4 Hi) | exact (Hv4 Hi)].
    - intros cid pos a Hf Hzr Htc.
      destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hf) as (Hf0 & Hfc & Hfa).
      pose proof (fs_frame_bytes_nonneg cid) as Hfb.
      apply (nx_same_aview W memc mem2 (spZ regs) tx chp parp valp d a);
        [exact HSAME | | exact Hd | | exact Htc].
      + (* the frame's own bytes, or the shadow bytes that cover them *)
        assert (HD1 : 0 <= frame_addr lyc cid pos / 8 <= 17592184995840)
          by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
        assert (HD2 : 0 <= fs_frame_bytes cid / 8 <= 17592184995840)
          by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
        destruct Hzr as [Hzr | Hzr]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hzr;
          cbn [fst snd] in Hzr; lia64.
      + assert (HD1 : 0 <= frame_addr lyc cid pos / 8 <= 17592184995840)
          by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
        assert (HD2 : 0 <= fs_frame_bytes cid / 8 <= 17592184995840)
          by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
        destruct Hzr as [Hzr | Hzr]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hzr;
          cbn [fst snd] in Hzr; unfold NX_STK in *; lia64.
    - intros a Ha Hst Hp. apply HpresK. exact Hp.
    - exact HpresS. }
  rewrite Hmodel.
  split; [exact H10|]. split; [exact Hobj|]. split; [exact Hrok|]. split; [exact Hr1|].
  intros H0. destruct (Hr0 H0) as (Q1 & Q2 & Q3). exact (conj Q1 (conj Q2 Q3)).
Qed.

(* ---- the six cuts of the walk, as statements ------------------------------------------------
   Each segment file proves one of these and takes the ones below it. The registers are image B's:
   the shadow base is s5 (x21), the table is s0 (x8), the value pointer s1 (x9), and the prologue
   saves ra and s0..s10, so gp, tp and s11 are the only registers the call never writes. *)
Definition nx_keep_gp (regs regsj : bvmap 5 word) : Prop :=
  forall r : bv 5, In r [3; 4; 27]%bv -> getr regsj r = getr regs r.

(* At the head of the edge scan, LOOPD 0x85fb8, with i the cell it is about to read. The index is
   held five times: a7 and a4 as i, a0 as tx + i, t2 as 288 + i, and t1 as the 32-bit count i - 144
   that reaches 0 when the scan is done. *)
Definition nx_at_loopd (regs regsj : bvmap 5 word) (tx chp parp valp i : Z) : Prop :=
  nx_keep_gp regs regsj /\
  getr regsj 2 = w64 (spZ regs - NX_FRAME) /\
  getr regsj 8 = w64 tx /\ getr regsj 9 = w64 valp /\
  getr regsj 11 = w64 chp /\ getr regsj 12 = w64 parp /\
  getr regsj 21 = w64 SB_NX /\
  getr regsj 17 = w64 i /\ getr regsj 14 = w64 i /\
  getr regsj 10 = w64 (tx + i) /\ getr regsj 7 = w64 (288 + i) /\
  getr regsj 6 = w64 (i - 144) /\
  getr regsj 5 = w64 (tx + 288) /\
  getr regsj 28 = w64 (18446744073709551615 - (tx + 288)) /\
  getr regsj 29 = w64 12297829382473034411 /\
  getr regsj 30 = w64 12297829383904690176.

(* At AFTR 0x86100, where the edge scan found no dirty cell. *)
Definition nx_at_aftr (regs regsA : bvmap 5 word) (tx chp parp valp : Z) : Prop :=
  nx_keep_gp regs regsA /\
  getr regsA 2 = w64 (spZ regs - NX_FRAME) /\
  getr regsA 8 = w64 tx /\ getr regsA 9 = w64 valp /\
  getr regsA 11 = w64 chp /\ getr regsA 12 = w64 parp /\
  getr regsA 21 = w64 SB_NX.

(* At the head of the replay scan, LOOPR 0x861cc, with j the cursor. The prologue of the scan has
   put the three field addresses and their shadow bytes in s2..s4 and s6..s8, three times the
   replay width in s9, and (tx + 440) mod 8 + 3 in s10 for the four-byte check of the cursor. *)
Definition nx_at_loopr (regs regsj : bvmap 5 word) (tx chp parp valp : Z) (T : list byte) (j : Z)
  : Prop :=
  nx_keep_gp regs regsj /\
  getr regsj 2 = w64 (spZ regs - NX_FRAME) /\
  getr regsj 8 = w64 tx /\ getr regsj 9 = w64 valp /\
  getr regsj 11 = w64 chp /\ getr regsj 12 = w64 parp /\
  getr regsj 21 = w64 SB_NX /\
  getr regsj 18 = w64 (tx + 437) /\ getr regsj 22 = w64 (SHADOW_OFF + (tx + 437) / 8) /\
  getr regsj 19 = w64 (tx + 444) /\ getr regsj 23 = w64 (SHADOW_OFF + (tx + 444) / 8) /\
  getr regsj 20 = w64 (tx + 440) /\ getr regsj 24 = w64 (SHADOW_OFF + (tx + 440) / 8) /\
  getr regsj 25 = w64 (3 * tb T 437) /\ getr regsj 26 = w64 ((tx + 440) mod 8 + 3) /\
  getr regsj 5 = w64 j /\
  getr regsj 14 = w64 (Z.max (s32 T 440) (3 * tb T 437)) /\
  getr regsj 15 = w64 (tb T 436) /\ getr regsj 13 = w64 (tb T 448) /\
  getr regsj 16 = w64 (tx + 144) /\
  getr regsj 6 = w64 (18446744073709551615 - (tx + 144)) /\
  getr regsj 7 = w64 1431655766 /\ getr regsj 28 = w64 47.

(* At the emit block EMIT 0x863a0, with c the channel and p the parameter the scan found. *)
Definition nx_at_emit (regs regsj : bvmap 5 word) (tx chp parp valp : Z) (T : list byte) (c p : Z)
  : Prop :=
  nx_keep_gp regs regsj /\
  getr regsj 2 = w64 (spZ regs - NX_FRAME) /\
  getr regsj 8 = w64 tx /\ getr regsj 9 = w64 valp /\
  getr regsj 11 = w64 chp /\ getr regsj 12 = w64 parp /\
  getr regsj 21 = w64 SB_NX /\
  getr regsj 18 = w64 (tx + 437) /\ getr regsj 22 = w64 (SHADOW_OFF + (tx + 437) / 8) /\
  getr regsj 19 = w64 (tx + 444) /\ getr regsj 23 = w64 (SHADOW_OFF + (tx + 444) / 8) /\
  getr regsj 20 = w64 (tx + 440) /\ getr regsj 24 = w64 (SHADOW_OFF + (tx + 440) / 8) /\
  getr regsj 25 = w64 (3 * tb T 437) /\ getr regsj 26 = w64 ((tx + 440) mod 8 + 3) /\
  getr regsj 17 = w64 c /\ getr regsj 5 = w64 p.

(* At the re-assert tail RSWP 0x8626c. Only the table, its width field and the shadow base are
   live: both ways in (the idle width at 0x86118 and the exhausted scan at 0x86268) leave the rest
   of the scan's registers behind. *)
Definition nx_at_rswp (regs regsj : bvmap 5 word) (tx chp parp valp : Z) : Prop :=
  nx_keep_gp regs regsj /\
  getr regsj 2 = w64 (spZ regs - NX_FRAME) /\
  getr regsj 8 = w64 tx /\ getr regsj 9 = w64 valp /\
  getr regsj 11 = w64 chp /\ getr regsj 12 = w64 parp /\
  getr regsj 21 = w64 SB_NX /\
  getr regsj 18 = w64 (tx + 437) /\ getr regsj 22 = w64 (SHADOW_OFF + (tx + 437) / 8).

(* At the re-arm block REARM 0x86304: a0 is the silence counter's address, a3 its shadow byte's
   address (the counter's granule is only partly usable, so that check takes its slow path) and a2
   the remembered scene width it read, which is not 0. *)
Definition nx_at_rearm (regs regsj : bvmap 5 word) (tx valp w : Z) : Prop :=
  nx_keep_gp regs regsj /\
  getr regsj 2 = w64 (spZ regs - NX_FRAME) /\
  getr regsj 8 = w64 tx /\ getr regsj 9 = w64 valp /\
  getr regsj 21 = w64 SB_NX /\
  getr regsj 18 = w64 (tx + 437) /\ getr regsj 22 = w64 (SHADOW_OFF + (tx + 437) / 8) /\
  getr regsj 10 = w64 (tx + 456) /\ getr regsj 13 = w64 (SHADOW_OFF + (tx + 456) / 8) /\
  getr regsj 12 = w64 w.

(* The re-arm, as NextRearm.v proves it: the table with the silence counter ticked is in memory and
   the answer is the re-armed table, silently. *)
Definition nx_rearm_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj
    (tx chp parp valp : Z) (T Tj : list byte),
  nx_ctx STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) true ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals (set4 Tj 456 (u32 Tj 456 + 1))) ->
  length Tj = 460%nat ->
  next_model T tx = silent (rearm Tj) ->
  nx_at_rearm regs regsj tx valp (tb Tj 450) ->
  SRr SEGS W (cfg_at SEGS (BASE + REARM) regsj memj mdj)
    (tnext_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).

(* The re-assert tail, as NextReplayTail.v proves it. Tj is the table at the tail's entry. *)
Definition nx_resweep_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj
    (tx chp parp valp : Z) (T Tj : list byte),
  nx_ctx STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) true ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals Tj) ->
  length Tj = 460%nat -> tb Tj 437 = 0 ->
  (forall l, 0 <= l < 432 -> tb Tj l = tb T l) ->
  next_model T tx = resweep Tj ->
  nx_at_rswp regs regsj tx chp parp valp ->
  SRr SEGS W (cfg_at SEGS (BASE + RSWP) regsj memj mdj)
    (tnext_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).

(* The emit block, as NextEmit.v proves it: the cursor is already stored, and the answer is the
   model's emit_res for the cell the scan found. This is the one segment that calls
   reac_headamp_tx_effective, so its file takes that contract. *)
Definition nx_emit_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj
    (tx chp parp valp : Z) (T : list byte) (j : Z) (q : bool),
  nx_ctx STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) q ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals (set4 T 440 (j + 1))) ->
  tb T 437 <> 0 -> 0 <= j < 3 * tb T 437 ->
  carried (set4 T 440 (j + 1)) (tb T 436) (tb T 448) j = true ->
  next_model T tx = emit_res (set4 T 440 (j + 1)) tx (tb T 436 + j / 3) (j mod 3) j (3 * tb T 437) ->
  nx_at_emit regs regsj tx chp parp valp T (tb T 436 + j / 3) (j mod 3) ->
  SRr SEGS W (cfg_at SEGS (BASE + EMIT) regsj memj mdj)
    (tnext_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).

(* The replay scan, as NextReplayScan.v proves it, by induction on the cursor's remaining room. *)
Definition nx_rloop_spec : Prop :=
  forall (n : nat) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj
    (tx chp parp valp : Z) (T : list byte) (j : Z),
  nx_ctx STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) true ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals (set4 T 440 j)) ->
  tb T 437 <> 0 -> 0 <= j -> s32 T 440 <= j < 3 * tb T 437 ->
  Z.of_nat n = 3 * tb T 437 - j ->
  next_model T tx = walk (set4 T 440 j) tx (tb T 436) (tb T 448) (3 * tb T 437) j n ->
  nx_at_loopr regs regsj tx chp parp valp T j ->
  SRr SEGS W (cfg_at SEGS (BASE + LOOPR) regsj memj mdj)
    (tnext_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).

(* The after-scan, as NextAfter.v proves it: the wait, the exhausted scan, or the replay. *)
Definition nx_after_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs regsA : bvmap 5 word) memA mdA (tx chp parp valp : Z) (T : list byte),
  nx_ctx STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memA mdA tx chp parp valp (tx + 432) true ->
  nx_saved W memA regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memA) tx LAY_TX (tx_vals T) ->
  ~ (u32 T 432 = 0 /\ tb T 437 = 0) ->
  (forall l, 0 <= l < 144 -> tb T (288 + l) = 0) ->
  nx_at_aftr regs regsA tx chp parp valp ->
  SRr SEGS W (cfg_at SEGS (BASE + AFTR) regsA memA mdA)
    (tnext_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).

(* The edge scan, as NextEdge.v proves it, by induction on the cells left. *)
Definition nx_dloop_stmt : Prop :=
  forall (n : nat) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
     memc mdc k (regs regsj : bvmap 5 word) memj mdj (tx chp parp valp : Z) (T : list byte) (i : Z),
  nx_ctx STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) true ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals T) ->
  ~ (u32 T 432 = 0 /\ tb T 437 = 0) ->
  0 <= i < 144 -> Z.of_nat n = 144 - i ->
  (forall l, 0 <= l < i -> tb T (288 + l) = 0) ->
  nx_at_loopd regs regsj tx chp parp valp i ->
  SRr SEGS W (cfg_at SEGS (BASE + LOOPD) regsj memj mdj)
    (tnext_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).

End h.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Mem.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits AXF_efbz AXF_efmem AXF_maz AXF_mb0z.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma u_vaddi'' : forall (w : word) k, 0 <= bv_unsigned w + k < 2^64 -> bv_unsigned (v_addi w k) = bv_unsigned w + k.
Proof. intros w k H. unfold v_addi. apply u_small. exact H. Qed.

Ltac peelw := rewrite MngWb.wbytes_out by (cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_vaddi'', ?u_wa_small by lia; lia).

Section MAM.
Variables (m : word -> option byte) (regs : bvmap 5 word).
Hypothesis Hsp : 2^20 <= bv_unsigned (getr regs 2) <= 2^47.

#[using="Hsp"] Lemma ma_mem_out : forall x, 0 <= x < 2^64 -> ~ (bv_unsigned (getr regs 2) - 48 <= x < bv_unsigned (getr regs 2)) ->
  ma_mem m regs (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). intros x Hx H1. unfold ma_mem. do 6 peelw. reflexivity. Qed.

#[using="Type"] Lemma ma_mem_grows : mem_grows m (ma_mem m regs).
Proof. LiaFast.lf_pins LiaFast.u0. unfold ma_mem. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

#[using="Hsp"] Lemma ma_rdn_save : forall k (r : bvmap 5 word -> word),
  In (k, r) [(8, fun R => getr R 1); (16, fun R => getr R 8); (24, fun R => getr R 9); (32, fun R => getr R 18);
             (40, fun R => getr R 19); (48, fun R => getr R 20)] ->
  rdn SEGS (ma_mem m regs) (wa (bv_unsigned (getr regs 2) + - k)) 8 = Some (word_to_le_bytes 8 (r regs)).
Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0).
  intros k r Hk. pose proof (u64_range (getr regs 2)) as R.
  cbn [In] in Hk. unfold ma_mem.
  Ltac dj := rewrite rdn_wbytes_disjoint; [| cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_vaddi'', ?u_wa_small by lia; lia | rewrite ?u_vaddi'', ?u_wa_small by lia; lia].
  Ltac hit k r := replace (wa (bv_unsigned (getr regs 2) + - k)) with (v_addi (getr regs 2) (- k)) by reflexivity;
                  apply (rdn_wbytes_hit SEGS (word_to_le_bytes 8 (r))); cbn [length word_to_le_bytes Z_to_le_bytes]; unfold v_addi; rewrite ?u_small by lia; lia.
  destruct Hk as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <-.
  - do 5 dj. hit 8 (getr regs 1).
  - do 4 dj. hit 16 (getr regs 8).
  - do 3 dj. hit 24 (getr regs 9).
  - do 2 dj. hit 32 (getr regs 18).
  - do 1 dj. hit 40 (getr regs 19).
  - hit 48 (getr regs 20).
Qed.
End MAM.

Section MB0M.
Variables (m : word -> option byte) (G avail : Z).
Hypothesis HG : 0 <= G + 24 /\ G + 28 <= 2^64.

#[using="HG"] Lemma mb0_mem_out : forall x, 0 <= x < 2^64 -> ~ (G + 24 <= x < G + 28) -> mb0_mem m G avail (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (HG : LiaFast.U) => LiaFast.u0). intros x Hx H. unfold mb0_mem. peelw. reflexivity. Qed.

#[using="Type"] Lemma mb0_mem_grows : mem_grows m (mb0_mem m G avail).
Proof. LiaFast.lf_pins LiaFast.u0. unfold mb0_mem. apply wbytes_grows. Qed.

#[using="HG"] Lemma mb0_mem_at : forall j, (j < 4)%nat -> bview SEGS (mb0_mem m G avail) (G + 24 + Z.of_nat j) = Some (le_byte (avail - lowbit avail) 4 j).
Proof. LiaFast.lf_pins (fun (HG : LiaFast.U) => LiaFast.u0). intros j Hj. unfold mb0_mem. apply wb_byte; [lia | cbn; lia | lia | lia]. Qed.
End MB0M.

(* [comment removed for export] *)
Lemma rdn_frame' : forall m m' (a : Z) n, 0 <= a -> a + Z.of_nat n <= 2^64 ->
  (forall x, a <= x < a + Z.of_nat n -> m' (wa x) = m (wa x)) -> rdn SEGS m' (wa a) n = rdn SEGS m (wa a) n.
Proof.
  intros m m' a n Ha Hn H. revert a Ha Hn H. induction n as [|n IH]; intros a Ha Hn H; [reflexivity|].
  rewrite (Mem.rdn_unfold SEGS m' (wa a) (S n)), (Mem.rdn_unfold SEGS m (wa a) (S n)). unfold Mem.mrd. change (Mem.wa a) with (wa a) in *. rewrite (H a) by lia.
  replace (wa a + 1)%bv with (wa (a + 1)) by (rewrite wa_add1; reflexivity).
  rewrite (IH (a + 1)) by (try lia; intros x Hx; apply H; lia). reflexivity.
Qed.


Lemma bview_grows : forall m m' x, mem_grows m m' -> bview SEGS m x <> None -> bview SEGS m' x <> None.
Proof.
  intros m m' x G H. unfold bview in *. destruct ((0 <=? x) && (x <? 2^64)); [|exact H].
  unfold wview in *. cbn [ov_read_bytes] in *.
  destruct (m (wa x)) as [b|] eqn:E.
  - destruct (m' (wa x)) as [b'|] eqn:E'; [|exfalso; apply (G (wa x)); [rewrite E; discriminate | exact E']].
    destruct (ov_read_bytes SEGS m' (wa x + 1) 0); discriminate.
  - destruct (m' (wa x)) as [b'|] eqn:E'; [destruct (ov_read_bytes SEGS m' (wa x + 1) 0); discriminate | exact H].
Qed.

Lemma grows_wb : forall m mm a l, mem_grows m mm -> mem_grows m (wbytes mm a l).
Proof. intros m mm a l H. eapply mem_grows_trans; [exact H|apply wbytes_grows]. Qed.

Ltac grows_wbs := repeat lazymatch goal with |- mem_grows _ (wbytes _ _ _) => apply grows_wb end.

Lemma efb_mem_grows : forall m idx n mem sz st off, mem_grows m (efb_mem m idx n mem sz st off).
Proof.
  intros m idx n mem sz st off. unfold efb_mem. cbv zeta. grows_wbs.
  destruct (efb_rsv sz n off =? 0); [| destruct (efb_rsv sz n off <? 5)]; grows_wbs;
  destruct (off =? 0); grows_wbs; apply mem_grows_refl.
Qed.

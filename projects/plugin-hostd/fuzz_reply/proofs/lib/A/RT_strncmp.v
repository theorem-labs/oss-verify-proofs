(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contract astrncmp_realizes (lib/A/W_sites.v) proved for
   fuzz_reply.asan's strncmp interceptor, entered at the trampoline __interceptor_trampoline_strncmp 0x4219c. *)
(* Route (R2Cmp, a Theorem Labs lane, 2026-10-29): the body walk is a Theorem Labs lane's (a working branch f8664b31b9c
   lib/A/Bz/A/I_strncmp.v istrncmp_spec), relocated onto fuzz_reply.asan in lib/A/Bz/A/I_strncmp*.v (the interceptor is
   the same 374 instructions modulo relocation, checked word by word); its range check's Section hypothesis is met by
   R_isPoisoned.rip_proof.  The bridge is R1's RT_kit / RT_post (the walk runs on the normalized memory, read back on
   the machine through rom_view), as in RT_strlen.v.  A Theorem Labs lane's donor-form theorem FMstrncmp.astrncmp_holds is NOT used:
   it asks full C strings and store_clean, which W_sites' form does not give.
   The walk takes byte lists b1, b2 of the lengths it reads (strncmp_ok); here they are the bytes [x, x + min(n, kx+1))
   and [y, y + min(n, ky+1)) that W_sites' first_byte / ain_ok premises make visible, and strncmp_fn shows that the
   walk's stop index fits in them and that its answer is 0 exactly when astrn_agree holds. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Img0.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.MState.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_consts.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_qck.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.IcptSpec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strncmpw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strncmpw3.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strncmp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YK14 YP09 YP02 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
AB1v W_syms W_listing W_kit W_tbl W_place W_img W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require FRbz_bridge RT_kit RT_post AE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module NM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Module L6 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Regs6ss.
Module I0 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Img0.
Module BE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Exec.
Module BM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Mem.
Module BF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Frame.
Module BMS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.MState.
Module BI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
Module BK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_consts.
Module BQ := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_qck.
Module BR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.
Module BP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_isPoisoned.
Module SCS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.IcptSpec.
Module SW := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strncmpw.
Module SCP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strncmpw3.
Module SCW := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strncmp.
Module FSB := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FRbz_bridge.
Module K := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_kit.
Module RP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_post.

(* ---- the walk's answer, read on the bytes the reader sees ---- *)
Lemma aux_char : forall K b1 b2,
  (SCS.strncmp_idx_aux b1 b2 K <= K)%nat /\
  (forall j, (j < SCS.strncmp_idx_aux b1 b2 K)%nat ->
     exists z, nth_error b1 j = Some z /\ nth_error b2 j = Some z /\ bv_unsigned z <> 0) /\
  ((SCS.strncmp_idx_aux b1 b2 K < K)%nat ->
     (length b1 <= SCS.strncmp_idx_aux b1 b2 K)%nat \/ (length b2 <= SCS.strncmp_idx_aux b1 b2 K)%nat \/
     exists u w, nth_error b1 (SCS.strncmp_idx_aux b1 b2 K) = Some u /\ nth_error b2 (SCS.strncmp_idx_aux b1 b2 K) = Some w /\
       (bv_unsigned u <> bv_unsigned w \/ bv_unsigned u = 0)).
Proof.
  induction K as [|K IH]; intros b1 b2.
  - (* strncmp_idx_aux recurses on its first list: expose its head before reducing *)
    destruct b1; simpl; (split; [constructor|]); (split; [intros j Hj; inversion Hj | intros Hi; inversion Hi]).
  - destruct b1 as [|u b1'].
    { simpl. split; [apply le_0_n|]. split; [intros j Hj; inversion Hj | intros _; left; apply le_n]. }
    destruct b2 as [|w b2'].
    { simpl. split; [apply le_0_n|]. split; [intros j Hj; inversion Hj | intros _; right; left; apply le_n]. }
    cbn [SCS.strncmp_idx_aux].
    destruct (negb (bv_unsigned u =? bv_unsigned w) || (bv_unsigned u =? 0))%bool eqn:E.
    + split; [lia|]. split; [intros j Hj; lia|]. intros _. right; right. exists u, w.
      split; [reflexivity|]. split; [reflexivity|].
      apply orb_true_iff in E as [E|E].
      * left. apply negb_true_iff, Z.eqb_neq in E. exact E.
      * right. apply Z.eqb_eq in E. exact E.
    + apply orb_false_iff in E as [E1 E2]. apply negb_false_iff, Z.eqb_eq in E1. apply Z.eqb_neq in E2.
      assert (Euw : w = u) by (apply bv_eq; lia). subst w.
      destruct (IH b1' b2') as (IB & IP & IS).
      split; [lia|]. split.
      * intros j Hj. destruct j as [|j]; cbn [nth_error].
        -- exists u. auto.
        -- exact (IP j ltac:(lia)).
      * intros Hi. destruct (IS ltac:(lia)) as [L|[L|(u' & w' & H1 & H2 & H3)]].
        -- left. cbn [length]. lia.
        -- right; left. cbn [length]. lia.
        -- right; right. exists u', w'. cbn [nth_error]. auto.
Qed.

Section fn.
Variable rd : Z -> option Z.

Theorem strncmp_fn : forall (x y n kx ky : Z) (b1 b2 : list byte),
  0 <= n ->
  0 <= kx <= n -> (forall i, 0 <= i < kx -> exists v, rd (x + i) = Some v /\ v <> 0) -> (kx < n -> rd (x + kx) = Some 0) ->
  0 <= ky <= n -> (forall i, 0 <= i < ky -> exists v, rd (y + i) = Some v /\ v <> 0) -> (ky < n -> rd (y + ky) = Some 0) ->
  Z.of_nat (length b1) = Z.min n (kx + 1) -> Z.of_nat (length b2) = Z.min n (ky + 1) ->
  (forall j z, nth_error b1 j = Some z -> rd (x + Z.of_nat j) = Some (bv_unsigned z)) ->
  (forall j z, nth_error b2 j = Some z -> rd (y + Z.of_nat j) = Some (bv_unsigned z)) ->
  SCS.strncmp_ok n b1 b2 /\
  (SCS.strncmp_res n b1 b2 = 0 <->
   (forall i, 0 <= i < n -> (forall j, 0 <= j < i -> rd (x + j) <> Some 0) -> rd (x + i) = rd (y + i))).
Proof.
  intros x y n kx ky b1 b2 Hn Kx Bx Lx Ky By Ly L1 L2 R1 R2.
  destruct (aux_char (Z.to_nat n) b1 b2) as (IB & IP & IS).
  set (i0 := SCS.strncmp_idx_aux b1 b2 (Z.to_nat n)) in *.
  (* the stop index is at or before each string's NUL *)
  assert (Cx : kx < n -> (i0 <= Z.to_nat kx)%nat).
  { intros Hk. destruct (Nat.le_gt_cases i0 (Z.to_nat kx)) as [Le|Gt]; [exact Le|]. exfalso.
    destruct (IP (Z.to_nat kx) Gt) as (z & H1 & _ & Hz).
    pose proof (R1 _ _ H1) as V. rewrite Z2Nat.id in V by lia. rewrite (Lx Hk) in V. injection V as V. lia. }
  assert (Cy : ky < n -> (i0 <= Z.to_nat ky)%nat).
  { intros Hk. destruct (Nat.le_gt_cases i0 (Z.to_nat ky)) as [Le|Gt]; [exact Le|]. exfalso.
    destruct (IP (Z.to_nat ky) Gt) as (z & _ & H2 & Hz).
    pose proof (R2 _ _ H2) as V. rewrite Z2Nat.id in V by lia. rewrite (Ly Hk) in V. injection V as V. lia. }
  assert (EI : SCS.strncmp_idx n b1 b2 = Z.of_nat i0) by reflexivity.
  split.
  - unfold SCS.strncmp_ok, SCS.strncmp_sz. rewrite EI.
    split.
    + destruct (Z_lt_le_dec kx n) as [Hk|Hk]; [pose proof (Cx Hk); lia | lia].
    + destruct (Z_lt_le_dec ky n) as [Hk|Hk]; [pose proof (Cy Hk); lia | lia].
  - unfold SCS.strncmp_res. rewrite EI, Nat2Z.id.
    destruct (Z.eqb_spec (Z.of_nat i0) n) as [Eq|Ne].
    + (* all n positions equal and nonzero *)
      split; [intros _|intros _; reflexivity].
      intros i Hi _. destruct (IP (Z.to_nat i) ltac:(lia)) as (z & H1 & H2 & _).
      pose proof (R1 _ _ H1) as V1. pose proof (R2 _ _ H2) as V2. rewrite Z2Nat.id in V1, V2 by lia.
      rewrite V1, V2. reflexivity.
    + assert (Hlt : (i0 < Z.to_nat n)%nat) by lia.
      assert (B1 : (i0 < length b1)%nat).
      { destruct (Z_lt_le_dec kx n) as [Hk|Hk]; [pose proof (Cx Hk); lia | lia]. }
      assert (B2 : (i0 < length b2)%nat).
      { destruct (Z_lt_le_dec ky n) as [Hk|Hk]; [pose proof (Cy Hk); lia | lia]. }
      destruct (IS Hlt) as [L|[L|(u & w & H1 & H2 & Hstop)]]; [lia | lia |].
      rewrite H1, H2.
      pose proof (R1 _ _ H1) as V1. pose proof (R2 _ _ H2) as V2.
      assert (Pre : forall j, 0 <= j < Z.of_nat i0 -> rd (x + j) <> Some 0).
      { intros j Hj. destruct (IP (Z.to_nat j) ltac:(lia)) as (z & Hz & _ & Hz0).
        pose proof (R1 _ _ Hz) as V. rewrite Z2Nat.id in V by lia. rewrite V. intros E. injection E as E. lia. }
      split.
      * intros Hr.
        assert (Euw : bv_unsigned u = bv_unsigned w).
        { destruct (Z.ltb_spec (bv_unsigned u) (bv_unsigned w)) as [A|A]; [discriminate Hr|].
          destruct (Z.ltb_spec (bv_unsigned w) (bv_unsigned u)) as [C|C]; [discriminate Hr|]. lia. }
        assert (Eu0 : bv_unsigned u = 0) by (destruct Hstop as [S|S]; [lia | exact S]).
        intros i Hi Hpre.
        destruct (Z_lt_le_dec i (Z.of_nat i0)) as [Li|Li].
        -- destruct (IP (Z.to_nat i) ltac:(lia)) as (z & Hz1 & Hz2 & _).
           pose proof (R1 _ _ Hz1) as W1. pose proof (R2 _ _ Hz2) as W2. rewrite Z2Nat.id in W1, W2 by lia.
           rewrite W1, W2. reflexivity.
        -- destruct (Z.eq_dec i (Z.of_nat i0)) as [->|Nei].
           ++ rewrite V1, V2, Euw. reflexivity.
           ++ exfalso. apply (Hpre (Z.of_nat i0)); [lia|]. rewrite V1, Eu0. reflexivity.
      * intros Hagree.
        pose proof (Hagree (Z.of_nat i0) ltac:(lia) Pre) as A. rewrite V1, V2 in A. injection A as A.
        rewrite A. rewrite Z.ltb_irrefl. reflexivity.
Qed.
End fn.

Lemma res_range : forall n b1 b2, -1 <= SCS.strncmp_res n b1 b2 <= 1.
Proof.
  intros n b1 b2. unfold SCS.strncmp_res. cbv zeta.
  destruct (SCS.strncmp_idx n b1 b2 =? n); [lia|].
  destruct (nth_error b1 (Z.to_nat (SCS.strncmp_idx n b1 b2))) as [u|];
  destruct (nth_error b2 (Z.to_nat (SCS.strncmp_idx n b1 b2))) as [w|]; try lia.
  destruct (bv_unsigned u <? bv_unsigned w); [lia|]. destruct (bv_unsigned w <? bv_unsigned u); lia.
Qed.

Lemma res0 : forall b1 b2, SCS.strncmp_res 0 b1 b2 = 0.
Proof. intros b1 b2. unfold SCS.strncmp_res, SCS.strncmp_idx. destruct b1; reflexivity. Qed.

(* Build identity: this is fuzz_reply.asan (ofl_head 0x5f9b68 is the ASan sink head AE2k.tfib_sink_head carries;
   main and LLVMFuzzerTestOneInput begin with their frame allocations at 0x81e4c and 0x840b0), the entry the walks
   call as WS_strncmp is 0x4219c, and its word is `j 0x42fa0` (into ___interceptor_strncmp). *)
Lemma rt_strncmp_build_id :
  AE2k.A_ofl_head = 0x5f9b68 /\ @YI16.sk_ofl_head AE2k.tfib_sink_head = 0x5f9b68 /\
  fr_sigma WS_strncmp = 0x4219c /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x81e4c)) = Some 0xfb010113 /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x840b0)) = Some 0xec010113 /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x4219c)) = Some 0x6050006f.
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity.
Qed.

(* ---- the trampoline and the interceptor walk, in the Bz tree's words ---- *)
Module W.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Tac.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Exec.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.MState.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Step.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.StoreFast.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.P.Str_tac.

(* __interceptor_trampoline_strncmp 0x4219c: `j 0x42fa0` *)
Lemma tramp_strncmp : forall (Q : machine_state -> Prop) R F fc m,
  evt asegs Q (MS R F (Z_to_bv 64 0x42fa0) fc None m (YK11.seg_rom asegs)) ->
  evt asegs Q (MS R F (Z_to_bv 64 0x4219c) fc None m (YK11.seg_rom asegs)).
Proof. intros Q R F fc m H. lstep. exact H. Qed.
End W.

(* the interceptor walk from the trampoline, at the canonical register tree (istrncmp_spec with RIP met; for n = 0,
   which reads no byte, isc_zero) *)
Lemma bz_strncmp : forall regs F fc m0 (p1 p2 n : Z) (b1 b2 : list byte) (lo : Z),
  reg_get regs 10 = Z_to_bv 64 p1 -> reg_get regs 11 = Z_to_bv 64 p2 -> reg_get regs 12 = Z_to_bv 64 n ->
  BF.stk BI.asegs m0 lo (bv_unsigned (reg_get regs 2)) -> lo <= bv_unsigned (reg_get regs 2) - 2256 ->
  BR.kHighShadowEnd < lo -> bv_unsigned (reg_get regs 2) < 2 ^ 63 ->
  0 <= p1 < 2 ^ 64 -> 0 <= p2 < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  (0 < n ->
     BM.bytes_at BI.asegs m0 p1 b1 /\ BM.bytes_at BI.asegs m0 p2 b2 /\ SCS.strncmp_ok n b1 b2 /\
     p1 + SCS.strncmp_sz n b1 b2 <= 2 ^ 47 /\ p2 + SCS.strncmp_sz n b1 b2 <= 2 ^ 47 /\
     (p1 + SCS.strncmp_sz n b1 b2 <= bv_unsigned (reg_get regs 2) - 2256 \/ bv_unsigned (reg_get regs 2) <= p1) /\
     (p2 + SCS.strncmp_sz n b1 b2 <= bv_unsigned (reg_get regs 2) - 2256 \/ bv_unsigned (reg_get regs 2) <= p2) /\
     BQ.chk_ok m0 p1 (SCS.strncmp_sz n b1 b2) /\ BQ.chk_ok m0 p2 (SCS.strncmp_sz n b1 b2)) ->
  BR.m2s_cells m0 -> SW.icells_sc m0 -> BM.mem_inv BI.asegs m0 ->
  BE.evt BI.asegs
    (SCP.istrncmp_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) F fc (SCS.strncmp_res n b1 b2) lo m0)
    (BMS.MS (L6.mkR_of regs) F (Z_to_bv 64 0x4219c) fc None m0 (YK11.seg_rom BI.asegs)).
Proof.
  intros regs F fc m0 p1 p2 n b1 b2 lo Ha0 Ha1 Ha2 ST LO LOLO SPH P1 P2 N0 POS M2S IC MI.
  apply W.tramp_strncmp.
  change (L6.mkR_of regs) with (BF.mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10) (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)).
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite res0. eapply SCW.isc_zero; eassumption.
  - destruct (POS ltac:(lia)) as (B1 & B2 & OK & R1 & R2 & S1 & S2 & C1 & C2).
    eapply (SCW.istrncmp_spec BP.rip_proof); eassumption.
Qed.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma ra_mono : forall rd B x n n', range_addressable rd B x n -> n' <= n -> range_addressable rd B x n'.
Proof. intros rd B x n n' H Hn a Ha. apply H. lia. Qed.

Lemma hull_mono : forall rd x n n', 0 < n' <= n -> shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
  intros rd x n n' Hn H s Hs. apply H. unfold shadow_addr in *.
  assert (D1 : (x + n' - 1) / 8 <= (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : (SHADOW_OFF + (x + n' - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
  lia.
Qed.

(* a byte of the list the walk reads is the byte the donor's reader sees *)
Lemma mk_view : forall (H : word -> bool) mem x (k : nat) j z,
  (forall a, x <= a < x + Z.of_nat k -> aview tfibsegs H mem a <> None) ->
  nth_error (K.mk_slack (mrestrict H mem) x k) j = Some z ->
  aview tfibsegs H mem (x + Z.of_nat j) = Some (bv_unsigned z).
Proof.
  intros H mem x k j z Hv Hn.
  assert (Hj : (j < k)%nat).
  { assert (Hs : nth_error (K.mk_slack (mrestrict H mem) x k) j <> None) by (rewrite Hn; discriminate).
    apply nth_error_Some in Hs. rewrite K.length_mk_slack in Hs. exact Hs. }
  rewrite K.nth_mk_slack in Hn by exact Hj. injection Hn as <-.
  destruct (aview tfibsegs H mem (x + Z.of_nat j)) as [v|] eqn:E.
  - destruct (K.byte_at_view H mem _ v E) as (Eb & Rv). rewrite Eb.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity.
  - exfalso. apply (Hv (x + Z.of_nat j)); [lia | exact E].
Qed.

Theorem rt_strncmp : forall B, AR_laws frsegs B -> K.FrShadowSyms B -> K.FrRtCells B ->
  astrncmp_realizes (PI := PB_fr) B (fr_sigma WS_strncmp).
Proof.
  intros B LAWS TL CELLS ly S W regs mem md x y n kx ky Hpre (Hslo2 & Hpres2) Hx Hy Hn Hn63 Hn40 Hx0 Hy0
    Hfb1 Hfb2 Hxe Hye Hin1 Hin2 (Ham1 & Hra1 & Hhull1) (Ham2 & Hra2 & Hhull2) Hrom (Ham8x & Ham8y).
  change (@pa_segs _ fr_prog_listing PB_fr) with tfibsegs in *.
  pose proof LAWS as LAWS'. change frsegs with tfibsegs in LAWS'.
  change (fr_sigma WS_strncmp) with 0x4219c.
  pose proof Hpre as (HAR & Hret & Hal & Hlo1 & Hhi & HpresE & Hgp & Htp).
  pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
  assert (HK : 2 * ESTACK = 8192) by reflexivity.
  pose proof (RP.ro_agree_of_rom_view W mem Hrom) as RO.
  pose proof (K.walk_cells B LAWS TL CELLS ly S W mem md HAR) as (M2S & _ & _ & _ & ICS & _ & _).
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs) by (unfold spZ; rewrite RP.getr_nz by reflexivity; reflexivity).
  assert (Ha0 : reg_get regs 10 = Z_to_bv 64 x) by (rewrite <- RP.getr_nz by reflexivity; exact Hx).
  assert (Ha1 : reg_get regs 11 = Z_to_bv 64 y) by (rewrite <- RP.getr_nz by reflexivity; exact Hy).
  assert (Ha2 : reg_get regs 12 = Z_to_bv 64 n) by (rewrite <- RP.getr_nz by reflexivity; exact Hn).
  destruct Hfb1 as (Kx & Bx & Lx). destruct Hfb2 as (Ky & By & Ly).
  set (H := w_H W) in *. set (mR := mrestrict H mem) in *. set (sp := spZ regs) in *.
  set (lo := sp - 2 * ESTACK).
  set (L1 := Z.min n (kx + 1)) in *. set (L2 := Z.min n (ky + 1)) in *.
  set (b1 := K.mk_slack mR x (Z.to_nat L1)). set (b2 := K.mk_slack mR y (Z.to_nat L2)).
  assert (LB1 : Z.of_nat (length b1) = L1) by (unfold b1; rewrite K.length_mk_slack; lia).
  assert (LB2 : Z.of_nat (length b2) = L2) by (unfold b2; rewrite K.length_mk_slack; lia).
  assert (V1 : forall a, x <= a < x + Z.of_nat (Z.to_nat L1) -> aview tfibsegs H mem a <> None)
    by (intros a Ha; apply (proj1 (Hin1 a ltac:(lia)))).
  assert (V2 : forall a, y <= a < y + Z.of_nat (Z.to_nat L2) -> aview tfibsegs H mem a <> None)
    by (intros a Ha; apply (proj1 (Hin2 a ltac:(lia)))).
  assert (R1 : forall j z, nth_error b1 j = Some z -> aview tfibsegs H mem (x + Z.of_nat j) = Some (bv_unsigned z))
    by (intros j z Hj; exact (mk_view H mem x _ j z V1 Hj)).
  assert (R2 : forall j z, nth_error b2 j = Some z -> aview tfibsegs H mem (y + Z.of_nat j) = Some (bv_unsigned z))
    by (intros j z Hj; exact (mk_view H mem y _ j z V2 Hj)).
  destruct (strncmp_fn (aview tfibsegs H mem) x y n kx ky b1 b2 ltac:(lia) Kx Bx Lx Ky By Ly LB1 LB2 R1 R2)
    as (OK & RES).
  set (sz := SCS.strncmp_sz n b1 b2) in *.
  assert (SZ : (0 < n -> 1 <= sz) /\ sz <= L1 /\ sz <= L2 /\ sz <= n).
  { destruct OK as (O1 & O2). unfold sz, SCS.strncmp_sz, SCS.strncmp_idx in *. lia. }
  apply (FSB.srr_of_evt K.Hwx_fr W 0x4219c regs mem md
    (RP.walk_at (SCP.istrncmp_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) fp_regs fp_csr (SCS.strncmp_res n b1 b2) lo (NM.normalize_cj I0.rsegs mR)) mR)).
  - refine (_ : BE.evt BI.asegs _ (RP.st_at regs fp_regs (Z_to_bv 64 0x4219c) fp_csr mR)).
    apply RP.bz_transport; [exact RO|].
    apply (bz_strncmp regs fp_regs fp_csr _ x y n b1 b2 lo).
    + exact Ha0.
    + exact Ha1.
    + exact Ha2.
    + rewrite Esp. apply RP.stk_norm_high; [unfold lo, RP.FR_IMG_TOP; lia | unfold TASK_SIZE; lia |].
      apply FSB.stk_of_apresent; [unfold lo; lia | lia | exact Hpres2].
    + rewrite Esp. unfold lo. lia.
    + unfold BR.kHighShadowEnd, lo. lia.
    + rewrite Esp. lia.
    + lia.
    + lia.
    + lia.
    + intros NP.
      assert (Hamr1 : (0 <= x /\ x + L1 <= 0x7fff7fff /\ x + 8 <= 0x7fff7fff) \/
                      (0x10007fff8000 <= x /\ x + L1 <= 0x7fffffffffff /\ x + 8 <= 0x7fffffffffff))
        by (unfold amem_range, YG0f.kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham1, Ham8x; lia).
      assert (Hamr2 : (0 <= y /\ y + L2 <= 0x7fff7fff /\ y + 8 <= 0x7fff7fff) \/
                      (0x10007fff8000 <= y /\ y + L2 <= 0x7fffffffffff /\ y + 8 <= 0x7fffffffffff))
        by (unfold amem_range, YG0f.kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham2, Ham8y; lia).
      assert (Hfr1 : x + L1 - 1 < sp - 8192 \/ sp <= x).
      { apply (K.off_window sp (2 * ESTACK) x L1); [lia | lia |]. intros a Ha. exact (proj2 (Hin1 a Ha)). }
      assert (Hfr2 : y + L2 - 1 < sp - 8192 \/ sp <= y).
      { apply (K.off_window sp (2 * ESTACK) y L2); [lia | lia |]. intros a Ha. exact (proj2 (Hin2 a Ha)). }
      split; [|split; [|split; [exact OK|split; [|split; [|split; [|split; [|split]]]]]]].
      * refine (NM.bytes_at_normalize_cj_low I0.rsegs mR x b1 RO _ _); [rewrite LB1; unfold TASK_SIZE; lia |].
        apply K.bytes_at_mk; [lia | lia | exact V1].
      * refine (NM.bytes_at_normalize_cj_low I0.rsegs mR y b2 RO _ _); [rewrite LB2; unfold TASK_SIZE; lia |].
        apply K.bytes_at_mk; [lia | lia | exact V2].
      * lia.
      * lia.
      * rewrite Esp. lia.
      * rewrite Esp. lia.
      * apply RP.chk_norm; [lia | lia | lia | lia | | | ].
        -- unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd. lia.
        -- apply (ra_mono _ _ _ L1); [exact Hra1 | lia].
        -- apply (hull_mono _ _ L1); [lia | exact (Hhull1 ltac:(lia))].
      * apply RP.chk_norm; [lia | lia | lia | lia | | | ].
        -- unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd. lia.
        -- apply (ra_mono _ _ _ L2); [exact Hra2 | lia].
        -- apply (hull_mono _ _ L2); [lia | exact (Hhull2 ltac:(lia))].
    + exact M2S.
    + exact ICS.
    + apply RP.bz_mem_inv_normalize.
  - intros ms' model' (c & s0 & HQ & Hrel & Hsame & Heqv) Hsbm _.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Es0 & MU & _ & _ & ST').
    subst s0. rewrite Esp in MU, ST'.
    apply (RP.aentry_post_of_walk B LAWS (2 * ESTACK) 2256 [] (fun _ => False) _ (SCS.strncmp_res n b1 b2)
      ly S W regs mem md ms' model' c m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
    + exact Hpre.
    + exact Hslo2.
    + exact RO.
    + lia.
    + intros a Ha. inversion Ha.
    + intros a [].
    + intros a [].
    + exact Hrel.
    + exact Hsame.
    + exact Heqv.
    + rewrite app_nil_r. exact MU.
    + exact ST'.
    + exact Hsbm.
    + intros regs'' mem'' Hr _. rewrite Hr.
      pose proof (res_range n b1 b2) as Rr.
      destruct (Z.eq_dec (SCS.strncmp_res n b1 b2) 0) as [E0|N0].
      * rewrite E0. split; [intros _; exact (proj1 RES E0) | intros _; reflexivity].
      * split.
        -- intros E. exfalso. apply N0. apply (f_equal bv_unsigned) in E. unfold w64 in E.
           rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
           rewrite Z.mod_0_l in E by lia.
           destruct (Z.eq_dec (SCS.strncmp_res n b1 b2) (-1)) as [Em|Nm].
           ++ rewrite Em in E. cbn in E. discriminate E.
           ++ assert (E1 : SCS.strncmp_res n b1 b2 = 1) by lia. rewrite E1 in E. cbn in E. discriminate E.
        -- intros A. exfalso. apply N0. exact (proj2 RES A).
Qed.

End core.

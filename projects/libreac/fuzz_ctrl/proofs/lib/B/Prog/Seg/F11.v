(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names and numbers changed; 1592 of its 1709 lines of code are new or changed and 894 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F12.v, with its module paths and module names changed; 801 of its 923 lines of code are new or changed and 1587 lines of the source are left out. *)
(* Segment F11 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0; v1.8 0x821fc-0x82294,
   segment table row S_F11: IDENTICAL-RENUMBER) = 0x8226c-0x82300, 38 instructions ending with the call of
   reac_identity_ingest (0x87e0c) at 0x82300; FAIL branches
   0x82288 / 0x822e8, trap branches T23-T25 (0x82274 / 0x82294 / 0x822a0), shadow rows 25 / 26 (the checks at
   0x822b4 / 0x822d0). The segment runs from the F10 exit cut 0x8226c (the identity reply was accepted, a1 = ir_s - 13)
   to the return point 0x82304 of the ingest call (the F12 entry).

   Image A inlines the record sum here (its down-counter loop a1 = a3 + 5, a4 += byte[s6 + 16 + i]); image B calls it
   at 0x82284 (record_sum_closes, the function check_1 at 0x83614), so the loop runs inside the callee, whose contract
   (lib/B/Prog/record_sum_closes_c.v) gives a0 = 1 when the sum of the N bytes closes (recsum bs = 0).
     0x8226c li a0,-17 ; ld a2,312(s1) ; bltu a0,a2   T23: blk = [A+312] = phi + 18, blk + 16 does not wrap
     0x82278 ld a0,312(s1) ; addi a0,a0,16           a0 = phi + 34, the record ir_rec = G[34 .. 26 + ir_s)
     0x82280 addi a1,a1,5                            a1 = ir_s - 8, its length
     0x82284 jal 83614                               record_sum_closes(phi + 34, ir_s - 8); writes [sp - 16, sp)
     0x82288 beqz a0,82fa4                           recsum (ir_rec G) = 0 (ir, from reply_ok): a0 = 1, not taken
     0x8228c-0x822a0                                 T24 / T25: blk + 18 / blk + 19 do not wrap, not taken
     0x822a4-0x822b4 a4 = blk ; a0 = phi + 36 ; lb a2 = the shadow byte of phi + 36
     0x822b8 ld a1,288(s1) ; lhu a1,0(a1)            a1 = the u16 at pa = fr + 256 (the reply address cell)
     0x822c0 bnez a2,82d74                           the shadow byte is 0 (the granule of phi + 36 lies inside the
                                                     addressable block HB(phi), len >= 50): the slow path and the
                                                     error path 0x8308c are not reached
     0x822c4-0x822d8                                 the same for phi + 37 (slow path 0x82d80, error path 0x83090);
                                                     a0 = G[36]
     0x822dc lbu a2 ; slli ; or                      a0 = G[36] << 8 | G[37]
     0x822e8 bne a0,a1,82fa4                         reply_addr G = [G[37]; G[36]] is that u16: not taken
     0x822ec-0x822fc a2 = [[A+304]] = [fr+272] = phi + 38, a3 = [[A+296]] = [fr+304] = ir_s - 13,
                     a0 = [A+176] = fr + 2688
     0x82300 jal 87e0c                               reac_identity_ingest(fr + 2688, ad, phi + 38, ir_s - 13);
                                                     writes [sp - 32, sp) and [fr + 2688, fr + 2726)
   The callees are Section hypotheses: HRSC (record_sum_closes_c.v) and HING (reac_identity_ingest_c.v). The whole
   segment writes W = [sp - 32, sp) and [fr + 2688, fr + 2726) (the write set of lib/B/Prog/Seg/F16.v); FRA and ENT
   cross it by f11_fra (the per-arm heap-invariant analysis of F16's f16_fra, then Tac_slot.sl_fr_cl / ent_store),
   which reads FRA only through its named lemmas and f11_fra_get (tauto, not by position). The heap block Phi lies
   below stklo and outside the frame (AC.a_laws_blocks with the frame-location disjunction of FRA: f11_place).

   Entry cut: the official Inv_B8226c_at of lib/B/Prog/SlotInv.v. FTURN gives the spill [A+224], FLI's RAD the
   identity record's 38 addressable bytes, REC0 the record t_ID j the ingest call updates and the fragment record,
   RCA the three reply cells. Exit cut: the official Inv_B82304_at, whose FS9 ([A+248] = 1 - sum_ok) is f10_K's
   [A+248] spill (neither callee writes the spill area). The exit's record RECR: the ingest post writes snd (ING (t_ID j) ad pl) at
   fr + 2688, which is t_IDr j on this ir-true path (SlotModel.rp_id), and id_ok survives the ingest
   (RcIdentLib.ING_id_ok). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require record_sum_closes_c reac_identity_ingest_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcParse RcReply RcRec RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_fs Tac_ro.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Import ListNotations.
(* lib.Prog's RcParse / RcFrag chain loads lib/Reusable/YK11.v, so the short name YK11 would resolve to that copy;
   this file's registers, mkst and FPState must be image B's, as SlotInv's and Tac_slot's are. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.
(* The v1.9 frame size and its shadow length are the named constants FRAME_BYTES = 3136 and FRAME_SHADOW = 392 of
   SlotInv.v; every lia of this file gets their values. *)
Local Ltac lia := pose proof FRAME_BYTES_val; pose proof FRAME_SHADOW_val; Lia.lia.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module BZB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.BzBridge.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Mem.
Module UEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.
Module UMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.MState.
Module UFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Frame.
Module LEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LSt := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCl := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module RSC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.record_sum_closes_c.
Module IGC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_identity_ingest_c.

(* ---- The two step engines. The callee contracts speak lib/Lib (Exec.evt, MState.MS, Frame.mkR); this file steps
   with the UL engine (lib/B/Tk/UL), whose evt, MS and mkR have the same bodies. ---- *)
Lemma f11_lu_msteps : forall s s', LEx.msteps rsegs s s' -> UEx.msteps rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH]; [apply UEx.msteps_refl|].
  eapply UEx.msteps_cons; [exact Hs | exact IH].
Qed.
Lemma f11_lu_evt : forall Q ms, LEx.evt rsegs Q ms -> UEx.evt rsegs Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (f11_lu_msteps _ _ H) | exact HQ]. Qed.
(* A contract's post state, in the constructors the UL step tactic matches. *)
Lemma f11_MS_ul : forall R F pc fc rv m ro, LMS.MS R F pc fc rv m ro = UMS.MS R F pc fc rv m ro.
Proof. reflexivity. Qed.
Lemma f11_mkR_ul : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
  x25 x26 x27 x28 x29 x30 x31,
  LFr.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 =
  UFr.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31.
Proof. reflexivity. Qed.

(* mkR_of regs is definitionally the explicit 31-slot register map; exposing it lets `step` read a slot we have
   rewritten to a concrete value (as lib/B/Prog/Seg/F22.v). *)
Lemma f11_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a known register slot `getr regs r` to its carried concrete value, from H : rg regs r v. *)
Ltac f11_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* ---- Carried byte facts in the `ov_read_bytes _ _ _ n = Some bs` form the UL `step` consumes. ---- *)
Lemma f11_rd1 : forall m a b, LMem.bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (ULMem.wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (ULMem.bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.
Lemma f11_rd2 : forall m a bs, LMem.bytes_at rsegs m a bs -> length bs = 2%nat ->
  ov_read_bytes rsegs m (ULMem.wa a) 2 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (ULMem.bytes_at_ov_read rsegs m a bs 0 2 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.
Lemma f11_rd8 : forall m a bs, LMem.bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (ULMem.wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (ULMem.bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.
(* One byte k of a carried byte list. *)
Lemma f11_rdk : forall m a (bs : list byte) k, LMem.bytes_at rsegs m a bs -> (k < length bs)%nat ->
  ov_read_bytes rsegs m (ULMem.wa (a + Z.of_nat k)) 1 = Some [nth k bs cp_z].
Proof.
  intros m a bs k H Hk.
  rewrite (ULMem.bytes_at_ov_read rsegs m a bs k 1 H ltac:(lia)). f_equal.
  clear H. revert k Hk. induction bs as [|b bs IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hk. lia.
Qed.

(* A sub-range of a carried byte range. *)
Lemma f11_nth_sub : forall (l : list byte) k n i, (i < n)%nat ->
  nth_error (firstn n (skipn k l)) i = nth_error l (k + i).
Proof.
  intros l k. revert l. induction k as [|k IH]; intros l n i Hi.
  - cbn [skipn Nat.add]. revert n i Hi. induction l as [|x l IHl]; intros n i Hi.
    + rewrite firstn_nil. destruct i; reflexivity.
    + destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth_error]. apply IHl. lia.
  - destruct l as [|x l].
    + rewrite skipn_nil, firstn_nil. destruct i; reflexivity.
    + cbn [skipn Nat.add nth_error]. apply IH. exact Hi.
Qed.
Lemma f11_sub : forall m a (bs : list byte) k n, LMem.bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  LMem.bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n (H0 & H1 & H) Hkn.
  assert (HL : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite HL; lia|].
  intros i Hi. rewrite HL in Hi. rewrite f11_nth_sub by exact Hi.
  replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
  apply H. lia.
Qed.

(* `bltu x,y` is not taken when y <= x (unsigned); the left operand may be a sign-extended immediate (the UBSan
   checks `li aX,-c; bltu aX,blk`), so it is compared through its value mod 2^64 (as lib/B/Prog/Seg/F10.v). *)
Lemma f11_ltu_false : forall x y, 0 <= y < 2 ^ 64 -> y <= x mod 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hy Hxy. unfold bv_ltu. rewrite LMS.unsigned_lit_wrap, (LMS.unsigned_lit y) by lia.
  apply Z.ltb_ge. lia.
Qed.
Ltac f11_mlia := rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia.

(* The shadow byte of phi + c (7 <= c <= 42) is 0 when the heap block (phi, len) with len >= 50 is addressable: the
   whole 8-byte granule of phi + c lies in [phi, phi + 50) (AsanRTFacts.meta8 on the granule start; the twin of
   lib/B/Prog/Seg/F10.v f10_sh26). *)
Lemma f11_sh : forall m phi L c, addressable m phi (AC.a_size L) -> 50 <= L -> 7 <= c <= 42 ->
  LMem.bytes_at rsegs m (Z.shiftr (phi + c) 3 + ASAN_K) [Z_to_bv 8 0].
Proof.
  intros m phi L c HA HL Hc.
  pose proof HA as (Hp0 & _ & _ & _).
  pose proof (Z.mod_pos_bound (phi + c) 8 ltac:(lia)) as Hr.
  assert (H8 : addressable m (phi + (c - (phi + c) mod 8)) 8)
    by (apply (addressable_sub m phi (AC.a_size L)); [exact HA | lia | lia | unfold AC.a_size; lia]).
  destruct (meta8 m _ H8) as [[_ RB] _].
  assert (E : Z.shiftr (phi + (c - (phi + c) mod 8)) 3 = Z.shiftr (phi + c) 3).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (Z.div_mod (phi + c) 8 ltac:(lia)) as D.
    replace (phi + (c - (phi + c) mod 8)) with ((phi + c) / 8 * 8) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  rewrite E in RB. exact RB.
Qed.

(* The shadow byte of an application address lies below HIGHMEM_BEG, hence below any stack window of this function. *)
Lemma f11_sh_lt : forall a, 0 <= a -> a < APPMEM_END -> Z.shiftr a 3 + ASAN_K + 1 <= HIGHMEM_BEG.
Proof.
  intros a H0 H1. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold ASAN_K, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* Byte values, the u16 of the reply address cell, and the byte combine of 0x822d4-0x822e4. *)
Lemma f11_ubv : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range _ b) as H. unfold bv_modulus in H. exact H. Qed.
Lemma f11_le2 : forall b0 b1 : byte,
  [b0; b1] = LMem.le2 (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1)).
Proof.
  intros b0 b1. pose proof (f11_ubv b0) as R0. pose proof (f11_ubv b1) as R1.
  unfold LMem.le2. rewrite LMS.unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  replace ((bv_unsigned b0 + 256 * bv_unsigned b1) / 256) with (bv_unsigned b1)
    by (rewrite Z.mul_comm, Z.div_add, Z.div_small by lia; lia).
  f_equal; [|f_equal]; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    change (2 ^ 8) with 256.
  - rewrite Z.mul_comm, Z.mod_add, Z.mod_small by lia. reflexivity.
  - rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma f11_zx16 : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zx16. rewrite (LMS.unsigned_lit v) by lia.
  rewrite Z.mod_small by (change (2 ^ 16) with 65536; lia). reflexivity.
Qed.
Lemma f11_cmp16 : forall b36 b37 : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b36)) 8))) (bv_unsigned (zxb b37)))
  = Z_to_bv 64 (bv_unsigned b37 + 256 * bv_unsigned b36).
Proof.
  intros b36 b37. pose proof (f11_ubv b36) as R6. pose proof (f11_ubv b37) as R7.
  unfold zxb. rewrite (LMS.unsigned_lit (bv_unsigned b36)), (LMS.unsigned_lit (bv_unsigned b37)) by lia.
  rewrite (LMS.unsigned_lit (Z.shiftl (bv_unsigned b36) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia. reflexivity.
Qed.

(* ---- Write sets (the helpers of lib/B/Prog/Seg/F16.v, whose write set this segment shares). ---- *)
Lemma f11_out2 : forall lo1 hi1 lo2 hi2 x,
  (x < lo1 \/ hi1 <= x) -> (x < lo2 \/ hi2 <= x) -> LFr.outside [(lo1, hi1); (lo2, hi2)] x.
Proof. intros lo1 hi1 lo2 hi2 x H1 H2. cbn. split; [lia | split; [lia | exact I]]. Qed.
Lemma f11_not_out2 : forall lo1 hi1 lo2 hi2 x,
  ~ LFr.outside [(lo1, hi1); (lo2, hi2)] x -> (lo1 <= x < hi1) \/ (lo2 <= x < hi2).
Proof.
  intros lo1 hi1 lo2 hi2 x H.
  destruct (Z_lt_le_dec x lo1) as [H1|H1].
  - destruct (Z_lt_le_dec x lo2) as [H3|H3].
    + exfalso. apply H. apply f11_out2; lia.
    + destruct (Z_lt_le_dec x hi2) as [H4|H4]; [right; lia|].
      exfalso. apply H. apply f11_out2; lia.
  - destruct (Z_lt_le_dec x hi1) as [H2|H2]; [left; lia|].
    destruct (Z_lt_le_dec x lo2) as [H3|H3].
    + exfalso. apply H. apply f11_out2; lia.
    + destruct (Z_lt_le_dec x hi2) as [H4|H4]; [right; lia|].
      exfalso. apply H. apply f11_out2; lia.
Qed.
Lemma f11_out_dec : forall (W : list (Z * Z)) x, LFr.outside W x \/ ~ LFr.outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x; [left; exact I|].
  destruct (Z.le_gt_cases lo x) as [H1|H1].
  - destruct (Z.le_gt_cases hi x) as [H2|H2].
    + destruct (IH x) as [Ho|Hno]; [left; split; [lia|exact Ho] | right; intros [_ Ho]; exact (Hno Ho)].
    + right. intros [Hc _]. apply Hc. lia.
  - destruct (IH x) as [Ho|Hno]; [left; split; [lia|exact Ho] | right; intros [_ Ho]; exact (Hno Ho)].
Qed.
(* Every interval of W starts at or above GT, so W misses the runtime's cells (all in the image). *)
Lemma f11_dj_GT : forall (W : list (Z * Z)) a n,
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> a + n <= AC.GT -> LFr.disjoint_from W a n.
Proof.
  intros W a n H Hn. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  split.
  - left. pose proof (H lo hi ltac:(left; reflexivity)). lia.
  - apply IH. intros lo' hi' Hin. apply (H lo' hi'). right. exact Hin.
Qed.
Lemma f11_rtdj_GT : forall (W : list (Z * Z)),
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> AsanRTInv.rt_disjoint W.
Proof.
  intros W H. unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF,
    RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
    RT_AGLOB, RT_AGLOB_LEN, AC.GT in *.
  repeat split; apply (f11_dj_GT W); solve [ exact H | unfold AC.GT; lia ].
Qed.
(* A non-app address is outside an all-app write set. *)
Lemma f11_out_not_app : forall (W : list (Z * Z)) x, all_app W -> ~ app_mem x -> LFr.outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x HA Hn; [exact I|].
  destruct HA as [Ha HA].
  split; [intro Hr; apply Hn; apply Ha; lia | apply IH; [exact HA | exact Hn]].
Qed.
(* ro_agree crosses a write set whose intervals all start at or above GT (every read-only byte is below GT). *)
Lemma f11_ro_lt_GT : forall x, LMem.ro_addr rsegs x = true -> bv_unsigned x < AC.GT.
Proof.
  intros x H. unfold LMem.ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|discriminate H].
  destruct (BZB.find_segment_below rsegs AC.GT (bv_unsigned x) 1 s img_tops_true E ltac:(lia))
    as [L|L]; [exact L | lia].
Qed.
Lemma f11_out_GT : forall (W : list (Z * Z)) x,
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> x < AC.GT -> LFr.outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x H Hx; [exact I|].
  split.
  - pose proof (H lo hi ltac:(left; reflexivity)). lia.
  - apply IH; [intros lo' hi' Hin; apply (H lo' hi'); right; exact Hin | exact Hx].
Qed.
Lemma f11_ro_keep : forall (W : list (Z * Z)) m m',
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> LFr.munch W m m' ->
  ro_agree rsegs m -> ro_agree rsegs m'.
Proof.
  intros W m m' HGT MU Hro a Ha.
  pose proof (Hro a Ha) as H. unfold LMem.mrd in H |- *.
  rewrite (MU a (f11_out_GT W (bv_unsigned a) HGT (f11_ro_lt_GT a Ha))). exact H.
Qed.
(* The runtime cells the callees read and the shadow map are outside the callees' stack scratch and outside the
   identity record. *)
Lemma f11_rt_out1 : forall sp x k, HIGHMEM_BEG <= sp - k -> 0 <= k ->
  (GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x) ->
  LFr.outside [(sp - k, sp)] x.
Proof.
  intros sp x k Hsp Hk Hx. cbn. split; [|exact I].
  unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia.
Qed.
Lemma f11_rt_out2 : forall sp fr x, HIGHMEM_BEG <= sp - 32 -> AC.GT <= fr ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  (GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x) ->
  LFr.outside [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)] x.
Proof.
  intros sp fr x Hsp Hfr Happ Hx.
  assert (Hs : ~ (sp - 32 <= x < sp)).
  { unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
  assert (Hi : ~ (fr + 2688 <= x < fr + 2688 + 38)).
  { destruct Hx as [Hx|[Hx|Hx]].
    - unfold GOT_CELL_K, AC.GT in *. lia.
    - unfold CELL_K, AC.GT in *. lia.
    - intro Hin. exact (app_not_shadow x (Happ x ltac:(lia)) Hx). }
  cbn. split; [exact Hs | split; [exact Hi | exact I]].
Qed.
(* The FRAME_SHADOW shadow bytes of the frame base are all shadow addresses. *)
Lemma f11_frame_shadow : forall fr x, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x.
Proof.
  intros fr x Happ Hx.
  assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
  { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (Hinfr : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
  pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hinfr)) as His.
  replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
  unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia.
Qed.
(* A byte inside a carried byte range is present. *)
Lemma f11_present : forall m A bs q, LMem.bytes_at rsegs m A bs -> A <= q < A + Z.of_nat (length bs) ->
  exists b, LMem.mrd rsegs m (LMem.wa q) = Some b.
Proof.
  intros m A bs q (Ha & Hl & H) Hq.
  assert (Hk : (Z.to_nat (q - A) < length bs)%nat) by lia.
  pose proof (H (Z.to_nat (q - A)) Hk) as HH.
  replace (A + Z.of_nat (Z.to_nat (q - A))) with q in HH by lia.
  destruct (nth_error bs (Z.to_nat (q - A))) as [b|] eqn:Eb.
  - exists b. exact HH.
  - apply nth_error_None in Eb. lia.
Qed.
(* The bytes of a CB cell, and the cell of a writable byte range. *)
Lemma f11_cb_bytes : forall m a n bs, LSt.rw_cells rsegs m a [LCl.CB n bs] -> LMem.bytes_at rsegs m a bs.
Proof. intros m a n bs [[_ H] _]. cbn [LCl.cells_bytes LCl.cbytes] in H. rewrite app_nil_r in H. exact H. Qed.
Lemma f11_cb_rw : forall m a n bs, LMem.bytes_at rsegs m a bs -> length bs = n ->
  LMem.wr_at rsegs m a (Z.of_nat n) -> LSt.rw_cells rsegs m a [LCl.CB n bs].
Proof.
  intros m a n bs Hb Hl Hw. split.
  - split; [cbn; split; [exact Hl | exact I]|]. cbn [LCl.cells_bytes LCl.cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [LCl.cells_size LCl.csize Nat.add]. rewrite Nat.add_0_r. exact Hw.
Qed.
(* A writable sub-range of a byte-backed stack range, after a run that keeps writability. *)
Lemma f11_wr_of_stk : forall m m' lo hi a n, LFr.stk rsegs m lo hi -> LFr.wmono rsegs m m' ->
  lo <= a -> a + n <= hi -> 0 <= n -> LMem.wr_at rsegs m' a n.
Proof.
  intros m m' lo hi a n (H0 & H1 & H) WM Ha Hn Hn0. split; [lia|]. split; [lia|].
  intros i Hi. apply WM. destruct (H (a + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.
(* stk across a run: outside the write set by munch, inside it by the caller's presence facts. *)
Lemma f11_stk_tr : forall W m m' lo hi,
  LFr.stk rsegs m lo hi -> LFr.munch W m m' -> LFr.wmono rsegs m m' ->
  (forall x, lo <= x < hi -> LFr.outside W x \/ (exists b, LMem.mrd rsegs m' (LMem.wa x) = Some b)) ->
  LFr.stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM HK.
  split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb).
  split; [exact (WM (LMem.wa a) Hw)|].
  destruct (HK a Ha) as [Ho|Hp].
  - exists b. unfold LMem.mrd in *. rewrite (MU (LMem.wa a)); [exact Hb|].
    unfold LMem.wa. rewrite LMS.unsigned_lit by lia. exact Ho.
  - exact Hp.
Qed.
(* Z_to_bv 64 is injective on [0, 2^64). *)
Lemma f11_bv_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
  intros x y Hx Hy E. apply (f_equal (bv_unsigned (n:=64))) in E.
  rewrite !LMS.unsigned_lit in E by lia. exact E.
Qed.
(* A spilled word at s1 + off read at the spill base A, and its move across a run that keeps s1 and writes outside
   the 448-byte spill area. *)
Lemma f11_spill : forall regs m off v A, spill regs m off v -> rg regs 9 A ->
  0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 -> q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA H0 H1 Hoff.
  unfold rg in HA, HA'. rewrite HA in HA'.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite LMem.length_le8 in Hq1.
  assert (E : A' = A).
  { apply (f_equal (bv_unsigned (n:=64))) in HA'. rewrite !LMS.unsigned_lit_wrap in HA'.
    rewrite (Z.mod_small A) in HA' by lia. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.
Lemma f11_spill_move : forall W regs regs' m m' off v A,
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 ->
  getr regs' 9 = getr regs 9 -> LFr.munch W m m' -> (forall x, A <= x < A + 448 -> LFr.outside W x) ->
  spill regs' m' off v.
Proof.
  intros W regs regs' m m' off v A Hs HA H0 H1 Hoff E9 MU HO.
  pose proof (f11_spill regs m off v A Hs HA H0 H1 Hoff) as Hq.
  exists A. split; [unfold rg in *; rewrite E9; exact HA|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite LMem.length_le8. intros x Hx. apply HO. lia.
Qed.
(* FM (v1.9: [A+184] = the fill flag, s8 = k, s6 = 1, s9 = sum_ok, [A+312] = blk) across a run that keeps s1, s6, s8
   and s9 and writes outside the 448-byte spill area. *)
Lemma f11_FM_move : forall W g j phi fr regs regs' m m' A, FM g j phi fr regs m ->
  rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> LFr.munch W m m' ->
  (forall x, A <= x < A + 448 -> LFr.outside W x) ->
  getr regs' 9 = getr regs 9 -> getr regs' 22 = getr regs 22 -> getr regs' 24 = getr regs 24 ->
  getr regs' 25 = getr regs 25 -> FM g j phi fr regs' m'.
Proof.
  intros W g j phi fr regs regs' m m' A (S184 & R24 & R22 & R25 & S312) HA H0 H1 MU HO E9 E22 E24 E25.
  split; [exact (f11_spill_move W regs regs' m m' 184 _ A S184 HA H0 H1 ltac:(lia) E9 MU HO)|].
  split; [unfold rg in *; rewrite E24; exact R24|].
  split; [unfold rg in *; rewrite E22; exact R22|].
  split; [unfold rg in *; rewrite E25; exact R25|].
  exact (f11_spill_move W regs regs' m m' 312 _ A S312 HA H0 H1 ltac:(lia) E9 MU HO).
Qed.

Section F11.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contracts: record_sum_closes (check_1, 0x83614) and reac_identity_ingest (0x87e0c). *)
Hypothesis HRSC : RSC.record_sum_closes_contract.
Hypothesis HING : IGC.reac_identity_ingest_contract.

(* The FRA facts this file reads, taken out of FRA by tauto (not by position, so FRA may grow): RT, the heap
   invariant, ro_agree, the model not halted, sp = aspZ, the stack-low bound, s1 = A and s10 = K, the frame's
   alignment and its place below A, A's place below S, sp near S, the entry-anchored slot window, and the
   frame-location disjunction without its selector and FakeStack-record parts. *)
Lemma f11_fra_get : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists A sp,
    AsanRTInv.RT sp mem md /\ AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md /\
    ro_agree rsegs mem /\ m_halted md = None /\ AC.aspZ regs = sp /\
    AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= g_S g - AF.SLOT_STACK /\
    rg regs 9 A /\ rg regs 26 ASAN_K /\ fr mod 32 = 0 /\ sp <= A /\ fr + FRAME_BYTES <= A /\ A + 448 <= g_S g /\
    g_S g - 4096 < sp /\ g_S g < APPMEM_END /\ LFr.stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g) /\
    ((sp = fr /\
        (forall a, fr <= a < fr + FRAME_BYTES -> AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END)) \/
     ((forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS + 6328320 <= fr) /\
        (forall a, fr <= a < fr + FRAME_BYTES -> AC.a_in_fs AC.ASYMS mem a))).
Proof.
  intros g fr hb regs mem md H. destruct H as (A & sp & s5 & H). exists A, sp. tauto.
Qed.

(* The heap block (phi, n): below stklo, so below the sp-anchored window [sp - FN_STACK, sp) (fra_win), and apart
   from the frame. Real arm: the frame is in [stklo, APPMEM_END). Side arm: every frame byte is in the side stack FS
   and no block byte is (AC.a_laws_blocks), so a block that met the frame would share a byte with it. *)
Lemma f11_place : forall g fr phi n regs mem md,
  FRA B APIf ra g fr (hb1 phi n) regs mem md -> 0 < n ->
  phi + n <= AC.aspZ regs - FN_STACK /\ (phi + n <= fr \/ fr + FRAME_BYTES <= phi).
Proof.
  intros g fr phi n regs mem md HFRA Hn.
  pose proof (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hlow & _).
  destruct (f11_fra_get g fr _ regs mem md HFRA) as (A & sp & _ & HAH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & Hloc).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (lw_blocks (APIf rc) _ _ _ phi n HAH ltac:(cbn; left; reflexivity)) as [_ Hp4096 Hpst _ Hblk].
  split; [lia|].
  destruct Hloc as [[_ Hreal] | [_ Hfs]].
  - destruct (Z_le_gt_dec (phi + n) fr) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [L2|L2]; [right; exact L2|].
    destruct (Hreal (Z.max phi fr) ltac:(lia)) as (Hr & _). lia.
  - destruct (Z_le_gt_dec (phi + n) fr) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [L2|L2]; [right; exact L2|].
    exfalso. destruct (Hblk (Z.max phi fr) ltac:(lia)) as (_ & _ & _ & _ & Hn').
    exact (Hn' (Hfs (Z.max phi fr) ltac:(lia))).
Qed.

(* FRA and ENT across the segment's two calls: they write only W = [sp - 32, sp) (the callees' stack scratch; the
   ingest frame is the larger of the two) and the 38 identity bytes [fr + 2688, fr + 2726) inside the frame body
   (the write set of lib/B/Prog/Seg/F16.v, whose per-arm analysis f16_fra this follows). The heap invariant and
   the stack bounds: the stack part is a_store_ok on both arms; the identity part is a_store_ok on the real arm
   (the frame is in [stklo, APPMEM_END)) and inside the side stack on the side arm (Tac_fs.a_fs_ok_store_AH). FRA
   then crosses by Tac_slot.sl_fr_cl (W misses the low image, the frame header, the spills A+56..A+72 and A+336,
   the saved registers, the frame's shadow bytes and the input block; FSREC by Tac_slot.fsrec_stklo) and moves to
   the materialized model by sl_fra_move; ENT crosses by ent_store and ent_mat. *)
Lemma f11_fra : forall g fr hb regs regs' mem mem' md md' A,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  LFr.munch [(AC.aspZ regs - 32, AC.aspZ regs); (fr + 2688, fr + 2688 + 38)] mem mem' ->
  LFr.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  LFr.stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs) ->
  (forall q, fr + 2688 <= q < fr + 2688 + 38 -> exists b, LMem.mrd rsegs mem' (LMem.wa q) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md' /\ ENT APIf g hb mem' md'.
Proof.
  intros g fr hb regs regs' mem mem' md md' A HFRA HENT Hs1 HAb
    MU WM HroM HSTKW HPRES E2 E3 E4 E8 E9 E19 E26 Hmat.
  destruct (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGTfr & Hfrapp).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hfrw & _ & _ & _).
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hlow & _).
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  assert (Hdisjfr : fr + FRAME_BYTES <= AC.aspZ regs - 32 \/ AC.aspZ regs <= fr)
    by (apply Hfrw; unfold FN_STACK, AF.SLOT_STACK; lia).
  destruct (f11_fra_get g fr hb regs mem md HFRA) as (A2 & sp & HRT & HAH & Hro & Hhalt & Haspz & Hstklo &
    Hr9 & Hr26 & Hfrm & Hspa & Hfa & HA448 & HS4 & HAPP & Hwin & Hloc).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhi.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (EA : A2 = A).
  { apply f11_bv_inj; [lia | lia |]. unfold rg in *. rewrite <- Hr9. exact Hs1. }
  subst A2.
  rewrite Haspz in Hdisjfr, MU, HSTKW, Hlow.
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (Hfrhi : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Hfrapp (fr + FRAME_BYTES - 1) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
  set (W := [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)]).
  assert (HOW : forall x, (x < sp - 32 \/ sp <= x) -> (x < fr + 2688 \/ fr + 2688 + 38 <= x) ->
                  LFr.outside W x) by (intros x H1 H2; subst W; apply f11_out2; assumption).
  assert (Hallapp : all_app W).
  { subst W. cbn [all_app]. split; [|split; [|exact I]].
    - intros a Ha. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia.
    - intros a Ha. apply Hfrapp. lia. }
  assert (HGTW : forall lo hi, In (lo, hi) W -> AC.GT <= lo).
  { subst W. intros lo hi Hin. cbn in Hin.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold AC.GT in *; lia. }
  assert (Hrtdj : AsanRTInv.rt_disjoint W) by exact (f11_rtdj_GT W HGTW).
  assert (Hwr : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
    by (intros q _ Hq; exact (WM (Z_to_bv 64 q) Hq)).
  (* the heap invariant, the stack bounds and the owned set after the run, by arm (ENT reads the last three) *)
  assert (HAHS : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
                 (forall q, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md q <->
                            AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md q) /\
                 AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                 AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                 AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                 AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { destruct Hloc as [[Hspfr Hreal] | [Hfsb Hfs]].
    - assert (Hmc : forall q, 0 <= q < 2 ^ 64 ->
                ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
      { intros q Hq Hnok.
        destruct (f11_out_dec W q) as [Ho|Hno].
        - apply MU. rewrite LMS.unsigned_lit by exact Hq. exact Ho.
        - exfalso. apply Hnok. subst W. apply f11_not_out2 in Hno. destruct Hno as [Hx|Hx].
          + right; left. unfold AF.SLOT_STACK in *. split; lia.
          + right; left. apply Hreal. lia. }
      destruct (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH Hmc Hwr) as [HAH' Hown' HSTKeq HSTKHIeq].
      split; [exact HAH'|]. split; [exact Hown'|]. split; [exact HSTKeq | exact HSTKHIeq].
    - destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FS & HFSr & HwFS & HFSlo & HFShi).
      pose proof (Hfsb FS HwFS HFSr) as HFSfr.
      destruct (lw_fs_place (APIf rc) (hb ++ g_H g) mem md FS HAH HwFS HFSr) as [HGTFS HFSend _ HFSapp].
      assert (HFS64 : FS + AC.FS_SIZE <= 2 ^ 64).
      { pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(unfold AC.FS_SIZE; lia)) as H.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
      assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                exists b, mbyte rsegs mem' q = Some b).
      { intros q Hq (b & Hb).
        destruct (f11_out_dec W q) as [Ho|Hno].
        - exists b. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
          rewrite LMS.unsigned_lit by exact Hq. exact Ho.
        - subst W. apply f11_not_out2 in Hno. destruct Hno as [Hx|Hx].
          + destruct HSTKW as (_ & _ & Hs). destruct (Hs q ltac:(unfold FN_STACK, AF.SLOT_STACK in *; lia))
              as (_ & bb & Hbb). exists bb. exact Hbb.
          + destruct (HPRES q ltac:(lia)) as (bb & Hbb). exists bb. exact Hbb. }
      assert (Hmeta : forall q, Tac_fs.fs_meta FS q -> LFr.outside W q).
      { intros q Hq. pose proof (Tac_fs.fs_meta_below FS q Hq) as Hqb.
        apply HOW; unfold AF.SLOT_STACK in *; lia. }
      assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
                ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                ~ (FS <= q < FS + AC.FS_SIZE) ->
                ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
                mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
      { intros q Hq Hnok Hnfs Hnsh.
        destruct (f11_out_dec W q) as [Ho|Hno].
        - apply MU. rewrite LMS.unsigned_lit by exact Hq. exact Ho.
        - exfalso. subst W. apply f11_not_out2 in Hno. destruct Hno as [Hx|Hx].
          + apply Hnok. right; left. unfold AF.SLOT_STACK in *. split; lia.
          + apply Hnfs. lia. }
      destruct (Tac_fs.a_fs_ok_store_AH AC.ASYMS _ _ _ _ W (hb ++ g_H g) mem mem' md FS
                  LAWS HAH HwFS HFSr HFS64 MU Hwr Hpres Hmeta Hagree)
        as (HAH' & Hown' & HSTKeq & HSTKHIeq).
      split; [exact HAH'|]. split; [exact Hown'|]. split; [exact HSTKeq | exact HSTKHIeq]. }
  destruct HAHS as (HAHm & Hownm & HSTK & HSTKHI).
  assert (HSTKS : LFr.stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
  { apply (f11_stk_tr W mem mem' _ _ Hwin MU WM).
    intros x Hx.
    destruct (f11_out_dec W x) as [Ho|Hno]; [left; exact Ho|].
    right. subst W. apply f11_not_out2 in Hno. destruct Hno as [Hr|Hr].
    - destruct HSTKW as (_ & _ & Hs). destruct (Hs x ltac:(unfold FN_STACK, AF.SLOT_STACK in *; lia))
        as (_ & bb & Hbb). exists bb. exact Hbb.
    - exact (HPRES x ltac:(lia)). }
  (* the spill base named by any value of register 9 is A *)
  assert (HAs : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = A).
  { intros A' HA' HA'b. apply f11_bv_inj; [lia | lia |]. unfold rg in Hs1. rewrite <- HA'. exact Hs1. }
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { apply (sl_fr_cl B APIf ra empty FF g fr hb regs regs' mem mem' md W HFRA MU WM HroM Hallapp Hrtdj HAHm HSTK).
    - intros x Hx. apply HOW; unfold AC.GT in *; lia.
    - intros x Hx. apply HOW; lia.
    - intros A' HA' HA'b x Hx. pose proof (HAs A' HA' HA'b) as ->. apply HOW; lia.
    - intros x Hx. apply HOW; lia.
    - intros x Hx. apply (f11_out_not_app W x Hallapp). intro Hap.
      exact (app_not_shadow x Hap (f11_frame_shadow fr x Hfrapp Hx)).
    - intros A' HA' HA'b x Hx. pose proof (HAs A' HA' HA'b) as ->. apply HOW; lia.
    - apply (fsrec_stklo APIf (hb ++ g_H g) mem mem' md W fr HAH MU).
      intros x Hx Hnf. apply HOW; lia.
    - intros x Hx. destruct (Hinap x Hx) as (_ & Hxlo & Hxfr & _). apply HOW; [lia|].
      destruct (Z_lt_le_dec x fr); [left; lia|]. right. lia.
    - exact HSTKS.
    - exact E2.
    - exact E3.
    - exact E4.
    - exact E8.
    - exact E9.
    - exact E19.
    - exact E26. }
  split.
  - apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA'); try reflexivity; exact Hmat.
  - eapply ent_mat; [|exact Hmat].
    apply (ent_store B APIf ra g fr hb regs mem mem' md W HENT HFRA MU).
    + intros x Hx.
      destruct (f11_out_dec W x) as [Ho|Hno]; [left; exact Ho|].
      subst W. apply f11_not_out2 in Hno. destruct Hno as [Hr|Hr].
      * right; left. unfold AF.SLOT_STACK in *. lia.
      * right; right; left. lia.
    + exact HSTK.
    + exact HSTKHI.
    + intros a Hia Ho. apply (proj2 (Hownm a)). exact Ho.
Qed.

(* ---- The segment, from the official entry cut Inv_B8226c_at to the official exit cut Inv_B82304_at. ---- *)
Lemma seg_F11 : forall j : nat,
  Hat B APIf ra (Inv_B82304_at B APIf ra) j -> Hat B APIf ra (Inv_B8226c_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    HK & HFSj & Hphi0 & Hphi50 & H50 & Hsum & HG & Hok & HRP & Ha1 & HFT & HREC0 & HFPS & H272 & HRCA).
  pose proof HFT as (H216 & _ & _ & _).
  destruct HRCA as (HADpa & HADpp & HADpn).
  subst c. rewrite SEGS.
  destruct HK as (Hgn & Hj & HHB & HLK & (A & HFL & HAb & H280 & H184 & H200 & H240 & H288 & H312) &
    Hs2 & Hs4 & Hs9 & Hs8 & Hs5 & Hs6 & Hargs).
  (* v1.9 f10_K: H280 = [A+288] = fr + 256, H184 = [A+176] = fr + 2688, H240 = [A+208] = fragb fr,
     H288 = [A+248] = 1 - sum_ok; Hs9 = s9 = sum_ok, Hs5 = [A+184] = the fill flag, Hs6 = s6 = 1 *)
  pose proof HFL as (Hs1 & H96 & H104 & H256 & H304 & H296).
  pose proof HRP as (RWa & RWp & RWn).
  (* the reply was accepted: ir holds, so 14 <= ir_s <= 23 and the record sum closes *)
  assert (Hir : RcReply.ir (flen g j) (t_g (g_in g) j) = true).
  { unfold RcReply.reply_ok in Hok. apply andb_prop in Hok. exact (proj2 Hok). }
  destruct (ir_bytes _ _ Hir) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsr & _ & _ & _ & Hrec).
  assert (Hbig : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; exact H50).
  assert (H312b : q64 mem (A + 312) (phi + 18)) by (rewrite Hbig in H312; exact H312).
  assert (HGL : length (t_g (g_in g) j) = 50%nat) by (unfold t_g; apply fr50_length).
  destruct (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGTfr & Hfrapp).
  destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hlow & HW0).
  pose proof (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hfrw & _ & _ & Hfrwr).
  destruct (f11_place g fr phi (AC.a_size (flen g j)) regs mem md HFRA ltac:(unfold AC.a_size; lia))
    as (Hpl1 & Hpl2).
  assert (Hasz : 50 <= AC.a_size (flen g j)) by (unfold AC.a_size; lia).
  assert (Hasz2 : t_len (g_in g) j <= AC.a_size (flen g j)) by (unfold AC.a_size, flen; lia).
  destruct (f11_fra_get g fr _ regs mem md HFRA) as (A2 & sp & HRT & HAH & Hro & Hhalt & Haspz & Hstklo &
    Hr9 & Hr26 & Hfrm & Hspa & Hfa & HA448 & HS4 & HAPP & Hwin & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hstkhi.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (EA : A2 = A).
  { apply f11_bv_inj; [lia | lia |]. unfold rg in *. rewrite <- Hr9. exact Hs1. }
  subst A2.
  assert (HaspB : AC.aspZ regs <= APPMEM_END) by lia.
  assert (HspA : AC.aspZ regs <= A) by lia.
  rewrite Haspz in Hpl1, Hlow.
  assert (Hdisjfr : fr + FRAME_BYTES <= sp - 32 \/ sp <= fr).
  { pose proof (Hfrw 32 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as H. rewrite Haspz in H. exact H. }
  assert (Hfrhi : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Hfrapp (fr + FRAME_BYTES - 1) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
  assert (Hfr0 : 0 <= fr) by (unfold AC.GT in HGTfr; lia).
  assert (Efragb : fragb fr = fr + 2768) by reflexivity.
  assert (Esp : bv_unsigned (getr regs 2) = sp) by (unfold AC.aspZ in Haspz; exact Haspz).
  destruct HHB as (Hphinz & HAd).
  pose proof HAd as (_ & _ & Hpe & _). unfold AC.a_size in Hpe.
  (* the identity record t_ID j (REC0) as writable cells (FLI's frame body is byte-backed), the record and its
     slices *)
  pose proof (Tac_ro.fli_mem _ _ _ _ (proj2 (proj2 (proj2 HLK)))) as (HOURa & HSTKfr & HADid & HADfg & HKNT & Hfst).
  destruct HREC0 as ((HIDB & HIDok) & (HFGB & HFGok)).
  set (idb := t_ID (g_in g) j) in *.
  assert (Hidbl : length idb = 38%nat) by exact (Tac_ro.tr_ID_length (g_in g) j).
  assert (Hidc : LSt.rw_cells rsegs mem (fr + 2688) [LCl.CB 38 idb]).
  { apply f11_cb_rw; [exact HIDB | exact Hidbl |].
    exact (f11_wr_of_stk mem mem fr (fr + FRAME_BYTES) (fr + 2688) 38 HSTKfr (fun x H => H)
             ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (Hlrec : length (RcReply.ir_rec (t_g (g_in g) j)) = Z.to_nat (RcReply.ir_s (t_g (g_in g) j) - 8)).
  { unfold RcReply.ir_rec. rewrite length_firstn, length_skipn, HGL. lia. }
  assert (HBrec : LMem.bytes_at rsegs mem (phi + 34) (RcReply.ir_rec (t_g (g_in g) j))).
  { pose proof (f11_sub mem phi _ 34 (Z.to_nat (RcReply.ir_s (t_g (g_in g) j) - 8)) HG
      ltac:(rewrite HGL; lia)) as H.
    change (Z.of_nat 34) with 34 in H. exact H. }
  assert (HADrec : addressable mem (phi + 34) (RcReply.ir_s (t_g (g_in g) j) - 8))
    by (apply (addressable_sub mem phi (AC.a_size (flen g j))); [exact HAd | lia | lia | unfold AC.a_size; lia]).
  (* L = ir_s - 13, the payload length, kept opaque so that the step engine and lia see one atom *)
  set (L := RcReply.ir_s (t_g (g_in g) j) - 13) in *.
  assert (EL : L = RcReply.ir_s (t_g (g_in g) j) - 13) by reflexivity.
  clearbody L.
  set (pb := firstn (Z.to_nat L) (skipn 38 (t_g (g_in g) j))).
  assert (Hpbl : length pb = Z.to_nat L).
  { subst pb. rewrite length_firstn, length_skipn, HGL. lia. }
  assert (HBpb : LMem.bytes_at rsegs mem (phi + 38) pb).
  { pose proof (f11_sub mem phi _ 38 (Z.to_nat L) HG ltac:(rewrite HGL; lia)) as H.
    change (Z.of_nat 38) with 38 in H. exact H. }
  assert (HADpb : addressable mem (phi + 38) L)
    by (apply (addressable_sub mem phi (AC.a_size (flen g j))); [exact HAd | lia | lia | unfold AC.a_size; lia]).
  (* the reply address cell as a u16, the two record bytes the compare reads, and their shadow bytes *)
  set (AD := cp_v (t_g (g_in g) j) 37 + 256 * cp_v (t_g (g_in g) j) 36).
  assert (HADb : 0 <= AD < 65536).
  { subst AD. unfold cp_v. pose proof (f11_ubv (cp_b (t_g (g_in g) j) 37)).
    pose proof (f11_ubv (cp_b (t_g (g_in g) j) 36)). lia. }
  assert (HU16 : u16 mem (fr + 256) AD).
  { unfold u16. pose proof (f11_cb_bytes _ _ _ _ RWa) as H. unfold RcReply.reply_addr in H.
    rewrite (f11_le2 (cp_b (t_g (g_in g) j) 37) (cp_b (t_g (g_in g) j) 36)) in H. exact H. }
  pose proof (f11_sh mem phi (flen g j) 36 HAd H50 ltac:(lia)) as Hsh36.
  pose proof (f11_sh mem phi (flen g j) 37 HAd H50 ltac:(lia)) as Hsh37.
  pose proof (f11_sh_lt (phi + 36) ltac:(lia) ltac:(lia)) as Hsh36lt.
  pose proof (f11_sh_lt (phi + 37) ltac:(lia) ltac:(lia)) as Hsh37lt.
  (* the runtime cells, for both callee contracts *)
  assert (HAC0 : asan_cells mem) by exact (RT_cells sp mem md HRT).
  assert (HSW0 : shadow_rw mem) by exact (RT_shadow_rw sp mem md HRT).
  (* the ingest call is not refused: the identity record and the payload pointer are not null *)
  assert (Hid0 : fr + 2688 <> 0) by (unfold AC.GT in HGTfr; lia).
  assert (Href : IGC.ingest_refused (fr + 2688) (phi + 38) L = false).
  { unfold IGC.ingest_refused. apply Bool.orb_false_intro.
    - apply Z.eqb_neq. exact Hid0.
    - apply Bool.andb_false_intro2. apply Z.eqb_neq. lia. }
  assert (Hv0 : IGC.ingest_ret (fr + 2688) AD (phi + 38) L idb pb = 0 \/
                IGC.ingest_ret (fr + 2688) AD (phi + 38) L idb pb = 1).
  { unfold IGC.ingest_ret. rewrite Href. apply ING_ret. }
  assert (Hv0b : 0 <= IGC.ingest_ret (fr + 2688) AD (phi + 38) L idb pb < 2 ^ 63)
    by (destruct Hv0 as [E|E]; rewrite E; lia).
  set (v0 := IGC.ingest_ret (fr + 2688) AD (phi + 38) L idb pb).
  (* the record the ingest writes is t_IDr j (SlotModel.rp_id on this ir-true path), and it keeps id_ok *)
  assert (EIDr : t_IDr (g_in g) j = snd (ING idb AD pb)).
  { assert (Hir' : RcReply.ir (t_len (g_in g) j) (t_g (g_in g) j) = true) by exact Hir.
    unfold t_IDr, rp_id. rewrite Hir'. unfold r_addr, r_pl, r_pll, bsl. rewrite <- EL.
    replace (cp_v (t_g (g_in g) j) 36 * 256 + cp_v (t_g (g_in g) j) 37) with AD by (subst AD; lia).
    reflexivity. }
  assert (HIDok' : id_ok (snd (ING idb AD pb))) by exact (RcIdentLib.ING_id_ok idb AD pb Hidbl HIDok).
  (* the identity record is 2-aligned: the frame base is 32-aligned (FRA) *)
  assert (Hidev : (fr + 2688) mod 2 = 0).
  { pose proof (Z.div_mod fr 32 ltac:(lia)) as D. rewrite Hfrm in D.
    pose proof (Z.div_mod (fr + 2688) 2 ltac:(lia)) as D3.
    pose proof (Z.mod_pos_bound (fr + 2688) 2 ltac:(lia)). lia. }
  set (W := [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)]).
  assert (HGTW : forall lo hi, In (lo, hi) W -> AC.GT <= lo).
  { subst W. intros lo hi Hin. cbn in Hin.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold AC.GT in *; lia. }
  pose proof HRSC as HR.
  unfold RSC.record_sum_closes_contract, RSC.RECORD_SUM_CLOSES, RSC.RECORD_SUM_CLOSES_FRAME in HR.
  pose proof HING as HI.
  unfold IGC.reac_identity_ingest_contract, IGC.REAC_IDENTITY_INGEST, IGC.REAC_IDENTITY_INGEST_FRAME in HI.
  pose proof (f11_rd8 mem _ _ H312b ltac:(apply LMem.length_le8)) as RD312.
  (* The one lazy-model run of this segment (Tac_slot.sl_run, AsanLift.evt_SR_canon_lazy), 0x8226c -> 0x82304.
     Pages it reads: the spills [A+176], [A+288], [A+296], [A+304], [A+312]; the reply cells [fr+256, fr+258),
     [fr+272, fr+280), [fr+304, fr+312); the record bytes Phi + 36, Phi + 37 and their shadow bytes
     ((Phi + 36) >> 3) + 0x7fff8000, ((Phi + 37) >> 3) + 0x7fff8000; in the callees the record [Phi + 34, Phi + 26 +
     ir_s) with its shadow bytes, the identity record [fr + 2688, fr + 2726), the payload [Phi + 38, Phi + 25 + ir_s)
     and the runtime cells CELL_K / GOT_CELL_K. Pages it writes: the callees' stack scratch [sp - 32, sp) and the
     identity record [fr + 2688, fr + 2726). *)
  apply (sl_run regs (Z_to_bv 64 0x8226c) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x82304 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\ getr R 18 = getr regs 18 /\ getr R 20 = getr regs 20 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 24 = getr regs 24 /\
       getr R 27 = getr regs 27 /\ getr R 25 = getr regs 25 /\
       getr R 10 = Z_to_bv 64 v0 /\
       LFr.munch W mem mem' /\ LFr.wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       LFr.stk rsegs mem' (sp - FN_STACK) sp /\
       LSt.rw_cells rsegs mem' (fr + 2688) [LCl.CB 38 (snd (ING idb AD pb))])
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* the run 0x8226c -> 0x82304 through the two calls *)
    rewrite f11_mkR_of_expand.
    f11_slot Hs1. f11_slot Ha1. f11_slot Hr26.
    (* 0x8226c li a0,-17 ; 0x82270 ld a2,312(s1) ; 0x82274 bltu a0,a2 (T23): blk + 16 does not wrap *)
    step. step. step. rewrite (f11_ltu_false _ (phi + 18)) by f11_mlia. cbv_concl_iota.
    (* 0x82278 ld a0,312(s1) ; 0x8227c addi a0,a0,16 ; 0x82280 addi a1,a1,5 ; 0x82284 jal record_sum_closes *)
    step. step. step. step.
    (* the record-sum call: the callee contract at 0x83614 (frame 16), back at 0x82288 *)
    eapply UEx.evt_cut.
    { apply f11_lu_evt. eapply HR with (bs := RcReply.ir_rec (t_g (g_in g) j)) (lo := sp - FN_STACK).
      all: rewrite ?Esp; rewrite ?LMS.unsigned_lit by lia.
      - rewrite Hlrec. f_equal. lia.
      - right. split; [lia|]. split; [lia|]. split; [exact HBrec|]. left. unfold FN_STACK, AF.SLOT_STACK in *. lia.
      - rewrite Haspz in HW0. exact HW0.
      - unfold FN_STACK. lia.
      - intros _. exact HAC0.
      - intros _. exact HSW0.
      - intros _. replace (L + 5) with (RcReply.ir_s (t_g (g_in g) j) - 8) by lia. exact HADrec.
      - intros _ x Hx. apply (f11_rt_out1 sp x 16); [lia | lia | exact Hx]. }
    intros ms' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m1 & Ems & MU1 & WM1 & MI1 & ST1).
    subst ms'.
    replace (if recsum (RcReply.ir_rec (t_g (g_in g) j)) =? 0 then 1 else 0) with 1 by (rewrite Hrec; reflexivity).
    rewrite (LMS.ret_pc_even 0x82288) by first [lia | reflexivity].
    rewrite f11_MS_ul, f11_mkR_ul.
    rewrite Esp in MU1, ST1.
    (* the facts the rest of the run reads, carried to the post-call memory m1 (the callee wrote [sp-16, sp)) *)
    assert (TR1 : forall a (bs0 : list byte), LMem.bytes_at rsegs mem a bs0 ->
              (a + Z.of_nat (length bs0) <= sp - 16 \/ sp <= a) -> LMem.bytes_at rsegs m1 a bs0).
    { intros a bs0 Hb Hd. eapply fl_bytes; [exact Hb | exact MU1 |].
      intros x Hx. cbn. split; [lia | exact I]. }
    assert (HAW1 : all_app [(sp - 16, sp)]).
    { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
    assert (HD1 : AsanRTInv.rt_disjoint [(sp - 16, sp)]).
    { apply f11_rtdj_GT. intros lo hi Hin. cbn in Hin. destruct Hin as [E|[]].
      injection E as <- <-. unfold AC.GT in *. lia. }
    assert (HRT1 : AsanRTInv.RT sp m1 md) by exact (AsanRTInv.RT_store sp sp mem m1 md md _ HRT MU1 WM1 HAW1 HD1).
    assert (HAC1 : asan_cells m1) by exact (RT_cells sp m1 md HRT1).
    assert (HSW1 : shadow_rw m1) by exact (RT_shadow_rw sp m1 md HRT1).
    assert (Q1 : forall off v, 0 <= off -> q64 mem (A + off) v -> q64 m1 (A + off) v).
    { intros off v Hoff Hq. unfold q64 in *. apply TR1; [exact Hq | right; lia]. }
    assert (QF : forall a v, fr <= a -> a + 8 <= fr + FRAME_BYTES -> q64 mem a v -> q64 m1 a v).
    { intros a v H1 H2 Hq. unfold q64 in *. apply TR1; [exact Hq | rewrite LMem.length_le8].
      destruct Hdisjfr; [left | right]; lia. }
    pose proof (f11_rd8 m1 _ _ (Q1 312 _ ltac:(lia) H312b) ltac:(apply LMem.length_le8)) as RD312'.
    pose proof (f11_rd8 m1 _ _ (Q1 288 _ ltac:(lia) H280) ltac:(apply LMem.length_le8)) as RD280.
    pose proof (f11_rd8 m1 _ _ (Q1 304 _ ltac:(lia) H304) ltac:(apply LMem.length_le8)) as RD304.
    pose proof (f11_rd8 m1 _ _ (Q1 296 _ ltac:(lia) H296) ltac:(apply LMem.length_le8)) as RD296.
    pose proof (f11_rd8 m1 _ _ (Q1 176 _ ltac:(lia) H184) ltac:(apply LMem.length_le8)) as RD184.
    pose proof (f11_rd8 m1 _ _ (QF (fr + 272) _ ltac:(lia) ltac:(lia) (f11_cb_bytes _ _ _ _ RWp))
                  ltac:(apply LMem.length_le8)) as RDpp.
    pose proof (f11_rd8 m1 _ _ (QF (fr + 304) _ ltac:(lia) ltac:(lia) (f11_cb_bytes _ _ _ _ RWn))
                  ltac:(apply LMem.length_le8)) as RDpn.
    assert (HU16' : u16 m1 (fr + 256) AD).
    { unfold u16 in *. apply TR1; [exact HU16 | rewrite LMem.length_le2; destruct Hdisjfr; [left | right]; lia]. }
    pose proof (f11_rd2 m1 _ _ HU16' ltac:(apply LMem.length_le2)) as RDpa.
    assert (HG1 : LMem.bytes_at rsegs m1 phi (t_g (g_in g) j))
      by (apply TR1; [exact HG | rewrite HGL; left; unfold FN_STACK, AF.SLOT_STACK in *; lia]).
    pose proof (f11_rdk m1 phi _ 36 HG1 ltac:(rewrite HGL; lia)) as RDb36.
    pose proof (f11_rdk m1 phi _ 37 HG1 ltac:(rewrite HGL; lia)) as RDb37.
    change (Z.of_nat 36) with 36 in RDb36. change (Z.of_nat 37) with 37 in RDb37.
    pose proof (f11_rd1 m1 _ _ (TR1 _ _ Hsh36 ltac:(cbn [length]; left; lia))) as RDsh36.
    pose proof (f11_rd1 m1 _ _ (TR1 _ _ Hsh37 ltac:(cbn [length]; left; lia))) as RDsh37.
    assert (HBpb' : LMem.bytes_at rsegs m1 (phi + 38) pb)
      by (apply TR1; [exact HBpb | left; rewrite Hpbl; unfold FN_STACK, AF.SLOT_STACK in *; lia]).
    assert (Hidc' : LSt.rw_cells rsegs m1 (fr + 2688) [LCl.CB 38 idb]).
    { eapply LFr.rw_cells_transport; [exact Hidc | exact MU1 | exact WM1 |].
      cbn [LCl.cells_size LCl.csize Nat.add]. cbn.
      split; [destruct Hdisjfr as [Hd|Hd]; [left | right]; lia | exact I]. }
    assert (HADid' : addressable m1 (fr + 2688) 38)
      by exact (sl_addr_keep mem m1 [(sp - 16, sp)] (fr + 2688) 38 HADid MU1 HAW1).
    assert (HADpb' : addressable m1 (phi + 38) L)
      by exact (sl_addr_keep mem m1 [(sp - 16, sp)] (phi + 38) L HADpb MU1 HAW1).
    (* 0x82288 beqz a0 : a0 = 1, not taken *)
    step. if_false.
    (* 0x8228c li a0,-19 ; ld a1,312(s1) ; bltu a0,a1 (T24) and 0x82298 li a0,-20 ; ld ; bltu (T25): not taken *)
    step. step. step. rewrite (f11_ltu_false _ (phi + 18)) by f11_mlia. cbv_concl_iota.
    step. step. step. rewrite (f11_ltu_false _ (phi + 18)) by f11_mlia. cbv_concl_iota.
    (* 0x822a4 ld a4,312(s1) ; addi a0,a4,18 ; srli a1,a0,3 ; add a1,a1,s10 ; lb a2 = shadow(phi + 36) = 0 *)
    step. step. step. step. rewrite (LMS.unsigned_lit (phi + 36)) by lia.
    step.
    (* 0x822b8 ld a1,288(s1) ; 0x822bc lhu a1,0(a1) = AD ; 0x822c0 bnez a2 (= 0) not taken *)
    step. step. step. if_false.
    (* 0x822c4 addi a2,a4,19 ; srli a3,a2,3 ; add a3,a3,s10 ; lb a3 = shadow(phi + 37) = 0 *)
    step. step. step. rewrite (LMS.unsigned_lit (phi + 37)) by lia.
    step.
    (* 0x822d4 lbu a0,0(a0) = G[36] ; 0x822d8 bnez a3 (= 0) not taken ; 0x822dc lbu a2,0(a2) = G[37] *)
    step. step. if_false. step.
    (* 0x822e0 slli a0,a0,8 ; 0x822e4 or a0,a0,a2 ; 0x822e8 bne a0,a1 : the two addresses agree, not taken *)
    step. step. step.
    rewrite (f11_cmp16 (nth 36 (t_g (g_in g) j) cp_z) (nth 37 (t_g (g_in g) j) cp_z)), (f11_zx16 AD HADb).
    rewrite bv_eqb_refl; cbn [negb]; cbv_concl_iota.
    (* 0x822ec-0x822fc: a2 = pl = phi + 38, a3 = pll = ir_s - 13, a0 = id ; 0x82300 jal reac_identity_ingest *)
    step. step. step. step. step. step.
    eapply UEx.evt_cut.
    { apply f11_lu_evt. eapply HI with (id := fr + 2688) (ad := AD) (p := phi + 38) (len := L)
        (idb := idb) (pb := pb) (lo := sp - FN_STACK).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - exact HADb.
      - lia.
      - lia.
      - intros _. split; [exact Hidev | exact Hidc'].
      - exact Hpbl.
      - intros _ _. exact HBpb'.
      - intros _ _ _. destruct Hpl2 as [Hd|Hd]; [left | right]; lia.
      - rewrite Esp. exact ST1.
      - rewrite Esp. unfold FN_STACK, AF.SLOT_STACK. lia.
      - intros _. rewrite Esp. destruct Hdisjfr as [Hd|Hd]; [left | right]; lia.
      - intros _ _. rewrite Esp. left. unfold FN_STACK, AF.SLOT_STACK in *. lia.
      - exact HAC1.
      - exact HSW1.
      - intros _. exact HADid'.
      - intros _ _. exact HADpb'.
      - intros x Hx. rewrite Esp.
        unfold IGC.reac_identity_ingest_W, IGC.REAC_IDENTITY_INGEST_FRAME.
        apply (f11_rt_out2 sp fr x); [lia | exact HGTfr | exact Hfrapp | exact Hx]. }
    intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6''
                & m2 & Ems2 & MU2 & WM2 & MI2 & ST2 & _ & HRW).
    subst ms'.
    rewrite Esp in MU2, ST2. unfold IGC.reac_identity_ingest_W, IGC.REAC_IDENTITY_INGEST_FRAME in MU2.
    assert (MUW : LFr.munch W mem m2).
    { subst W. intros x Hx. rewrite (MU2 x Hx). apply MU1.
      cbn in Hx |- *. destruct Hx as (Hx1 & _). split; [lia | exact I]. }
    apply UEx.evt_done. cbv beta.
    do 3 eexists. split; [reflexivity|].
    split; [apply bv_eq; vm_compute; reflexivity|].
    do 15 (split; [reflexivity|]).
    split; [exact MUW|].
    split; [intros x Hx; apply WM2; apply WM1; exact Hx|].
    split; [exact (f11_ro_keep W mem m2 HGTW MUW Hro)|].
    split; [exact ST2|].
    exact (HRW Href).
  - (* the continuation: rebuild the exit cut Inv_B82304_at at 0x82304 *)
    intros R pc' mem' regs' md'
      (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er26 & Er18 & Er20 & Er21 & Er22 & Er24 & Er27 & Er25 & Er10 &
       MU & WM & HroM & ST' & HIB) Hreg Hmat.
    subst pc'. rewrite <- SEGS. apply Hexit. clear Hexit HRSC HING HR HI.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 v0) by (rewrite Hreg; exact Er10).
    assert (Easp : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    assert (HOW : forall x, (x < sp - 32 \/ sp <= x) -> (x < fr + 2688 \/ fr + 2688 + 38 <= x) ->
                    LFr.outside W x) by (intros x H1 H2; subst W; apply f11_out2; assumption).
    assert (Hallapp : all_app W).
    { subst W. cbn [all_app]. split; [|split; [|exact I]].
      - intros a Ha. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia.
      - intros a Ha. apply Hfrapp. lia. }
    assert (HPRES : forall q, fr + 2688 <= q < fr + 2688 + 38 ->
              exists b, LMem.mrd rsegs mem' (LMem.wa q) = Some b).
    { intros q Hq. apply (f11_present mem' (fr + 2688) (snd (ING idb AD pb)) q (f11_cb_bytes mem' _ _ _ HIB)).
      rewrite (ING_length idb AD pb Hidbl). change (Z.of_nat ID_SIZE) with 38. lia. }
    assert (MUa : LFr.munch [(AC.aspZ regs - 32, AC.aspZ regs); (fr + 2688, fr + 2688 + 38)] mem mem')
      by (rewrite Haspz; exact MU).
    assert (STa : LFr.stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs))
      by (rewrite Haspz; exact ST').
    (* FRA and ENT cross the run together (f11_fra). *)
    destruct (f11_fra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem mem' md md' A HFRA HENT Hs1 HAb
                MUa WM HroM STa HPRES Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat)
      as (HFRA' & HENT').
    (* Phi's whole block lies below the window and apart from the frame (f11_place) *)
    assert (HOphi : forall x, phi <= x < phi + AC.a_size (flen g j) -> LFr.outside W x).
    { intros x Hx. apply HOW; [left; unfold FN_STACK, AF.SLOT_STACK in *; lia |].
      destruct Hpl2 as [Hd|Hd]; lia. }
    assert (HOA : forall x, A <= x < A + 448 -> LFr.outside W x) by (intros x Hx; apply HOW; lia).
    assert (SPK : forall off v, 0 <= off <= 336 -> spill regs mem off v -> spill regs' mem' off v)
      by (intros off v Hoff Hs;
          exact (f11_spill_move W regs regs' mem mem' off v A Hs Hs1 ltac:(lia) ltac:(lia) ltac:(lia) Fr9 MU HOA)).
    (* the frame body stays byte-backed: outside W it is unchanged, inside W the ingest post's cells hold it *)
    assert (HSTKfr' : LFr.stk rsegs mem' fr (fr + FRAME_BYTES)).
    { apply (f11_stk_tr W mem mem' fr (fr + FRAME_BYTES) HSTKfr MU WM).
      intros x Hx. destruct (Z_lt_ge_dec x (fr + 2688)) as [Dlo|Dlo];
        [|destruct (Z_lt_ge_dec x (fr + 2688 + 38)) as [Dhi|Dhi]].
      + left. apply HOW; [destruct Hdisjfr; lia | lia].
      + right. exact (HPRES x ltac:(lia)).
      + left. apply HOW; [destruct Hdisjfr; lia | lia]. }
    (* FM from f10_K's registers and spills *)
    assert (HFM : FM g j phi fr regs mem).
    { split; [exact Hs5|]. split; [exact Hs8|]. split; [exact Hs6|]. split; [exact Hs9|].
      exists A. split; [exact Hs1 | exact H312]. }
    assert (Hfst' : addressable mem' (fr + 2880) 40) by exact (sl_addr_keep mem mem' W (fr + 2880) 40 Hfst MU Hallapp).
    exists phi, regs', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA'|].
    split; [exact HENT'|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split.
    { split; [exact Hphinz|].
      exact (sl_addr_keep mem mem' W phi (AC.a_size (flen g j)) HAd MU Hallapp). }
    split; [unfold rg in *; rewrite Fr18; exact Hs2|].
    split; [unfold rg in *; rewrite Fr20; exact Hs4|].
    (* FTURN: the two cursor spills and the frame's len bytes at Phi, inside its block *)
    split.
    { apply (Tac_ro.turn_munch g j phi regs regs' W mem mem' HFT SPK MU).
      intros x Hx. apply HOphi. lia. }
    split.
    { (* LK: FLI's spills, our[], the frame's stk and RAD *)
      pose proof HLK as (_ & _ & HOURb & _).
      eapply Tac_ro.lk_keep; [exact HLK | | | | | | | | | exact SPK].
      - pose proof (proj2 (proj2 (proj2 HLK))) as (H27 & _). unfold rg in *. rewrite Fr27. exact H27.
      - exact (sl_addr_keep mem mem' W (fr + 2624) 6 HOURa MU Hallapp).
      - exact HSTKfr'.
      - exact (sl_addr_keep mem mem' W (fr + 2688) 38 HADid MU Hallapp).
      - exact (sl_addr_keep mem mem' W (fragb fr) 72 HADfg MU Hallapp).
      - (* KNT: the kind-name table is image data below GT, which W misses; its shadow bytes are not in W *)
        destruct HKNT as (HKb & HKa). split.
        + eapply fl_bytes; [exact HKb | exact MU |].
          change (length KNC.kind_name_bytes) with 112%nat.
          intros x Hx. apply (f11_out_GT W x HGTW). unfold KNC.KIND_NAME, AC.GT in *. lia.
        + exact (sl_addr_keep mem mem' W KNC.KIND_NAME 112 HKa MU Hallapp).
      - exact Hfst'.
      - unfold OURb in *. eapply fl_bytes; [exact HOURb | exact MU |].
        rewrite OUR_length. intros x Hx. apply HOW; lia. }
    split; [exact (f11_FM_move W g j phi fr regs regs' mem mem' A HFM Hs1 ltac:(lia) ltac:(lia)
                     MU HOA Fr9 Fr22 Fr24 Fr25)|].
    (* FSj: the local `first` [fr + 2880, fr + 2920) is frame memory outside W *)
    split.
    { apply (Tac_ro.fsj_keep g fr j regs regs' mem mem' HFSj); [|exact Hfst'].
      intros a bs Ha Hab Hb. eapply fl_bytes; [exact Hb | exact MU |].
      intros x Hx. apply HOW; [destruct Hdisjfr; lia | lia]. }
    (* RECR: the identity record the ingest wrote (t_IDr j, id_ok kept) and the fragment record, outside W *)
    split.
    { split; split.
      - unfold IDBe. rewrite EIDr. exact (f11_cb_bytes mem' _ _ _ HIB).
      - rewrite EIDr. exact HIDok'.
      - unfold FGBe in *. eapply fl_bytes; [exact HFGB | exact MU |].
        rewrite (Tac_ro.tr_FG_length (g_in g) j). intros x Hx. apply HOW; [destruct Hdisjfr; lia | lia].
      - exact HFGok. }
    split.
    { intros _. eapply fl_bytes; [exact HG | exact MU |]. rewrite HGL. intros x Hx. apply HOphi. lia. }
    (* FPS: the parse struct at fr + 176 and its 36 addressable bytes, outside W *)
    split.
    { destruct HFPS as (HpB & HaB). split.
      - unfold pBb in *. eapply fl_bytes; [exact HpB | exact MU |].
        unfold t_B. rewrite ctrlparse_length. intros x Hx. apply HOW; [destruct Hdisjfr; lia | lia].
      - exact (sl_addr_keep mem mem' W (fr + 176) 36 HaB MU Hallapp). }
    split; [exact (SPK 272 _ ltac:(lia) H272)|].
    split.
    { split; [exact (sl_addr_keep mem mem' W (fr + 256) 2 HADpa MU Hallapp)|].
      split; [exact (sl_addr_keep mem mem' W (fr + 272) 8 HADpp MU Hallapp)|].
      exact (sl_addr_keep mem mem' W (fr + 304) 8 HADpn MU Hallapp). }
    split; [exists v0; split; [unfold rg; exact Fr10 | exact Hv0b]|].
    (* FS9 ([A+248] = 1 - sum_ok): the spill area is outside W *)
    unfold FS9. apply (SPK 248 _ ltac:(lia)). exists A. split; [exact Hs1 | exact H288].
Qed.

End F11.

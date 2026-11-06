(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgWords BgArith BgMont.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_callsAF W_calls3AF W_small3A W_small4A W_calls4AF AFrameKit AFrameCall AFrameTac AFrameEnv AFrameComp ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import W_ctxAF W_ctx_getAF W_ctx_endAF W_copyAF W_set_wordAF ShiftKitAF W_shiftAF W_div_padAF W_div_tailAF W_divAF W_set_bitAF W_bndivAF PlaceTmodA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require W_sub_wordAF InvClosedAF W_mod_inverseAF W_int_invAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import RecpKitAF ExpBodyKitF InvKitAF MontSetSimF MontSetKitAF Fr_mont_set.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStructF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import W_mont_setAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.

Definition zfill (j : nat) (ws : list word) : list word := repeat (Z_to_bv 64 0) j ++ skipn j ws.
Lemma zfill_length : forall j ws, (j <= length ws)%nat -> length (zfill j ws) = length ws.
Proof. intros j ws H. unfold zfill. rewrite length_app, repeat_length, length_skipn. clear - H. lia. Qed.
Lemma zfill_upd : forall j ws, (j < length ws)%nat -> Arr.upd (zfill j ws) j (Z_to_bv 64 0) = zfill (S j) ws.
Proof.
  induction j as [|j IH]; intros [|x ws] H; cbn [length] in H; try (exfalso; clear - H; lia).
  - reflexivity.
  - change (zfill (S j) (x :: ws)) with (Z_to_bv 64 0 :: zfill j ws).
    change (zfill (S (S j)) (x :: ws)) with (Z_to_bv 64 0 :: zfill (S j) ws).
    cbn [Arr.upd]. rewrite IH by (clear - H; lia). reflexivity.
Qed.
Lemma zfill_all : forall ws, zfill (length ws) ws = repeat (Z_to_bv 64 0) (length ws).
Proof. intros ws. unfold zfill. rewrite skipn_all, app_nil_r. reflexivity. Qed.
Lemma u64s_repeat0 : forall k, u64s (repeat (Z_to_bv 64 0) k) = repeat (Z_to_bv 8 0) (8 * k).
Proof. intros k. rewrite <- lbytes_repeat0. unfold wlimbs. rewrite map_repeat. reflexivity. Qed.

Lemma fill_loop : forall (POST : machine_state -> Prop)
    (x1 x2 gp tp x8 x9 x10 x12 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (D top cnt dmax : Z) (ws : list word) (k j : nat) (mc : mem) (r6 r7 : word),
  acc bgbsegs m D (8 * dmax) -> D mod 8 = 0 -> (0 <= D /\ D + 8 * dmax <= 140737488355328) -> 0 < D ->
  offshW [(D + 8 * top, D + 8 * top + 8 * cnt)] ->
  0 <= top -> top + cnt <= dmax -> dmax <= 512 -> Z.of_nat (length ws) = cnt ->
  (0 < k)%nat -> Z.of_nat j + Z.of_nat k = cnt ->
  mem_inv bgbsegs mc -> munch [(D + 8 * top, D + 8 * top + 8 * cnt)] m mc -> wmono bgbsegs m mc ->
  u64arr bgbsegs mc (D + 8 * top) (zfill j ws) ->
  (forall (mM : mem) (y6 y7 y11 y14 y17 : word),
     mem_inv bgbsegs mM -> munch [(D + 8 * top, D + 8 * top + 8 * cnt)] m mM -> wmono bgbsegs m mM ->
     u64arr bgbsegs mM (D + 8 * top) (zfill (j + k) ws) ->
     evt bgbsegs POST (MS (mkR x1 x2 gp tp (Z_to_bv 64 1) y6 y7 x8 x9 x10 y11 x12 (Z_to_bv 64 (top + cnt)) y14 (Z_to_bv 64 D) (Z_to_bv 64 1) y17
                               x18 x19 x20 x21 x22 x23 (Z_to_bv 64 SHB) x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x226d04) fc None mM (seg_rom bgbsegs))) ->
  evt bgbsegs POST (MS (mkR x1 x2 gp tp (Z_to_bv 64 1) r6 r7 x8 x9 x10 (Z_to_bv 64 (D + 8 * top + 8 * Z.of_nat j)) x12 (Z_to_bv 64 (top + cnt))
                            (Z_to_bv 64 (top + Z.of_nat j)) (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 (D + 8 * top + 8 * Z.of_nat j))
                            x18 x19 x20 x21 x22 x23 (Z_to_bv 64 SHB) x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x226cc0) fc None mc (seg_rom bgbsegs)).
Proof.
  intros POST x1 x2 gp tp x8 x9 x10 x12 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 F fc m D top cnt dmax ws k.
  induction k as [|k IH]; intros j mc r6 r7 ACCD D8 BD D0 OFF T0 TC D512 LW K0 EJ MI MU WM U K; [exfalso; clear - K0; lia|].
  assert (JB : 0 <= Z.of_nat j /\ Z.of_nat j + 1 <= cnt) by (clear - EJ; lia).
  assert (LZ : Z.of_nat (length (zfill j ws)) = cnt) by (rewrite zfill_length by (clear - LW JB; lia); exact LW).
  assert (KR : D + 8 * top <= D + 8 * top + 8 * Z.of_nat j /\ D + 8 * top + 8 * Z.of_nat j + 8 <= D + 8 * top + 8 * cnt) by (clear - JB; lia).
  unfold SHLO, SHHI in OFF.

  ub.

  do 2 step. shl_limb ACCD D8 BD (top + Z.of_nat j). chk0.

  assert (IDX : 0 <= Z.of_nat j < Z.of_nat (length (zfill j ws))) by (rewrite LZ; clear - JB; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u64arr_store_ok bgbsegs mx (D + 8 * top) _ (Z.of_nat j) (wa (D + 8 * top + 8 * Z.of_nat j)) U IDX eq_refl) as SOKW;
    pose proof (u64arr_write bgbsegs mx (D + 8 * top) _ (Z.of_nat j) (Z_to_bv 64 0) U IDX) as U2 end.
  rewrite Nat2Z.id, zfill_upd in U2 by (clear - LW JB; lia).
  clear U. step. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). store_done.

  step. step. step.
  setreg 11%Z (Z_to_bv 64 (D + 8 * top + 8 * Z.of_nat (S j))) ltac:(f_equal; clear; lia).
  setreg 14%Z (Z_to_bv 64 (top + Z.of_nat (S j))) ltac:(f_equal; clear; lia).
  setreg 17%Z (Z_to_bv 64 (D + 8 * top + 8 * Z.of_nat (S j))) ltac:(f_equal; clear; lia).
  step. if_cases KE; zify_cond KE; rewrite ?unsigned_lit in KE by (clear - T0 TC D512 JB; lia).
  -
    eapply (IH (S j)); [exact ACCD| exact D8| exact BD| exact D0| cbn [offshW]; unfold SHLO, SHHI; exact OFF| exact T0| exact TC| exact D512| exact LW
                       | clear - KE EJ; lia| clear - EJ; lia| assumption| assumption| assumption| exact U2|].
    intros mM y6 y7 y11 y14 y17 MIM MUM WMM UM.
    replace (S j + k)%nat with (j + S k)%nat in UM by (clear; lia).
    eapply K; [exact MIM| exact MUM| exact WMM| exact UM].
  -
    assert (k = 0)%nat by (clear - KE EJ; lia). subst k.
    replace (S j) with (j + 1)%nat in U2 by (clear; lia).
    eapply K; [assumption| assumption| assumption| exact U2].
Qed.

Section Fill.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma fix_fill : fix_fill_stmt.
Proof.
  unfold fix_fill_stmt. intros until pr. intros HEAP ST MI CEIL LO16 SPT Hin DCELL ACCR ALR AR0 SEPR OFRR SEPD T0 C0 TC D512 -> -> -> -> -> K.
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (D0 & D16 & _ & DC & DI).
  destruct (AH_acc _ _ _ _ (pr, D, 8 * dmax) HEAP ltac:(apply in_or_app; left; exact Hin)) as (WRD & ACCD). cbn [blk_addr blk_size fst snd] in WRD, ACCD.
  pose proof (AH_offsh _ _ _ _ (pr, D, 8 * dmax) HEAP ltac:(apply in_or_app; left; exact Hin)) as OFFD. cbn [blk_addr blk_size fst snd] in OFFD.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (D8 : D mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
  assert (BD : 0 <= D /\ D + 8 * dmax <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - D0 DC C1 C2 C3; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - C1 CEIL LO16 SPT; lia).
  pose proof (munch_refl [(D + 8 * top, D + 8 * top + 8 * cnt)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(D + 8 * top, D + 8 * top + 8 * cnt)]%Z) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - OFFD T0 C0 TC; lia).
  do 2 step. shl_with ACCR ALR. chk0.
  step.
  do 2 step. ub. step. ub. step.

  assert (L7 : Z.land D 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by (clear; lia); change (2 ^ 3) with 8; exact D8).
  assert (LD : (0 <? D) = true) by (apply Z.ltb_lt; exact D0).
  setreg 5%Z (Z_to_bv 64 1) ltac:(f_equal; rewrite L7, LD; reflexivity).
  setreg 16%Z (Z_to_bv 64 1) ltac:(f_equal; rewrite LD; reflexivity).
  setreg 11%Z (Z_to_bv 64 (D + 8 * top + 8 * Z.of_nat 0)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
  setreg 17%Z (Z_to_bv 64 (D + 8 * top + 8 * Z.of_nat 0)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
  setreg 14%Z (Z_to_bv 64 (top + Z.of_nat 0)) ltac:(f_equal; clear; lia).
  assert (DLO : D + 8 * dmax <= lo /\ D + 8 * dmax <= FB - 16) by (clear - DC CEIL LO16; lia).

  pose proof (wr_at_sub bgbsegs m D (8 * dmax) (8 * top) (8 * cnt) WRD ltac:(clear - T0; lia) ltac:(clear - C0; lia) ltac:(clear - T0 C0 TC; lia)) as WRT.
  destruct (wr_at_rw_CB m _ (8 * cnt) WRT ltac:(clear - C0; lia)) as (jt & TG).
  assert (LJ : length jt = (8 * Z.to_nat cnt)%nat).
  { pose proof TG as [[WF _] _]. cbn [cells_wf cell_wf] in WF. destruct WF as [WF _]. rewrite WF. clear - C0. lia. }
  destruct (u64s_exists (Z.to_nat cnt) jt LJ) as (ws & LWS & EWS).
  assert (U0 : u64arr bgbsegs m (D + 8 * top) (zfill 0 ws)).
  { change (zfill 0 ws) with ws. eapply CB_u64arr. rewrite EWS. exact TG. }
  assert (LW : Z.of_nat (length ws) = cnt) by (rewrite LWS; clear - C0; lia).

  eapply (fill_loop POST) with (m := m) (D := D) (top := top) (cnt := cnt) (dmax := dmax) (ws := ws) (k := Z.to_nat cnt) (j := 0%nat);
    [ exact ACCD | exact D8 | exact BD | exact D0 | exact OFF | exact T0 | exact TC | exact D512 | exact LW
    | clear - C0; lia | clear - C0; lia | exact MI | exact MU | exact WM | exact U0 | ].
  intros mM y6 y7 y11 y14 y17 MIM MUM WMM UM.

  replace (0 + Z.to_nat cnt)%nat with (length ws) in UM by (rewrite LWS; reflexivity).
  rewrite zfill_all in UM. destruct UM as [BZ WRM]. rewrite u64s_repeat0, LWS in BZ. rewrite repeat_length, LWS in WRM.
  eapply K.
  - exact MIM.
  - eapply (stk_transport_disjoint bgbsegs _ m mM lo FB ST MUM WMM). cbn [disjoint_from]. split; [right; clear - DLO T0 C0 TC; lia| exact I].
  - eapply (AH_frame _ _ _ m mM _ HEAP MUM WMM). constructor; [| constructor].
    right; right. exists (pr, D, 8 * dmax). split; [apply in_or_app; left; exact Hin|]. cbn [blk_addr blk_size fst snd]. clear - T0 C0 TC. lia.
  - exact WMM.
  - eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MUM)|]. intros a [_ Ha]. cbn [outside]. split; [exact Ha| exact I].
  - replace (Z.to_nat (8 * cnt)) with (8 * Z.to_nat cnt)%nat by (clear - C0; lia). exact BZ.
  - replace (8 * cnt) with (8 * Z.of_nat (Z.to_nat cnt)) by (clear - C0; lia). exact WRM.
Qed.
End Fill.

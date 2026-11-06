(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv MonadX Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Exit Imp_ios_defs Exit_iface F_stdio_exit F_stdio_exit0.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Ltac norm_addr H := lazymatch type of H with rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v in H end.
Ltac norm_goal_addr := lazymatch goal with |- rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v; eassumption end.

Definition F_FUNCS_ON_EXIT : Z := 0xb9598.
Definition AEX_HRA : Z := 0xb9618.
Definition RLIBCH : Z := 0x10a028.
Definition FINB : Z := 0xd7ae8.
Definition RCALL : Z := 0xb97f0.
Definition RGUARD : Z := 0x3eb28.

Ltac xport H AG :=
  eapply rw_cells_agree'; [exact AG| exact H| intros a Ha; unfold XW, RTPLOC, AEX_VEC_OBJ; cbn [outside fst snd] in *; cbn in Ha; lia].

Lemma agree_on'_trans : forall P m1 m2 m3, agree_on' P m1 m2 -> agree_on' P m2 m3 -> agree_on' P m1 m3.
Proof.
  intros P m1 m2 m3 A B a Ha HP. destruct (A a Ha HP) as [E1 W1]. destruct (B a Ha HP) as [E2 W2].
  split; [rewrite E2; exact E1| intros H; apply W2, W1, H].
Qed.
Lemma agree_on'_mono : forall (P Q : Z -> Prop) m m', agree_on' P m m' -> (forall a, Q a -> P a) -> agree_on' Q m m'.
Proof. intros P Q m m' A HQ a Ha Hq. apply A; [exact Ha| apply HQ, Hq]. Qed.

Ltac xw_lia := intros a [Ho Hn]; unfold xagree, XW, RTPLOC, AEX_VEC_OBJ, AEX in *; cbn [outside fst snd] in *; lia.

Section Aex.
  Context {St : Type}.
  Variables (cv ci : @M St unit) (FV AV FI AI lo hi HDEPTH : Z).
  Hypotheses (FVB : 0 <= FV < 2^47) (FVE : FV mod 2 = 0) (AVB : 0 <= AV < 2^64) (FIB : 0 <= FI < 2^47) (FIE : FI mod 2 = 0) (AIB : 0 <= AI < 2^64).
  Variables (PREV MID POSTI : mem -> St -> Prop).

  Definition hpost (P : mem -> St -> Prop) (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
      : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AEX_HRA) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (Z_to_bv 64 AEX_HRA) fc None m' (seg_rom psegs)
      /\ xagree (bv_unsigned sp) m m' /\ mem_inv psegs m'
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ P m' s'.
  Hypothesis VEC : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : St),
      stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - HDEPTH -> bv_unsigned sp <= hi -> tp = Z_to_bv 64 RTP -> PREV m s -> mem_inv psegs m ->
      implM psegs cv s (hpost MID sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
            (MS (mkR (Z_to_bv 64 AEX_HRA) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AV) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 FV) fc None m (seg_rom psegs)).
  Hypothesis IOS : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : St),
      stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - HDEPTH -> bv_unsigned sp <= hi -> tp = Z_to_bv 64 RTP -> MID m s -> mem_inv psegs m ->
      implM psegs ci s (hpost POSTI sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
            (MS (mkR (Z_to_bv 64 AEX_HRA) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AI) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 FI) fc None m (seg_rom psegs)).

  Definition exit_own (W : list (Z * Z)) : Prop :=
    exists a b c d, W = [(a, b); (c, d)] /\ lo <= a /\ b <= hi /\ ((c = AEX /\ d = AEX + 24) \/ (c = AEX + 544 /\ d = AEX + 548) \/ (c = FINB /\ d = FINB + 1)).

  Lemma exit_own_loop : forall a b, lo <= a -> b <= hi -> exit_own [(a, b); (AEX, AEX + 24)]%Z.
  Proof. intros a b Ha Hb. exists a, b, AEX, (AEX + 24). split; [reflexivity|]. split; [exact Ha|]. split; [exact Hb|]. left. split; reflexivity. Qed.
  Hypothesis PREV_frame : forall W m m' s, PREV m s -> munch W m m' -> wmono psegs m m' -> exit_own W -> PREV m' s.
  Hypothesis MID_frame : forall W m m' s, MID m s -> munch W m m' -> wmono psegs m m' -> exit_own W -> MID m' s.
  Hypothesis POSTI_frame : forall W m m' s, POSTI m s -> munch W m m' -> wmono psegs m m' -> exit_own W -> POSTI m' s.

  Hypothesis MID_lch : forall m s, MID m s -> exists (cdt thr sec : byte) (tm1 : word), rw_cells psegs m RLIBCH [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
  Hypothesis POSTI_lch : forall m s, POSTI m s -> exists (cdt thr sec : byte) (tm1 : word), rw_cells psegs m RLIBCH [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
  Hypothesis MID_incb : forall m s, MID m s -> rw_cells psegs m RINCB [C1 (Z_to_bv 8 0)].

  Definition foe_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc None m' (seg_rom psegs)
      /\ agree_on' (fun a => outside (XW (bv_unsigned sp)) a /\ ~ (AEX <= a < AEX + 24)) m m' /\ mem_inv psegs m'
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ POSTI m' s'.

  Lemma funcs_on_exit3_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : St) (cdt thr sec : byte) (tm1 : word),
    stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - (48 + HDEPTH)) -> (GLOBALS_TOP <= lo) -> (16 <= HDEPTH) -> (bv_unsigned sp <= hi) -> (tp = Z_to_bv 64 RTP) ->
    rw_cells psegs m RLIBCH [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells psegs m AEX [C1 (Z_to_bv 8 0)] ->
    rw_cells psegs m (AEX + 4) [C4 z64; C4 (Z_to_bv 64 3)] ->
    rw_cells psegs m (AEX + 16) [C8 (Z_to_bv 64 (AEX + 24)); C8 z64; C8 (Z_to_bv 64 FI); C8 (Z_to_bv 64 RCALL); C8 (Z_to_bv 64 FV)] ->
    rw_cells psegs m (AEX + 288) [C8 (Z_to_bv 64 AI); C8 (Z_to_bv 64 RGUARD); C8 (Z_to_bv 64 AV)] ->
    PREV m s -> mem_inv psegs m ->
    implM psegs (cv ;;; ci) s (foe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 F_FUNCS_ON_EXIT) fc None m (seg_rom psegs)).
  Proof.
    intros until tm1. intros ST LO GLO HD HHI TPE LCH X1 X2 X3 X4 PRE MI.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold F_FUNCS_ON_EXIT, AEX, AEX_HRA, RLIBCH, FINB, RCALL, RGUARD, RINCB, GLOBALS_TOP in *.
    norm_addr X2. norm_addr X3. norm_addr X4.
    match type of X3 with context [Z_to_bv 64 (?a + 24)%Z] => let v := eval vm_compute in (a + 24)%Z in change (a + 24)%Z with v in X3 end.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x109de0, 0x109de0 + 24)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x109de0, 0x109de0 + 24)]%Z m) as MUF. pose proof (wmono_refl psegs m) as WMF.
    unfold implM.
    eapply (implM_bind psegs _ _ s
              (fun _ s' ms' => exists (t0 t1 t2 q1 a0 a1 a2 a3 a4 a5 a6 a7 q3 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (m' : mem) (j8 : list byte) cdt2 thr2 sec2 tm2,
                 ms' = MS (mkR (Z_to_bv 64 0xb9618) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 0x109de4) q1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x109de0) q3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F' (Z_to_bv 64 0xb9618) fc None m' (seg_rom psegs)
                 /\ agree_on' (fun a => outside (XW (bv_unsigned sp)) a /\ ~ (0x109de0 <= a < 0x109de0 + 24)) m m' /\ mem_inv psegs m'
                 /\ stk psegs m' lo (bv_unsigned sp + -48)
                 /\ rw_cells psegs m' (bv_unsigned sp + -48) [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                 /\ rw_cells psegs m' 0x109de0 [C1 (Z_to_bv 8 0)] /\ rw_cells psegs m' 0x109de4 [C4 z64; C4 (Z_to_bv 64 1)]
                 /\ rw_cells psegs m' 0x109df0 [C8 (Z_to_bv 64 0x109df8); C8 z64; C8 (Z_to_bv 64 FI); C8 (Z_to_bv 64 0xb97f0); C8 (Z_to_bv 64 FV)]
                 /\ rw_cells psegs m' 0x109f00 [C8 (Z_to_bv 64 AI); C8 (Z_to_bv 64 0x3eb28); C8 (Z_to_bv 64 AV)]
                 /\ rw_cells psegs m' 0x10a028 [C1 cdt2; C1 thr2; C1 sec2; C1 (Z_to_bv 8 0); C4 tm2]
                 /\ MID m' s')).
    -
      eapply (implM_evt psegs). 2:{ intros ms' H; exact H. } cbv beta.
      carve_frame 48%nat ST.
      steps_to 0xcb21c%Z. lock_ret.
      lstep. lstep. if_false.
      lstep. replace (sx32 (Z_to_bv 64 3)) with (Z_to_bv 64 3 : word) by (vm_compute; reflexivity).
      astep. lstep. try change (bv_swrap 32 (3 + -1)) with 2%Z.
      lstep. lstep. if_false.
      steps_to 0xb9608%Z.
      lstep. astep. unlock_ret.
      lstep. astep.
      rewrite (ret_pc_even FV) by (first [lia | exact FVE]).
      apply evt_done.
      name_sp sp (-48)%Z. replace (bv_unsigned sp + -48) with (bv_unsigned sp0) in ST by lia.
      lazymatch type of MUF with munch ?W ?m0 ?m1 =>
        assert (PRE1 : PREV m1 s) by (eapply (PREV_frame W m0 m1 s PRE MUF WMF); apply exit_own_loop; lia) end.

      lazymatch goal with |- context [MS _ _ _ _ _ ?m1 (seg_rom psegs)] =>
        lazymatch type of MUF with munch ?W ?m0 _ =>
          assert (AG0 : agree_on' (fun a => outside W a) m0 m1) by (apply (agree_on'_of_munch W m0 m1 MUF WMF)) end end.
      clear MUF WMF PRE.
      eapply implM_post_evt'.
      { eapply VEC; [ exact ST | clear - LO Hsp HD; lia | clear - HHI Hsp; lia | exact TPE | exact PRE1 | assumption ]. }
      cbv beta. intros [] st2 ms2 PO.
      destruct PO as (x0 & x1 & x2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x3 & x4 & x5 & x6 & F2 & m2 & -> & XA2 & MI2 & ST2 & MID2).

      repeat match goal with H : rw_cells psegs ?mo ?A ?cs |- _ =>
        lazymatch type of XA2 with xagree _ mo _ =>
          first [ assert_fails (constr_eq A A) | idtac ];
          tryif (eapply rw_cells_agree' in H; [| exact XA2 | intros a Ha; unfold XW, RTPLOC, AEX_VEC_OBJ; cbn [outside fst snd]; cbn in Ha; rewrite ?Hsp in *; lia])
          then idtac else clear H
        | _ => fail end end.
      destruct (MID_lch _ _ MID2) as (cdt2 & thr2 & sec2 & tm2 & LCH2). unfold RLIBCH in LCH2.
      pose proof (MID_incb _ _ MID2) as INCB. unfold RINCB in INCB.
      clear ST MU WM. unname_sp. rename ST2 into ST.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x109de0, 0x109de0 + 24)]%Z mm) as MUF2; pose proof (wmono_refl psegs mm) as WMF2;
        pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x109de0, 0x109de0 + 24)]%Z mm) as MU; pose proof (wmono_refl psegs mm) as WM end.

      lstep. astep. lock_ret.
      lstep. replace (sx32 (Z_to_bv 64 2)) with (Z_to_bv 64 2 : word) by (vm_compute; reflexivity).
      lstep. try change (bv_swrap 32 (2 + -1)) with 1%Z.
      lstep. lstep. if_true.
      steps_to 0xb9608%Z.
      lstep. astep. unlock_ret.
      lstep. astep.
      astep.
      steps_to 0x3eb30%Z. lstep. if_false.
      lstep.
      lazymatch type of MUF2 with munch ?W ?m0 ?m1 =>
        assert (MID3 : MID m1 st2) by (eapply (MID_frame W m0 m1 st2 MID2 MUF2 WMF2); apply exit_own_loop; lia);
        assert (AG3 : agree_on' (fun a => outside W a) m0 m1) by (apply (agree_on'_of_munch W m0 m1 MUF2 WMF2)) end.
      clear MUF2 WMF2 MID2 INCB.
      apply evt_done. cbv beta.
      do 17 eexists. exists F2. eexists. eexists. exists cdt2, thr2, sec2, tm2.
      split; [cbv delta [mkR]; reflexivity|].
      split.
      {
        eapply agree_on'_trans; [eapply agree_on'_trans; [eapply (agree_on'_mono _ _ _ _ AG0); xw_lia | eapply (agree_on'_mono _ _ _ _ XA2); xw_lia] | eapply (agree_on'_mono _ _ _ _ AG3); xw_lia]. }
      repeat match goal with |- _ /\ _ => split end; try assumption; try norm_goal_addr.
    -
      cbv beta. intros [] st2 ms2 PO.
      destruct PO as (x0 & x1 & x2 & q1 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & q3 & x3 & x4 & x5 & x6 & F2 & m2 & j8 & cdt2 & thr2 & sec2 & tm2 & -> & XA & MI2 & STm & FR & Y1 & Y2 & Y3 & Y4 & LCH2 & MID2).
      clear ST MU WM MUF WMF LCH X1 X2 X3 X4 PRE MI. rename STm into ST.
      pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x109de0, 0x109de0 + 24)]%Z m2) as MUF. pose proof (wmono_refl psegs m2) as WMF.
      pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x109de0, 0x109de0 + 24)]%Z m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      eapply (implM_evt psegs). 2:{ intros ms' H; exact H. } cbv beta.
      lstep. astep. lock_ret.
      lstep. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
      lstep. try change (bv_swrap 32 (1 + -1)) with 0%Z.
      lstep. lstep. if_true.
      steps_to 0xb9608%Z.
      lstep. astep. unlock_ret.
      lstep. astep.
      rewrite (ret_pc_even FI) by (first [lia | exact FIE]).
      apply evt_done.
      name_sp sp (-48)%Z. replace (bv_unsigned sp + -48) with (bv_unsigned sp0) in ST by lia.
      lazymatch type of MUF with munch ?W ?m0 ?m1 =>
        assert (MID3 : MID m1 st2) by (eapply (MID_frame W m0 m1 st2 MID2 MUF WMF); apply exit_own_loop; lia);
        assert (AG4 : agree_on' (fun a => outside W a) m0 m1) by (apply (agree_on'_of_munch W m0 m1 MUF WMF)) end.
      clear MUF WMF MID2.
      eapply implM_post_evt'.
      { eapply IOS; [ exact ST | clear - LO Hsp HD; lia | clear - HHI Hsp; lia | exact TPE | exact MID3 | assumption ]. }
      cbv beta. intros [] st3 ms3 PO.
      destruct PO as (y0 & y1 & y2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y3 & y4 & y5 & y6 & F3 & m3 & -> & XA3 & MI3 & ST3 & POST3).
      repeat match goal with H : rw_cells psegs ?mo ?A ?cs |- _ =>
        lazymatch type of XA3 with xagree _ mo _ =>
          tryif (eapply rw_cells_agree' in H; [| exact XA3 | intros a Ha; unfold XW, RTPLOC, AEX_VEC_OBJ; cbn [outside fst snd]; cbn in Ha; rewrite ?Hsp in *; lia])
          then idtac else clear H
        | _ => fail end end.
      destruct (POSTI_lch _ _ POST3) as (cdt3 & thr3 & sec3 & tm3 & LCH3). unfold RLIBCH in LCH3.
      clear ST MU WM. unname_sp. rename ST3 into ST.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x109de0, 0x109de0 + 24)]%Z mm) as MUF4; pose proof (wmono_refl psegs mm) as WMF4;
        pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x109de0, 0x109de0 + 24)]%Z mm) as MU; pose proof (wmono_refl psegs mm) as WM end.
      lstep. astep. lock_ret.
      lstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
      lstep. try change (bv_swrap 32 (0 + -1)) with (-1)%Z.
      lstep. lstep. if_false.
      lstep. astep.
      lstep. lstep. lstep. lstep.
      lstep. if_true.
      steps_to 0xb965c%Z.
      release_frame FR ST (bv_unsigned sp).
      astep. unlock_ret.
      lazymatch type of MUF4 with munch ?W ?m0 ?m1 =>
        assert (POST4 : POSTI m1 st3) by (eapply (POSTI_frame W m0 m1 st3 POST3 MUF4 WMF4); apply exit_own_loop; lia);
        assert (AG5 : agree_on' (fun a => outside W a) m0 m1) by (apply (agree_on'_of_munch W m0 m1 MUF4 WMF4)) end.
      clear MUF4 WMF4 POST3.
      apply evt_done. unfold foe_post, AEX. sys_finish.
      all: first [ exact POST4 | norm_goal_addr
                 | eapply agree_on'_trans; [eapply agree_on'_trans; [eapply agree_on'_trans; [exact XA | eapply (agree_on'_mono _ _ _ _ AG4); xw_lia] | eapply (agree_on'_mono _ _ _ _ XA3); xw_lia]
                                          | eapply (agree_on'_mono _ _ _ _ AG5); xw_lia] ].
  Qed.

  Lemma funcs_on_exit1_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : St) (cdt thr sec : byte) (tm1 : word),
    stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - (48 + HDEPTH)) -> (GLOBALS_TOP <= lo) -> (16 <= HDEPTH) -> (bv_unsigned sp <= hi) -> (tp = Z_to_bv 64 RTP) ->
    rw_cells psegs m RLIBCH [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells psegs m AEX [C1 (Z_to_bv 8 0)] ->
    rw_cells psegs m (AEX + 4) [C4 z64; C4 (Z_to_bv 64 1)] ->
    rw_cells psegs m (AEX + 16) [C8 (Z_to_bv 64 (AEX + 24)); C8 z64; C8 (Z_to_bv 64 FI); C8 z64; C8 z64] ->
    rw_cells psegs m (AEX + 288) [C8 (Z_to_bv 64 AI); C8 z64; C8 z64] ->
    MID m s -> mem_inv psegs m ->
    implM psegs ci s (foe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 F_FUNCS_ON_EXIT) fc None m (seg_rom psegs)).
  Proof.
    intros until tm1. intros ST LO GLO HD HHI TPE LCH X1 X2 X3 X4 MID0 MI.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold F_FUNCS_ON_EXIT, AEX, AEX_HRA, RLIBCH, FINB, RCALL, RGUARD, RINCB, GLOBALS_TOP in *.
    norm_addr X2. norm_addr X3. norm_addr X4.
    match type of X3 with context [Z_to_bv 64 (?a + 24)%Z] => let v := eval vm_compute in (a + 24)%Z in change (a + 24)%Z with v in X3 end.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x109de0, 0x109de0 + 24)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x109de0, 0x109de0 + 24)]%Z m) as MUF. pose proof (wmono_refl psegs m) as WMF.
    unfold implM.
    eapply (implM_evt psegs). 2:{ intros ms' H; exact H. } cbv beta.
    carve_frame 48%nat ST.
    steps_to 0xcb21c%Z. lock_ret.
    lstep. lstep. if_false.
    lstep. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
    astep. lstep. try change (bv_swrap 32 (1 + -1)) with 0%Z.
    lstep. lstep. if_false.
    steps_to 0xb9608%Z.
    lstep. astep. unlock_ret.
    lstep. astep.
    rewrite (ret_pc_even FI) by (first [lia | exact FIE]).
    apply evt_done.
    name_sp sp (-48)%Z. replace (bv_unsigned sp + -48) with (bv_unsigned sp0) in ST by lia.
    lazymatch type of MUF with munch ?W ?m0 ?m1 =>
      assert (MID1 : MID m1 s) by (eapply (MID_frame W m0 m1 s MID0 MUF WMF); apply exit_own_loop; lia);
      assert (AG0 : agree_on' (fun a => outside W a) m0 m1) by (apply (agree_on'_of_munch W m0 m1 MUF WMF)) end.
    clear MUF WMF MID0.
    eapply implM_post_evt'.
    { eapply IOS; [ exact ST | clear - LO Hsp HD; lia | clear - HHI Hsp; lia | exact TPE | exact MID1 | assumption ]. }
    cbv beta. intros [] st3 ms3 PO.
    destruct PO as (y0 & y1 & y2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y3 & y4 & y5 & y6 & F3 & m3 & -> & XA3 & MI3 & ST3 & POST3).
    repeat match goal with H : rw_cells psegs ?mo ?A ?cs |- _ =>
      lazymatch type of XA3 with xagree _ mo _ =>
        tryif (eapply rw_cells_agree' in H; [| exact XA3 | intros a Ha; unfold XW, RTPLOC, AEX_VEC_OBJ; cbn [outside fst snd]; cbn in Ha; rewrite ?Hsp in *; lia])
        then idtac else clear H
      | _ => fail end end.
    destruct (POSTI_lch _ _ POST3) as (cdt3 & thr3 & sec3 & tm3 & LCH3). unfold RLIBCH in LCH3.
    clear ST MU WM. unname_sp. rename ST3 into ST.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x109de0, 0x109de0 + 24)]%Z mm) as MUF4; pose proof (wmono_refl psegs mm) as WMF4;
      pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x109de0, 0x109de0 + 24)]%Z mm) as MU; pose proof (wmono_refl psegs mm) as WM end.

    lstep. astep. lock_ret.
    lstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    lstep. try change (bv_swrap 32 (0 + -1)) with (-1)%Z.
    lstep. lstep. if_false.
    lstep. astep.
    lstep. lstep. lstep. lstep.
    lstep. if_true.
    steps_to 0xb965c%Z.
    release_frame FR ST (bv_unsigned sp).
    astep. unlock_ret.
    lazymatch type of MUF4 with munch ?W ?m0 ?m1 =>
      assert (POST4 : POSTI m1 st3) by (eapply (POSTI_frame W m0 m1 st3 POST3 MUF4 WMF4); apply exit_own_loop; lia);
      assert (AG5 : agree_on' (fun a => outside W a) m0 m1) by (apply (agree_on'_of_munch W m0 m1 MUF4 WMF4)) end.
    clear MUF4 WMF4 POST3.
    apply evt_done. unfold foe_post, AEX. sys_finish.
    all: first [ exact POST4 | norm_goal_addr
               | eapply agree_on'_trans; [eapply agree_on'_trans; [eapply (agree_on'_mono _ _ _ _ AG0); xw_lia | eapply (agree_on'_mono _ _ _ _ XA3); xw_lia]
                                        | eapply (agree_on'_mono _ _ _ _ AG5); xw_lia] ].
  Qed.

  Variables (Sin Sout Serr : Z).
  Hypothesis POSTI_files : forall m s, POSTI m s ->
      exists i0 irp i1 iwp i2 i3 o0 orp o1 owp o2 o3 e0 erp e1 ewp e2 e3,
        rw_cells psegs m Sin (clean_file_cells i0 irp i1 iwp i2 i3) /\ rw_cells psegs m Sout (clean_file_cells o0 orp o1 owp o2 o3)
        /\ rw_cells psegs m Serr (clean_file_cells e0 erp e1 ewp e2 e3)
        /\ (0 <= irp < 2^64) /\ (0 <= iwp < 2^64) /\ (0 <= orp < 2^64) /\ (0 <= owp < 2^64) /\ (0 <= erp < 2^64) /\ (0 <= ewp < 2^64).

  Definition exit_pre (m : mem) (sp tp a0 : word) (code t : Z) (td0 td1 td2 td3 : word) (cdt thr sec : byte) (tm1 : word) : Prop :=
    rw_cells psegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells psegs m 0x10a000 [C4 z64]
    /\ rw_cells psegs m 0xd66b8 [C8 (Z_to_bv 64 0xd0608); C8 (Z_to_bv 64 0xd0600)]
    /\ rw_cells psegs m 0xd0600 [C8 (Z_to_bv 64 0x3e670)]
    /\ rw_cells psegs m 0xd7ae8 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs m 0xd64f8 [C8 (Z_to_bv 64 0xb9660); C8 z64]
    /\ rw_cells psegs m 0xd76e0 [C8 (Z_to_bv 64 0xd76e0)]
    /\ rw_cells psegs m RLIBCH [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ rw_cells psegs m ROFL_LOCK [C4 z64; C4 z64; C8 z64]
    /\ rw_cells psegs m RSTDIN_USED [C8 (Z_to_bv 64 Sin)] /\ (0 < Sin) /\ (Sin + 148 <= GLOBALS_TOP)
    /\ rw_cells psegs m RSTDOUT_USED [C8 (Z_to_bv 64 Sout)] /\ (0 < Sout) /\ (Sout + 148 <= GLOBALS_TOP)
    /\ rw_cells psegs m RSTDERR_USED [C8 (Z_to_bv 64 Serr)] /\ (0 < Serr) /\ (Serr + 148 <= GLOBALS_TOP)
    /\ tp = Z_to_bv 64 RTP /\ a0 = Z_to_bv 64 code /\ (0 < t < 4194304)%Z /\ (0 <= code < 2^64).

  Definition foe_stmt (c : @M St unit) (P : mem -> St -> Prop) (T : mem -> Prop) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : St) (cdt thr sec : byte) (tm1 : word),
      stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - (48 + HDEPTH)) -> (GLOBALS_TOP <= lo) -> (16 <= HDEPTH) -> (bv_unsigned sp <= hi) -> (tp = Z_to_bv 64 RTP) ->
      rw_cells psegs m RLIBCH [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
      T m -> P m s -> mem_inv psegs m ->
      implM psegs c s (foe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 F_FUNCS_ON_EXIT) fc None m (seg_rom psegs)).

  Definition exit_prologue_ok (W : list (Z * Z)) : Prop := forall x, outside W x \/ (AEX + 544 <= x < AEX + 548) \/ (lo <= x).

  Lemma exit_spec_gen : forall (c : @M St unit) (P : mem -> St -> Prop) (T : mem -> Prop),
    foe_stmt c P T ->
    (forall W m m' s, P m s -> munch W m m' -> wmono psegs m m' -> exit_own W -> P m' s) ->
    (forall W m m', GLOBALS_TOP <= lo -> T m -> munch W m m' -> wmono psegs m m' -> exit_prologue_ok W -> T m') ->
    forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (code t : Z) (td0 td1 td2 td3 : word) (cdt thr sec : byte) (tm1 : word),
    stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - (64 + HDEPTH)) -> (GLOBALS_TOP <= lo) -> (16 <= HDEPTH) -> (bv_unsigned sp <= hi) -> (tp = Z_to_bv 64 RTP) ->
    exit_pre m sp tp a0 code t td0 td1 td2 td3 cdt thr sec tm1 ->
    T m -> P m s -> mem_inv psegs m ->
    implM psegs (c ;;; msys (NExit code) dec_exit) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 REXIT) fc None m (seg_rom psegs)).
  Proof.
    intros c P T FOE P_frame T_frame.
    intros until tm1; intros ST LO GLO HD HHI TPE XP XT PRE MI.
    destruct XP as (TDa & EXL & GF & FA & FIN & GCX & DSO & LCH & OFL & SIU & Sin0 & SinH & SOU & Sout0 & SoutH & SEU & Serr0 & SerrH & -> & -> & Ht & CODE).
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    unfold REXIT, AEX, RLIBCH, FINB, GLOBALS_TOP, ROFL_LOCK, RSTDIN_USED, RSTDOUT_USED, RSTDERR_USED in *.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (0x10a000, 0x10a004)]%Z m) as MU; pose proof (wmono_refl psegs m) as WM.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (0x10a000, 0x10a004)]%Z m) as MUF; pose proof (wmono_refl psegs m) as WMF.
    eapply (implM_bind psegs _ _ s
              (fun _ s' ms' => exists sp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F' m',
                 ms' = MS (mkR (Z_to_bv 64 0xb98b0) sp' gp (Z_to_bv 64 RTP) x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F' (Z_to_bv 64 0xb98b0) fc None m' (seg_rom psegs))).
    - eapply (implM_evt psegs). 2:{ intros ms' H; exact H. } cbv beta.
      carve_frame 16%nat ST.
      do 6 lstep.
      replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t) by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
      lstep. lstep.

      amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
      lstep. if_false. amo_step. lstep. if_false.
      lstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
      lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. lstep. if_true.
      lstep. astep.

      apply evt_done.
      name_sp sp (-16)%Z. replace (bv_unsigned sp + -16) with (bv_unsigned sp0) in ST by lia.
      lazymatch type of MUF with munch ?W ?m0 ?m1 =>
        assert (PRE1 : P m1 s) by (eapply (P_frame W m0 m1 s PRE MUF WMF); eexists _, _, _, _; split; [reflexivity|]; split; [lia|]; split; [lia|]; right; left; unfold AEX; split; reflexivity);
        assert (XT1 : T m1) by (eapply (T_frame W m0 m1 ltac:(lia) XT MUF WMF); intros x; unfold AEX; destruct (Z.le_gt_cases lo x) as [Hx|Hx]; [right; right; exact Hx|];
                                   destruct (Z.le_gt_cases 0x10a000 x) as [H2|H2]; [| left; cbn; lia]; destruct (Z.lt_ge_cases x 0x10a004) as [H3|H3]; [right; left; lia| left; cbn; lia]) end.
      clear MUF WMF PRE XT.
      eapply implM_post_evt'.
      { eapply FOE; first [ exact ST | exact PRE1 | exact XT1 | eassumption | reflexivity | lia ]. }
      cbv beta. intros [] st2 ms2 PO.
      destruct PO as (x0 & x1 & x2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x3 & x4 & x5 & x6 & F2 & m2 & -> & AG2 & MI2 & ST2 & POST2). unfold AEX in AG2.

      repeat match goal with H : rw_cells psegs ?mo ?A ?cs |- _ =>
        lazymatch type of AG2 with agree_on' _ mo _ =>
          tryif (eapply rw_cells_agree' in H; [| exact AG2 | intros a Ha; unfold XW, RTPLOC, AEX_VEC_OBJ; cbn [outside fst snd]; cbn in Ha; rewrite ?Hsp in *; lia])
          then idtac else clear H
        | _ => fail end end.
      clear ST MU WM. unname_sp. rename ST2 into ST.
      lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] => rewrite (ret_pc_even r) by (cbn; lia) end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (883432, 883433)]%Z mm) as MUF3; pose proof (wmono_refl psegs mm) as WMF3;
        pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (883432, 883433)]%Z mm) as MU; pose proof (wmono_refl psegs mm) as WM end.
      steps_to 0xb97f8%Z.

      carve_frame 32%nat ST. steps_to 0x3e670%Z.
      carve_frame 16%nat ST. steps_to 0x3e6fc%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. astep.
      steps_to 0xb9840%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z. astep. astep.
      astep.
      lazymatch type of MUF3 with munch ?W ?m0 ?m1 =>
        assert (POST3 : POSTI m1 st2) by (eapply (POSTI_frame W m0 m1 st2 POST2 MUF3 WMF3); eexists _, _, _, _; split; [reflexivity|]; split; [lia|]; split; [lia|]; right; right; unfold FINB; split; reflexivity) end.
      clear MUF3 WMF3 POST2.
      destruct (POSTI_files _ _ POST3) as (i0 & irp & i1 & iwp & i2 & i3 & o0 & orp & o1 & owp & o2 & o3 & e0 & erp & e1 & ewp & e2 & e3 & CI & CO & CE & B1 & B2 & B3 & B4 & B5 & B6).
      destruct (POSTI_lch _ _ POST3) as (cdt3 & thr3 & sec3 & tm3 & LCH3). unfold RLIBCH in LCH3.
      name_sp sp (-16)%Z. replace (bv_unsigned sp + -16) with (bv_unsigned sp0) in ST by lia.
      eapply evt_cut; [ eapply stdio_exit_idle_spec with (irp := irp) (iwp := iwp) (orp := orp) (owp := owp) (erp := erp) (ewp := ewp)
                                  (i0 := i0) (i1 := i1) (i2 := i2) (i3 := i3) (o0 := o0) (o1 := o1) (o2 := o2) (o3 := o3) (e0 := e0) (e1 := e1) (e2 := e2) (e3 := e3);
                        first [ exact ST | exact CI | exact CO | exact CE | eassumption | norm_goal_addr | unfold RLIBC_HEAD, F_stdio_exit0.ROFL_LOCK, GLOBALS_TOP; lia ] | ].
      cbv beta. intros ms4 PO4.
      destruct PO4 as (y0 & y1 & y2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y3 & y4 & y5 & y6 & m4 & -> & MU4 & WM4 & MI4 & ST4).
      lazymatch type of MU4 with munch _ ?ma ?mb => transport_after_call psegs ma mb MU4 WM4 end. clear MU4 WM4.
      unname_sp. rename ST4 into ST.
      lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] => rewrite (ret_pc_even r) by (cbn; lia) end.

      apply evt_done. cbv beta. repeat eexists.
    -
      cbv beta. intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implM_sys. do 4 lstep. step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
  Qed.

  Definition tbl1 (m : mem) : Prop :=
    rw_cells psegs m AEX [C1 (Z_to_bv 8 0)] /\ rw_cells psegs m (AEX + 4) [C4 z64; C4 (Z_to_bv 64 1)]
    /\ rw_cells psegs m (AEX + 16) [C8 (Z_to_bv 64 (AEX + 24)); C8 z64; C8 (Z_to_bv 64 FI); C8 z64; C8 z64] /\ rw_cells psegs m (AEX + 288) [C8 (Z_to_bv 64 AI); C8 z64; C8 z64].

  Definition tbl3 (m : mem) : Prop :=
    rw_cells psegs m AEX [C1 (Z_to_bv 8 0)] /\ rw_cells psegs m (AEX + 4) [C4 z64; C4 (Z_to_bv 64 3)]
    /\ rw_cells psegs m (AEX + 16) [C8 (Z_to_bv 64 (AEX + 24)); C8 z64; C8 (Z_to_bv 64 FI); C8 (Z_to_bv 64 RCALL); C8 (Z_to_bv 64 FV)]
    /\ rw_cells psegs m (AEX + 288) [C8 (Z_to_bv 64 AI); C8 (Z_to_bv 64 RGUARD); C8 (Z_to_bv 64 AV)].
  Lemma foe1 : foe_stmt ci MID tbl1.
  Proof. intros until tm1. intros ST LO GLO HD HHI TPE LCH (X1 & X2 & X3 & X4) PRE MI. eapply funcs_on_exit1_spec; eassumption. Qed.
  Lemma foe3 : foe_stmt (cv ;;; ci) PREV tbl3.
  Proof. intros until tm1. intros ST LO GLO HD HHI TPE LCH (X1 & X2 & X3 & X4) PRE MI. eapply funcs_on_exit3_spec; eassumption. Qed.
  Lemma tbl1_frame : forall W m m', GLOBALS_TOP <= lo -> tbl1 m -> munch W m m' -> wmono psegs m m' -> exit_prologue_ok W -> tbl1 m'.
  Proof.
    intros W m m' GLO (X1 & X2 & X3 & X4) MU WM HW. pose proof (agree_on'_of_munch W m m' MU WM) as AG. unfold tbl1, exit_prologue_ok, AEX, RCALL, RGUARD in *.
    repeat match goal with |- _ /\ _ => split end;
      (eapply (rw_cells_agree' _ _ _ _ _ AG); [eassumption | intros a Ha; cbn in Ha; destruct (HW a) as [Ho|[Ho|Ho]]; [exact Ho| exfalso; lia| exfalso; unfold GLOBALS_TOP in *; lia]]).
  Qed.
  Lemma tbl3_frame : forall W m m', GLOBALS_TOP <= lo -> tbl3 m -> munch W m m' -> wmono psegs m m' -> exit_prologue_ok W -> tbl3 m'.
  Proof.
    intros W m m' GLO (X1 & X2 & X3 & X4) MU WM HW. pose proof (agree_on'_of_munch W m m' MU WM) as AG. unfold tbl3, exit_prologue_ok, AEX, RCALL, RGUARD in *.
    repeat match goal with |- _ /\ _ => split end;
      (eapply (rw_cells_agree' _ _ _ _ _ AG); [eassumption | intros a Ha; cbn in Ha; destruct (HW a) as [Ho|[Ho|Ho]]; [exact Ho| exfalso; lia| exfalso; unfold GLOBALS_TOP in *; lia]]).
  Qed.
End Aex.

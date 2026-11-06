(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib Arr SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts BzContracts0 DecCut DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecAuxM DecTac DecTac2 DecTacM BzWalkArith3 S0_dec_U13 S0_decCuts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_decCuts7.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_decCuts7.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_hbCreate.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_hbCreate.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac.DecAuxB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAuxM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_dec_U13 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_decCuts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_decCuts7.S0_decCutsB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_decCuts7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_hbCreate.S0_hbCreateB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_hbCreate.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit DecFast DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import DecFastM.
Local Ltac DecTacM.revive_f H MUL WML AOK ::= DecFastM.revive_f_fast H MUL WML AOK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import  BzImg0Tac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia RelLiaR.
Local Ltac lia ::= RelLia.lia_rf3.
Local Ltac StoreFast.tlia ::= RelLiaR.tlia_rr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Definition S0_hbCreateZ_post (ra : word) (spz : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (DS t : Z) (lws bws pws : list word) (lbs : list byte) (minLen maxLen alpha lo : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' lws' bws' pws',
    ms' = MS (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom s0segs)
    /\ munch [(DS + 45436 + 1032 * t, DS + 45436 + 1032 * t + 1032);
              (DS + 51628 + 1032 * t, DS + 51628 + 1032 * t + 1032);
              (DS + 57820 + 1032 * t, DS + 57820 + 1032 * t + 1032);
              (spz + -64, spz)]%Z m m'
    /\ wmono s0segs m m' /\ mem_inv s0segs m'
    /\ u32arr s0segs m' (DS + 45436 + 1032 * t) lws' /\ length lws' = 258%nat
    /\ u32arr s0segs m' (DS + 51628 + 1032 * t) bws' /\ length bws' = 258%nat
    /\ u32arr s0segs m' (DS + 57820 + 1032 * t) pws' /\ length pws' = 258%nat
    /\ u8arr s0segs m' (DS + 43888 + 258 * t) lbs
    /\ stk s0segs m' lo spz
    /\ (let '(limit, base, perm) := hb_create (sv32 lws) (sv32 bws) (sv32 pws) (uv8 lbs) minLen maxLen alpha in
        ag32s lws' limit 258 /\ ag32s bws' base 258 /\ ag32s pws' perm 258).

Lemma S0_hbCreate_specZ :
  forall (DS t : Z) (lws bws pws : list word) (lbs : list byte) (minLen maxLen alpha lo spz : Z)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  u32arr s0segs m (DS + 45436 + 1032 * t) lws -> length lws = 258%nat ->
  u32arr s0segs m (DS + 51628 + 1032 * t) bws -> length bws = 258%nat ->
  u32arr s0segs m (DS + 57820 + 1032 * t) pws -> length pws = 258%nat ->
  u8arr s0segs m (DS + 43888 + 258 * t) lbs -> length lbs = 258%nat ->
  (0 <= DS)%Z /\ (DS mod 16 = 0)%Z /\ (0 <= t < 6)%Z ->
  (DS + 64144 <= lo)%Z /\ (lo + 64 <= spz)%Z -> (0 <= spz < 2^64)%Z ->
  stk s0segs m lo spz -> mem_inv s0segs m ->
  (1 <= alpha <= 258)%Z -> (1 <= minLen /\ minLen <= maxLen <= 20)%Z ->
  (forall j, (0 <= j < alpha)%Z -> (minLen <= uv8 lbs j <= maxLen)%Z) ->
  a0 = Z_to_bv 64 (DS + 45436 + 1032 * t) -> a1 = Z_to_bv 64 (DS + 51628 + 1032 * t) ->
  a2 = Z_to_bv 64 (DS + 57820 + 1032 * t) -> a3 = Z_to_bv 64 (DS + 43888 + 258 * t) ->
  a4 = Z_to_bv 64 minLen -> a5 = Z_to_bv 64 maxLen -> a6 = Z_to_bv 64 alpha ->
  evt s0segs (S0_hbCreateZ_post ra spz gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DS t lws bws pws lbs minLen maxLen alpha lo m)
      (MS (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bb78) fc None m (seg_rom s0segs)).
Proof.
  intros DS t lws bws pws lbs minLen maxLen alpha lo spz ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ARL LENl ARB LENb ARP LENp AR8 LEN8 HS HLO Hsp ST MI Halpha Hmm Hlen E0 E1 E2 E3 E4 E5 E6.
  assert (E : bv_unsigned (Z_to_bv 64 spz) = spz) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { apply (S0_hbCreate_spec ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             DS t lws bws pws lbs minLen maxLen alpha lo ARL LENl ARB LENb ARP LENp AR8 LEN8 HS);
      [ rewrite E; exact HLO | rewrite E; exact ST | exact MI | exact Halpha | exact Hmm | exact Hlen
      | exact E0 | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact E6 ]. }
  intros ms' PO. unfold S0_hbCreate_post in PO. rewrite E in PO. exact PO.
Qed.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variables ng nsc alpha : Z.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation Q := (POST14 DI_S0 A).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmem DM; s2img.

  Lemma S0_U7_C : forall t mn mx, (0 <= t < ng)%Z ->
    S0_cut_L7D A ng nsc alpha t -> S0_cut_L7C A ng nsc alpha t mn mx.
  Proof.
    intros t mn mx Ht NXD. unfold S0_cut_L7C. intros until pb.
    intros DM FR ST MU WM MI DP IB NS2 NIU NG NSC SOK AL Ht' LOK TU Hmm SCAN.
    (* [comment removed for export] *)
    prep DM MU.
    dr_open.
    (* [comment removed for export] *)
    set (i0 := Z.to_nat (258 * t)).
    assert (Hi0 : Z.of_nat i0 = (258 * t)%Z) by (subst i0; lia).
    lazymatch goal with H : u32arr _ _ (S + 45436)%Z ?l |- _ =>
      cps_destruct (u32arr_split3 s0segs m (S + 45436) l i0 258 ltac:(lia) H) as (LIMa & LIMb & LIMc & LNLa & LNLb & LNLc & EQL); clear H end.
    lazymatch goal with H : u32arr _ _ (S + 51628)%Z ?l |- _ =>
      cps_destruct (u32arr_split3 s0segs m (S + 51628) l i0 258 ltac:(lia) H) as (BASa & BASb & BASc & LNBa & LNBb & LNBc & EQB); clear H end.
    lazymatch goal with H : u32arr _ _ (S + 57820)%Z ?l |- _ =>
      cps_destruct (u32arr_split3 s0segs m (S + 57820) l i0 258 ltac:(lia) H) as (PRMa & PRMb & PRMc & LNPa & LNPb & LNPc & EQP); clear H end.
    lazymatch goal with H : u8arr _ _ (S + 43888)%Z ?l |- _ =>
      cps_destruct (u8arr_split3 s0segs m (S + 43888) l i0 258 ltac:(lia) H) as (LENa & LENb & LENc & LN8a & LN8b & LN8c & EQ8); clear H end.
    remember (firstn i0 (r_lim (dv_r v))) as preL eqn:E1. remember (firstn 258 (skipn i0 (r_lim (dv_r v)))) as lws eqn:E2.
    remember (skipn (i0 + 258) (r_lim (dv_r v))) as sufL eqn:E3.
    remember (firstn i0 (r_base (dv_r v))) as preB eqn:E4. remember (firstn 258 (skipn i0 (r_base (dv_r v)))) as bws eqn:E5.
    remember (skipn (i0 + 258) (r_base (dv_r v))) as sufB eqn:E6.
    remember (firstn i0 (r_perm (dv_r v))) as preP eqn:E7. remember (firstn 258 (skipn i0 (r_perm (dv_r v)))) as pws eqn:E8.
    remember (skipn (i0 + 258) (r_perm (dv_r v))) as sufP eqn:E9.
    remember (firstn i0 (r_len (dv_r v))) as preN eqn:E10. remember (firstn 258 (skipn i0 (r_len (dv_r v)))) as lbs eqn:Elbs.
    remember (skipn (i0 + 258) (r_len (dv_r v))) as sufN eqn:E12.
    clear E1 E3 E4 E6 E7 E9 E10 E12 E2 E5 E8.
    (* [comment removed for export] *)
    assert (ZLa : Z.of_nat (length preL) = (258 * t)%Z) by lia.
    assert (ZBa : Z.of_nat (length preB) = (258 * t)%Z) by lia.
    assert (ZPa : Z.of_nat (length preP) = (258 * t)%Z) by lia.
    assert (ZNa : Z.of_nat (length preN) = (258 * t)%Z) by lia.
    pose proof (f_equal (@length _) EQL) as XL; rewrite !length_app in XL.
    pose proof (f_equal (@length _) EQB) as XB; rewrite !length_app in XB.
    pose proof (f_equal (@length _) EQP) as XP; rewrite !length_app in XP.
    pose proof (f_equal (@length _) EQ8) as XN; rewrite !length_app in XN.
    assert (ZLc : Z.of_nat (length sufL) = (1548 - 258 - 258 * t)%Z) by lia.
    assert (ZBc : Z.of_nat (length sufB) = (1548 - 258 - 258 * t)%Z) by lia.
    assert (ZPc : Z.of_nat (length sufP) = (1548 - 258 - 258 * t)%Z) by lia.
    assert (ZNc : Z.of_nat (length sufN) = (1548 - 258 - 258 * t)%Z) by lia.
    clear XL XB XP XN LNLa LNLc LNBa LNBc LNPa LNPc LN8a LN8c.
    replace (S + 45436 + 4 * Z.of_nat i0)%Z with (S + 45436 + 1032 * t)%Z in LIMb by lia.
    replace (S + 51628 + 4 * Z.of_nat i0)%Z with (S + 51628 + 1032 * t)%Z in BASb by lia.
    replace (S + 57820 + 4 * Z.of_nat i0)%Z with (S + 57820 + 1032 * t)%Z in PRMb by lia.
    replace (S + 43888 + Z.of_nat i0)%Z with (S + 43888 + 258 * t)%Z in LENb by lia.
    replace (S + 45436 + 4 * Z.of_nat (i0 + 258))%Z with (S + 45436 + 1032 * t + 1032)%Z in LIMc by lia.
    replace (S + 51628 + 4 * Z.of_nat (i0 + 258))%Z with (S + 51628 + 1032 * t + 1032)%Z in BASc by lia.
    replace (S + 57820 + 4 * Z.of_nat (i0 + 258))%Z with (S + 57820 + 1032 * t + 1032)%Z in PRMc by lia.
    replace (S + 43888 + Z.of_nat (i0 + 258))%Z with (S + 43888 + 258 * t + 258)%Z in LENc by lia.
    (* [comment removed for export] *)
    assert (Hlen : forall j, (0 <= j < alpha)%Z -> (mn <= uv8 lbs j <= mx)%Z).
    { intros j Hj. rewrite Elbs. rewrite uv8_window by lia. rewrite Hi0. apply SCAN. lia. }
    clear Elbs Hi0. clearbody i0. clear i0.
    pose proof (act_lin _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof (act_ok_al _ _ AOK) as ALG; unfold ctx_al in ALG.
    cps_destruct ALG as (ALG1 & ALG2 & ALG3 & ALG4 & _). apply Z.mod_divide in ALG1; [|lia]. apply Z.mod_divide in ALG2; [|lia]. apply Z.mod_divide in ALG3; [|lia]. apply Z.mod_divide in ALG4; [|lia].
    destruct ALG1 as [qa1 ALG1]. destruct ALG2 as [qa2 ALG2]. destruct ALG3 as [qa3 ALG3]. destruct ALG4 as [qa4 ALG4].
    hide_all_but_at [S + 45436 + 1032 * t; S + 51628 + 1032 * t; S + 57820 + 1032 * t; S + 43888 + 258 * t; S + 64012; usp + -320]%Z.
    (* [comment removed for export] *)
    pose proof (munch_refl ([(S + 45436 + 1032 * t, S + 45436 + 1032 * t + 1032); (S + 51628 + 1032 * t, S + 51628 + 1032 * t + 1032);
                             (S + 57820 + 1032 * t, S + 57820 + 1032 * t + 1032); (usp + -320 + -64, usp + -320)]
                            ++ [(S + 64012, S + 64036); (usp + -320, usp)])%Z m) as MUL.
    pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    do 13 wstepl.
    eapply evt_cut.
    { eapply (S0_hbCreate_specZ S t lws bws pws lbs mn mx alpha (a_lo A) (usp + -320)%Z);
        [ exact LIMb | exact LNLb | exact BASb | exact LNBb | exact PRMb | exact LNPb | exact LENb | exact LN8b
        | lia | lia | lia | exact ST | exact MI | lia | lia | exact Hlen
        | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia]
        | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia]
        | first [reflexivity | f_equal; lia] ]. }
    intros ms' PO. unfold S0_hbCreateZ_post in PO.
    cps_destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & lws' & bws' & pws'
                    & Ems & MUc & WMc & MIc & ARL' & LNl' & ARB' & LNb' & ARP' & LNp' & AR8' & ST' & AG).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 122252)) with (Z_to_bv 64 122252) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    lazymatch type of MUL with munch ?Wq _ _ =>
      pose proof (munch_weaken _ Wq m m' (sub_fp_app_l _ _) MUc) as MULn end.
    clear MUL. rename MULn into MUL. cbn [app] in MUL.
    lazymatch type of MU with munch ?W14 ?m0 _ =>
    lazymatch type of MUc with munch ?Wc _ _ =>
      assert (SUB14 : sub_fp Wc W14) by (lin_unbox LIN; clear - LIN Ht NG; sub_fp_solve);
      apply (munch_trans W14 m0 m m') in MU; [ | exact (munch_weaken Wc W14 m m' SUB14 MUc) ]; clear SUB14 end end.
    apply (wmono_trans s0segs _ m m') in WM; [ | exact WMc ].
    clear WML. pose proof WMc as WML.
    lazymatch type of MUc with munch ?Wc _ _ =>
      apply (rw_cells_transport s0segs Wc m m') in FR; [ | exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia ];
      lazymatch goal with H : u32arr s0segs m (S + 64012)%Z ?ws |- _ =>
        apply (u32arr_transport s0segs Wc m m') in H; [ | exact MUc | exact WMc | cbn [disjoint_from]; lia ] end end.
    clear LIMb BASb PRMb LENb ST MI MUc WMc.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl. wstepl.
    lazymatch goal with H : u32arr _ ?mm (S + 64012)%Z ?ws |- _ =>
      pose proof (u32arr_store_ok s0segs mm (S + 64012) ws t _ H ltac:(lia) eq_refl) as SO;
      wstepl; u32_store_done H t end.
    try clear SO.
    Ltac tabs_new t TU EQL EQB EQP AG ZLa ZBa ZPa LNl' LNb' LNp' Hmm Hlen :=
      cbn [dv_r r_lim r_base r_perm r_minl r_len];
      let t' := fresh "tq" in let Ht' := fresh "Htq" in
      intros t' Ht';
      destruct (Z.eq_dec t' t) as [->|?NE];
      [ eexists; eapply grp_tab_intro;
          [ exact Hmm | exact Hlen | reflexivity | reflexivity | reflexivity | exact ZLa | exact ZBa | exact ZPa
          | exact LNl' | exact LNb' | exact LNp' | exact AG | ];
        cbn [r_minl]; rewrite sv32_upd_same by lia; rewrite unsigned_lit by lia; apply swrap32_small; lia
      | let G := fresh "G" in let mn' := fresh "mn'" in
        destruct (TU t' ltac:(lia)) as [mn' G]; exists mn';
        eapply grp_tab_ext; [ | | | | exact G];
        [ intros; rewrite EQL; apply sv32_app_other; [lia | lia | lia]
        | intros; rewrite EQB; apply sv32_app_other; [lia | lia | lia]
        | intros; rewrite EQP; apply sv32_app_other; [lia | lia | lia]
        | apply sv32_upd_other; lia ] ].
    (* [comment removed for export] *)
    Ltac rejoin t A pre mid suf Ha Hb Hc NEWNAME LENNAME :=
      lazymatch type of Hb with
      | u32arr ?sg ?mm _ _ =>
          replace (A + 1032 * t)%Z with (A + 4 * Z.of_nat (length pre))%Z in Hb by lia;
          replace (A + 1032 * t + 1032)%Z with (A + 4 * Z.of_nat (length pre + length mid))%Z in Hc by lia;
          pose proof (u32arr_join3 sg mm A pre mid suf Ha Hb Hc) as NEWNAME; clear Ha Hb Hc;
          assert (LENNAME : Z.of_nat (length (pre ++ mid ++ suf)) = 1548%Z) by (rewrite !length_app; lia)
      | u8arr ?sg ?mm _ _ =>
          replace (A + 258 * t)%Z with (A + Z.of_nat (length pre))%Z in Hb by lia;
          replace (A + 258 * t + 258)%Z with (A + Z.of_nat (length pre + length mid))%Z in Hc by lia;
          pose proof (u8arr_join3 sg mm A pre mid suf Ha Hb Hc) as NEWNAME; clear Ha Hb Hc;
          assert (LENNAME : Z.of_nat (length (pre ++ mid ++ suf)) = 1548%Z) by (rewrite !length_app; lia)
      end.
    (* [comment removed for export] *)
    unfold S0_cut_L7D in NXD.
    revive_all_f MUL WML AOK.
    rejoin t (S + 45436)%Z preL lws' sufL LIMa ARL' LIMc DRlimN LlimN.
    rejoin t (S + 51628)%Z preB bws' sufB BASa ARB' BASc DRbasN LbasN.
    rejoin t (S + 57820)%Z preP pws' sufP PRMa ARP' PRMc DRprmN LprmN.
    rejoin t (S + 43888)%Z preN lbs sufN LENa AR8' LENc DRlenN LlenN.
    dr_close.
    enter_cut NXD DP; [ ib_close IB | cbn; lia | cbn; lia | lia | lia | cbn [dv_r]; exact SOK | cbn; lia | lia
                     | cbn [dv_r r_len]; rewrite <- EQ8; exact LOK | ].
    tabs_new t TU EQL EQB EQP AG ZLa ZBa ZPa LNl' LNb' LNp' Hmm Hlen.
  Qed.
End R.


End ACeilS1.

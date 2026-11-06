(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasT BzLemmasT2 BzWalkArith BzWalkArith2 BzWalkArith3 BzWalkArith4 BzDU9 DecAux12F BzDU5 BzDUM BzDU11 BzDU12F BzDU12S DecAux12S BzDOKS DecTacF3 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet A0F_decRet3 DecTacSA A0F_decCutsA.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsA.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast FLiaA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecTac2.
Local Ltac AsanKit.a_norm ::= DecTac2.lit_store_fix.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0_glue10K.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0F_g10A.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDU2 BzDU10M DecCutF10 DecCutF10A.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU10M OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF10 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF10A.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsA.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section H.
  Variable A : act14.
  Hypothesis AOK : act_ok AIHI0 A.
  Variable Qd : dres -> machine_state -> Prop.
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Lemma A0F_g10_H14 : forall (hH : dsh) (nbu0 : Z) (cf0 : list word) (dH : dsm) (r0 : drest) (k : blk) (b0 : bzs) (til tih : word)
      (v : Z) (rest : list Z) (m : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w8 w16 : word)
      (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word),
    let jd := jd_of hH nbu0 cf0 dH r0 k in
    let Fh := (9 * length rest + 92)%nat in
    A0F_cut_H14 A Qd Fh ->
    (* [comment removed for export] *)
    (49 <= v <= 57)%Z -> b_n cx = (v - 48)%Z -> map bv_unsigned (a_payload A) = (66 :: 90 :: 104 :: v :: rest)%Z ->
    a_b0 A = bupd b0 (b_len cx - 4) til tih ->
    bs_S b0 = b_s cx -> bs_src b0 = b_src cx -> bs_len b0 = b_len cx -> bs_dst b0 = b_dst cx -> bs_dlen b0 = b_dlen cx -> bs_av b0 = b_dlen cx ->
    (* [comment removed for export] *)
    rw_cells a0segs m S (HEAD_CELLS hH) -> sh_strm hH = b_strm cx -> sh_state hH = 13%Z -> sh_bsLive hH = 0%Z ->
    sh_bsBuff hH = (((66 * 256 + 90) * 256 + 104) * 256 + v)%Z -> sh_n hH = (v - 48)%Z -> bv_unsigned (sh_small hH) = b_small cx ->
    sh_cbn hH = 0%Z -> sh_verb hH = 0%Z ->
    rw_cells a0segs m (S + 1092) [C4 (Z_to_bv 64 nbu0)] -> (0 <= nbu0)%Z ->
    u32arr a0segs m (S + 1096) cf0 -> length cf0 = 257%nat ->
    rw_cells a0segs m (S + 3152) (MID_CELLS dH) -> sm_tt dH = b_tt cx -> sm_ll16 dH = b_ll16 cx -> sm_ll4 dH = b_ll4 cx -> sm_cccrc dH = Z_to_bv 64 0 ->
    rw_cells a0segs m (S + 64036) (SAVE_CELLS (repeat (Z_to_bv 8 0) 44) 0 (repeat (Z_to_bv 8 0) 60)) ->
    drest_at a0segs m S r0 ->
    rw_cells a0segs m (b_strm cx) (STRM_CELLS (bupd b0 (b_len cx - 4) til tih)) ->
    blk_at a0segs m cx k ->
    bytes_at a0segs m (b_src cx) (a_payload A) ->
    ro_cells a0segs m 0xc06b8 [C8 (Z_to_bv 64 0xbf950); C8 (a_g1 A); C8 (Z_to_bv 64 0xbf958); C8 (Z_to_bv 64 0xc4000); C8 (Z_to_bv 64 0xc4500)] ->
    ro_cells a0segs m 0xbf950 [C8 (a_sv A)] ->
    u32arr a0segs m 0xc4500 rnums_words ->
    (* [comment removed for export] *)
    rw_cells a0segs m (a_P A) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (a_fb A + 32)); C8 (Z_to_bv 64 (S + 7884)); C8 (Z_to_bv 64 (S + 2124)); C8 (Z_to_bv 64 (S + 3192)); C8 (Z_to_bv 64 (S + 3152)); C8 (Z_to_bv 64 (S + 2047)); C8 (Z_to_bv 64 (S + 8)); C8 (Z_to_bv 64 (S + 3176)); C8 (Z_to_bv 64 (S + 7820))] ->
    rw_cells a0segs m (a_P A + 496) [C8 w496; C8 w504; C8 w512; C8 w520; C8 w528; C8 w536; C8 w544; C8 w552; C8 (Z_to_bv 64 (a_shs A)); C8 w568; C8 w576; C8 w584; C8 w592; C8 w600; C8 w608; C8 w616; C8 w624; C8 w632; C8 w640; C8 (Z_to_bv 64 0); C8 w656; C8 w664; C8 (Z_to_bv 64 (a_fb A)); C8 w680; C8 (Z_to_bv 64 (a_shs A + 1)); C8 w696; C8 w704; C8 w712; C8 w720] ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    evt a0segs (Qd (drun Fh 14 dsv_zero (d14 jd (b_small cx) v) (s14 rest (b_dlen cx))))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x9f54c) (a_fc A) None m (seg_rom a0segs)).
  Proof.
    intros until w720. cbv zeta.
    intros HCUT Hv Hn PZ Eb HbS Hsrc Hlen Hdst Hdlen AV0 HDx Hstrm Hst HbL HbB HnH Hsm Hcbn Hverb NBUx Rnbu CFx Lcf MIDx Ett El16 El4 Hcc SAVx DRx STRMx BLK PAYx GOT SEV RN
           FRL FRH AF ST MU WM MI.
    assert (Hv8 : (0 <= v < 256)%Z) by lia.
    assert (PL : Z.of_nat (length (a_payload A)) = b_len cx) by (cps_destruct AOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PL0 & _); exact PL0).
    assert (LL : Z.of_nat (length rest) = (b_len cx - 4)%Z).
    { pose proof (f_equal (@length Z) PZ) as X. rewrite length_map in X. cbn [length] in X. lia. }
    (* [comment removed for export] *)
    cps_pose (d14_fields (jd_of hH nbu0 cf0 dH r0 k) (b_small cx) v Hv8) as
      (Fst & FbL & FbB & Fn & Fsm & Fsv & Fbn & Fvb & Fcc & Ftal & Flal & Foc & Fol & Frd & Frn & Frt & Fop & Ftp & Fk0 & Fuz & Fnu & Frest).
    assert (RAW : dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m
                    (dvF cx (jk_of hH (repeat (Z_to_bv 8 0) 44) (repeat (Z_to_bv 8 0) 60) b0 til tih)
                         ((fun jd => d14 jd (b_small cx) v) (jd_of hH nbu0 cf0 dH r0 k)) (s14 rest (b_dlen cx)))
                  /\ jk_wf (jk_of hH (repeat (Z_to_bv 8 0) 44) (repeat (Z_to_bv 8 0) 60) b0 til tih)
                  /\ jk_static b0 (jk_of hH (repeat (Z_to_bv 8 0) 44) (repeat (Z_to_bv 8 0) 60) b0 til tih)
                  /\ drep ((fun jd => d14 jd (b_small cx) v) (jd_of hH nbu0 cf0 dH r0 k))).
    { eapply (raw_dvFA DI_A0 (fun jd => d14 jd (b_small cx) v) cx (a_g1 A) (a_sv A) (a_payload A) m hH nbu0 cf0 dH
                (repeat (Z_to_bv 8 0) 44) 0 (repeat (Z_to_bv 8 0) 60) r0 b0 (b_len cx - 4) til tih k (s14 rest (b_dlen cx)));
        cbv beta; try (cbn [di_got di_stderrp di_crc di_rnums di_segs DI_A0]).
      - apply junk_kept_d14. exact Hv8.
      - exact HDx.
      - exact NBUx.
      - exact CFx.
      - exact Lcf.
      - exact MIDx.
      - exact SAVx.
      - exact DRx.
      - exact STRMx.
      - exact BLK.
      - exact PAYx.
      - exact GOT.
      - exact SEV.
      - exact RN.
      - exact Hstrm.
      - rewrite Fst. symmetry. exact Hst.
      - rewrite FbB. symmetry. exact HbB.
      - rewrite FbL. symmetry. exact HbL.
      - rewrite Fn, HnH. reflexivity.
      - rewrite Fsm. symmetry. exact Hsm.
      - rewrite Fbn. symmetry. exact Hcbn.
      - rewrite Fvb. symmetry. exact Hverb.
      - rewrite Fcc, Hcc. reflexivity.
      - rewrite Fsv. reflexivity.
      - exact Ett.
      - exact El16.
      - exact El4.
      - exact HbS.
      - exact Hsrc.
      - exact Hlen.
      - exact Hdst.
      - exact Hdlen.
      - cbn [s_avail_out s14]. exact AV0.
      - cbn [s_in s14]. lia. }
    cbv beta in RAW. cps_destruct RAW as (DM & JW & JS & DRP).
    assert (NBU0 : d_nused (jd_of hH nbu0 cf0 dH r0 k) = nbu0) by reflexivity.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply (HCUT dsv_zero (d14 (jd_of hH nbu0 cf0 dH r0 k) (b_small cx) v) (s14 rest (b_dlen cx))
                              (jk_of hH (repeat (Z_to_bv 8 0) 44) (repeat (Z_to_bv 8 0) 60) b0 til tih)) ].
    - st_eq.
    - exact DM.
    - exact FRL.
    - exact FRH.
    - exact AF.
    - exact ST.
    - exact MU.
    - exact WM.
    - exact MI.
    - unfold dpureF. rewrite Fn, Fsm, Fvb, FbB, FbL, Fbn, Fsv, Fnu, NBU0. cbn [s_avail_out s_in s14 sv_nblock dsv_zero].
      split; [exact JW|].
      split. { clear - JS Eb. rewrite Eb. unfold jk_static, bupd in *. destruct b0; cbn in *. exact JS. }
      split; [symmetry; exact Hn|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [rewrite Eb; unfold bupd; cbn [bs_av]; symmetry; exact AV0|].
      split; [rewrite Eb; unfold bupd; cbn [bs_ai]; lia|].
      split. { exists 4%nat. replace rest with (skipn 4 (map bv_unsigned (a_payload A))) by (rewrite PZ; reflexivity). rewrite skipn_map. reflexivity. }
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [rewrite Eb; unfold bupd; cbn [bs_len]; rewrite Hlen; lia|].
      split; [lia|]. split; [lia|]. exact DRP.
    - unfold dinv_H14, nb_ok. cbn [sv_nblock dsv_zero]. lia.
    - unfold fuel_ok. rewrite FbL. cbn [s_in s14]. lia.
  Qed.
End H.
End ACeilS1.

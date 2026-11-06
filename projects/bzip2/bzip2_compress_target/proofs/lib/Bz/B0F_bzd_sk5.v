(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0 StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables BzLemmasT BzLemmasMtf BzContracts BzWalkArith DecCut S0_bzd_out S0_bzd_loop1 BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDFrame DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDFrame OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_out S0F_bzd_outS S0F_bzd_loop1.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac2 AsanKit AsanCut AsanCutB0 AsanKitB0 DecCutB DecCutFB B0F_decV B0F_bzdV B0F_bzd_uV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0F_bzd_skV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_loop3s.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_loop5.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require B0F_bzd_sk1 B0F_bzd_sk2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA SasFastF RelLiaS.
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac tlia ::= RelLiaS.tlia_bzd_r.
Local Ltac BzSepTac.tlia1 ::= RelLiaS.tlia1_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold; AsanKit.sh_norm.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section BZD.
  Variable z : bzdctx.
  Variable SHS : Z.
  Variable Q : machine_state -> Prop.
  Hypothesis ZOK : bzdctx_okA z SHS.
  Notation cx := (z_cx z).
  Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)).
  Notation usp := (bv_unsigned (z_sp z)). Notation uspi := (bv_unsigned (z_spi z)). Notation lo := (z_lo z).
  Notation FSAVA := (B0F_bzd_skV.FSAVA z).

  (* [comment removed for export] *)
  Ltac zok :=
    let Z' := fresh "ZOK" in pose proof ZOK as Z';
    cps_destruct Z' as (((LS1 & LS2) & (LM1 & LM2) & (LR1 & LR2 & LR3) & (LD1 & LD2) & LDL & (AL1 & AL2) & LSM & LN & (LO1 & LO2 & LO3) & SPI & SPI2 & PAYL & (LOI & LSI & ALTT & AL16))
                        & ANS & (D_SM & D_SR & D_SD & D_MR & D_MD & D_RD & IA_S & IA_M & IA_D) & BTT & B16 & B4 & B164);
    unfold disj, bzd_img_apart in *; pose proof alloc_ceiling_range as ACR;
    pose proof (word_urange (z_sp z)) as USPR; pose proof (word_urange (z_spi z)) as USPIR;
    lazymatch goal with HA : sanchor _ _ |- _ => pose proof (proj2 HA : saddr S SHS) as ANS0 end.

  (* [comment removed for export] *)
  Lemma B0_bzd_Lraw : forall (W : list ivl) (m0 : word -> option byte)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s9 t3 t4 t5 t6 w0 w8 w40 w48 w56 w64 w72 w88 w224 w232 : word)
      (m : word -> option byte) (h : dsh) (rv : Z),
    rw_cells b0segs m S (HEAD_CELLS h) -> (0 <= sh_state h < 2^31)%Z -> sh_state h <> 2%Z ->
    (-5 <= rv <= 4)%Z -> rv <> 4%Z ->
    rw_cells b0segs m uspi (bzd_slots S SHS w0 w8 w40 w48 w56 w64 w72 w88 w224 w232) ->
    rw_cells b0segs m (uspi + 264) FSAVA -> stk b0segs m lo uspi ->
    shzW b0segs W m0 S (S + 64144) -> munch W m0 m ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       stk b0segs m lo usp ->
       evt b0segs Q (MS (mkR (z_ra z) (z_sp z) (z_gp z) (z_tp z) t0' t1' t2' (z_s0 z) (z_s1 z) (Z_to_bv 64 rv) a1' a2' a3' a4' a5' a6' a7'
                             (z_s2 z) (z_s3 z) (z_s4 z) (z_s5 z) (z_s6 z) (z_s7 z) (z_s8 z) (z_s9 z) (z_s10 z) (z_s11 z) t3' t4' t5' t6')
                        (z_F z) (ret_pc (z_ra z)) (z_fc z) None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (ZRA z SHS ra t0 t1 t2 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s9 t3 t4 t5 t6)
                     (z_F z) (Z_to_bv 64 0x840b8) (z_fc z) None m (seg_rom b0segs)).
  Proof.
    intros until rv. intros HD Rst NEst Rrv NErv FR FS ST SHs MU K.
    zok. clear D_SM D_SR D_SD D_MR D_MD D_RD IA_S IA_M IA_D BTT B16 B4 B164. hide_disj.
    change (2^31)%Z with 2147483648%Z in Rst.
    unfold B0F_bzd_skV.ZRA. unfold bzd_slots in FR. unfold B0F_bzd_skV.FSAVA in FS.
    (* [comment removed for export] *)
    wstep. wstep. wstep. rewrite (S0F_bzd_loop5.beq_rv4 rv Rrv). destruct (Z.eqb_spec rv 4) as [Erv|_]; [exfalso; exact (NErv Erv)|]. cbn [negb].
    (* [comment removed for export] *)
    brun_to 0x8798c%Z. try rewrite (sx32_of_Z (sh_state h)) by lia.
    (* [comment removed for export] *)
    wstep. wstep. if_cases Ks; zify_cond Ks.
    2:{ exfalso. apply NEst. clear -Ks Rst. lia. }
    clear Ks.
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    wstep.
    release_frame FR ST (uspi + 264)%Z.
    release_frame FS ST (bv_unsigned (z_sp z)).
    (* [comment removed for export] *)
    wstep. rewrite SPI2.
    eapply K; eassumption.
  Time Qed.
End BZD.
End ACeilS1.

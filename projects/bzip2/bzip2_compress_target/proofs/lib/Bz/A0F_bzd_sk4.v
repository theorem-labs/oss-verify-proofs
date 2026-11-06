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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables BzLemmasT BzLemmasMtf BzContracts BzWalkArith DecCut S0_bzd_out S0_bzd_loop1 BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDFrame DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDFrame OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_out S0F_bzd_outS S0F_bzd_loop1.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit DecCutA DecCutFA A0F_decV A0F_bzdV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit DecTac2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0F_bzd_skV.
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
Local Ltac AsanKit.a_norm ::= DecTac2.lit_store_fix; AsanKit.sh_fold; AsanKit.sh_norm.
Ltac split_at_cb8 cs :=
  lazymatch cs with
  | CB 8 ?bs :: ?post => constr:((@nil cell, bs, post))
  | ?c :: ?rest => let r := split_at_cb8 rest in lazymatch r with (?pre, ?bs, ?post) => constr:((c :: pre, bs, post)) end
  end.
Ltac cb8_all H :=
  repeat (lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
            let r := split_at_cb8 cs in
            lazymatch r with (?pre, ?bs, ?post) => apply (CmpHmKit.rw_cells_CB8_C8 segs m A pre bs post) in H; cbn [app] in H end end).

Lemma land7_al : forall X k, (X mod 8 = 0)%Z -> (0 <= X)%Z -> (0 <= k)%Z -> Z.land (X + k) 7 = (k mod 8)%Z.
Proof.
  intros X k HX H0 Hk. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z.
  rewrite Z.add_mod by lia. rewrite HX. rewrite Z.add_0_l. apply Z.mod_mod. lia.
Qed.

Section ACeilS1. Context {ACEIL__ : ACeil}.

Section BZD.
  Variable z : bzdctx.
  Variable SHS : Z.
  Variable Q : machine_state -> Prop.
  Hypothesis ZOK : bzdctx_okA z SHS.
  Notation cx := (z_cx z).
  Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)).
  Notation usp := (bv_unsigned (z_sp z)). Notation uspi := (bv_unsigned (z_spi z)). Notation lo := (z_lo z).
  Notation FSAVA := (A0F_bzd_skV.FSAVA z).

  (* [comment removed for export] *)
  Ltac zok :=
    let Z' := fresh "ZOK" in pose proof ZOK as Z';
    cps_destruct Z' as (((LS1 & LS2) & (LM1 & LM2) & (LR1 & LR2 & LR3) & (LD1 & LD2) & LDL & (AL1 & AL2) & LSM & LN & (LO1 & LO2 & LO3) & SPI & SPI2 & PAYL)
                        & ANS & (D_SM & D_SR & D_SD & D_MR & D_MD & D_RD & IA_S & IA_M & IA_D) & BTT & B16 & B4 & B164);
    unfold disj, bzd_img_apart in *; pose proof alloc_ceiling_range as ACR;
    pose proof (word_urange (z_sp z)) as USPR; pose proof (word_urange (z_spi z)) as USPIR;
    lazymatch goal with HA : sanchor _ _ |- _ => pose proof (proj2 HA : saddr S SHS) as ANS0 end.

  Definition WEA : list ivl := [(uspi, uspi + 400)]%Z.

  Lemma A0_bzd_entry : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (h : dsh) (b : bzs),
    rw_cells a0segs m S (HEAD_CELLS h) -> sh_strm h = STRM -> sh_state h = 10%Z ->
    rw_cells a0segs m STRM (STRM_CELLS b) -> bs_S b = S ->
    aconsts A0C m -> stk a0segs m lo usp -> mem_inv a0segs m ->
    shzW a0segs WEA m S (S + 64144) -> shzW a0segs WEA m STRM (STRM + 80) ->
    (forall (m' : word -> option byte) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 w0 w32 w104 w112 w120 w184 w192 w200 w208 w240 w248 : word),
       rw_cells a0segs m' S (HEAD_CELLS h) -> rw_cells a0segs m' STRM (STRM_CELLS b) -> aconsts A0C m' ->
       rw_cells a0segs m' uspi (bzd_slots S SHS w0 w32 w104 w112 w120 w184 w192 w200 w208 w240 w248) ->
       rw_cells a0segs m' (uspi + 296) FSAVA -> stk a0segs m' lo uspi ->
       mem_inv a0segs m' -> munch WEA m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (ZRA z SHS (Z_to_bv 64 0x87038) y5 y6 y7 (Z_to_bv 64 S) y11 y12 y13 y14 y15 y16 y17 (z_s4 z) (Z_to_bv 64 (-2)) y28 y29 y30 y31)
                        (z_F z) (Z_to_bv 64 0x9e368) (z_fc z) None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (z_ra z) (z_sp z) (z_gp z) (z_tp z) t0 t1 t2 (z_s0 z) (z_s1 z) (Z_to_bv 64 STRM) a1 a2 a3 a4 a5 a6 a7
                          (z_s2 z) (z_s3 z) (z_s4 z) (z_s5 z) (z_s6 z) (z_s7 z) (z_s8 z) (z_s9 z) (z_s10 z) (z_s11 z) t3 t4 t5 t6)
                     (z_F z) (Z_to_bv 64 0x84294) (z_fc z) None m (seg_rom a0segs)).
  Proof.
    intros until b. intros HD Hstrm H10 SM HbS AC ST MI SHs SHt K.
    zok. clear D_SR D_SD D_MR D_MD D_RD IA_D BTT B16 B4 B164. hide_disj.
    destruct AC as [GOTS SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar A0C ci_segs] in GOTS, SBV.
    rewrite Hstrm, H10 in HD. rewrite HbS in SM.
    pose proof (munch_refl WEA m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold WEA in MU, SHs, SHt.
    assert (ESP : Z_to_bv 64 (usp + -400) = z_spi z) by (transitivity (Z_to_bv 64 uspi); [f_equal; clear -SPI; lia| apply Z_to_bv_bv_unsigned]).
    carve_frame 400%nat ST.
    apply (rw_cells_split_CB a0segs _ _ [] 400 _ []
             [8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    replace (usp + -400)%Z with uspi in FR, ST by (clear -SPI; lia).
    (* [comment removed for export] *)
    wstep. rewrite ESP.
    (* [comment removed for export] *)
    do 13 wstep. wstep.
    wstep. if_cases KZ; zify_cond KZ; [exfalso; clear -KZ LM1 LM2 ACR; lia|]. clear KZ.
    (* [comment removed for export] *)
    arun_to 0x84300%Z.
    wstep. if_cases KS; zify_cond KS; [exfalso; clear -KS LS1 LS2 ACR; lia|]. clear KS.
    (* [comment removed for export] *)
    arun_to 0x8431c%Z.
    wstep. if_cases KE; zify_cond KE; [| exfalso; apply KE; reflexivity]. clear KE.
    (* [comment removed for export] *)
    assert (AL8 : (S mod 8 = 0)%Z) by (clear -AL1; lia). assert (S0' : (0 <= S)%Z) by (clear -LS1; lia).
    arun_to 0x843e0%Z. rewrite (land7_al S 8 AL8 S0' ltac:(lia)). change (8 mod 8)%Z with 0%Z.
    arun_to 0x84424%Z. rewrite (land7_al S 44 AL8 S0' ltac:(lia)). change (44 mod 8)%Z with 4%Z.
    arun_to 0x84430%Z. rewrite (land7_al S 20 AL8 S0' ltac:(lia)). change (20 mod 8)%Z with 4%Z.
    (* [comment removed for export] *)
    arun_to 0x87034%Z.
    (* [comment removed for export] *)
    wstep.
    cb8_all FR.
    lazymatch type of FR with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13; ?c14; ?c15; ?c16; ?c17; ?c18; ?c19;
                                               ?c20; ?c21; ?c22; ?c23; ?c24; ?c25; ?c26; ?c27; ?c28; ?c29; ?c30; ?c31; ?c32; ?c33; ?c34; ?c35; ?c36;
                                               ?d0; ?d1; ?d2; ?d3; ?d4; ?d5; ?d6; ?d7; ?d8; ?d9; ?d10; ?d11; ?d12] =>
      apply (proj1 (DecTac2.rw_cells_app_iff a0segs _ uspi
               [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19;
                c20; c21; c22; c23; c24; c25; c26; c27; c28; c29; c30; c31; c32; c33; c34; c35; c36]
               [d0; d1; d2; d3; d4; d5; d6; d7; d8; d9; d10; d11; d12])) in FR end.
    destruct FR as [FRS FSV]. cbn [cells_size csize Nat.add] in FSV. change (Z.of_nat 296) with 296%Z in FSV.
    rewrite <- Hstrm in HD. rewrite <- H10 in HD. rewrite <- HbS in SM.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ unfold A0F_bzd_skV.ZRA; st_eq
      | exact HD | exact SM
      | split; cbn [aci_segs aci_c aci_got_sh aci_shvar A0C ci_segs]; assumption
      | unfold bzd_slots; exact FRS
      | unfold A0F_bzd_skV.FSAVA; exact FSV
      | exact ST | exact MI | unfold WEA; exact MU | exact WM ].
  Time Qed.
End BZD.
End ACeilS1.

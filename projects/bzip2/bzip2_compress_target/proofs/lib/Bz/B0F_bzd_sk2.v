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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require B0F_bzd_sk1.
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
  Variable SHS : Z. Variable w0 : word.
  Variable QF : Z * dst * dstrm -> machine_state -> Prop.
  Hypothesis ZOK : bzdctx_okA z SHS.
  Notation cx := (z_cx z).
  Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)). Notation SRC := (b_src (z_cx z)). Notation len := (b_len (z_cx z)).
  Notation DST := (b_dst (z_cx z)). Notation dlen := (b_dlen (z_cx z)). Notation n := (b_n (z_cx z)).
  Notation TT := (b_tt (z_cx z)). Notation L16 := (b_ll16 (z_cx z)). Notation L4 := (b_ll4 (z_cx z)).
  Notation usp := (bv_unsigned (z_sp z)). Notation uspi := (bv_unsigned (z_spi z)). Notation lo := (z_lo z).
  Notation KRet := (B0_KRet z QF). Notation KCall := (B0_KCall z SHS w0 QF).
  Notation FCHA := (B0F_bzd_skV.FCHA z SHS w0). Notation FIMGA := B0F_bzd_skV.FIMGA. Notation FDESTA := (B0F_bzd_skV.FDESTA z).
  Notation WLA := (B0F_bzd_skV.WLA z). Notation WLF := (B0F_bzd_skV.WLF z). Notation FSAVA := (B0F_bzd_skV.FSAVA z).
  Notation fmkcA := (B0F_bzd_skV.fmkcA z QF).

  (* [comment removed for export] *)
  Ltac hide H := lazymatch type of H with ?T => change T with (id T) in H end.
  Ltac splits := lazymatch goal with |- _ /\ _ => split; splits | |- _ => idtac end.
  Ltac ofmkc := cbn [o_cx o_J o_d o_s o_g1 o_s1v o_SP o_gp o_tp o_F o_fc o_KQ o_m0 B0F_bzd_skV.fmkcA] in *.
  (* [comment removed for export] *)
  Ltac zok :=
    let Z' := fresh "ZOK" in pose proof ZOK as Z';
    cps_destruct Z' as (((LS1 & LS2) & (LM1 & LM2) & (LR1 & LR2 & LR3) & (LD1 & LD2) & LDL & (AL1 & AL2) & LSM & LN & (LO1 & LO2 & LO3) & SPI & SPI2 & PAYL & (LOI & LSI & ALTT & AL16))
                        & ANS & (D_SM & D_SR & D_SD & D_MR & D_MD & D_RD & IA_S & IA_M & IA_D) & BTT & B16 & B4 & B164);
    unfold disj, bzd_img_apart in *; pose proof alloc_ceiling_range as ACR;
    pose proof (word_urange (z_sp z)) as USPR; pose proof (word_urange (z_spi z)) as USPIR;
    pose proof crc_words_length as CWL; pose proof rnums_words_length as RNL;
    lazymatch goal with HA : sanchor _ _ |- _ => pose proof (proj2 HA : saddr S SHS) as ANS0 end.
  Hypothesis SHL : bzd_sh z WLA (z_m0 z).
  Let bzd_fepiA := B0F_bzd_sk1.bzd_fepiA z SHS w0 QF ZOK.

  (* [comment removed for export] *)
  Ltac cl := cbn [disjoint_from]; unfold B0F_bzd_skV.FSAVA; simpl_sizes; repeat split; try exact I; lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma blockend_transport : forall (mm m' : word -> option byte) (dbytes : list byte) (rr : drest) (k : blk) (cf : list word) (cs : list cell) (g1 sv : word),
    munch ([(S + 8, S + 12); (S + 3184, S + 3192)])%Z mm m' -> wmono b0segs mm m' ->
    (forall A n0, blk_range cx A n0 -> (0 < A /\ A + n0 <= alloc_ceiling)%Z /\ disj S 64144 A n0) ->
    bytes_at b0segs mm SRC (z_payload z) -> u8arr b0segs mm DST dbytes -> Z.of_nat (length dbytes) = dlen ->
    u32arr b0segs mm 857056 crc_words -> u32arr b0segs mm 858432 rnums_words ->
    ro_cells b0segs mm 842392 [C8 (Z_to_bv 64 838960); C8 g1; C8 (Z_to_bv 64 838968); C8 (Z_to_bv 64 857056); C8 (Z_to_bv 64 858432)] -> ro_cells b0segs mm 838960 [C8 sv] ->
    rw_cells b0segs mm (uspi + 264) FSAVA -> u32arr b0segs mm (S + 1096) cf -> length cf = 257%nat ->
    drest_at b0segs mm S rr -> blk_at b0segs mm cx k -> rw_cells b0segs mm STRM cs -> cells_size cs = 80%nat -> aconsts B0C mm ->
    aconsts B0C m' /\ bytes_at b0segs m' SRC (z_payload z) /\ u8arr b0segs m' DST dbytes /\
    u32arr b0segs m' 857056 crc_words /\ u32arr b0segs m' 858432 rnums_words /\
    ro_cells b0segs m' 842392 [C8 (Z_to_bv 64 838960); C8 g1; C8 (Z_to_bv 64 838968); C8 (Z_to_bv 64 857056); C8 (Z_to_bv 64 858432)] /\ ro_cells b0segs m' 838960 [C8 sv] /\
    rw_cells b0segs m' (uspi + 264) FSAVA /\ u32arr b0segs m' (S + 1096) cf /\
    drest_at b0segs m' S rr /\ blk_at b0segs m' cx k /\ rw_cells b0segs m' STRM cs.
  Proof.
    intros until sv. intros MU2 WM2 BLKS PAY DSTA DL CRC RNA GOT SV FS CF CFL DR BLK SM SML AC. zok.
    splits.
    - destruct AC as [A1 A2]. unfold aconsts in *. cbn [aci_segs aci_got_sh aci_shvar aci_c CmpCut.ci_segs B0C] in A1, A2 |- *.
      split; (eapply ro_cells_transport; [eassumption| exact MU2|]); clear -IA_S LS1 LS2; cl.
    - eapply bytes_at_transport; [exact PAY| exact MU2|]. rewrite PAYL. clear -D_SR LS1 LS2 LR1 LR2 LR3. cl.
    - eapply u8arr_transport; [exact DSTA| exact MU2| exact WM2|]. rewrite DL. clear -D_SD LS1 LS2 LD1 LD2 LDL. cl.
    - eapply u32arr_transport; [exact CRC| exact MU2| exact WM2|]. rewrite CWL. clear -IA_S LS1 LS2. cl.
    - eapply u32arr_transport; [exact RNA| exact MU2| exact WM2|]. rewrite RNL. clear -IA_S LS1 LS2. cl.
    - eapply ro_cells_transport; [exact GOT| exact MU2|]. clear -IA_S LS1 LS2. cl.
    - eapply ro_cells_transport; [exact SV| exact MU2|]. clear -IA_S LS1 LS2. cl.
    - eapply rw_cells_transport; [exact FS| exact MU2| exact WM2|]. clear -LS1 LS2 LO1 LO2 LO3 SPI ACR. cl.
    - eapply u32arr_transport; [exact CF| exact MU2| exact WM2|]. rewrite CFL. clear -LS1 LS2. cl.
    - eapply drest_transport; [exact DR| exact MU2| exact WM2| | |]; clear -LS1 LS2; cl.
    - eapply blk_at_transport; [exact BLK| exact MU2| exact WM2|].
      intros A n0 HR. destruct (BLKS A n0 HR) as [RA DA]. unfold disj in DA. clear -RA DA LS1 LS2. cl.
    - eapply rw_cells_transport; [exact SM| exact MU2| exact WM2|]. rewrite SML. clear -D_SM LS1 LS2 LM1 LM2. cl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bzd_joinA : forall f (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s9 t3 t4 t5 t6 w8 w40 w48 w56 w64 w72 w88 : word)
      (m : word -> option byte) (J : jk) (d : dst) (s : dstrm)
      (oc ol nu k0 tp rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (dbytes rest : list byte),
    let J' := jk_set_o J tol toh in let d' := set8 d oc ol nu k0 tp rn rt cb in let s' := smod s out av tout in
    KRet WLA -> KCall WLA f ->
    FCHA m J' d' s' dbytes rest w8 w40 w48 w56 w64 w72 w88 (Z_to_bv 64 (SHS + -2147450744)) (Z_to_bv 64 (SHS + -2147442870)) ->
    munch WLA (z_m0 z) m -> wmono b0segs (z_m0 z) m -> mem_inv b0segs m ->
    dpureF cx (bs_of cx J s) (z_payload z) J d s ->
    (forall A k, blk_range cx A k -> (0 < A /\ A + k <= alloc_ceiling)%Z /\ disj S 64144 A k) ->
    (0 <= d_cccrc d < 4294967296)%Z -> (0 <= d_sbcrc d < 4294967296)%Z -> (len / 6 - d_blockNo d <= Z.of_nat f)%Z ->
    (0 <= nu <= sv_nblock (d_sv d) + 2)%Z -> (0 <= cb < 4294967296)%Z -> (0 <= ol <= 260)%Z -> (0 <= av <= dlen)%Z ->
    evt b0segs (QF (K_J f d' s'))
        (MS (mkR ra (z_spi z) (z_gp z) (z_tp z) t0 t1 t2 (Z_to_bv 64 SHS) (Z_to_bv 64 (S + 1096)) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 S) s3 (Z_to_bv 64 (S + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 (SHS + -2147450878)) (Z_to_bv 64 (S + 3184))
                 s9 (Z_to_bv 64 (S + 12)) (Z_to_bv 64 (SHS + 398)) t3 t4 t5 t6)
            (z_F z) (Z_to_bv 64 0x87840) (z_fc z) None m (seg_rom b0segs)).
  Proof.
    intros until rest. intros J' d' s'. intros KR KC CH MU WM MI DP BLKS Hcc Hsb BND Rnu Rcb Rol Rav.
    cps_destruct CH as (DM & CRC & DE & FR & FS & ST & AC). pose proof DE as DE'. cps_destruct DE' as (DSTA & DL & Edb & Lout).
    pose proof DM as DM'. unfold DecCutB.dmem in DM'. cps_destruct DM' as (HD & NBU & CF & MID & SAV & DR & SM & BLK & PAY & GOT & SV & RNA).
    b0img. unfold B0F_bzd_skV.FIMGA in CRC.
    (* [comment removed for export] *)
    dvF_cbn_in DR. unfold r_of in DR. subst d'. focbn_in DR. dmodel_cbn_in DR.
    dvF_cbn_in BLK. unfold blk_of in BLK. focbn_in BLK. dmodel_cbn_in BLK.
    set (d' := set8 d oc ol nu k0 tp rn rt cb) in *.
    pose proof (dpureF_verb _ _ _ _ _ _ DP) as Everb. pose proof (dpureF_snb _ _ _ _ _ _ DP) as Rsnb.
    pose proof (dpureF_set8 z J d s oc ol nu k0 tp rn rt cb out av tout tol toh DP ltac:(lia)) as DP'. cbv zeta in DP'.
    fold J' d' s' in DP'.
    unfold K_J.
    assert (Esnb : sv_nblock (d_sv d') = sv_nblock (d_sv d)) by reflexivity.
    assert (Enu : d_nused d' = nu) by reflexivity. assert (Eol : d_out_len d' = ol) by reflexivity.
    assert (Ecb : d_cbcrc d' = cb) by reflexivity. assert (Esb : forall v, d_sbcrc (d_set_cbcrc d' v) = d_sbcrc d) by reflexivity.
    assert (Ecc : forall v, d_cccrc (d_set_cbcrc d' v) = d_cccrc d) by reflexivity.
    rewrite Esnb, Enu, Eol, Ecb, Esb, Ecc.
    zok. cps_destruct SHL as (SHs & SHt & SHd & SHc & SHr & _ & _). unfold B0F_bzd_skV.WLA in MU, SHs, SHt, SHd, SHc, SHr.
    hide_disj.
    subst J' d' s'. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. rewrite Everb in HD. unfold bzd_slots in FR.
    (* [comment removed for export] *)
    hide PAY. hide DSTA. hide CRC. hide RNA. hide GOT. hide SV. hide FS. hide CF. hide DR. hide BLK. hide SM. hide AC.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl ([(S + 8, S + 12); (S + 3184, S + 3192)])%Z mm) as MU2; pose proof (wmono_refl b0segs mm) as WM2 end.
    (* [comment removed for export] *)
    brun_to 0x87858%Z. try rewrite (sx32_of_Z (sv_nblock (d_sv d))) by (clear -Rsnb; lia).
    (* [comment removed for export] *)
    brun_to 0x8787c%Z. try rewrite (sx32_of_Z nu) by (clear -Rnu Rsnb; lia).
    (* [comment removed for export] *)
    wstep. if_cases K1; zify_cond K1.
    { abstract (replace (nu =? sv_nblock (d_sv d) + 1) with false by (symmetry; apply Z.eqb_neq; clear -K1 Rnu Rsnb; lia); cbn [andb];
      wstep; wstep;
      eapply (bzd_fepiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BZ_OK _ _ _ dbytes rest KR);
        [unfold bzd_slots; exact FR| exact FS| exact ST| unfold B0F_bzd_skV.WLA; exact MU| exact WM| exact MI| exact DM| exact CRC| exact DE| exact DP'| unfold BZ_OK; lia]). }
    replace (nu =? sv_nblock (d_sv d) + 1) with true by (symmetry; apply Z.eqb_eq; clear -K1 Rnu Rsnb; lia). cbn [andb].
    (* [comment removed for export] *)
    brun_to 0x87890%Z. try rewrite (sx32_of_Z ol) by (clear -Rol; lia).
    wstep. wstep. if_cases K2; zify_cond K2.
    { replace (ol =? 0) with false by (symmetry; apply Z.eqb_neq; clear -K2 Rol; lia).
      wstep. wstep.
      eapply (bzd_fepiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BZ_OK _ _ _ dbytes rest KR);
        [unfold bzd_slots; exact FR| exact FS| exact ST| unfold B0F_bzd_skV.WLA; exact MU| exact WM| exact MI| exact DM| exact CRC| exact DE| exact DP'| unfold BZ_OK; lia]. }
    replace (ol =? 0) with true by (symmetry; apply Z.eqb_eq; clear -K2 Rol; lia). cbv zeta.
    clear DM.
    remember (crc_final cb) as crc' eqn:Ecrc. pose proof (crc_final_range cb ltac:(clear -Rcb; lia)) as Rcrc. rewrite <- Ecrc in Rcrc.
    (* [comment removed for export] *)
    brun_to 0x878ac%Z. wstep.
    (* [comment removed for export] *)
    lazymatch goal with MID : rw_cells _ _ (S + 3152)%Z ?cs |- _ =>
      lazymatch cs with [?c0; ?c1; ?c2; ?c3; ?c4; C4 ?w; ?c6; ?c7] =>
        apply (C4_recell b0segs _ (S + 3152)%Z [c0; c1; c2; c3; c4] w crc' [c6; c7]) in MID; [cbn [app] in MID| rewrite low32_lit, Ecrc; apply not_crc_final; clear -Rcb; lia] end end.
    (* [comment removed for export] *)
    brun_to 0x878c0%Z. try rewrite (sx32_of_Z 0) by lia.
    (* [comment removed for export] *)
    brun_to 0x8791c%Z.
    (* [comment removed for export] *)
    Ltac unhide_all MU2 WM2 PAY DSTA DL CRC RNA GOT SV FS CF DR BLK SM BLKS AC :=
      unfold id in PAY, DSTA, CRC, RNA, GOT, SV, FS, CF, DR, BLK, SM, AC;
      let X := fresh "X" in
      pose proof (blockend_transport _ _ _ _ _ _ _ _ _ MU2 WM2 BLKS PAY DSTA DL CRC RNA GOT SV FS CF (zw32_length_nat _ _) DR BLK SM eq_refl AC) as X;
      clear PAY DSTA CRC RNA GOT SV FS CF DR BLK SM AC;
      cps_destruct X as (AC & PAY & DSTA & CRC & RNA & GOT & SV & FS & CF & DR & BLK & SM).
    (* [comment removed for export] *)
    wstep. if_cases K5; zify_cond K5.
    { (* [comment removed for export] *)
      assert (NE : crc' <> d_sbcrc d) by (intros E; apply K5; rewrite E; reflexivity).
      replace (crc' =? d_sbcrc d) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [negb]. clear K5 NE.
      wstep. wstep. unhide_all MU2 WM2 PAY DSTA DL CRC RNA GOT SV FS CF DR BLK SM BLKS AC.
      eapply (bzd_fepiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BZ_DATA_ERROR _ _ _ dbytes rest KR);
        [unfold bzd_slots; exact FR| exact FS| exact ST| unfold B0F_bzd_skV.WLA; exact MU| exact WM| exact MI| | exact CRC| | apply S0F_bzd_loop3s.S0F_bzd_loop3.dpureF_setcb; exact DP'| unfold BZ_DATA_ERROR; lia].
      - (* [comment removed for export] *)
        eapply dmemF_intro; b0img; focbn;
          [ abstract (exact_cells HD)| abstract (exact_cells NBU)| abstract (exact CF)| abstract (exact_cells MID)| abstract (exact_cells SAV)
          | abstract (unfold r_of; focbn; dmodel_cbn; exact DR)
          | abstract (exact_cells SM)
          | abstract (unfold blk_of; focbn; dmodel_cbn; exact BLK)
          | abstract (exact PAY)| exact GOT| exact SV| exact RNA].
      - unfold B0F_bzd_skV.FDESTA. focbn. split; [exact DSTA| split; [exact DL| split; [exact Edb| exact Lout]]]. }
    assert (EQ : crc' = d_sbcrc d).
    { pose proof (sx32_mod32 crc' ltac:(clear -Rcrc; lia)) as X1. pose proof (sx32_mod32 (d_sbcrc d) ltac:(clear -Hsb; lia)) as X2. clear -K5 X1 X2. rewrite <- X1, <- X2. rewrite K5. reflexivity. }
    replace (crc' =? d_sbcrc d) with true by (symmetry; apply Z.eqb_eq; exact EQ). cbn [negb]. clear K5.
    remember (Z.lxor (Z.lor (d_cccrc d * 2) (d_cccrc d / 2147483648) mod 4294967296) crc') as cc eqn:Ecc2.
    assert (Rcc2 : (0 <= cc < 4294967296)%Z).
    { subst cc. pose proof (Z.mod_pos_bound (Z.lor (d_cccrc d * 2) (d_cccrc d / 2147483648)) 4294967296 ltac:(lia)).
      change 4294967296%Z with (2^32)%Z. apply lxor_lt_pow2; clear -H Rcrc; lia. }
    (* [comment removed for export] *)
    brun_to 0x8794c%Z. wstep.
    (* [comment removed for export] *)
    lazymatch goal with MID : rw_cells _ _ (S + 3152)%Z ?cs |- _ =>
      lazymatch cs with [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; C4 ?w; ?c7] =>
        apply (C4_recell b0segs _ (S + 3152)%Z [c0; c1; c2; c3; c4; c5] w cc [c7]) in MID; [cbn [app] in MID| rewrite low32_lit, (low32_small cc) by (clear -Rcc2; lia); rewrite Ecc2; apply S0F_bzd_loop3s.S0F_bzd_loop3.cccrc_step2; [clear -Hcc; lia| clear -Rcrc; lia]] end end.
    (* [comment removed for export] *)
    brun_to 0x87960%Z. wstep. wstep. wstep.
    unhide_all MU2 WM2 PAY DSTA DL CRC RNA GOT SV FS CF DR BLK SM BLKS AC. clear MU2 WM2.
    unfold B0_KCall in KC.
    eapply (KC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (jk_set_o J tol toh) _ (smod s out av tout) dbytes rest).
    - unfold B0F_bzd_skV.FCHA; split;
        [ eapply dmemF_intro; b0img; focbn;
          [ abstract (exact_cells HD)| abstract (exact_cells NBU)| abstract (exact CF)| abstract (exact_cells MID)| abstract (exact_cells SAV)
          | abstract (unfold r_of; focbn; dmodel_cbn; exact DR)
          | abstract (exact_cells SM)
          | abstract (unfold blk_of; focbn; dmodel_cbn; exact BLK)
          | abstract (exact PAY)| exact GOT| exact SV| exact RNA]
        | split; [exact CRC| split; [unfold B0F_bzd_skV.FDESTA; focbn; split; [exact DSTA| split; [exact DL| split; [exact Edb| exact Lout]]]
                                  | split; [unfold bzd_slots; exact FR| split; [exact FS| split; [exact ST| exact AC]]]]]].
    - unfold B0F_bzd_skV.WLA. exact MU.
    - exact WM.
    - exact MI.
    - Time abstract (apply S0F_bzd_loop3s.S0F_bzd_loop3.dpureF_setccs; exact DP').
    - Time abstract reflexivity.
    - focbn. exact Rcc2.
    - focbn. exact Rav.
    - focbn. exact BND.
  Time Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let cf_transportA := B0F_bzd_sk1.cf_transportA z SHS ZOK.
  Let fheld_transportA := B0F_bzd_sk1.fheld_transportA z SHS ZOK.
  Let stk_transportFA := B0F_bzd_sk1.stk_transportFA z SHS ZOK.
  Let aconsts_transportA := B0F_bzd_sk1.aconsts_transportA z SHS ZOK.

  Lemma bzd_fjoinFA : forall f (m1 : word -> option byte) (J : jk) (d : dst) (s : dstrm) (rr : drest),
    KRet WLA -> KCall WLA f ->
    b_small cx = 0%Z -> TT <> 0%Z -> dpureF cx (bs_of cx J s) (z_payload z) J d s -> r_of d = rr ->
    (0 <= d_cccrc d < 4294967296)%Z -> (0 <= d_sbcrc d < 4294967296)%Z -> (len / 6 - d_blockNo d <= Z.of_nat f)%Z ->
    u32arr b0segs m1 (S + 1096) (zw32 (d_cftab d) 257) -> drest_at b0segs m1 S rr ->
    bytes_at b0segs m1 SRC (z_payload z) -> ro_cells b0segs m1 838960 [C8 (z_sv z)] ->
    rw_cells b0segs m1 (uspi + 264) FSAVA -> stk b0segs m1 lo uspi -> aconsts B0C m1 -> munch WLA (z_m0 z) m1 -> wmono b0segs (z_m0 z) m1 ->
    B0_FKjoin (fmkcA m1 J d s f) SHS w0 (FROfA DI_B0 (fmkcA m1 J d s f)) (FWBA (fmkcA m1 J d s f)).
  Proof.
    intros until rr. intros KR KC Hsm TNZ DP Err Hcc Hsb BND CF DR PAY SV FS ST AC MU0 WM0.
    unfold B0_FKjoin. ofmkc. intros until rest. cbv zeta. intros DSm DE FSL RO MU WM OJ.
    assert (MUf : munch WLF m1 m) by exact MU.
    pose proof (munch_weaken _ _ _ _ (B0F_bzd_skV.wlf_sub z) MUf) as MUw.
    pose proof (cf_transportA m1 m _ MUw WM CF ltac:(rewrite zw32_length_nat; reflexivity)) as CF'.
    pose proof (stk_transportFA m1 m MUf WM ST) as ST'. pose proof (aconsts_transportA m1 m MUw AC) as AC'.
    cps_destruct (fheld_transportA m1 m rr MUw WM DR PAY SV FS MU0 WM0) as (DR' & PAY' & SV' & FS' & MU' & WM').
    clear CF DR PAY SV FS ST AC MU0 WM0 MU WM MUw MUf.
    cps_destruct RO as (SAV & TTA & CRC & RNA & GOT & MI). unfold FGOTA in GOT. b0img. ofmkc.
    cps_destruct DSm as (HD & NBU & MID & SM). pose proof DE as DE'. cps_destruct DE' as (DSTA & DL & Edb & Lout).
    unfold ojoin in OJ. ofmkc. focbn_in OJ. cps_destruct OJ as (Rnu & Rcb & Rol & Roc & Rk0 & Rtp & Rrnd & Rav).
    cbn [K_U Z.eqb].
    assert (Rav2 : (0 <= av <= dlen)%Z).
    { focbn_in Lout. pose proof (f_equal (@length byte) Edb) as X. rewrite length_app, length_map, length_rev in X. clear -X Lout DL Rav. lia. }
    eapply (bzd_joinA f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m J d s oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest KR KC);
      [ | exact MU'| exact WM'| exact MI| exact DP| | exact Hcc| exact Hsb| exact BND| exact Rnu| exact Rcb| exact Rol| exact Rav2].
    - unfold B0F_bzd_skV.FCHA. split; [| split; [exact CRC| split; [exact DE| split; [exact FSL| split; [exact FS'| split; [exact ST'| exact AC']]]]]].
      eapply dmemF_intro; b0img; focbn;
        [ abstract (exact_cells HD)| abstract (exact_cells NBU)| abstract (exact CF')| abstract (exact_cells MID)| abstract (exact_cells SAV)
        | abstract (change (r_of (set8 d oc ol nu k0 tp rn rt cb)) with (r_of d); rewrite Err; exact DR')
        | abstract (exact_cells SM)
        | | abstract (exact PAY')| exact GOT| exact SV'| exact RNA].
      change (blk_of cx (set8 d oc ol nu k0 tp rn rt cb)) with (blk_of cx d).
      unfold blk_of. rewrite Hsm. cbn [Z.eqb blk_at di_segs DI_B0].
      zok. split; [exact Hsm| split; [exact TTA| apply zw32_length; clear -LN; lia]].
    - intros A k HR. zok. cps_destruct (BTT TNZ) as ((RT1 & RT2) & DT1 & _).
      destruct HR as [(_ & -> & ->) | (Hs1 & _)]; [split; [split; assumption| exact DT1]| exfalso; clear -Hs1 Hsm; lia].
  Qed.

  Lemma bzd_fjoinSA : forall f (m1 : word -> option byte) (J : jk) (d : dst) (s : dstrm) (rr : drest),
    KRet WLA -> KCall WLA f ->
    b_small cx = 1%Z -> L16 <> 0%Z -> L4 <> 0%Z -> dpureF cx (bs_of cx J s) (z_payload z) J d s -> r_of d = rr ->
    (0 <= d_cccrc d < 4294967296)%Z -> (0 <= d_sbcrc d < 4294967296)%Z -> (len / 6 - d_blockNo d <= Z.of_nat f)%Z ->
    drest_at b0segs m1 S rr ->
    bytes_at b0segs m1 SRC (z_payload z) -> ro_cells b0segs m1 838960 [C8 (z_sv z)] ->
    rw_cells b0segs m1 (uspi + 264) FSAVA -> munch WLA (z_m0 z) m1 -> wmono b0segs (z_m0 z) m1 ->
    B0_FKjoin (fmkcA m1 J d s f) SHS w0 (FROsB (fmkcA m1 J d s f) lo) (FWBAc (fmkcA m1 J d s f)).
  Proof.
    intros until rr. intros KR KC Hsm NZ16 NZ4 DP Err Hcc Hsb BND DR PAY SV FS MU0 WM0.
    unfold B0_FKjoin. ofmkc. intros until rest. cbv zeta. intros DSm DE FSL RO MU WM OJ.
    assert (MUw : munch WLA m1 m) by exact MU.
    cps_destruct (fheld_transportA m1 m rr MUw WM DR PAY SV FS MU0 WM0) as (DR' & PAY' & SV' & FS' & MU' & WM').
    clear DR PAY SV FS MU0 WM0 MU WM MUw.
    unfold FROsB in RO. ofmkc. cps_destruct RO as ((SAV & L16A & L4A & CFA & CRC & RNA & GOT & MI) & AC' & ST'). unfold FGOTA in GOT. b0img. ofmkc.
    cps_destruct DSm as (HD & NBU & MID & SM). pose proof DE as DE'. cps_destruct DE' as (DSTA & DL & Edb & Lout).
    unfold ojoin in OJ. ofmkc. focbn_in OJ. cps_destruct OJ as (Rnu & Rcb & Rol & Roc & Rk0 & Rtp & Rrnd & Rav).
    cbn [K_U Z.eqb].
    assert (Rav2 : (0 <= av <= dlen)%Z).
    { focbn_in Lout. pose proof (f_equal (@length byte) Edb) as X. rewrite length_app, length_map, length_rev in X. clear -X Lout DL Rav. lia. }
    eapply (bzd_joinA f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m J d s oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest KR KC);
      [ | exact MU'| exact WM'| exact MI| exact DP| | exact Hcc| exact Hsb| exact BND| exact Rnu| exact Rcb| exact Rol| exact Rav2].
    - unfold B0F_bzd_skV.FCHA. split; [| split; [exact CRC| split; [exact DE| split; [exact FSL| split; [exact FS'| split; [exact ST'| exact AC']]]]]].
      eapply dmemF_intro; b0img; focbn;
        [ abstract (exact_cells HD)| abstract (exact_cells NBU)| abstract (exact CFA)| abstract (exact_cells MID)| abstract (exact_cells SAV)
        | abstract (change (r_of (set8 d oc ol nu k0 tp rn rt cb)) with (r_of d); rewrite Err; exact DR')
        | abstract (exact_cells SM)
        | | abstract (exact PAY')| exact GOT| exact SV'| exact RNA].
      change (blk_of cx (set8 d oc ol nu k0 tp rn rt cb)) with (blk_of cx d).
      unfold blk_of. rewrite Hsm. cbn [Z.eqb blk_at di_segs DI_B0].
      zok. split; [exact Hsm| split; [exact L16A| split; [apply zh16_length; clear -LN; lia| split; [exact L4A| apply zb8_length; clear -LN; lia]]]].
    - intros A k HR. zok. cps_destruct (B16 NZ16) as ((RA1 & RA2) & DA1 & _). cps_destruct (B4 NZ4) as ((RB1 & RB2) & DB1 & _).
      destruct HR as [(Hs0 & _) | (_ & [(-> & ->) | (-> & ->)])];
        [exfalso; clear -Hs0 Hsm; lia | split; [split; assumption| exact DA1] | split; [split; assumption| exact DB1]].
  Qed.
End BZD.
End ACeilS1.

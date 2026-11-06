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
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bzd_fepiA : forall (W : list ivl) (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6
                            w8 w40 w48 w56 w64 w72 w88 w224 w232 : word)
      (m : word -> option byte) (rv : Z) (J : jk) (d : dst) (s : dstrm) (dbytes rest : list byte),
    KRet W ->
    rw_cells b0segs m uspi (bzd_slots S SHS w0 w8 w40 w48 w56 w64 w72 w88 w224 w232) ->
    rw_cells b0segs m (uspi + 264) FSAVA -> stk b0segs m lo uspi ->
    munch W (z_m0 z) m -> wmono b0segs (z_m0 z) m -> mem_inv b0segs m ->
    DecCutB.dmem DI_B0 cx (z_g1 z) (z_sv z) (z_payload z) m (dvF cx J d s) -> FIMGA m -> FDESTA m s dbytes rest ->
    dpureF cx (bs_of cx J s) (z_payload z) J d s -> (-5 <= rv <= 4)%Z ->
    evt b0segs (QF (rv, d, s))
        (MS (mkR (Z_to_bv 64 rv) (z_spi z) (z_gp z) (z_tp z) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
            (z_F z) (Z_to_bv 64 0x83f50) (z_fc z) None m (seg_rom b0segs)).
  Proof.
    intros until rest. intros KR FR FS ST MU WM MI DM IM DE DP RV. zok. hide_disj. unfold B0F_bzd_skV.FSAVA in FS.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    wstep.
    unfold bzd_slots in FR. release_frame FR ST (uspi + 264)%Z.
    release_frame FS ST (bv_unsigned (z_sp z)).
    (* [comment removed for export] *)
    wstep. rewrite SPI2.
    eapply KR; eassumption.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fmkc_okA : forall m1 J d s f dbytes rest m,
    dpureF cx (bs_of cx J s) (z_payload z) J d s -> dout_okW d -> (0 <= s_avail_out s <= dlen)%Z ->
    FDESTA m s dbytes rest ->
    foctx_okA (fmkcA m1 J d s f) BIHI0.
  Proof.
    intros until m. (intros DP OKW Hav; cps_intros (_ & _ & _ & Lout)).
    pose proof DP as X. unfold dpureF, jk_static, in_rel, drep in X. dvF_cbn_in X.
    cps_destruct X as (JWF & _ & En & Esm & Evb & _ & _ & _ & RbB & RbL & Rbn & Rcred & Rsnb & Rnu & Rtt & Rl16 & Rl4 & Rs2u).
    cps_destruct OKW as (Eol & Rtp & NK & Rsnb1 & Ecb & Rsb & Rr01 & Rrnd & Rcf & Eoc & Rn9).
    zok. unfold foctx_okA, oent, disj, bzd_img_apart. ofmkc. rewrite Ecb, Eoc, En.
    change (2^32)%Z with 4294967296%Z in Rtt. change (2^16)%Z with 65536%Z in Rl16.
    splits; try assumption.
    all: try (rewrite <- En; exact NK).
    (* [comment removed for export] *)
    all: clear D_SM D_SR D_SD D_MR D_MD D_RD IA_S IA_M IA_D BTT B16 B4 B164 NK Rr01 Rrnd Rcf LSM; lia.
  Qed.

  Lemma fmkc_okFA : forall m1 J d s f, b_small cx = 0%Z -> TT <> 0%Z -> foctx_okFA (fmkcA m1 J d s f) BIHI0.
  Proof.
    intros m1 J d s f Hsm TNZ. zok. unfold foctx_okFA, disj, bzd_img_apart. ofmkc.
    cps_destruct (BTT TNZ) as ((RT1 & RT2) & DT1 & DT2 & DT3 & IAT). splits; assumption.
  Qed.

  Lemma fmkc_okSA : forall m1 J d s f, b_small cx = 1%Z -> L16 <> 0%Z -> L4 <> 0%Z -> foctx_okSA (fmkcA m1 J d s f) BIHI0.
  Proof.
    intros m1 J d s f Hsm NZ16 NZ4. zok. unfold foctx_okSA, disj, bzd_img_apart. ofmkc.
    cps_destruct (B16 NZ16) as ((R16a & R16b) & DA1 & DA2 & DA3 & IA16). cps_destruct (B4 NZ4) as ((R4a & R4b) & DB1 & DB2 & DB3 & IA4).
    pose proof (B164 NZ16 NZ4) as D164. splits; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma fmkc_alF : forall m1 J d s f, (b_tt (o_cx (fmkcA m1 J d s f)) mod 4 = 0)%Z.
  Proof. intros. zok. ofmkc. exact ALTT. Qed.
  Lemma fmkc_okSB : forall m1 J d s f,
    (BIHI0 <= lo /\ alloc_ceiling <= lo /\ lo + 16 <= bv_unsigned (o_SP (fmkcA m1 J d s f)) /\ BIHI0 <= b_s (o_cx (fmkcA m1 J d s f)) /\ b_ll16 (o_cx (fmkcA m1 J d s f)) mod 2 = 0)%Z.
  Proof. intros. zok. ofmkc. clear D_SM D_SR D_SD D_MR D_MD D_RD IA_S IA_M IA_D BTT B16 B4 B164 LSM. repeat split; try assumption; lia. Qed.

  (* [comment removed for export] *)
  Lemma bzd_sh_rebase : forall W m0 m1, bzd_sh z W m0 -> munch W m0 m1 -> bzd_sh z W m1.
  Proof.
    intros W m0 m1 SH MU. assert (SF : sub_fp W W) by (intros x H; exact H).
    cps_destruct SH as (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold bzd_sh. splits.
    - eapply shzW_sub; [exact H1| exact MU| exact SF| lia| lia].
    - eapply shzW_sub; [exact H2| exact MU| exact SF| lia| lia].
    - eapply shpW_sub; [exact H3| exact MU| exact SF| lia| lia].
    - eapply shzW_sub; [exact H4| exact MU| exact SF| lia| lia].
    - eapply shzW_sub; [exact H5| exact MU| exact SF| lia| lia].
    - intros E. eapply shzW_sub; [exact (H6 E)| exact MU| exact SF| lia| lia].
    - intros E. destruct (H7 E) as [Ha Hb]. split; [eapply shzW_sub; [exact Ha| exact MU| exact SF| lia| lia] | eapply shzW_sub; [exact Hb| exact MU| exact SF| lia| lia]].
  Qed.
  (* [comment removed for export] *)
  Lemma bzd_sh_sub : forall W W' m0 m1, bzd_sh z W m0 -> munch W m0 m1 -> sub_fp W' W -> bzd_sh z W' m1.
  Proof.
    intros W W' m0 m1 SH MU SF.
    cps_destruct SH as (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold bzd_sh. splits.
    - eapply shzW_sub; [exact H1| exact MU| exact SF| lia| lia].
    - eapply shzW_sub; [exact H2| exact MU| exact SF| lia| lia].
    - eapply shpW_sub; [exact H3| exact MU| exact SF| lia| lia].
    - eapply shzW_sub; [exact H4| exact MU| exact SF| lia| lia].
    - eapply shzW_sub; [exact H5| exact MU| exact SF| lia| lia].
    - intros E. eapply shzW_sub; [exact (H6 E)| exact MU| exact SF| lia| lia].
    - intros E. destruct (H7 E) as [Ha Hb]. split; [eapply shzW_sub; [exact Ha| exact MU| exact SF| lia| lia] | eapply shzW_sub; [exact Hb| exact MU| exact SF| lia| lia]].
  Qed.
  Lemma fmkc_sh : forall W m0 m1 J d s f, bzd_sh z W m0 -> obz_sh DI_B0 (fmkcA m1 J d s f) W m0.
  Proof. intros W m0 m1 J d s f SH. unfold obz_sh. b0img. ofmkc. exact SH. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac dj := cbn [disjoint_from]; unfold B0F_bzd_skV.FSAVA; simpl_sizes; repeat split; try exact I; lia.
  Lemma cf_transportA : forall m1 m cf, munch WLA m1 m -> wmono b0segs m1 m ->
    u32arr b0segs m1 (S + 1096) cf -> length cf = 257%nat -> u32arr b0segs m (S + 1096) cf.
  Proof.
    intros m1 m cf MU WM CF CFL. zok. unfold B0F_bzd_skV.WLA in MU.
    eapply u32arr_transport; [exact CF| exact MU| exact WM|]. rewrite CFL.
    clear D_SR D_MR D_MD D_RD IA_S IA_M IA_D BTT B16 B4 B164 LSM. dj.
  Qed.
  Lemma fheld_transportA : forall m1 m rr,
    munch WLA m1 m -> wmono b0segs m1 m ->
    drest_at b0segs m1 S rr ->
    bytes_at b0segs m1 SRC (z_payload z) -> ro_cells b0segs m1 838960 [C8 (z_sv z)] ->
    rw_cells b0segs m1 (uspi + 264) FSAVA -> munch WLA (z_m0 z) m1 -> wmono b0segs (z_m0 z) m1 ->
    drest_at b0segs m S rr /\ bytes_at b0segs m SRC (z_payload z) /\
    ro_cells b0segs m 838960 [C8 (z_sv z)] /\ rw_cells b0segs m (uspi + 264) FSAVA /\
    munch WLA (z_m0 z) m /\ wmono b0segs (z_m0 z) m.
  Proof.
    intros m1 m rr MU WM DR PAY SV FS MU0 WM0. zok.
    pose proof MU as MU'. unfold B0F_bzd_skV.WLA in MU.
    splits.
    - eapply drest_transport; [exact DR| exact MU| exact WM| | |];
        clear D_SR D_MR D_MD D_RD IA_S IA_M IA_D BTT B16 B4 B164 LSM; dj.
    - eapply bytes_at_transport; [exact PAY| exact MU|]. rewrite PAYL.
      clear D_SM D_SD D_MD IA_S IA_M IA_D BTT B16 B4 B164 LSM. dj.
    - eapply ro_cells_transport; [exact SV| exact MU|].
      clear D_SM D_SR D_SD D_MR D_MD D_RD BTT B16 B4 B164 LSM. dj.
    - eapply rw_cells_transport; [exact FS| exact MU| exact WM|].
      clear D_SM D_SR D_SD D_MR D_MD D_RD IA_S IA_M IA_D BTT B16 B4 B164 LSM. dj.
    - eapply munch_trans; [exact MU0| exact MU'].
    - eapply wmono_trans; [exact WM0| exact WM].
  Qed.
  (* [comment removed for export] *)
  Lemma stk_transportFA : forall m1 m, munch WLF m1 m -> wmono b0segs m1 m -> stk b0segs m1 lo uspi -> stk b0segs m lo uspi.
  Proof.
    intros m1 m MU WM ST. zok. unfold B0F_bzd_skV.WLF in MU.
    eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|].
    clear D_SM D_SR D_SD D_MR D_MD D_RD IA_S IA_M IA_D BTT B16 B4 B164 LSM. dj.
  Qed.
  (* [comment removed for export] *)
  Lemma aconsts_transportA : forall m1 m, munch WLA m1 m -> aconsts B0C m1 -> aconsts B0C m.
  Proof.
    intros m1 m MU [A1 A2]. zok. unfold B0F_bzd_skV.WLA in MU.
    cbn [aci_segs aci_got_sh aci_shvar aci_c CmpCut.ci_segs B0C] in A1, A2 |- *. unfold aconsts. cbn [aci_segs aci_got_sh aci_shvar aci_c CmpCut.ci_segs B0C].
    split; (eapply ro_cells_transport; [eassumption| exact MU|]);
      clear D_SM D_SR D_SD D_MR D_MD D_RD BTT B16 B4 B164 LSM; dj.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bzd_fexitFA : forall (m1 : word -> option byte) (J : jk) (d : dst) (s : dstrm) (f : nat) (rr : drest),
    KRet WLA ->
    b_small cx = 0%Z -> dpureF cx (bs_of cx J s) (z_payload z) J d s -> r_of d = rr ->
    u32arr b0segs m1 (S + 1096) (zw32 (d_cftab d) 257) -> drest_at b0segs m1 S rr ->
    bytes_at b0segs m1 SRC (z_payload z) -> ro_cells b0segs m1 838960 [C8 (z_sv z)] ->
    rw_cells b0segs m1 (uspi + 264) FSAVA -> stk b0segs m1 lo uspi -> munch WLA (z_m0 z) m1 -> wmono b0segs (z_m0 z) m1 ->
    B0_FKexit (fmkcA m1 J d s f) SHS w0 (FROfA DI_B0 (fmkcA m1 J d s f)) (FWBA (fmkcA m1 J d s f)).
  Proof.
    intros until rr. intros KR Hsm DP Err CF DR PAY SV FS ST MU0 WM0.
    unfold B0_FKexit. ofmkc. intros until rest. cbv zeta.
    (intros DSm DE FSL RO MU WM; cps_intros (Hnu & Hav)).
    assert (MUf : munch WLF m1 m) by exact MU.
    pose proof (munch_weaken _ _ _ _ (B0F_bzd_skV.wlf_sub z) MUf) as MUw.
    pose proof (cf_transportA m1 m _ MUw WM CF ltac:(rewrite zw32_length_nat; reflexivity)) as CF'.
    pose proof (stk_transportFA m1 m MUf WM ST) as ST'.
    cps_destruct (fheld_transportA m1 m rr MUw WM DR PAY SV FS MU0 WM0) as (DR' & PAY' & SV' & FS' & MU' & WM').
    cps_destruct RO as (SAV & TTA & CRC & RNA & GOT & MI). unfold FGOTA in GOT. b0img. ofmkc.
    cps_destruct DSm as (HD & NBU & MID & SM). cps_destruct DE as (DSTA & DL & Edb & Lout).
    focbn_in Hnu. cbn [K_U Z.eqb].
    eapply (bzd_fepiA WLA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m BZ_DATA_ERROR (jk_set_o J tol toh)
              (set8 d oc ol nu k0 tp rn rt cb) (smod s out av tout) dbytes rest KR FSL FS' ST' MU' WM' MI).
    - eapply dmemF_intro; b0img; focbn; try exact_cells HD; try exact_cells NBU; try exact CF'; try exact_cells MID; try exact_cells SAV; try exact_cells SM;
        try exact PAY'; try exact GOT; try exact SV'; try exact RNA.
      + change (r_of (set8 d oc ol nu k0 tp rn rt cb)) with (r_of d). rewrite Err. exact DR'.
      + change (blk_of cx (set8 d oc ol nu k0 tp rn rt cb)) with (blk_of cx d).
        unfold blk_of. rewrite Hsm. cbn [Z.eqb blk_at di_segs DI_B0].
        zok. split; [exact Hsm| split; [exact TTA| apply zw32_length; clear -LN; lia]].
    - exact CRC.
    - unfold B0F_bzd_skV.FDESTA. split; [exact DSTA| split; [exact DL| split; [exact Edb| exact Lout]]].
    - apply dpureF_set8; [exact DP| exact Hnu].
    - unfold BZ_DATA_ERROR. lia.
  Qed.
  Lemma bzd_fexitSA : forall (m1 : word -> option byte) (J : jk) (d : dst) (s : dstrm) (f : nat) (rr : drest),
    KRet WLA ->
    b_small cx = 1%Z -> dpureF cx (bs_of cx J s) (z_payload z) J d s -> r_of d = rr ->
    drest_at b0segs m1 S rr ->
    bytes_at b0segs m1 SRC (z_payload z) -> ro_cells b0segs m1 838960 [C8 (z_sv z)] ->
    rw_cells b0segs m1 (uspi + 264) FSAVA -> munch WLA (z_m0 z) m1 -> wmono b0segs (z_m0 z) m1 ->
    B0_FKexit (fmkcA m1 J d s f) SHS w0 (FROsB (fmkcA m1 J d s f) lo) (FWBAc (fmkcA m1 J d s f)).
  Proof.
    intros until rr. intros KR Hsm DP Err DR PAY SV FS MU0 WM0.
    unfold B0_FKexit. ofmkc. intros until rest. cbv zeta.
    (intros DSm DE FSL RO MU WM; cps_intros (Hnu & Hav)).
    assert (MUw : munch WLA m1 m) by exact MU.
    unfold FROsB in RO. ofmkc. cps_destruct RO as ((SAV & L16A & L4A & CFA & CRC & RNA & GOT & MI) & _ & ST'). unfold FGOTA in GOT. b0img. ofmkc.
    cps_destruct (fheld_transportA m1 m rr MUw WM DR PAY SV FS MU0 WM0) as (DR' & PAY' & SV' & FS' & MU' & WM').
    cps_destruct DSm as (HD & NBU & MID & SM). cps_destruct DE as (DSTA & DL & Edb & Lout).
    focbn_in Hnu. cbn [K_U Z.eqb].
    eapply (bzd_fepiA WLA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m BZ_DATA_ERROR (jk_set_o J tol toh)
              (set8 d oc ol nu k0 tp rn rt cb) (smod s out av tout) dbytes rest KR FSL FS' ST' MU' WM' MI).
    - eapply dmemF_intro; b0img; focbn; try exact_cells HD; try exact_cells NBU; try exact CFA; try exact_cells MID; try exact_cells SAV; try exact_cells SM;
        try exact PAY'; try exact GOT; try exact SV'; try exact RNA.
      + change (r_of (set8 d oc ol nu k0 tp rn rt cb)) with (r_of d). rewrite Err. exact DR'.
      + change (blk_of cx (set8 d oc ol nu k0 tp rn rt cb)) with (blk_of cx d).
        unfold blk_of. rewrite Hsm. cbn [Z.eqb blk_at di_segs DI_B0].
        zok. split; [exact Hsm| split; [exact L16A| split; [apply zh16_length; clear -LN; lia| split; [exact L4A| apply zb8_length; clear -LN; lia]]]].
    - exact CRC.
    - unfold B0F_bzd_skV.FDESTA. split; [exact DSTA| split; [exact DL| split; [exact Edb| exact Lout]]].
    - apply dpureF_set8; [exact DP| exact Hnu].
    - unfold BZ_DATA_ERROR. lia.
  Qed.
End BZD.
End ACeilS1.

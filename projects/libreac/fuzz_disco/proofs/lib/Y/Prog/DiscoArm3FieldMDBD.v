(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8c.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AE2d.v, proofs/cgif/cgif_file_fuzzer/lib/UI2d.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on image B (fuzz_grant.asan-ubsan, bin fde52226dc48, 0x8363c = BASE + 0x2c00, 367 slots), ported from lib/A/Prog/CtrlBuildGrantSweep.v at a working branch 5aae1e8a0ce (its Require closure: 196 files, 0 Admitted / admit / Axiom / Parameter), with the steps of the class-6 side-stack frame adapted from lib/A/Prog/CtrlStampHeadamp.v at the same commit (whose own cgif sources are proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, ACam.v, ACbf.v, ACf6.v, AChd.v); every address, constant and byte is image B's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlBuildGrantSweep.v, with its module paths and module names changed; 458 of its 493 lines of code are new or changed and 3975 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3FieldMDA.v, with its module paths changed; 445 of its 537 lines of code are new or changed and 401 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC45.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YC81 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3 DiscoArm3FieldCut DiscoArm3FieldPFXKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoArm3FieldModel DiscoArm3FieldMDKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3FieldMDBKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c reac_disco_table_json_c disco_json_text disco_json_reader_model slot_ser_defs slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition MDD_CNT : nat := 563%nat.
Definition mdbd_sx (r : nat) : sv :=
  match r with 10%nat => SLit 1 | 27%nat => SOff AT_SH 0 | _ => a3f_srx 0 r end.
Definition mdbd_sr : list sv := map mdbd_sx (seq 0 32).
Definition mdbd_fin_sr (p : Z) : list sv :=
  map (fun r => match r with 10%nat => SOff MDD_CNT 0 | 11%nat => SLit (p + 1) | _ => mdbd_sx r end) (seq 0 32).
Definition mdbd_acs (p : Z) : list YP09.chunk :=
  [YP09.mkChunk 368 (CVal 8 (SLit p)); YP09.mkChunk 360 (CVal 8 (SOff MDD_CNT 0))].
Definition mdbd_rs (p : Z) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 368 376 (dslot_chunks ++ mdbd_acs p);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ []);
   YP09.mkRegion (Some AT_SH) 0 (fs_frame_bytes DFRAME_CLASS / 8) 224 261 (dsh_chunks dsh_age);
   got_regionP; bcell_regionP 32].
Definition mdbd_ss0 (p : Z) : sstate := mkSS MDJ_OFF mdbd_sr (mdbd_rs p) None (d_facts [] []).
Definition mdbd_c368 (p : Z) : list YP09.chunk := [YP09.mkChunk 368 (CVal 8 (SLit (p + 1)))].

Lemma mdbd_subw : forall b lo hi wlo whi wlo' whi' cs,
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) ->
  subregion (YP09.mkRegion b lo hi wlo' whi' cs) (YP09.mkRegion b lo hi wlo whi cs).
Proof.
  intros b lo hi wlo whi wlo' whi' cs Hw. unfold subregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hw|]. intros c Hc. exact Hc.
Qed.
Lemma mdbd_subrefl : forall r, subregion r r.
Proof. intros [b lo hi wlo whi cs]. apply mdbd_subw. lia. Qed.
Lemma mdbd_submem : forall p, submem (mdbd_rs p) (d_kregions dsh_age (mdbd_acs p) [] ++ []).
Proof.
  intros p. unfold mdbd_rs, d_kregions, fshadow_region. rewrite app_nil_r.
  apply submem_keep; [apply mdbd_subrefl|].
  apply submem_keep; [apply mdbd_subw; lia|].
  apply submem_keep; [apply mdbd_subw; lia|].
  apply submem_keep; [apply mdbd_subw; unfold DFRAME_SH; lia|].
  apply submem_keep; [apply mdbd_subrefl|].
  apply submem_keep; [apply mdbd_subrefl|].
  apply submem_nil.
Qed.
Lemma mdbd_wf : forall p, 0 <= p < 8 -> regions_wf (mdbd_rs p) = true.
Proof.
  intros p Hp. assert (Hc : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma mdbd_kwf : forall p, 0 <= p < 8 -> regions_wf (d_kregions dsh_age (mdbd_acs p) [] ++ []) = true.
Proof.
  intros p Hp. assert (Hc : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma mdbd_inw : forall E p a, in_wrange E (mdbd_rs p) a ->
  base_val E (Some AT_A) + 368 <= a < base_val E (Some AT_A) + 376 \/
  base_val E (Some AT_SH) + 224 <= a < base_val E (Some AT_SH) + 261.
Proof.
  intros E p a (r & Hin & Hr). unfold mdbd_rs in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    unfold got_regionP, bcell_regionP in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.
Lemma mdbd_awr_skel : forall E rs rs' STK sp0 FP bl0 blc ly own,
  awr_ok E rs' STK sp0 FP bl0 blc ly own -> skeleton rs = skeleton rs' -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
  intros E rs rs' STK sp0 FP bl0 blc ly own H Hsk a Ha. apply H. eapply in_wrange_skeleton; [exact Hsk | exact Ha].
Qed.

Lemma mdbd_cval_eqb_eq : forall a b, cval_eqb a b = true -> a = b.
Proof.
  intros [w v|l|l|d s l] [w' v'|l'|l'|d' s' l']; cbn [cval_eqb]; intros H; try discriminate H.
  - apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1. apply sv_eqb_eq in H2. subst. reflexivity.
  - apply Z.eqb_eq in H. subst. reflexivity.
  - apply Z.eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.
Lemma mdbd_chunk_eqb_eq : forall a b, chunk_eqb a b = true -> a = b.
Proof.
  intros [o v] [o' v']. unfold chunk_eqb. cbn [YP09.c_off YP09.c_val]. intros H.
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply mdbd_cval_eqb_eq in H2. subst. reflexivity.
Qed.
Lemma mdbd_cover_Forall : forall (P : YP09.chunk -> Prop) tgt src,
  chunks_cover tgt src = true -> Forall P src -> Forall P tgt.
Proof.
  intros P tgt src H Hs. unfold chunks_cover in H. apply Forall_forall. intros c Hc.
  pose proof (proj1 (forallb_forall _ _) H c Hc) as Hx. apply existsb_exists in Hx as (c' & Hin & He).
  apply mdbd_chunk_eqb_eq in He. subst c'. exact (proj1 (Forall_forall _ _) Hs c Hin).
Qed.
Lemma mdbd_cover_ok : forall segs E m b lo hi wlo whi tgt r,
  region_cover b lo hi tgt r = true -> region_ok segs E m r ->
  (forall o, wlo <= o < whi -> writable_at segs m (base_val E (Some b) + o)) ->
  region_ok segs E m (YP09.mkRegion (Some b) lo hi wlo whi tgt).
Proof.
  intros segs E m b lo hi wlo whi tgt [rb rlo rhi rwlo rwhi rcs] H (H1 & H2 & _ & H4) Hw.
  unfold region_cover in H. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_chunks] in H.
  apply andb_prop in H as [H Hc]. apply andb_prop in H as [H Hhi]. apply andb_prop in H as [Hb Hlo].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  destruct rb as [n|]; [|discriminate Hb]. cbn [obase_eqb] in Hb. apply Nat.eqb_eq in Hb. subst n.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in H1, H2, H4.
  unfold region_ok. cbv zeta. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [lia|]. split; [lia|]. split; [exact Hw|].
  exact (mdbd_cover_Forall _ tgt rcs Hc H4).
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma mdbd_app_nsh : forall F lo n x, in_app lo n -> 0 <= F -> F + 4096 <= CEIL_MAX ->
  lo <= x < lo + n -> ~ (shadow_addr F <= x < shadow_addr F + 512).
Proof.
  intros F lo n x Ha HF0 HF1 Hx Hs. unfold in_app, kLowShadowBeg, kHighMemBeg in Ha.
  unfold shadow_addr, SHADOW_OFF in Hs. destruct Ha as (Ha1 & [Ha2 | (Ha2 & _)]); lia.
Qed.

Lemma mdbd_env_reg : forall cx E regs ex (r : bv 5) a, a = (AT_X + Z.to_nat (bv_unsigned r))%nat ->
  ew (d_env cx E (a3f_vals regs ++ ex)) a = getr regs r.
Proof.
  intros cx E regs ex r a ->.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite d_env_x by (unfold a3f_vals; rewrite length_app, length_map, length_seq; lia).
  unfold a3f_vals. rewrite app_nth1 by (rewrite length_map, length_seq; lia).
  rewrite (nth_indep _ _ ((fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) 0%nat))
    by (rewrite length_map, length_seq; lia).
  pose proof (map_nth (fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32) 0%nat
    (Z.to_nat (bv_unsigned r))) as Hm.
  cbv beta in Hm |- *. rewrite Hm, seq_nth by lia. cbn [Nat.add]. rewrite Z2Nat.id by lia.
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Section h.
Variable B : asyms.

Lemma mdbd_regs_ok : forall cx E regs ex, d_E cx E -> d_rL B cx regs -> getr regs 10 = w64 1 ->
  regs_ok (d_env cx E (a3f_vals regs ++ ex)) mdbd_sr regs.
Proof.
  intros cx E regs ex HE HL R10.
  pose proof (d_E_env cx E (a3f_vals regs ++ ex) HE) as HE'.
  destruct HE' as (HER & H32 & _ & HA60 & _ & HSH). unfold AT_A in HA60. unfold AT_SH in HSH.
  destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
  all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
         let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  all: cbn [sv_denot].
  all: first
    [ rewrite getr_zero; reflexivity
    | exact R10
    | rewrite HSH, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H27
    | rewrite HA60, Z.add_0_r, Z_to_bv_bv_unsigned;
      first [ rewrite <- Hsp; unfold spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity | exact H9 ]
    | rewrite (HER 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, H8; unfold w64, d_S, spZ;
      rewrite Z_to_bv_bv_unsigned; reflexivity
    | rewrite H32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H19
    | exact H18
    | exact H20
    | match goal with |- getr ?rg ?x = Z_to_bv 64 (bv_unsigned (ew ?Ex ?a) + 0) =>
        rewrite (mdbd_env_reg cx E regs ex x a eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ].
Qed.

Lemma mdbd_fsh_nrd : forall (cx : dcx) h a,
  in_app (d_FB cx) 4096 -> 0 <= d_FB cx -> d_FB cx + 4096 <= CEIL_MAX -> in_app h 480 ->
  (0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))) ->
  (forall x, in_roP SEGS pa_relro_lo pa_relro_hi x -> 0 <= x < kLowMemEnd) ->
  shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> ~ d_rdset B cx h a.
Proof.
  intros cx h a HF HF0 HF1 Hh Hp Hro Ha Hr.
  unfold d_rdset, d_objr, d_obj in Hr. cbn [dobj_off dobj_size] in Hr. unfold HUNT_SIZE in Hr.
  destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | [(Hc & Hr) | [Hr | Hr]]]]]]].
  - exact (mdbd_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdbd_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdbd_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdbd_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdbd_app_nsh (d_FB cx) h 480 a Hh HF0 HF1 ltac:(lia) Ha).
  - pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq).
    exact (mdbd_app_nsh (d_FB cx) (c_p cx) (req_size (c_n cx)) a (Hp Hc) HF0 HF1 ltac:(lia) Ha).
  - assert (Hra : 0 <= a < kLowMemEnd) by (first [exact (Hro a Hr) | exact (Hro a (proj1 Hr))]).
    unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
  - unfold FF_canary in Hr. unfold shadow_addr, SHADOW_OFF in Ha. lia.
Qed.

Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DBRT : d_body_rt_stmt B.

Definition mdbd_run_stmt (p : Z) : Prop :=
  forall (fq : YK11.FPState) (W : world SEGS) (E : env) (ms : machine_state) (mdc : Model)
    STK sp0 FP ly S W0 mem md own lyc Sc k (Q : world SEGS -> config -> Prop),
  img_env VAL A_LIM E ->
  st_ok_pi (fx := fq) SEGS VAL E (mdbd_ss0 p) (restrict (w_H W) ms) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  awr_ok E (mdbd_rs p) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall (tk : bool) (ss : sstate) (ms' : machine_state) (mat' : list word),
     branch_taken BC_NE (sv_denot E (SLit (p + 1))) (sv_denot E (SOff MDD_CNT 0)) = tk ->
     ss_pc ss = (if tk then PH_OFF else R14_OFF) ->
     ss_regs ss = mdbd_fin_sr p -> ss_resv ss = None ->
     d_land_chk dsh_ser2 (ss_mem ss) = true ->
     existsb (region_cover AT_A 368 376 (mdbd_c368 p)) (ss_mem ss) = true ->
     st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms') ->
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     frame_of E (mdbd_rs p) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.

Ltac mdbd_post POST HS HJ HF2 HG2 HFr1 HG1 Hc tk :=
  rewrite wvb_collapse in HJ; rewrite wvb_collapse;
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?s _ =>
    apply (POST tk s _ _ Hc ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HS HJ);
    [ refine (frame_of_trans _ _ _ _ _ _ _ HFr1 HF2); vm_compute; reflexivity
    | exact (mem_grows_trans _ _ _ HG1 HG2) ]
  end.

Ltac mdbd_fin POST HS HJ tk :=
  lazymatch goal with
  | HFr2 : frame_of _ _ (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)),
    HFra : frame_of _ _ (mrestrict _ (ms_mem ?m0)) (mrestrict _ (ms_mem ?m1)),
    HG2 : mem_grows (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)),
    HGa : mem_grows (mrestrict _ (ms_mem ?m0)) (mrestrict _ (ms_mem ?m1)),
    Hc : branch_taken _ _ _ = _ |- _ => mdbd_post POST HS HJ HFr2 HG2 HFra HGa Hc tk
  end.

Ltac mdbd_walk RUNTOP RUNP BR HS HJ Hawr POST :=
  paj_run_to_shc RUNTOP HS HJ PH_OFF;
  [ exact Hawr
  | psrr_branch_pi RUNP BR HS;
    [ paj_run_to_shc RUNTOP HS HJ PH_OFF;
      [ apply (mdbd_awr_skel _ _ _ _ _ _ _ _ _ _ Hawr); vm_compute; reflexivity
      | mdbd_fin POST HS HJ true ]
    | paj_run_to_shc RUNTOP HS HJ R14_OFF;
      [ apply (mdbd_awr_skel _ _ _ _ _ _ _ _ _ _ Hawr); vm_compute; reflexivity
      | mdbd_fin POST HS HJ false ] ] ].

Lemma mdbd_run : forall p, 0 <= p < 8 -> mdbd_run_stmt p.
Proof.
  intros p Hp8 fq W E ms mdc STK sp0 FP ly S W0 mem md own lyc Sc k Q HEI HS HJ Hawr POST.
  pose proof (SRr_run_to_pi_AJ (fx := fq) (PI := PI) B LAWS) as RUNTOP.
  pose proof (SRr_run_pi_AJ (fx := fq) (PI := PI) B LAWS) as RUNP.
  pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
  assert (Hp : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct Hp as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
  - mdbd_walk RUNTOP RUNP BR HS HJ Hawr POST.
  - mdbd_walk RUNTOP RUNP BR HS HJ Hawr POST.
  - mdbd_walk RUNTOP RUNP BR HS HJ Hawr POST.
  - mdbd_walk RUNTOP RUNP BR HS HJ Hawr POST.
  - mdbd_walk RUNTOP RUNP BR HS HJ Hawr POST.
  - mdbd_walk RUNTOP RUNP BR HS HJ Hawr POST.
  - mdbd_walk RUNTOP RUNP BR HS HJ Hawr POST.
  - mdbd_walk RUNTOP RUNP BR HS HJ Hawr POST.
Qed.

Lemma mdbd_main : forall p, 0 <= p < 8 -> mdbd_run_stmt p -> mdbD_stmt B MT XM_LIB RLO RHI tfib_K p.
Proof.
intros p Hp8 RUNJ cx h i n now op W0 c0 T0 T1 buf count os vpad W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R24 & R10) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY).
destruct HY as (HSL & H408 & HUSED). destruct HSL as (Hp & H368 & H360).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
assert (LO : Z.of_nat (length (slot_ser_defs.objs_bytes buf vpad os)) <= 1296)
  by (rewrite (DiscoArm3FieldMDKit.mdk_objs_len buf vpad os HVP Lo6), Los; lia).
assert (LU : length (a3f_used (p + 1)) = 32%nat) by (unfold a3f_used; reflexivity).
pose proof HBUF as (Hr2 & HGB).
assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
  by (unfold a3_r; rewrite length_app; cbn [length]; lia).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20 & Rs27).
pose proof HBODY as (TT & GG & LL & HH & HFRM & HSHD & HOBJ & HBLK & _).
pose proof HFRM as (E & HE & HREG & HFLAG & V184 & V120 & V136 & V376 & V280 & V232 & V264).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GSHpres & GSTKpres & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as (Hceil & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBLK as (HPerm0 & _).
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym HPerm0)); unfold a3_xb; cbn [app]; left; reflexivity).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
assert (Hinh : In (h, HUNT_SIZE) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym HPerm0)); unfold a3_xb; cbn [app]; right; left; reflexivity).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinh) as (_ & _ & _ & HhA & _).
change (req_size HUNT_SIZE) with 480 in HhA.
assert (HpA : 0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))).
{ intros Hcn. pose proof HBASE as ((HPRE & _ & _ & _ & Hpn & _) & _). pose proof HPRE as (HAR0 & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin))))). }
assert (Hro : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd).
{ intros a [(s & Hs & _ & Hsa) | Hr]; apply pa_segs_low; [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a Hr)]. }
set (vals := a3f_vals regs ++ [Z_to_bv 64 count]).
assert (Lv : length vals = 33%nat)
  by (unfold vals, a3f_vals; rewrite length_app, length_map, length_seq; reflexivity).
assert (ECNT : ew (d_env cx E vals) MDD_CNT = Z_to_bv 64 count)
  by (unfold MDD_CNT; exact (d_env_x cx E vals 32 ltac:(rewrite Lv; lia))).
assert (EO : forall nn, (nn < AT_FL)%nat -> ew (d_env cx E vals) nn = ew E nn)
  by (intros nn Hnn; apply d_env_old; exact Hnn).
pose proof HE as (EE & E32 & HEI0 & E60 & EF & ESH).
pose proof (d_E_env cx E vals HE) as HE'.
assert (HEI : img_env VAL A_LIM (d_env cx E vals)) by exact (proj1 (proj2 (proj2 HE'))).
assert (U60 : bv_unsigned (ew (d_env cx E vals) 60) = d_A cx)
  by (rewrite EO by (unfold AT_FL; lia); change 60%nat with AT_A; rewrite E60; apply unsigned_lit_small; lia).
assert (U516 : bv_unsigned (ew (d_env cx E vals) 516) = d_FB cx)
  by (rewrite EO by (unfold AT_FL; lia); change 516%nat with AT_F; rewrite EF; apply unsigned_lit_small; lia).
assert (U529 : bv_unsigned (ew (d_env cx E vals) 529) = shadow_addr (d_FB cx))
  by (rewrite EO by (unfold AT_FL; lia); change 529%nat with AT_SH; rewrite ESH; apply unsigned_lit_small;
      unfold shadow_addr, SHADOW_OFF; lia).
assert (UCNT : bv_unsigned (ew (d_env cx E vals) MDD_CNT) = count)
  by (rewrite ECNT; apply unsigned_lit_small; lia).
assert (Hregs : regs_ok (d_env cx E vals) mdbd_sr regs)
  by exact (mdbd_regs_ok cx E regs [Z_to_bv 64 count] HE HRL R10).
assert (HGf : facts_ok (d_env cx E vals) (d_facts [] []))
  by exact (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HCTX HE I I).
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) (mdbd_acs p)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_ok_val SEGS _ _ (d_A cx) 368 8%N (SLit p) p); [reflexivity | cbn; lia | cbn; lia | exact H368].
  - apply (chunk_ok_val SEGS _ _ (d_A cx) 360 8%N (SOff MDD_CNT 0) count).
    + cbn [sv_denot]. rewrite UCNT, Z.add_0_r. reflexivity.
    + cbn. lia.
    + cbn. lia.
    + exact H360. }
pose proof (DSEAT LAWS PAL fq cx dsh_age ly3 S3 W regs mem3 md3 k E MDJ_OFF mdbd_sr vals (mdbd_acs p) [] []
  (d_facts [] []) HCTX HE HREG HFLAG Hregs HGf Hacs (Forall_nil _) (Forall_nil _) I (Forall_nil _)
  (mdbd_kwf p Hp8)) as HS0.
pose proof (st_ok_pi_submem _ _ _ (mdbd_rs p) HS0 (mdbd_submem p) (mdbd_wf p Hp8)) as HS.
clear HS0. cbn [ss_d ss_pc ss_regs ss_resv ss_facts] in HS.
assert (Hawr : awr_ok (d_env cx E vals) (mdbd_rs p) LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx))
  (ablocks B ly3 S3) ly3 [(DFRAME_CLASS, c_fpos cx)]).
{ unfold mdbd_rs.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
    [reflexivity | rewrite U60; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (shadow_addr (d_FB cx))); [reflexivity | exact U529 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
    exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia. }
  apply awr_ok_cons_ro; [unfold got_regionP; cbn; lia|].
  apply awr_ok_cons_ro; [unfold bcell_regionP; cbn; lia|].
  apply awr_ok_nil. }
unfold cfg_at, w64.
apply (RUNJ fq W (d_env cx E vals) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + MDJ_OFF)) mem3 (YK11.seg_rom SEGS))
  md3 LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 k _
  HEI HS HJ Hawr).
intros tk ss ms1 mat1 Htk Hpc Hsr Hrv Hchk Hxr HS1 HJ1 HFr1 HG1.
cbn [ms_mem YK11.mkst] in HFr1, HG1.
set (md' := with_vm_backing (m_vm_lazy md3) mat1 md3) in *.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 368 <= a < d_A cx + 376) ->
  ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha H1 H2. apply (aview_eq_of SEGS). apply HFr1. rewrite unsigned_lit_small by lia.
  intros Hw. apply mdbd_inw in Hw.
  change (base_val (d_env cx E vals) (Some AT_A)) with (bv_unsigned (ew (d_env cx E vals) 60)) in Hw.
  change (base_val (d_env cx E vals) (Some AT_SH)) with (bv_unsigned (ew (d_env cx E vals) 529)) in Hw.
  rewrite U60, U529 in Hw. lia. }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 368 <= a < d_A cx + 376) ->
  ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
  mbyte SEGS (rd W (ms_mem ms1)) a = mbyte SEGS (rd W mem3) a)
  by (intros a Ha H1 H2; apply (mbyte_of_aview SEGS); apply KM; assumption).
assert (KVA : forall off v, 0 <= off -> off + 8 <= 368 \/ 376 <= off ->
  off + 8 <= 472 -> val_mem SEGS (rd W mem3) (d_A cx + off) 8 v ->
  val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + off) 8 v).
{ intros off v H0 H1 H2 Hv. apply (val_mem_frame SEGS (rd W mem3)); [|exact Hv].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KB; [lia | lia |].
  unfold shadow_addr, SHADOW_OFF. lia. }
assert (KGF : forall a l, d_FB cx <= a -> a + Z.of_nat (length l) <= d_FB cx + 4096 ->
  garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms1)) a l).
{ intros a l H0 H1 Hg. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|]. intros x Hx.
  apply KB; [lia | lia |]. exact (mdbd_app_nsh (d_FB cx) (d_FB cx) 4096 x GFapp ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (KGB : forall l, Z.of_nat (length l) <= req_size (Z.max (slot_ser_defs.ser_cap op) 1) ->
  garr8 SEGS (rd W mem3) buf l -> garr8 SEGS (rd W (ms_mem ms1)) buf l).
{ intros l H1 Hg. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|]. intros x Hx.
  apply KB; [lia | lia |]. exact (mdbd_app_nsh (d_FB cx) buf _ x Hbapp ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (QR : forall r, getr (ms_regs ms1) r = sv_denot (d_env cx E vals) (sr_get (mdbd_fin_sr p) r)).
{ intros r. rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS1). rewrite Hsr. reflexivity. }
assert (X3 : ew (d_env cx E vals) 534 = getr regs 3)
  by exact (mdbd_env_reg cx E regs [Z_to_bv 64 count] (3%bv : bv 5) 534%nat eq_refl).
assert (X4 : ew (d_env cx E vals) 535 = getr regs 4)
  by exact (mdbd_env_reg cx E regs [Z_to_bv 64 count] (4%bv : bv 5) 535%nat eq_refl).
assert (X24 : ew (d_env cx E vals) 555 = getr regs 24)
  by exact (mdbd_env_reg cx E regs [Z_to_bv 64 count] (24%bv : bv 5) 555%nat eq_refl).
assert (Q2 : getr (ms_regs ms1) 2 = w64 (d_A cx)).
{ rewrite QR. change (sr_get (mdbd_fin_sr p) 2) with (SOff 60 0). cbn [sv_denot]. rewrite U60.
  unfold w64. f_equal; lia. }
assert (Q3 : getr (ms_regs ms1) 3 = getr regs 3).
{ rewrite QR. change (sr_get (mdbd_fin_sr p) 3) with (SOff 534 0). cbn [sv_denot].
  rewrite X3, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q4 : getr (ms_regs ms1) 4 = getr regs 4).
{ rewrite QR. change (sr_get (mdbd_fin_sr p) 4) with (SOff 535 0). cbn [sv_denot].
  rewrite X4, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q8 : getr (ms_regs ms1) 8 = w64 (d_S cx)).
{ rewrite QR. change (sr_get (mdbd_fin_sr p) 8) with (SOff 2 0). cbn [sv_denot].
  rewrite EO by (unfold AT_FL; lia). rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned.
  unfold w64, d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (Q9 : getr (ms_regs ms1) 9 = w64 (d_A cx)).
{ rewrite QR. change (sr_get (mdbd_fin_sr p) 9) with (SOff 60 0). cbn [sv_denot]. rewrite U60.
  unfold w64. f_equal; lia. }
assert (Q18 : getr (ms_regs ms1) 18 = w64 WS_MASK).
{ rewrite QR. change (sr_get (mdbd_fin_sr p) 18) with (SLit WS_MASK). reflexivity. }
assert (Q19 : getr (ms_regs ms1) 19 = w64 SHADOW_OFF).
{ rewrite QR. change (sr_get (mdbd_fin_sr p) 19) with (SOff 32 0). cbn [sv_denot].
  rewrite EO by (unfold AT_FL; lia). rewrite E32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (Q20 : getr (ms_regs ms1) 20 = w64 32).
{ rewrite QR. change (sr_get (mdbd_fin_sr p) 20) with (SLit 32). reflexivity. }
assert (Q24 : getr (ms_regs ms1) 24 = getr regs 24).
{ rewrite QR. change (sr_get (mdbd_fin_sr p) 24) with (SOff 555 0). cbn [sv_denot].
  rewrite X24, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q27 : getr (ms_regs ms1) 27 = w64 (shadow_addr (d_FB cx))).
{ rewrite QR. change (sr_get (mdbd_fin_sr p) 27) with (SOff 529 0). cbn [sv_denot]. rewrite U529.
  unfold w64. f_equal; lia. }
assert (HRL1 : d_rL B cx (ms_regs ms1)).
{ split; [unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia|].
  split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [exact Q8|].
  split; [exact Q9|]. split; [exact Q19|]. split; [exact Q18|]. split; [exact Q20|]. exact Q27. }
pose proof (st_ok_mem_ok SEGS _ _ _ HS1) as (_ & HMOK & _).
cbn [ss_mem abs_ss setpc restrict ms_mem] in HMOK.
apply existsb_exists in Hxr. destruct Hxr as (rx & Hrx & Hcov).
pose proof (proj1 (Forall_forall _ _) HMOK rx Hrx) as Hrxok.
pose proof (mdbd_cover_ok SEGS (d_env cx E vals) _ AT_A 368 376 0 0 (mdbd_c368 p) rx Hcov Hrxok
  ltac:(intros o Ho; lia)) as RX.
pose proof (field_of_region (d_env cx E vals) _ 60 (d_A cx) (mdbd_c368 p) 368 376 0 0 368 8%N (SLit (p + 1)) (p + 1)
  RX U60 (in_eq _ _) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V368.
pose proof (KVA 184 h ltac:(lia) ltac:(lia) ltac:(lia) V184) as V184'.
pose proof (KVA 120 (h + 440) ltac:(lia) ltac:(lia) ltac:(lia) V120) as V120'.
pose proof (KVA 136 0 ltac:(lia) ltac:(lia) ltac:(lia) V136) as V136'.
pose proof (KVA 376 (dnot (d_obj cx OG)) ltac:(lia) ltac:(lia) ltac:(lia) V376) as V376'.
pose proof (KVA 280 (dnot (d_obj cx OT)) ltac:(lia) ltac:(lia) ltac:(lia) V280) as V280'.
pose proof (KVA 232 (dnot (d_obj cx OO)) ltac:(lia) ltac:(lia) ltac:(lia) V232) as V232'.
pose proof (KVA 264 (dnot (d_obj cx OUSED)) ltac:(lia) ltac:(lia) ltac:(lia) V264) as V264'.
assert (HCTX1 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms1) md' k)
  by exact (conj HBASE (conj HJ1 HFR)).
destruct (DLAND LAWS FFL fq cx h dsh_ser2 ly3 S3 W md' k (d_env cx E vals) _ ms1
  HCTX1 HE' (d_env_fl cx E vals) HS1 Hchk V184' V120' V136' V376' V280' V232' V264') as (HFRM1 & HSHD1).
assert (HBODY1 : d_body B cx h n (a3_xb buf op) dsh_ser2 ly3 S3 W (ms_mem ms1)).
{ apply (DBRT cx h n n (a3_xb buf op) dsh_age dsh_ser2 ly3 S3 W mem3 (ms_mem ms1)
    (d_A cx + 368) (d_A cx + 376) (fun a => (d_A cx + 368 <= a < d_A cx + 376) \/ d_fsh cx a) HBODY).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a [Ha | Ha]; [left; exact Ha | right].
    unfold d_fsh in Ha. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha.
    exact (mdbd_fsh_nrd cx h a GFapp ltac:(lia) ltac:(lia) HhA HpA Hro Ha).
  - intros a Ha Hna. apply KM; [exact Ha | |].
    + intros H'. apply Hna. left. exact H'.
    + intros H'. apply Hna. right. unfold d_fsh. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. exact H'.
  - intros a _ Ha. eapply apresent_grows; [exact HG1 | exact Ha].
  - exact HFRM1.
  - exact HSHD1.
  - lia. }
pose proof HSP1 as ((H208 & H320) & H192 & H200).
pose proof HSP0 as (S208 & S320).
assert (HSP0' : d_sp0 cx i now W (ms_mem ms1)).
{ split; [apply KVA; [lia | lia | lia | exact S208] | apply KVA; [lia | lia | lia | exact S320]]. }
assert (HSP1' : d_sp1 cx i n now W (ms_mem ms1)).
{ split; [exact HSP0'|].
  split; [apply KVA; [lia | lia | lia | exact H192] | apply KVA; [lia | lia | lia | exact H200]]. }
assert (HTAB' : a3_tab cx now T0 T1 W (ms_mem ms1)).
{ split; [exact (proj1 HTAB)|].
  apply KGF; [unfold d_obj, dobj_off; lia | | exact HGT].
  rewrite length_map, HLT1. cbn [Z.of_nat]. unfold d_obj, dobj_off. lia. }
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS1 Hrv). rewrite Hpc.
apply SRr_ret.
destruct tk.
- assert (Hne : p + 1 <> count).
  { rewrite branch_ne_U in Htk. apply negb_true_iff in Htk. apply Z.eqb_neq in Htk.
    rewrite (U_lit _ (p + 1) ltac:(lia)) in Htk. rewrite U_SOff, UCNT, Z.add_0_r in Htk.
    first [ rewrite zcanon_id in Htk by (rewrite M64_val; lia)
          | rewrite YP0m.zcanon_small in Htk by lia ]. exact Htk. }
  left. split; [lia|].
  unfold f_ph, a3f_st. split; [exact Hfrom|]. unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms1), (ms_mem ms1), md', k, acc.
  split; [reflexivity|].
  split; [exact Hfrm|].
  split; [exact HBASE|]. split; [exact HJ1|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split; [exact HRL1|].
  split; [split; [rewrite Q24; exact R24 | exact I]|].
  split.
  { split; [exact HSP1'|].
    split; [exact HTAB'|].
    split.
    { split; [exact Hr2|]. apply KGB; [|exact HGB]. rewrite Lb. lia. }
    split; [exact HJR|]. split; [exact HVP|].
    split.
    { apply KGF; [unfold d_obj, dobj_off; lia | | exact HOO].
      rewrite length_map. unfold d_obj, dobj_off. lia. }
    split.
    { split; [lia|]. split; [exact V368|]. apply KVA; [lia | lia | lia | exact H360]. }
    apply KGF; [unfold d_obj, dobj_off; lia | | exact HUSED].
    rewrite LU. cbn [Z.of_nat]. unfold d_obj, dobj_off. lia. }
  split; [exact HSP0'|].
  exact HBODY1.
- right. unfold r14_in. split; [exact Hfrom|]. unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms1), (ms_mem ms1), md', k, acc.
  split; [reflexivity|].
  split; [exact Hfrm|].
  split; [exact HBASE|]. split; [exact HJ1|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split; [exact HRL1|].
  split; [split; [exact Q27 | rewrite Q24; exact R24]|].
  split; [split; [exact HSP1' | exact HTAB']|].
  split; [exact HSP0'|].
  exact HBODY1.
Qed.

Theorem a3f_mdbD : forall p, 0 <= p < 8 -> mdbD_stmt B MT XM_LIB RLO RHI tfib_K p.
Proof. intros p Hp. exact (mdbd_main p Hp (mdbd_run p Hp)). Qed.

End h.
End f.
End d.

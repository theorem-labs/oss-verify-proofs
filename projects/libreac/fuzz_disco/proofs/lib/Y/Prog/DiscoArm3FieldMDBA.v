(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's list_push, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v (allocator call sites) and lib/A/ACbk.v (entry and return). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_list_push.v, with its module paths and module names changed; 616 of its 666 lines of code are new or changed and 1541 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3FieldMDA2.v, with its module paths and numbers changed; 568 of its 651 lines of code are new or changed and 583 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require
DiscoArm3FieldModel DiscoArm3FieldMDFacts DiscoArm3FieldMDKit ReacDiscoTableAge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3FieldMDBKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c reac_disco_table_json_c disco_json_text disco_json_reader_model slot_ser_defs slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition MDA_NOW : nat := 563%nat.
Definition MDA_LS : nat := 564%nat.

Definition mdba_srx (r : nat) : sv := match r with 27%nat => SOff AT_SH 0 | _ => a3f_srx 0 r end.
Definition mdba_sr (p : Z) : list sv :=
  sr_set (map mdba_srx (seq 0 32)) 22%bv (SOff AT_F (2160 + 48 * p)).
Definition mdba_a3 (tk : bool) : sv :=
  if tk then SLit 0 else
  SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_ADD (SOff MDA_NOW 0) (SMd M_MUL (SOff MDA_LS 0) (SLit (-1))))
    (SLit a3f_KDV)) (SLit 18).
Definition mdba_finx (tk : bool) (r : nat) : sv :=
  match r with
  | 1%nat => SOff A_TEXT MDS_OFF
  | 10%nat => SOff AT_F 2064
  | 11%nat => SLit 24
  | 12%nat => SOff (A_OBJ 18) 0
  | 13%nat => mdba_a3 tk
  | 21%nat => SOff AT_F 2064
  | _ => mdba_srx r
  end.
Definition mdba_fin_sr (p : Z) (tk : bool) : list sv :=
  sr_set (map (mdba_finx tk) (seq 0 32)) 22%bv (SOff AT_F (2160 + 48 * p)).

Definition mdba_acs : list YP09.chunk := [YP09.mkChunk 320 (CVal 8 (SOff MDA_NOW 0))].
Definition mdba_fcs (p : Z) : list YP09.chunk := [YP09.mkChunk (2200 + 48 * p) (CVal 8 (SOff MDA_LS 0))].
Definition mdba_x : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 17)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit a3f_KDV))].
Definition mdba_rs4 (p : Z) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ mdba_acs);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ mdba_fcs p);
   YP09.mkRegion (Some AT_SH) 0 (fs_frame_bytes DFRAME_CLASS / 8) 258 261 (dsh_chunks dsh_md)].
Definition mdba_rs (p : Z) : smem := mdba_x :: mdba_rs4 p.
Definition mdba_al (p : Z) : sv * sv :=
  (SAlu ALU_ADD (SAlu ALU_SRL (SOff AT_F (2200 + 48 * p)) (SLit 3)) (SOff 32 0), SOff AT_SH (275 + 6 * p)).
Definition mdba_G (p : Z) : facts := mkFacts (d_atoms ++ []) [] (mdba_al p :: d_alias).
Definition mdba_ss0 (p : Z) : sstate := mkSS MO_OFF (mdba_sr p) (mdba_rs p) None (mdba_G p).

Lemma mdba_subw : forall b lo hi wlo whi wlo' whi' cs,
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) ->
  subregion (YP09.mkRegion b lo hi wlo' whi' cs) (YP09.mkRegion b lo hi wlo whi cs).
Proof.
  intros b lo hi wlo whi wlo' whi' cs Hw. unfold subregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hw|]. intros c Hc. exact Hc.
Qed.
Lemma mdba_subrefl : forall r, subregion r r.
Proof. intros [b lo hi wlo whi cs]. apply mdba_subw. lia. Qed.
Lemma mdba_submem : forall p, submem (mdba_rs4 p) (d_kregions dsh_md mdba_acs (mdba_fcs p) ++ []).
Proof.
  intros p. unfold mdba_rs4, d_kregions, fshadow_region. rewrite app_nil_r.
  apply submem_keep; [apply mdba_subrefl|].
  apply submem_keep; [apply mdba_subw; lia|].
  apply submem_keep; [apply mdba_subw; lia|].
  apply submem_keep; [apply mdba_subw; unfold DFRAME_SH; lia|].
  apply submem_nil.
Qed.
Lemma mdba_wf4 : forall p, 0 <= p < 8 -> regions_wf (mdba_rs4 p) = true.
Proof.
  intros p Hp. assert (E : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma mdba_xwf : region_wf mdba_x = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mdba_kwf : forall p, 0 <= p < 8 -> regions_wf (d_kregions dsh_md mdba_acs (mdba_fcs p) ++ []) = true.
Proof.
  intros p Hp. assert (E : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma mdba_inw : forall E p a, in_wrange E (mdba_rs p) a ->
  base_val E (Some AT_SH) + 258 <= a < base_val E (Some AT_SH) + 261.
Proof.
  intros E p a (r & Hin & Hr). unfold mdba_rs, mdba_rs4 in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    unfold mdba_x in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.
Lemma mdba_awr_skel : forall E rs rs' STK sp0 FP bl0 blc ly own,
  awr_ok E rs' STK sp0 FP bl0 blc ly own -> skeleton rs = skeleton rs' -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
  intros E rs rs' STK sp0 FP bl0 blc ly own H Hsk a Ha. apply H. eapply in_wrange_skeleton; [exact Hsk | exact Ha].
Qed.

Lemma mdba_alias_eq : forall (E : env) (fb p : Z),
  0 <= p < 8 -> 4096 <= fb -> fb + 4096 <= 2 ^ 47 -> fb mod 32 = 0 ->
  bv_unsigned (ew E AT_F) = fb -> bv_unsigned (ew E 32) = SHADOW_OFF ->
  bv_unsigned (ew E AT_SH) = shadow_addr fb ->
  sv_denot E (fst (mdba_al p)) = sv_denot E (snd (mdba_al p)).
Proof.
  intros E fb p Hp H1 H2 H32 HF HS HSH. apply U_inj. unfold mdba_al. cbn [fst snd].
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite !U_SOff, U_SLit, HF, HS, HSH.
  rewrite (zcanon_id 3) by (unfold M64; lia).
  change (Z.land 3 63) with 3.
  rewrite (zcanon_id (fb + (2200 + 48 * p))) by (unfold M64; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (zcanon_id ((fb + (2200 + 48 * p)) / 8)) by (unfold M64; lia).
  rewrite (zcanon_id (SHADOW_OFF + 0)) by (unfold SHADOW_OFF, M64; lia).
  unfold shadow_addr, SHADOW_OFF, zcanon, M64. f_equal. lia.
Qed.

Lemma mdba_u8_range : forall (T : list byte) (k : Z), 0 <= disco_table_c.u_at T k 8 < 2 ^ 64.
Proof.
  intros T k. pose proof (DiscoArm3FieldMDFacts.mdf_u_at_range T k 8) as H.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in H. exact H.
Qed.

Lemma mdba_age_denot : forall E x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> y < x ->
  U E (SOff MDA_NOW 0) = x -> U E (SOff MDA_LS 0) = y ->
  sv_denot E (mdba_a3 false) = Z_to_bv 64 ((x - y) / 1000000).
Proof.
  intros E x y Hx Hy Hxy H3 H4.
  transitivity (Z_to_bv 64 (U E (mdba_a3 false))); [unfold U; symmetry; apply Z_to_bv_bv_unsigned|].
  f_equal. cbn [mdba_a3].
  rewrite !U_SAlu, !U_SMd, !U_SAlu, !U_SMd, H3, H4, !U_SLit.
  cbn [zalu_raw zmd_raw]. change (Z.of_N 64) with 64.
  unfold zcanon, M64.
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  replace (a3f_KDV mod 2 ^ 64) with a3f_KDV by reflexivity.
  replace (Z.land (18 mod 2 ^ 64) 63) with 18 by reflexivity.
  assert (E1 : (x + (y * (2 ^ 64 - 1)) mod 2 ^ 64) mod 2 ^ 64 = x - y).
  { rewrite Z.add_mod_idemp_r by lia. replace (x + y * (2 ^ 64 - 1)) with ((x - y) + y * 2 ^ 64) by ring.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  rewrite E1. rewrite !Z.shiftr_div_pow2 by lia.
  assert (HK : 0 <= a3f_KDV < 2 ^ 64) by (unfold a3f_KDV; lia).
  assert (HM : 0 <= (x - y) * a3f_KDV / 2 ^ 64 < 2 ^ 64).
  { split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite (Z.mod_small ((x - y) * a3f_KDV / 2 ^ 64)) by exact HM.
  assert (HD : 0 <= (x - y) * a3f_KDV / 2 ^ 64 / 2 ^ 18 < 2 ^ 64).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite (Z.mod_small _ _ HD).
  exact (DiscoArm3FieldModel.a3f_quot (x - y) ltac:(lia)).
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma mdba_app_nsh : forall F lo n x, in_app lo n -> 0 <= F -> F + 4096 <= CEIL_MAX ->
  lo <= x < lo + n -> ~ (shadow_addr F <= x < shadow_addr F + 512).
Proof.
  intros F lo n x Ha HF0 HF1 Hx Hs. unfold in_app, kLowShadowBeg, kHighMemBeg in Ha.
  unfold shadow_addr, SHADOW_OFF in Hs. destruct Ha as (Ha1 & [Ha2 | (Ha2 & _)]); lia.
Qed.

Lemma mdba_env_reg : forall cx E regs ex (r : bv 5) a, a = (AT_X + Z.to_nat (bv_unsigned r))%nat ->
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

Lemma mdba_regs_ok : forall cx E regs ex p, d_E cx E -> d_rL B cx regs ->
  getr regs 22 = w64 (d_obj cx OT + 48 * p) ->
  0 <= d_FB cx -> d_FB cx + 4096 <= 2 ^ 47 ->
  regs_ok (d_env cx E (a3f_vals regs ++ ex)) (mdba_sr p) regs.
Proof.
  intros cx E regs ex p HE HL R22 HF0 HF1.
  pose proof (d_E_env cx E (a3f_vals regs ++ ex) HE) as HE'.
  destruct HE' as (HER & H32 & _ & HA60 & HAF & HSH). unfold AT_A in HA60. unfold AT_SH in HSH.
  destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
  unfold mdba_sr. apply regs_ok_pin.
  - apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
    repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
    all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
           let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    all: cbn [sv_denot].
    all: first
      [ rewrite getr_zero; reflexivity
      | rewrite HSH, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H27
      | rewrite HA60, Z.add_0_r, Z_to_bv_bv_unsigned;
        first [ rewrite <- Hsp; unfold spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity | exact H9 ]
      | rewrite (HER 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, H8; unfold w64, d_S, spZ;
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | rewrite H32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H19
      | exact H18
      | exact H20
      | match goal with |- getr ?rg ?x = Z_to_bv 64 (bv_unsigned (ew ?Ex ?a) + 0) =>
          rewrite (mdba_env_reg cx E regs ex x a eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ].
  - intros Hq. apply (f_equal bv_unsigned) in Hq. vm_compute in Hq. discriminate Hq.
  - cbn [sv_denot]. rewrite HAF. unfold w64. rewrite unsigned_lit_small by lia.
    rewrite R22. unfold w64, d_obj, dobj_off. f_equal. lia.
Qed.

Lemma mdba_fsh_nrd : forall (cx : dcx) h a,
  in_app (d_FB cx) 4096 -> 0 <= d_FB cx -> d_FB cx + 4096 <= CEIL_MAX -> in_app h 480 ->
  (0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))) ->
  (forall x, in_roP SEGS pa_relro_lo pa_relro_hi x -> 0 <= x < kLowMemEnd) ->
  shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> ~ d_rdset B cx h a.
Proof.
  intros cx h a HF HF0 HF1 Hh Hp Hro Ha Hr.
  unfold d_rdset, d_objr, d_obj in Hr. cbn [dobj_off dobj_size] in Hr. unfold HUNT_SIZE in Hr.
  destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | [(Hc & Hr) | [Hr | Hr]]]]]]].
  - exact (mdba_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdba_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdba_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdba_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdba_app_nsh (d_FB cx) h 480 a Hh HF0 HF1 ltac:(lia) Ha).
  - pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq).
    exact (mdba_app_nsh (d_FB cx) (c_p cx) (req_size (c_n cx)) a (Hp Hc) HF0 HF1 ltac:(lia) Ha).
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
Hypothesis DROH : d_ro_hyps B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.

Definition mdba_run_stmt (p : Z) : Prop :=
  forall (fq : YK11.FPState) (W : world SEGS) (E : env) (ms : machine_state) (mdc : Model)
    STK sp0 FP ly S W0 mem md own lyc Sc k (Q : world SEGS -> config -> Prop),
  img_env VAL A_LIM E ->
  st_ok_pi (fx := fq) SEGS VAL E (mdba_ss0 p) (restrict (w_H W) ms) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  awr_ok E (mdba_rs p) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall (tk : bool) (ss : sstate) (ms' : machine_state) (mat' : list word),
     branch_taken BC_GEU (sv_denot E (SOff MDA_LS 0)) (sv_denot E (SOff MDA_NOW 0)) = tk ->
     ss_regs ss = mdba_fin_sr p tk -> ss_resv ss = None ->
     d_land_chk dsh_age (ss_mem ss) = true ->
     YP0l.st_ok (fx := fq) SEGS E (YP0l.setpc ss (SIGMA AS___interceptor_trampoline_snprintf))
       (restrict (w_H W) ms') ->
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms')
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     frame_of E (mdba_rs p) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.

Ltac mdba_call RUNC HS HJ :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of RUNC with
    | forall W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
      let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
      lazymatch r with
      | (?ss', PRS_call ?s) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', PRS_call s)) by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "mdba_call: no img_env" end in
        eapply (RUNC W FUEL E ss ss' s ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ);
        [ clear Hrun
        | clear Hrun HS HJ;
          let ms' := fresh "ms" in let mat := fresh "mat" in
          let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
          intros ms' mat HS HJ HF HFr HG; cbn [ms_mem YK11.mkst] in HF, HFr, HG, HJ ]
      | (?ss', ?st) => fail "mdba_call: not a call:" st
      end
    end
  | _ => fail "mdba_call: HS must be st_ok_pi"
  end.

Ltac mdba_post POST HS HJ HF2 HG2 HFr1 HG1 Hc tk :=
  rewrite wvb_collapse in HJ; rewrite wvb_collapse;
  lazymatch type of HS with
  | YP0l.st_ok _ _ (YP0l.setpc ?s _) _ =>
    apply (POST tk s _ _ Hc ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) HS HJ);
    [ refine (frame_of_trans _ _ _ _ _ _ _ HFr1 HF2); vm_compute; reflexivity
    | exact (mem_grows_trans _ _ _ HG1 HG2) ]
  end.

Ltac mdba_fin POST HS HJ tk :=
  lazymatch goal with
  | HFr2 : frame_of _ _ (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)),
    HFra : frame_of _ _ (mrestrict _ (ms_mem ?m0)) (mrestrict _ (ms_mem ?m1)),
    HG2 : mem_grows (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)),
    HGa : mem_grows (mrestrict _ (ms_mem ?m0)) (mrestrict _ (ms_mem ?m1)),
    Hc : branch_taken _ _ _ = _ |- _ => mdba_post POST HS HJ HFr2 HG2 HFra HGa Hc tk
  end.

Ltac mdba_walk RUNTOP RUNC BR HS HJ Hawr POST :=
  paj_run_to_shc RUNTOP HS HJ MDS_OFF;
  [ exact Hawr
  | psrr_branch_pi RUNC BR HS;
    [ mdba_call RUNC HS HJ;
      [ apply (mdba_awr_skel _ _ _ _ _ _ _ _ _ _ Hawr); vm_compute; reflexivity
      | mdba_fin POST HS HJ true ]
    | mdba_call RUNC HS HJ;
      [ apply (mdba_awr_skel _ _ _ _ _ _ _ _ _ _ Hawr); vm_compute; reflexivity
      | mdba_fin POST HS HJ false ] ] ].

Lemma mdba_run : forall p, 0 <= p < 8 -> mdba_run_stmt p.
Proof.
  intros p Hp8 fq W E ms mdc STK sp0 FP ly S W0 mem md own lyc Sc k Q HEI HS HJ Hawr POST.
  pose proof (SRr_run_to_pi_AJ (fx := fq) (PI := PI) B LAWS) as RUNTOP.
  pose proof (SRr_run_pi_AJ_call (fx := fq) (PI := PI) B LAWS) as RUNC.
  pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
  assert (Hp : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct Hp as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
  - mdba_walk RUNTOP RUNC BR HS HJ Hawr POST.
  - mdba_walk RUNTOP RUNC BR HS HJ Hawr POST.
  - mdba_walk RUNTOP RUNC BR HS HJ Hawr POST.
  - mdba_walk RUNTOP RUNC BR HS HJ Hawr POST.
  - mdba_walk RUNTOP RUNC BR HS HJ Hawr POST.
  - mdba_walk RUNTOP RUNC BR HS HJ Hawr POST.
  - mdba_walk RUNTOP RUNC BR HS HJ Hawr POST.
  - mdba_walk RUNTOP RUNC BR HS HJ Hawr POST.
Qed.

Lemma mdba_main : forall p, 0 <= p < 8 -> mdba_run_stmt p -> mdbA_stmt B MT XM_LIB RLO RHI tfib_K p.
Proof.
intros p Hp8 RUNJ cx h i n now op W0 c0 T0 T1 buf count os vpad W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R24 & R22) & HX & HSP0 & HBODY).
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
pose proof HBODY as (TT & GG & LL & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTKF & HAWRF).
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
destruct (DCRO LAWS DROH ly3 S3 W mem3 md3 HAR3 HIMG) as (_ & _ & _ & HSTR & _).
destruct HSTR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K17 & R17).
assert (HLS : val_mem SEGS (rd W mem3) (d_FB cx + (2200 + 48 * p)) 8 (disco_table_c.last_of T1 p)).
{ replace (d_FB cx + (2200 + 48 * p)) with (d_obj cx OT + (48 * p + 40)) by (unfold d_obj, dobj_off; lia).
  unfold disco_table_c.last_of.
  apply (ReacDiscoTableAge.ta_vm_of_ga (rd W mem3) (d_obj cx OT) T1 (48 * p + 40) 8 HGT); [lia|].
  rewrite HLT1. cbn [Z.of_nat]. lia. }
assert (HLSr : 0 <= disco_table_c.last_of T1 p < 2 ^ 64)
  by (unfold disco_table_c.last_of; apply mdba_u8_range).
set (vals := a3f_vals regs ++ [Z_to_bv 64 now; Z_to_bv 64 (disco_table_c.last_of T1 p)]).
assert (Lv : length vals = 34%nat)
  by (unfold vals, a3f_vals; rewrite length_app, length_map, length_seq; reflexivity).
assert (E563 : ew (d_env cx E vals) MDA_NOW = Z_to_bv 64 now)
  by (unfold MDA_NOW; exact (d_env_x cx E vals 32 ltac:(rewrite Lv; lia))).
assert (E564 : ew (d_env cx E vals) MDA_LS = Z_to_bv 64 (disco_table_c.last_of T1 p))
  by (unfold MDA_LS; exact (d_env_x cx E vals 33 ltac:(rewrite Lv; lia))).
assert (EO : forall nn, (nn < AT_FL)%nat -> ew (d_env cx E vals) nn = ew E nn)
  by (intros nn Hnn; apply d_env_old; exact Hnn).
pose proof HE as (EE & E32 & HEI0 & E60 & EF & ESH).
pose proof (d_E_env cx E vals HE) as HE'.
assert (HEI : img_env VAL A_LIM (d_env cx E vals)) by exact (proj1 (proj2 (proj2 HE'))).
assert (U60 : bv_unsigned (ew (d_env cx E vals) AT_A) = d_A cx)
  by (rewrite EO by (unfold AT_FL, AT_A; lia); rewrite E60; apply unsigned_lit_small; lia).
assert (U516 : bv_unsigned (ew (d_env cx E vals) AT_F) = d_FB cx)
  by (rewrite EO by (unfold AT_FL, AT_F; lia); rewrite EF; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew (d_env cx E vals) 32) = SHADOW_OFF)
  by (rewrite EO by (unfold AT_FL; lia); rewrite E32; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U529 : bv_unsigned (ew (d_env cx E vals) AT_SH) = shadow_addr (d_FB cx))
  by (rewrite EO by (unfold AT_FL, AT_SH; lia); rewrite ESH; unfold w64; apply unsigned_lit_small;
      unfold shadow_addr, SHADOW_OFF; lia).
assert (U563 : U (d_env cx E vals) (SOff MDA_NOW 0) = now) by (apply U_atom; [exact E563 | lia]).
assert (U564 : U (d_env cx E vals) (SOff MDA_LS 0) = disco_table_c.last_of T1 p)
  by (apply U_atom; [exact E564 | exact HLSr]).
assert (U17 : bv_unsigned (ew (d_env cx E vals) (A_OBJ 17)) = VAL (A_OBJ 17))
  by (apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (HI17 : in_img SEGS (VAL (A_OBJ 17))).
{ destruct (R17 (VAL (A_OBJ 17)) ltac:(lia)) as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr]. }
assert (HI17b : in_img SEGS (VAL (A_OBJ 17) + 7)).
{ destruct (R17 (VAL (A_OBJ 17) + 7) ltac:(lia)) as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr]. }
pose proof (pa_img_range _ HI17) as HR17. pose proof (pa_img_range _ HI17b) as HR17b.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HR17, HR17b.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in GFoff.
assert (Hregs : regs_ok (d_env cx E vals) (mdba_sr p) regs)
  by (unfold vals; apply (mdba_regs_ok cx E regs _ p HE HRL R22); lia).
assert (HGf : facts_ok (d_env cx E vals) (d_facts [] []))
  by exact (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HCTX HE I I).
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) mdba_acs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 320 8%N (SOff MDA_NOW 0) now).
  - cbn [sv_denot]. rewrite E563, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - exact (proj2 HSP0). }
assert (Hfcs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_FB cx)) (mdba_fcs p)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_FB cx) (2200 + 48 * p) 8%N (SOff MDA_LS 0) (disco_table_c.last_of T1 p)).
  - cbn [sv_denot]. rewrite E564, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - exact HLS. }
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E MO_OFF (mdba_sr p) vals mdba_acs (mdba_fcs p)
  [] (d_facts [] []) HCTX HE HREG HFLAG Hregs HGf Hacs Hfcs (Forall_nil _) I (Forall_nil _)
  (mdba_kwf p Hp8)) as HS0.
cbn [ss_d ss_pc ss_regs ss_resv ss_facts ss_mem] in HS0.
pose proof (st_ok_pi_add_alias (fx := fq) (d_env cx E vals) _ _ (fst (mdba_al p)) (snd (mdba_al p)) HS0
  (mdba_alias_eq (d_env cx E vals) (d_FB cx) p Hp8 ltac:(lia) ltac:(lia) GF32 U516 U32 U529)) as HS1.
clear HS0. cbn [ss_pc ss_regs ss_resv ss_facts ss_mem set_facts f_atoms f_conds f_alias d_facts] in HS1.
pose proof (st_ok_pi_submem _ _ _ (mdba_rs4 p) HS1 (mdba_submem p) (mdba_wf4 p Hp8)) as HS2.
clear HS1. cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS2.
assert (HX17 : region_ok SEGS (d_env cx E vals) (rd W mem3) mdba_x).
{ unfold region_ok, mdba_x. cbv zeta.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U17. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (VAL (A_OBJ 17)) 0 8%N (SLit a3f_KDV) a3f_KDV).
  - reflexivity.
  - unfold a3f_KDV. cbn. lia.
  - cbn. lia.
  - rewrite Z.add_0_r. exact K17. }
assert (U2 : bv_unsigned (ew (d_env cx E vals) AT_STK) = d_S cx).
{ change AT_STK with 2%nat. rewrite EO by (unfold AT_FL; lia).
  rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
assert (HD17 : all_disjoint (d_env cx E vals) mdba_x (mdba_rs4 p)).
{ unfold mdba_rs4, mdba_x, all_disjoint, extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U17, U60, U516, U529, U2.
  change (fs_frame_bytes DFRAME_CLASS) with 4096. change (4096 / 8) with 512.
  unfold shadow_addr, SHADOW_OFF.
  repeat split; first [exact I | lia]. }
pose proof (st_ok_pi_add_region (fx := fq) (d_env cx E vals) _ _ mdba_x HS2 mdba_xwf
  ltac:(cbn [ms_mem restrict YK11.mkst]; exact HX17) HD17) as HS.
clear HS2. cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS.
assert (Hawr : awr_ok (d_env cx E vals) (mdba_rs p) LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx))
  (ablocks B ly3 S3) ly3 [(DFRAME_CLASS, c_fpos cx)]).
{ unfold mdba_rs, mdba_rs4.
  apply awr_ok_cons_ro; [unfold mdba_x; cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ AT_SH (shadow_addr (d_FB cx))); [reflexivity | exact U529 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
    exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia. }
  apply awr_ok_nil. }
unfold cfg_at, w64.
apply (RUNJ fq W (d_env cx E vals) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + MO_OFF)) mem3 (YK11.seg_rom SEGS))
  md3 LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 k _
  HEI HS HJ Hawr).
intros tk ss ms1 mat1 Htk Hsr Hrv Hchk HS1 HJ1 HFr1 HG1.
cbn [ms_mem YK11.mkst] in HFr1, HG1.
set (md' := with_vm_backing (m_vm_lazy md3) mat1 md3) in *.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha H2. apply (aview_eq_of SEGS). apply HFr1. rewrite unsigned_lit_small by lia.
  intros Hw. apply mdba_inw in Hw.
  change (base_val (d_env cx E vals) (Some AT_SH)) with (bv_unsigned (ew (d_env cx E vals) AT_SH)) in Hw.
  rewrite U529 in Hw. lia. }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
  mbyte SEGS (rd W (ms_mem ms1)) a = mbyte SEGS (rd W mem3) a)
  by (intros a Ha H2; apply (mbyte_of_aview SEGS); apply KM; assumption).
assert (KVA : forall off v, 0 <= off -> off + 8 <= 472 ->
  val_mem SEGS (rd W mem3) (d_A cx + off) 8 v -> val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + off) 8 v).
{ intros off v H0 H1 Hv. apply (val_mem_frame SEGS (rd W mem3)); [|exact Hv].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KB; [lia|].
  unfold shadow_addr, SHADOW_OFF. lia. }
assert (KGF : forall a l, d_FB cx <= a -> a + Z.of_nat (length l) <= d_FB cx + 4096 ->
  garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms1)) a l).
{ intros a l H0 H1 Hg. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|]. intros x Hx.
  apply KB; [lia|]. exact (mdba_app_nsh (d_FB cx) (d_FB cx) 4096 x GFapp ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (KGB : forall l, Z.of_nat (length l) <= req_size (Z.max (slot_ser_defs.ser_cap op) 1) ->
  garr8 SEGS (rd W mem3) buf l -> garr8 SEGS (rd W (ms_mem ms1)) buf l).
{ intros l H1 Hg. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|]. intros x Hx.
  apply KB; [lia|]. exact (mdba_app_nsh (d_FB cx) buf _ x Hbapp ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (QR : forall r, getr (ms_regs ms1) r = sv_denot (d_env cx E vals) (sr_get (mdba_fin_sr p tk) r)).
{ intros r. rewrite (YA0o.st_ok_restrict_reg SEGS (w_H W) (d_env cx E vals) _ ms1 r HS1).
  cbn [YP0l.setpc ss_regs]. rewrite Hsr. reflexivity. }
assert (QA : forall (r : bv 5) (a : nat), a = (AT_X + Z.to_nat (bv_unsigned r))%nat ->
  sr_get (mdba_fin_sr p tk) r = SOff a 0 -> getr (ms_regs ms1) r = getr regs r).
{ intros r a Ha Hs. rewrite QR, Hs. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  unfold vals. exact (mdba_env_reg cx E regs _ r a Ha). }
assert (Q3 : getr (ms_regs ms1) 3 = getr regs 3) by exact (QA 3%bv 534%nat eq_refl eq_refl).
assert (Q4 : getr (ms_regs ms1) 4 = getr regs 4) by exact (QA 4%bv 535%nat eq_refl eq_refl).
assert (Q24 : getr (ms_regs ms1) 24 = getr regs 24) by exact (QA 24%bv 555%nat eq_refl eq_refl).
assert (Q2 : getr (ms_regs ms1) 2 = w64 (d_A cx)).
{ rewrite QR. change (sr_get (mdba_fin_sr p tk) 2) with (SOff AT_A 0). cbn [sv_denot]. rewrite U60.
  unfold w64. f_equal; lia. }
assert (Q8 : getr (ms_regs ms1) 8 = w64 (d_S cx)).
{ rewrite QR. change (sr_get (mdba_fin_sr p tk) 8) with (SOff AT_STK 0). cbn [sv_denot].
  rewrite U2. unfold w64. f_equal; lia. }
assert (Q9 : getr (ms_regs ms1) 9 = w64 (d_A cx)).
{ rewrite QR. change (sr_get (mdba_fin_sr p tk) 9) with (SOff AT_A 0). cbn [sv_denot]. rewrite U60.
  unfold w64. f_equal; lia. }
assert (Q18 : getr (ms_regs ms1) 18 = w64 WS_MASK).
{ rewrite QR. change (sr_get (mdba_fin_sr p tk) 18) with (SLit WS_MASK). reflexivity. }
assert (Q19 : getr (ms_regs ms1) 19 = w64 SHADOW_OFF).
{ rewrite QR. change (sr_get (mdba_fin_sr p tk) 19) with (SOff 32 0). cbn [sv_denot].
  rewrite U32, Z.add_0_r. reflexivity. }
assert (Q20 : getr (ms_regs ms1) 20 = w64 32).
{ rewrite QR. change (sr_get (mdba_fin_sr p tk) 20) with (SLit 32). reflexivity. }
assert (Q27 : getr (ms_regs ms1) 27 = w64 (shadow_addr (d_FB cx))).
{ rewrite QR. change (sr_get (mdba_fin_sr p tk) 27) with (SOff AT_SH 0). cbn [sv_denot]. rewrite U529.
  unfold w64. f_equal; lia. }
assert (Q1 : getr (ms_regs ms1) 1 = w64 (BASE + MDS_OFF)).
{ rewrite QR. change (sr_get (mdba_fin_sr p tk) 1) with (SOff A_TEXT MDS_OFF).
  rewrite (codeptr_val _ MDS_OFF HEI). reflexivity. }
assert (Q10 : getr (ms_regs ms1) 10 = w64 (d_obj cx OAGE)).
{ rewrite QR. change (sr_get (mdba_fin_sr p tk) 10) with (SOff AT_F 2064). cbn [sv_denot]. rewrite U516.
  unfold w64, d_obj, dobj_off. f_equal; lia. }
assert (Q21 : getr (ms_regs ms1) 21 = w64 (d_obj cx OAGE)).
{ rewrite QR. change (sr_get (mdba_fin_sr p tk) 21) with (SOff AT_F 2064). cbn [sv_denot]. rewrite U516.
  unfold w64, d_obj, dobj_off. f_equal; lia. }
assert (Q11 : getr (ms_regs ms1) 11 = w64 24).
{ rewrite QR. change (sr_get (mdba_fin_sr p tk) 11) with (SLit 24). reflexivity. }
assert (Q12 : getr (ms_regs ms1) 12 = w64 (VAL (A_OBJ 18))).
{ rewrite QR. change (sr_get (mdba_fin_sr p tk) 12) with (SOff (A_OBJ 18) 0). cbn [sv_denot].
  rewrite (HEI (A_OBJ 18) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Z.add_0_r. reflexivity. }
assert (Q13 : getr (ms_regs ms1) 13 = w64 (a3f_age T1 now p)).
{ rewrite QR. change (sr_get (mdba_fin_sr p tk) 13) with (mdba_a3 tk).
  rewrite branch_geu_U, U564, U563 in Htk.
  unfold a3f_age, disco_json_text.age_of.
  destruct tk.
  - apply negb_true_iff, Z.ltb_ge in Htk.
    replace (disco_table_c.last_of T1 p <? now) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  - apply negb_false_iff, Z.ltb_lt in Htk.
    rewrite (proj2 (Z.ltb_lt _ _) Htk).
    rewrite (mdba_age_denot (d_env cx E vals) now (disco_table_c.last_of T1 p) Hnow HLSr Htk U563 U564).
    reflexivity. }
assert (HRL1 : d_rL B cx (ms_regs ms1)).
{ split; [unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia|].
  split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [exact Q8|].
  split; [exact Q9|]. split; [exact Q19|]. split; [exact Q18|]. split; [exact Q20|]. exact Q27. }
assert (HS1p : st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals)
  (YP0l.setpc ss (SIGMA AS___interceptor_trampoline_snprintf - BASE)) (restrict (w_H W) ms1)).
{ unfold st_ok_pi, abs_ss, YP0l.setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
  replace (BASE + (SIGMA AS___interceptor_trampoline_snprintf - BASE))
    with (SIGMA AS___interceptor_trampoline_snprintf) by lia.
  exact HS1. }
assert (HCTX1 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms1) md' k)
  by exact (conj HBASE (conj HJ1 HFR)).
assert (HHS1 : d_hslots cx h W (ms_mem ms1)).
{ apply (d_hslots_kept cx h W W mem3 (ms_mem ms1));
    [intros a Ha; apply KM; [lia | unfold shadow_addr, SHADOW_OFF; lia]
    | exact (d_hslots_of_frame cx h dsh_md W mem3 HFRM)]. }
destruct (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fq cx h dsh_age ly3 S3 W md' k
  (d_env cx E vals) _ ms1 HCTX1 HE' (d_env_fl cx E vals) HS1p Hchk HHS1) as (HFRM1 & HSHD1).
assert (HBODY1 : d_body B cx h n (a3_xb buf op) dsh_age ly3 S3 W (ms_mem ms1)).
{ apply (DBRT cx h n n (a3_xb buf op) dsh_md dsh_age ly3 S3 W mem3 (ms_mem ms1)
    (d_A cx) (d_A cx) (d_fsh cx) HBODY).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a Ha. right.
    unfold d_fsh in Ha. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha.
    exact (mdba_fsh_nrd cx h a GFapp ltac:(lia) ltac:(lia) HhA HpA Hro Ha).
  - intros a Ha Hna. apply KM; [exact Ha|].
    intros H'. apply Hna. unfold d_fsh. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. exact H'.
  - intros a _ Ha. eapply apresent_grows; [exact HG1 | exact Ha].
  - exact HFRM1.
  - exact HSHD1.
  - lia. }
pose proof HSP1 as ((H208 & H320) & H192 & H200).
pose proof HSP0 as (S208 & S320).
assert (HSP0' : d_sp0 cx i now W (ms_mem ms1))
  by (split; [apply KVA; [lia | lia | exact S208] | apply KVA; [lia | lia | exact S320]]).
assert (HSP1' : d_sp1 cx i n now W (ms_mem ms1)).
{ split; [exact HSP0'|].
  split; [apply KVA; [lia | lia | exact H192] | apply KVA; [lia | lia | exact H200]]. }
assert (HTAB' : a3_tab cx now T0 T1 W (ms_mem ms1)).
{ split; [exact (proj1 HTAB)|].
  apply KGF; [unfold d_obj, dobj_off; lia | | exact HGT].
  rewrite length_map, HLT1. cbn [Z.of_nat]. unfold d_obj, dobj_off. lia. }
rewrite (YA0o.st_ok_restrict_mkst SEGS (w_H W) (d_env cx E vals) _ ms1 HS1 ltac:(cbn [YP0l.setpc ss_resv]; exact Hrv)).
apply SRr_ret.
unfold mdb_c1, a3f_st. split; [exact Hfrom|].
unfold d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms1), (ms_mem ms1), md', k, acc.
split.
{ unfold cfg_at, w64. cbn [ss_pc YP0l.setpc].
  replace (BASE + (SIGMA AS___interceptor_trampoline_snprintf - BASE))
    with (SIGMA AS___interceptor_trampoline_snprintf) by lia.
  reflexivity. }
split; [exact Hfrm|].
split; [exact HBASE|]. split; [exact HJ1|]. split; [exact HFR|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split; [exact HRL1|].
split.
{ split; [rewrite Q24; exact R24|].
  split; [exact Q1|]. split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|].
  split; [exact Q13|]. exact Q21. }
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
  { split; [lia|]. split; [apply KVA; [lia | lia | exact H368] | apply KVA; [lia | lia | exact H360]]. }
  split; [apply KVA; [lia | lia | exact H408]|].
  apply KGF; [unfold d_obj, dobj_off; lia | | exact HUSED].
  rewrite LU. cbn [Z.of_nat]. unfold d_obj, dobj_off. lia. }
split; [exact HSP0'|].
exact HBODY1.
Qed.

Theorem a3f_mdbA : forall p, 0 <= p < 8 -> mdbA_stmt B MT XM_LIB RLO RHI tfib_K p.
Proof. intros p Hp. exact (mdba_main p Hp (mdba_run p Hp)). Qed.

End h.
End f.
End d.

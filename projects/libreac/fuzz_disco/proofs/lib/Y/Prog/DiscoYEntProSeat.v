(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 163 of its 193 lines of code are new or changed and 515 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/TjLoopCuts.v, with its module paths and module names changed; 218 of its 249 lines of code are new or changed and 162 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YP0l YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_master_only_cadence_ns_c reac_rate_snap_c
reac_frame_clean_len_c slot_inv slot_frame reac_hunt_verdict_name_c disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryInv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0e YP02 YP0k YP06 YP03 YP04 YP01 YP00 YP0i YA0o YCbm YA0q YE00 YC5d YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntSeatStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntSeat DiscoYEntProCuts.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Theorem p_seat : AR_laws SEGS B -> PALib B ->
  forall (fq : YK11.FPState) (cx : dcx) (shf : Z -> Z) (acs0 : list YP09.chunk) ly3 S3 (W3 : world SEGS)
    (regs : bvmap 5 word) mem3 md3 k (E : env) (pc : Z) (sr : list sv) (vals : list word)
    (acs fcs : list YP09.chunk) (extra : smem) (G : facts),
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_E cx E -> Forall (region_ok SEGS E (rd W3 mem3)) (p_regions shf acs0) ->
  rdword (aview SEGS (w_H W3) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
    Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  regs_ok (d_env cx E vals) sr regs ->
  facts_ok (d_env cx E vals) G ->
  Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W3 mem3) (d_A cx)) acs ->
  Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W3 mem3) (d_FB cx)) fcs ->
  Forall (region_ok SEGS (d_env cx E vals) (rd W3 mem3)) extra ->
  pairwise_disjoint (d_env cx E vals) extra ->
  Forall (fun r => all_disjoint (d_env cx E vals) r (p_kregions shf (acs0 ++ acs) fcs)) extra ->
  regions_wf (p_kregions shf (acs0 ++ acs) fcs ++ extra) = true ->
  YP06.region_atoms_lt AT_FL (YP09.mkRegion (Some AT_A) 0 472 0 472 acs0) = true ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) (ss_p pc sr shf (acs0 ++ acs) fcs extra G)
    (restrict (w_H W3) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) mem3 (YK11.seg_rom SEGS))).
Proof.
  intros LAWS TL fq cx shf acs0 ly3 S3 W3 regs mem3 md3 k E pc sr vals acs fcs extra G HC HE HRG HFL Hregs HG
    Hacs Hfcs Hext Hpde Hdx Hwf Hat.
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
    as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
  pose proof asan_consts as (Hac & _).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
  pose proof (rdword_aview_range _ _ _ _ _ HFL) as HFLr.
  destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell & _ & Kgot & _).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
  pose proof (pal_got_cell B TL) as Hgc.
  pose proof (pa_obj_img 0 ltac:(vm_compute; lia)) as HO0. pose proof (pa_obj_img 12 ltac:(vm_compute; lia)) as HO12.
  pose proof (pa_val_range (A_OBJ 0)) as HV0. pose proof (pa_val_range (A_OBJ 12)) as HV12.
  unfold IMG_LO, IMG_TOP in HO0, HO12. unfold off_img, IMG_LO, IMG_TOP in HFo.
  set (E' := d_env cx E vals) in *.
  pose proof (d_env_agree cx E vals) as HAG. fold E' in HAG.
  pose proof (d_env_fl cx E vals) as EFL. fold E' in EFL.
  destruct (d_E_env cx E vals HE) as (EE & E32 & HEI & E60 & EF & ESH). fold E' in EE, E32, HEI, E60, EF, ESH.
  assert (Hd0 : 0 <= d_FB cx / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : d_FB cx / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  assert (U2 : base_val E' (Some AT_STK) = d_S cx).
  { cbn [base_val]. unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
  assert (U60 : base_val E' (Some AT_A) = d_A cx).
  { cbn [base_val]. rewrite E60. apply unsigned_lit_small. unfold MFRAME, LLVMF_STK in *. lia. }
  assert (U516 : base_val E' (Some AT_F) = d_FB cx).
  { cbn [base_val]. rewrite EF. apply unsigned_lit_small. lia. }
  assert (U529 : base_val E' (Some AT_SH) = shadow_addr (d_FB cx)).
  { cbn [base_val]. rewrite ESH. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
  assert (EA : forall n, (A_TEXT <= n < A_LIM)%nat -> base_val E' (Some n) = VAL n).
  { intros n Hn. cbn [base_val]. rewrite (img_env_atomP E' n HEI Hn). apply unsigned_lit_small. apply pa_val_range. }
  assert (UG0 : base_val E' (Some (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply EA; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (UG12 : base_val E' (Some (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply EA; unfold A_OBJ, A_TEXT, A_LIM; lia).
  unfold p_regions in HRG.
  pose proof (Forall_inv HRG) as R1. apply Forall_inv_tail in HRG.
  pose proof (Forall_inv HRG) as R2. apply Forall_inv_tail in HRG.
  pose proof (Forall_inv HRG) as R3. apply Forall_inv_tail in HRG.
  pose proof (Forall_inv HRG) as R4. clear HRG.
  lazymatch type of R1 with region_ok _ _ ?m ?r =>
    assert (R1x : region_ok SEGS E' m r) by (apply (region_ok_agree SEGS AT_FL E E' m r HAG); [vm_compute; reflexivity | exact R1]) end.
  clear R1. rename R1x into R1.
  lazymatch type of R2 with region_ok _ _ ?m ?r =>
    assert (R2x : region_ok SEGS E' m r) by (apply (region_ok_agree SEGS AT_FL E E' m r HAG); [exact Hat | exact R2]) end.
  clear R2. rename R2x into R2.
  lazymatch type of R3 with region_ok _ _ ?m ?r =>
    assert (R3x : region_ok SEGS E' m r) by (apply (region_ok_agree SEGS AT_FL E E' m r HAG); [vm_compute; reflexivity | exact R3]) end.
  clear R3. rename R3x into R3.
  lazymatch type of R4 with region_ok _ _ ?m ?r =>
    assert (R4x : region_ok SEGS E' m r) by (apply (region_ok_agree SEGS AT_FL E E' m r HAG); [vm_compute; reflexivity | exact R4]) end.
  clear R4. rename R4x into R4.
  unfold ss_p. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact Hregs.
  - exact Hwf.
  - apply Forall_app. split; [|exact Hext].
    unfold p_kregions. repeat apply Forall_cons; try apply Forall_nil.
    + exact R1.
    + destruct R2 as (B1 & B2 & W2 & C2). unfold region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in B1, B2, W2, C2 |- *.
      split; [exact B1|]. split; [exact B2|]. split; [exact W2|]. apply Forall_app. split; [exact C2|].
      rewrite U60. exact Hacs.
    + destruct R3 as (B1 & B2 & W2 & C2). unfold region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in B1, B2, W2, C2 |- *.
      split; [exact B1|]. split; [exact B2|]. split; [exact W2|]. apply Forall_app. split; [|rewrite U516; exact Hfcs].
      unfold dfhdr_chunks.
      apply Forall_cons; [exact (Forall_inv C2)|]. apply Forall_inv_tail in C2.
      apply Forall_cons; [exact (Forall_inv C2)|]. apply Forall_inv_tail in C2.
      apply Forall_cons; [exact (Forall_inv C2)|]. apply Forall_cons; [|apply Forall_nil].
      rewrite U516.
      apply (chunk_ok_val SEGS E' _ (d_FB cx) 4088 8%N (SOff AT_FL 0) (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx))).
      * cbn [sv_denot]. rewrite EFL, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * cbn [Z.of_N]. change (8 * 8) with 64. exact HFLr.
      * cbn [Z.of_N]. lia.
      * cbn [N.to_nat]. change (fs_frame_bytes DFRAME_CLASS) with 4096 in HFL.
        replace (d_FB cx + 4088) with (d_FB cx + 4096 - 8) by lia.
        exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ HFL).
    + exact R4.
    + unfold got_regionP, region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite UG0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E' _ (VAL (A_OBJ 0)) 0 8%N (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12))).
      * cbn [sv_denot]. rewrite (img_env_atomP E' (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
        rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      * cbn [Z.of_N]. change (8 * 8) with 64. lia.
      * cbn [Z.of_N]. lia.
      * cbn [N.to_nat]. rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ Kgot).
    + unfold bcell_regionP, region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite UG12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E' _ (VAL (A_OBJ 12)) 0 8%N (SOff 32 0) SHADOW_OFF).
      * cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
        rewrite Z.add_0_r. reflexivity.
      * cbn [Z.of_N]. change (8 * 8) with 64. unfold SHADOW_OFF. lia.
      * cbn [Z.of_N]. lia.
      * cbn [N.to_nat]. rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ Kcell).
  - apply pwd_app; [| exact Hpde | exact Hdx].
    apply pairwise_disjoint_of_extents.
    unfold p_kregions, fshadow_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite U2, U60, U516, U529, UG0, UG12.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. change (4096 / 8) with 512.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold shadow_addr, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, MFRAME, LLVMF_STK in *.
    repeat split; lia.
  - exact HG.
Qed.
Theorem p_land : AR_laws SEGS B -> frame_flag_lawP SEGS B ->
  forall (fq : YK11.FPState) (cx : dcx) (shf : Z -> Z) (acs : list YP09.chunk) ly3 S3 (W3 : world SEGS) md3 k
    (E : env) (ss : sstate) (ms : machine_state),
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 (ms_mem ms) md3 k ->
  d_E cx E -> ew E AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W3) ms) ->
  p_land_chk shf acs (ss_mem ss) = true ->
  p_frame cx shf acs W3 (ms_mem ms) /\ d_shadow cx shf W3 (ms_mem ms).
Proof.
  intros LAWS FFL fq cx shf acs ly3 S3 W3 md3 k E ss ms HC HE HE530 HS Hchk.
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
    as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
  pose proof asan_consts as (Hac & _).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
  destruct (FFL ly3 S3 W3 (ms_mem ms) md3 DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as (_ & _ & HFLr).
  rewrite Efl in HFLr.
  pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
  assert (Hd0 : 0 <= d_FB cx / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : d_FB cx / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  assert (U2 : base_val E (Some AT_STK) = d_S cx).
  { cbn [base_val]. unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
  assert (U60 : base_val E (Some AT_A) = d_A cx).
  { cbn [base_val]. rewrite E60. apply unsigned_lit_small. unfold MFRAME, LLVMF_STK in *. lia. }
  assert (U516 : base_val E (Some AT_F) = d_FB cx).
  { cbn [base_val]. rewrite EF. apply unsigned_lit_small. lia. }
  assert (U529 : base_val E (Some AT_SH) = shadow_addr (d_FB cx)).
  { cbn [base_val]. rewrite ESH. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
  pose proof (st_ok_mem_ok _ _ _ _ HS) as (_ & Hrs & _).
  cbn [abs_ss setpc ss_mem] in Hrs.
  change (ms_mem (restrict (w_H W3) ms)) with (rd W3 (ms_mem ms)) in Hrs.
  unfold p_land_chk in Hchk.
  apply andb_prop in Hchk as [Hchk Hc4]. apply andb_prop in Hchk as [Hchk Hc3]. apply andb_prop in Hchk as [Hc1 Hc2].
  apply existsb_exists in Hc1 as (r1 & Hr1 & Hc1). apply existsb_exists in Hc2 as (r2 & Hr2 & Hc2).
  apply existsb_exists in Hc3 as (r3 & Hr3 & Hc3). apply existsb_exists in Hc4 as (r4 & Hr4 & Hc4).
  pose proof (proj1 (Forall_forall _ _) Hrs _ Hr1) as R1. pose proof (proj1 (Forall_forall _ _) Hrs _ Hr2) as R2.
  pose proof (proj1 (Forall_forall _ _) Hrs _ Hr3) as R3. pose proof (proj1 (Forall_forall _ _) Hrs _ Hr4) as R4.
  assert (Hb4 : YP09.r_base r4 = Some AT_SH).
  { unfold sh_region_ok in Hc4. apply andb_prop in Hc4 as [Hc4 _]. apply andb_prop in Hc4 as [Hc4 _].
    apply andb_prop in Hc4 as [Hc4 _]. destruct (YP09.r_base r4) as [n|]; [|discriminate Hc4].
    cbn [obase_eqb] in Hc4. apply Nat.eqb_eq in Hc4. subst n. reflexivity. }
  pose proof (sh_region_bytes _ _ _ shf r4 Hc4 R4) as HSB. rewrite Hb4, U529 in HSB.
  assert (FR : region_ok SEGS E (rd W3 (ms_mem ms))
    (YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 DFRAME_SIZE dfhdr_chunks)).
  { apply (region_cover_ok _ _ _ _ _ _ _ _ _ r3 Hc3 R3). rewrite U516. intros o Ho.
    apply (apresent_writable SEGS). apply HFpres. unfold DFRAME_SIZE in Ho. lia. }
  destruct FR as (_ & _ & _ & FC). cbn [YP09.r_base YP09.r_chunks] in FC. rewrite U516 in FC.
  unfold dfhdr_chunks in FC.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail FC)))) as CFL.
  pose proof (val_of_chunk_ok SEGS E _ (d_FB cx) 4088 8%N (SOff AT_FL 0) (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx))
    CFL ltac:(cbn [sv_denot]; rewrite HE530, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(cbn [Z.of_N]; change (8 * 8) with 64; lia) ltac:(cbn [Z.of_N]; lia)) as VFL.
  split.
  - exists E. split; [exact HE|]. split.
    + unfold p_regions. repeat apply Forall_cons; try apply Forall_nil.
      * apply (region_cover_ok _ _ _ _ _ _ _ _ _ r1 Hc1 R1). intros o Ho. lia.
      * apply (region_cover_ok _ _ _ _ _ _ _ _ _ r2 Hc2 R2). rewrite U60. intros o Ho.
        apply (apresent_writable SEGS). apply HWpres. unfold MFRAME, LLVMF_STK in *. lia.
      * pose proof (region_cover_ok _ _ _ _ _ _ 0 DFRAME_SIZE _ r3 Hc3 R3) as FR.
        rewrite U516 in FR. specialize (FR ltac:(intros o Ho; apply (apresent_writable SEGS); apply HFpres;
          unfold DFRAME_SIZE in Ho; lia)).
        destruct FR as (F1 & F2 & F3 & F4). unfold region_ok. cbv zeta.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in F1, F2, F3, F4 |- *.
        split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. unfold dfhdr_chunks in F4. unfold dfhdr3.
        apply Forall_cons; [exact (Forall_inv F4)|]. apply Forall_inv_tail in F4.
        apply Forall_cons; [exact (Forall_inv F4)|]. apply Forall_inv_tail in F4.
        apply Forall_cons; [exact (Forall_inv F4)|]. apply Forall_nil.
      * unfold region_ok, fshadow_region. cbv zeta.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite U529. change (fs_frame_bytes DFRAME_CLASS / 8) with 512.
        split; [unfold shadow_addr, SHADOW_OFF; lia|]. split; [unfold shadow_addr, SHADOW_OFF; lia|]. split.
        -- intros o Ho. apply (apresent_writable SEGS). apply HSpres. unfold DFRAME_SH in Ho. lia.
        -- apply dsh_chunks_ok. exact HSB.
    + change (fs_frame_bytes DFRAME_CLASS) with 4096. replace (d_FB cx + 4096 - 8) with (d_FB cx + 4088) by lia.
      apply rdword_of_val_mem; [exact VFL | lia].
  - intros kk Hk. destruct (HSB kk Hk) as (Hr & Hm). unfold aview. rewrite Hm. cbn [option_map].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. f_equal. apply Z.mod_small. exact Hr.
Qed.
End h.
End f.
End d.

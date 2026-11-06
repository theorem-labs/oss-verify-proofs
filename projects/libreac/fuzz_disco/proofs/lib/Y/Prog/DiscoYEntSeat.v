(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, with its module paths, module names and numbers changed; 356 of its 490 lines of code are new or changed and 232 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntProA.v, with its module paths and module names changed; 384 of its 440 lines of code are new or changed and 434 lines of the source are left out. *)
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
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma cval_eqb_eq : forall a b, cval_eqb a b = true -> a = b.
Proof.
  intros [w v|l|l|d s l] [w' v'|l'|l'|d' s' l']; cbn [cval_eqb]; intros H; try discriminate H.
  - apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1. apply sv_eqb_eq in H2. subst. reflexivity.
  - apply Z.eqb_eq in H. subst. reflexivity.
  - apply Z.eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.
Lemma chunk_eqb_eq : forall a b, chunk_eqb a b = true -> a = b.
Proof.
  intros [o v] [o' v']. unfold chunk_eqb. cbn [YP09.c_off YP09.c_val]. intros H.
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply cval_eqb_eq in H2. subst. reflexivity.
Qed.
Lemma chunks_cover_Forall : forall (P : YP09.chunk -> Prop) tgt src,
  chunks_cover tgt src = true -> Forall P src -> Forall P tgt.
Proof.
  intros P tgt src H Hs. unfold chunks_cover in H. apply Forall_forall. intros c Hc.
  pose proof (proj1 (forallb_forall _ _) H c Hc) as Hx. apply existsb_exists in Hx as (c' & Hin & He).
  apply chunk_eqb_eq in He. subst c'. exact (proj1 (Forall_forall _ _) Hs c Hin).
Qed.
Lemma extent_disjoint_sym : forall E r r', extent_disjoint E r r' -> extent_disjoint E r' r.
Proof. unfold extent_disjoint. intros E r r' H. lia. Qed.
Lemma all_disjoint_Forall : forall E r rs, all_disjoint E r rs <-> Forall (extent_disjoint E r) rs.
Proof.
  intros E r rs. induction rs as [|x rs IH]; cbn [all_disjoint].
  - split; intros _; [constructor | exact I].
  - split.
    + intros [H1 H2]. constructor; [exact H1 | apply IH; exact H2].
    + intros H. inversion H as [|? ? H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.
Lemma pwd_app : forall E l1 l2, pairwise_disjoint E l1 -> pairwise_disjoint E l2 ->
  Forall (fun r => all_disjoint E r l1) l2 -> pairwise_disjoint E (l1 ++ l2).
Proof.
  intros E l1. induction l1 as [|x l1 IH]; intros l2 H1 H2 H3; cbn [app]; [exact H2|].
  cbn [pairwise_disjoint] in H1 |- *. destruct H1 as [Hx H1]. split.
  - apply all_disjoint_Forall. apply Forall_app. split; [apply all_disjoint_Forall; exact Hx|].
    apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) H3 r Hr) as Hd.
    cbn [all_disjoint] in Hd. apply extent_disjoint_sym. exact (proj1 Hd).
  - apply IH; [exact H1 | exact H2 |]. apply Forall_forall. intros r Hr.
    pose proof (proj1 (Forall_forall _ _) H3 r Hr) as Hd. cbn [all_disjoint] in Hd. exact (proj2 Hd).
Qed.
Lemma region_cover_ok : forall segs E m b lo hi wlo whi tgt r,
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
  exact (chunks_cover_Forall _ tgt rcs Hc H4).
Qed.
Lemma byte_of_word_lit : forall v i, byte_of_word (Z_to_bv 64 v) i = Z_to_bv 8 (Z.shiftr (v mod 2 ^ 64) (8 * i)).
Proof. intros v i. unfold byte_of_word. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma Z_to_bv_mod8 : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H. Qed.
Lemma sh_region_bytes : forall segs E m shf r, sh_region_ok shf r = true -> region_ok segs E m r ->
  forall k, 0 <= k < DFRAME_SH ->
  0 <= shf k < 256 /\ mbyte segs m (base_val E (YP09.r_base r) + k) = Some (Z_to_bv 8 (shf k)).
Proof.
  intros segs E m shf r H (_ & _ & _ & H4) k Hk.
  unfold sh_region_ok in H. apply andb_prop in H as [_ Hall].
  assert (Hin : In (Z.to_nat k) (seq 0 (Z.to_nat DFRAME_SH))) by (apply in_seq; unfold DFRAME_SH in *; lia).
  pose proof (proj1 (forallb_forall _ _) Hall _ Hin) as Hb. cbv beta in Hb. rewrite Z2Nat.id in Hb by lia.
  unfold sh_byte_ok in Hb.
  destruct (find_chunk (YP09.r_chunks r) k 1) as [c|] eqn:Hf; [|discriminate Hb].
  destruct c as [o cv]. destruct cv as [w v|l|l|d s l]; try discriminate Hb.
  destruct v; try discriminate Hb.
  apply andb_prop in Hb as [Hb Hlt]. apply andb_prop in Hb as [Heq Hge].
  apply Z.eqb_eq in Heq. apply Z.leb_le in Hge. apply Z.ltb_lt in Hlt.
  split; [lia|].
  destruct (find_chunk_sound _ _ _ _ Hf) as (Hc & Ho & Hol). cbn [YP09.c_off YP09.c_len YP09.c_val cv_len] in Ho, Hol.
  pose proof (proj1 (Forall_forall _ _) H4 _ Hc) as Hck.
  destruct (Hck (k - o) ltac:(cbn [YP09.c_len YP09.c_val cv_len]; lia)) as (b & Hb1 & Hb2).
  cbn [YP09.c_off YP09.c_val cbyte sv_denot] in Hb1, Hb2.
  replace (base_val E (YP09.r_base r) + o + (k - o)) with (base_val E (YP09.r_base r) + k) in Hb2 by lia.
  rewrite Hb2. injection Hb1 as <-. f_equal. rewrite byte_of_word_lit. apply Z_to_bv_mod8.
  rewrite Heq. symmetry. apply Z.mod_small. lia.
Qed.
Lemma dsh_chunks_ok : forall segs E m base shf,
  (forall k, 0 <= k < DFRAME_SH -> 0 <= shf k < 256 /\ mbyte segs m (base + k) = Some (Z_to_bv 8 (shf k))) ->
  Forall (YP09.chunk_ok segs E m base) (dsh_chunks shf).
Proof.
  intros segs E m base shf H. unfold dsh_chunks. apply Forall_forall. intros c Hc.
  apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
  assert (Hk : 0 <= Z.of_nat j < DFRAME_SH) by (unfold DFRAME_SH in *; lia).
  destruct (H _ Hk) as (Hr & Hm).
  intros i Hi. unfold YP09.c_len, cv_len in Hi. cbn [YP09.c_val Z.of_N] in Hi.
  assert (i = 0) by lia. subst i.
  exists (Z_to_bv 8 (shf (Z.of_nat j))). cbn [YP09.c_off YP09.c_val cbyte sv_denot]. split.
  - f_equal. rewrite byte_of_word_lit. apply Z_to_bv_mod8.
    rewrite Z.mul_0_r, Z.shiftr_0_r, (Z.mod_small (shf (Z.of_nat j)) (2 ^ 64)) by lia. reflexivity.
  - rewrite Z.add_0_r. exact Hm.
Qed.
Lemma aview_range : forall segs H m a b, aview segs H m a = Some b -> 0 <= b < 256.
Proof.
  intros segs H m a b Hv. unfold aview in Hv. destruct (mbyte segs (mrestrict H m) a) as [x|]; [|discriminate Hv].
  cbn [option_map] in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range _ x) as Hr.
  change (bv_modulus 8) with 256 in Hr. exact Hr.
Qed.
Lemma rdword_aview_range : forall segs H m a v, rdword (aview segs H m) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
  intros segs H m a v Hv. unfold rdword in Hv.
  destruct (aview segs H m a) as [b0|] eqn:E0; [|discriminate Hv].
  destruct (aview segs H m (a + 1)) as [b1|] eqn:E1; [|discriminate Hv].
  destruct (aview segs H m (a + 2)) as [b2|] eqn:E2; [|discriminate Hv].
  destruct (aview segs H m (a + 3)) as [b3|] eqn:E3; [|discriminate Hv].
  destruct (aview segs H m (a + 4)) as [b4|] eqn:E4; [|discriminate Hv].
  destruct (aview segs H m (a + 5)) as [b5|] eqn:E5; [|discriminate Hv].
  destruct (aview segs H m (a + 6)) as [b6|] eqn:E6; [|discriminate Hv].
  destruct (aview segs H m (a + 7)) as [b7|] eqn:E7; [|discriminate Hv].
  injection Hv as <-.
  apply aview_range in E0, E1, E2, E3, E4, E5, E6, E7. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Lemma d_env_old : forall cx E vals n, (n < AT_FL)%nat -> ew (d_env cx E vals) n = ew E n.
Proof. intros cx E vals n Hn. unfold d_env. apply ew_havoc_old. exact Hn. Qed.
Lemma d_env_fl : forall cx E vals,
  ew (d_env cx E vals) AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
Proof.
  intros cx E vals. unfold d_env. replace AT_FL with (AT_FL + 0)%nat at 2 by lia.
  rewrite (ew_havoc_new _ AT_FL _ 0 (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.
Lemma d_env_x : forall cx E vals j, (j < length vals)%nat ->
  ew (d_env cx E vals) (AT_X + j) = nth j vals (Z_to_bv 64 0).
Proof.
  intros cx E vals j Hj. unfold d_env. replace (AT_X + j)%nat with (AT_FL + S j)%nat by (unfold AT_X, AT_FL; lia).
  rewrite (ew_havoc_new _ AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.
Lemma d_env_agree : forall cx E vals, env_agree AT_FL E (d_env cx E vals).
Proof. intros cx E vals. split; [intros n Hn; apply d_env_old; exact Hn | reflexivity]. Qed.
Lemma d_E_env : forall cx E vals, d_E cx E -> d_E cx (d_env cx E vals).
Proof.
  intros cx E vals (EE & E32 & HEI & E60 & EF & ESH). unfold d_E.
  rewrite !d_env_old by (unfold AT_FL, AT_A, AT_F, AT_SH; lia).
  split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
  - intros n r Hn. rewrite d_env_old; [exact (EE n r Hn)|].
    pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr. unfold AT_FL. lia.
  - unfold d_env. apply img_env_havoc_hi; [exact HEI | unfold A_LIM, AT_FL; lia].
Qed.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Lemma d_geom : AR_laws SEGS B -> forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_S cx mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= d_S cx /\ d_S cx <= 2 ^ 47 /\
  4096 <= d_FB cx /\ d_FB cx + 4096 <= alloc_ceiling /\ in_app (d_FB cx) 4096 /\
  off_img (d_FB cx) 4096 /\ d_FB cx mod 32 = 0 /\
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> apresent (w_H W3) mem3 a) /\
  (forall i, 0 <= i < 512 -> apresent (w_H W3) mem3 (shadow_addr (d_FB cx) + i)) /\
  (forall a, d_S cx - LLVMF_STK <= a < d_S cx -> apresent (w_H W3) mem3 a) /\
  AR SEGS B ly3 S3 W3 mem3 md3 /\ In (DFRAME_CLASS, c_fpos cx) (frames S3) /\
  frame_addr ly3 DFRAME_CLASS (c_fpos cx) = d_FB cx /\
  flag_addr ly3 DFRAME_CLASS (c_fpos cx) = flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx).
Proof.
  intros LAWS cx ly3 S3 W3 mem3 md3 k (HB & HJ & HFR).
  destruct HB as ((HPRE & _) & _).
  pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  assert (Hfin : In (DFRAME_CLASS, c_fpos cx) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _).
  assert (Efl : flag_addr ly3 DFRAME_CLASS (c_fpos cx) = flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
  { pose proof (Efa 0 0) as E00. unfold frame_addr in E00. unfold flag_addr. lia. }
  destruct (frames_bounds _ _ LAWS _ _ _ _ _ DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as (HF0 & HFc & HFia).
  pose proof (frm_off_imgP B ly3 S3 W3 mem3 md3 DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as HFo.
  destruct (al_frames _ _ LAWS _ _ _ _ _ DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as (Hal & _ & HFpres & HSpres).
  rewrite Efa in HF0, HFc, HFia, HFo, Hal, HFpres, HSpres.
  change (frame_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) with (d_FB cx) in *.
  change (fs_frame_bytes DFRAME_CLASS) with 4096 in *. change (4096 / 8) with 512 in HSpres.
  change (spZ (c_regs cx)) with (d_S cx) in *.
  split; [exact Hal16|]. split; [unfold LLVMF_STK in *; lia|]. split; [lia|].
  split; [exact HF0|]. split; [exact HFc|]. split; [exact HFia|]. split; [exact HFo|]. split; [exact Hal|].
  split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
  split; [intros i Hi; exact (proj1 (HSpres i Hi))|].
  split; [intros a Ha; apply HJpres; exact Ha|].
  split; [exact HAR3|]. split; [exact Hfin|]. split; [rewrite Efa; reflexivity|]. exact Efl.
Qed.
Lemma d_A_range : forall cx, 0 <= d_S cx - MFRAME ->
  d_S cx - MFRAME - 31 <= d_A cx <= d_S cx - MFRAME /\ d_A cx mod 32 = 0.
Proof.
  intros cx Hs. unfold d_A. pose proof (Z.div_mod (d_S cx - MFRAME) 32 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (d_S cx - MFRAME) 32 ltac:(lia)) as Hmp.
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Theorem d_facts_ok : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros LAWS cx ly3 S3 W3 mem3 md3 k E vals fa cs HC HE Hfa Hcs.
  destruct (d_geom LAWS _ _ _ _ _ _ _ HC)
    as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & _ & _ & _ & _ & _ & _ & _).
  pose proof asan_consts as (Hac & _).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
  destruct (d_E_env cx E vals HE) as (EE & E32 & HEI & E60 & EF & ESH).
  unfold facts_ok, d_facts. cbn [f_atoms f_conds f_alias].
  split; [|split; [exact Hcs|]].
  - apply atoms_ok_app; [|exact Hfa]. unfold d_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    unfold AT_STK, AT_A, AT_F, AT_SH in *.
    rewrite (EE 2%nat 2%bv eq_refl). change (bv_unsigned (getr (c_regs cx) 2)) with (d_S cx).
    rewrite E60, EF, ESH, E32. unfold w64.
    assert (Hd0 : 0 <= d_FB cx / 8) by (apply Z.div_pos; lia).
    assert (Hd1 : d_FB cx / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
    unfold shadow_addr. rewrite !unsigned_lit_small by (unfold MFRAME, LLVMF_STK, SHADOW_OFF in *; lia).
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 2) with 4. rewrite Z.pow_0_r, Z.mod_1_r.
    unfold SB, SHADOW_OFF, MFRAME, LLVMF_STK in *.
    assert (HF8lo : 512 <= d_FB cx / 8) by (apply Z.div_le_lower_bound; lia).
    assert (HFq : d_FB cx = 32 * (d_FB cx / 32)) by (pose proof (Z.div_mod (d_FB cx) 32 ltac:(lia)); lia).
    assert (HF8 : d_FB cx / 8 = 4 * (d_FB cx / 32)).
    { rewrite HFq at 1. replace (32 * (d_FB cx / 32)) with (4 * (d_FB cx / 32) * 8) by lia.
      rewrite Z.div_mul by lia. reflexivity. }
    repeat match goal with |- _ /\ _ => split end; try lia.
    all: rewrite HF8; replace (2147450880 + 4 * (d_FB cx / 32)) with ((536862720 + d_FB cx / 32) * 4) by lia;
      apply Z_mod_mult.
  - cbn [alias_ok d_alias]. split; [|exact I].
    apply (shadow_decl_ok _ AT_F 32 AT_SH (d_FB cx) SHADOW_OFF EF ltac:(lia) E32).
    rewrite ESH. reflexivity.
Qed.
Theorem d_seat : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros LAWS TL fq cx shf ly3 S3 W3 regs mem3 md3 k E pc sr vals acs fcs extra G HC HE HRG HFL Hregs HG
    Hacs Hfcs Hext Hpde Hdx Hwf.
  destruct (d_geom LAWS _ _ _ _ _ _ _ HC)
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
  unfold d_regions in HRG.
  pose proof (Forall_inv HRG) as R1. apply Forall_inv_tail in HRG.
  pose proof (Forall_inv HRG) as R2. apply Forall_inv_tail in HRG.
  pose proof (Forall_inv HRG) as R3. apply Forall_inv_tail in HRG.
  pose proof (Forall_inv HRG) as R4. clear HRG.
  lazymatch type of R1 with region_ok _ _ ?m ?r =>
    assert (R1x : region_ok SEGS E' m r) by (apply (region_ok_agree SEGS AT_FL E E' m r HAG); [vm_compute; reflexivity | exact R1]) end.
  clear R1. rename R1x into R1.
  lazymatch type of R2 with region_ok _ _ ?m ?r =>
    assert (R2x : region_ok SEGS E' m r) by (apply (region_ok_agree SEGS AT_FL E E' m r HAG); [vm_compute; reflexivity | exact R2]) end.
  clear R2. rename R2x into R2.
  lazymatch type of R3 with region_ok _ _ ?m ?r =>
    assert (R3x : region_ok SEGS E' m r) by (apply (region_ok_agree SEGS AT_FL E E' m r HAG); [vm_compute; reflexivity | exact R3]) end.
  clear R3. rename R3x into R3.
  lazymatch type of R4 with region_ok _ _ ?m ?r =>
    assert (R4x : region_ok SEGS E' m r) by (apply (region_ok_agree SEGS AT_FL E E' m r HAG); [vm_compute; reflexivity | exact R4]) end.
  clear R4. rename R4x into R4.
  unfold ss_d. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact Hregs.
  - exact Hwf.
  - apply Forall_app. split; [|exact Hext].
    unfold d_kregions. repeat apply Forall_cons; try apply Forall_nil.
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
    unfold d_kregions, fshadow_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite U2, U60, U516, U529, UG0, UG12.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. change (4096 / 8) with 512.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold shadow_addr, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, MFRAME, LLVMF_STK in *.
    repeat split; lia.
  - exact HG.
Qed.
Theorem d_land : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros LAWS FFL fq cx h shf ly3 S3 W3 md3 k E ss ms HC HE HE530 HS Hchk H184 H120 H136 H376 H280 H232 H264.
  destruct (d_geom LAWS _ _ _ _ _ _ _ HC)
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
  unfold d_land_chk in Hchk.
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
  - exists E. split; [exact HE|]. split; [|split; [|exact (conj H184 (conj H120 (conj H136 (conj H376 (conj H280 (conj H232 H264))))))]].
    + unfold d_regions. repeat apply Forall_cons; try apply Forall_nil.
      * apply (region_cover_ok _ _ _ _ _ _ _ _ _ r1 Hc1 R1). intros o Ho. lia.
      * apply (region_cover_ok _ _ _ _ _ _ _ _ _ r2 Hc2 R2). rewrite U60. intros o Ho.
        apply (apresent_writable SEGS). apply HWpres. unfold MFRAME, LLVMF_STK in *. lia.
      * pose proof (region_cover_ok _ _ _ _ _ _ 0 DFRAME_SIZE _ r3 Hc3 R3) as FR.
        rewrite U516 in FR. specialize (FR ltac:(intros o Ho; apply (apresent_writable SEGS); apply HFpres;
          unfold DFRAME_SIZE in Ho; lia)).
        destruct FR as (F1 & F2 & F3 & F4). unfold region_ok. cbv zeta.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in F1, F2, F3, F4 |- *.
        split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. unfold dfhdr_chunks in F4.
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

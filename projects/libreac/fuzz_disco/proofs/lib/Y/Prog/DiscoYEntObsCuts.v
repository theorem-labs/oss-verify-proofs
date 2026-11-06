(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 903 of its 965 lines of code are new or changed and 1216 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition OB_FE_RET : Z := 0xff0.
Definition OB_TO_RET : Z := 0x1844.
Definition OB_CT_RET : Z := 0x185c.
Definition OB_RO_RET : Z := 0x18a0.
Definition OB_C9 : Z := 0x18a8.
Definition OB_BC_RET : Z := 0x199c.
Definition OB_C10 : Z := 0x1b40.
Definition OB_C12 : Z := 0x1a58.
Definition OB_C9M : Z := 0x1964.

Definition sr_x (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0
  | 18%nat => SLit WS_MASK | 19%nat => SOff 32 0 | 20%nat => SLit 32 | 27%nat => SOff AT_SH 0
  | _ => SOff (AT_X + r) 0
  end.
Definition obs_sr : list sv := map sr_x (seq 0 32).
Definition obs_vals (regs : bvmap 5 word) : list word := map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32).
Definition u64 (z : Z) : Z := z mod 2 ^ 64.
Definition oldv (a v : Z) : Z := if a <? 0 then 0 else v.
Definition OBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma oy_cval_eqb_eq : forall a b, cval_eqb a b = true -> a = b.
Proof.
  intros [w v|l|l|d s l] [w' v'|l'|l'|d' s' l']; cbn [cval_eqb]; intros H; try discriminate H.
  - apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1. apply sv_eqb_eq in H2. subst. reflexivity.
  - apply Z.eqb_eq in H. subst. reflexivity.
  - apply Z.eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.
Lemma oy_chunk_eqb_eq : forall a b, chunk_eqb a b = true -> a = b.
Proof.
  intros [o v] [o' v']. unfold chunk_eqb. cbn [YP09.c_off YP09.c_val]. intros H.
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply oy_cval_eqb_eq in H2. subst. reflexivity.
Qed.
Lemma oy_chunks_cover_Forall : forall (P : YP09.chunk -> Prop) tgt src,
  chunks_cover tgt src = true -> Forall P src -> Forall P tgt.
Proof.
  intros P tgt src H Hs. unfold chunks_cover in H. apply Forall_forall. intros c Hc.
  rewrite forallb_forall in H. specialize (H c Hc). apply existsb_exists in H as (c' & Hc' & Heq).
  apply oy_chunk_eqb_eq in Heq. subst c'. exact (proj1 (Forall_forall _ _) Hs c Hc').
Qed.
Lemma oy_region_cover_ok : forall segs E m b lo hi wlo whi tgt r,
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
  exact (oy_chunks_cover_Forall _ tgt rcs Hc H4).
Qed.
Lemma oy_byte_of_word_lit : forall v i, byte_of_word (Z_to_bv 64 v) i = Z_to_bv 8 (Z.shiftr (v mod 2 ^ 64) (8 * i)).
Proof. intros v i. unfold byte_of_word. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma oy_Z_to_bv_mod8 : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H. Qed.
Lemma oy_sh_region_bytes : forall segs E m shf r, sh_region_ok shf r = true -> region_ok segs E m r ->
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
  rewrite Hb2. injection Hb1 as <-. f_equal. rewrite oy_byte_of_word_lit. apply oy_Z_to_bv_mod8.
  rewrite Heq. symmetry. apply Z.mod_small. lia.
Qed.
Lemma oy_dsh_chunks_ok : forall segs E m base shf,
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
  - f_equal. rewrite oy_byte_of_word_lit. apply oy_Z_to_bv_mod8.
    rewrite Z.mul_0_r, Z.shiftr_0_r, (Z.mod_small (shf (Z.of_nat j)) (2 ^ 64)) by lia. reflexivity.
  - rewrite Z.add_0_r. exact Hm.
Qed.
Lemma oy_aview_range : forall segs H m a b, aview segs H m a = Some b -> 0 <= b < 256.
Proof.
  intros segs H m a b Hv. unfold aview in Hv. destruct (mbyte segs (mrestrict H m) a) as [x|]; [|discriminate Hv].
  cbn [option_map] in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range _ x) as Hr.
  change (bv_modulus 8) with 256 in Hr. exact Hr.
Qed.
Lemma oy_rdword_aview_range : forall segs H m a v, rdword (aview segs H m) a = Some v -> 0 <= v < 2 ^ 64.
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
  apply oy_aview_range in E0, E1, E2, E3, E4, E5, E6, E7. lia.
Qed.
Lemma oy_frame_eq : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hw x. apply HF. intros (r & Hr & Ha).
rewrite forallb_forall in Hw. specialize (Hw r Hr). apply Z.leb_le in Hw. lia.
Qed.
Lemma oy_mrestrict_ext : forall (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall x, mrestrict H m' x = mrestrict H m x.
Proof. intros H m m' HM x. unfold mrestrict. rewrite HM. reflexivity. Qed.
Lemma oy_mbyte_ext : forall segs (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof. intros segs H m m' HM a. unfold mbyte, mrestrict. rewrite HM. reflexivity. Qed.
Lemma oy_aview_ext : forall segs (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, aview segs H m' a = aview segs H m a.
Proof. intros segs H m m' HM a. unfold aview. rewrite (oy_mbyte_ext segs H m m' HM). reflexivity. Qed.
Lemma oy_rok_ext : forall segs E (m m' : word -> option byte) r,
  (forall x, m' x = m x) -> region_ok segs E m r -> region_ok segs E m' r.
Proof.
intros segs E m m' r HM HR. unfold region_ok in *. cbv zeta in *.
destruct HR as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. apply (writable_at_grows segs m m'); [intros x Hx; rewrite HM; exact Hx | exact (H3 o Ho)].
- refine (Forall_impl _ _ H4). intros c Hc i Hi. destruct (Hc i Hi) as (b & Hb & Hm).
  exists b. split; [exact Hb|]. unfold mbyte in *. rewrite HM. exact Hm.
Qed.
Lemma oy_shadow_addr_off : forall F o, F mod 8 = 0 -> shadow_addr (F + o) = shadow_addr F + o / 8.
Proof.
intros F o HF. unfold shadow_addr. pose proof (Z.div_mod F 8 ltac:(lia)) as D.
replace (F + o) with (o + F / 8 * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.
Lemma oy_w64_add_w : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Z.add_mod_idemp_l by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.
Lemma oy_dsh_rec_t : forall k, 270 <= k < 320 -> dsh_rec k = 0.
Proof.
intros k Hk. assert (Hj : exists j, (j < 50)%nat /\ k = 270 + Z.of_nat j) by (exists (Z.to_nat (k - 270)); lia).
destruct Hj as (j & Hj & ->). do 50 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma oy_dsh_rec_s : forall k, 374 <= k < 377 -> dsh_rec k = 0.
Proof.
intros k Hk. assert (Hj : exists j, (j < 3)%nat /\ k = 374 + Z.of_nat j) by (exists (Z.to_nat (k - 374)); lia).
destruct Hj as (j & Hj & ->). do 3 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma oy_u64_small : forall v, 0 <= v < 2 ^ 64 -> u64 v = v.
Proof. intros v Hv. unfold u64. apply Z.mod_small. exact Hv. Qed.
Lemma oy_u64_rng : forall v, 0 <= u64 v < 2 ^ 64.
Proof. intros v. unfold u64. apply Z.mod_pos_bound. lia. Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma oy_d_env_old : forall cx E vals n, (n < AT_FL)%nat -> ew (d_env cx E vals) n = ew E n.
Proof. intros cx E vals n Hn. unfold d_env. apply ew_havoc_old. exact Hn. Qed.
Lemma oy_d_env_fl : forall cx E vals,
  ew (d_env cx E vals) AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
Proof.
  intros cx E vals. unfold d_env. replace AT_FL with (AT_FL + 0)%nat at 2 by lia.
  rewrite (ew_havoc_new _ AT_FL _ 0 (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.
Lemma oy_d_env_x : forall cx E vals j, (j < length vals)%nat ->
  ew (d_env cx E vals) (AT_X + j) = nth j vals (Z_to_bv 64 0).
Proof.
  intros cx E vals j Hj. unfold d_env. replace (AT_X + j)%nat with (AT_FL + S j)%nat by (unfold AT_X, AT_FL; lia).
  rewrite (ew_havoc_new _ AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.
Lemma oy_d_E_env : forall cx E vals, d_E cx E -> d_E cx (d_env cx E vals).
Proof.
  intros cx E vals (EE & E32 & HEI & E60 & EF & ESH). unfold d_E.
  rewrite !oy_d_env_old by (unfold AT_FL, AT_A, AT_F, AT_SH; lia).
  split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
  - intros n r Hn. rewrite oy_d_env_old; [exact (EE n r Hn)|].
    pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr. unfold AT_FL. lia.
  - unfold d_env. apply img_env_havoc_hi; [exact HEI | unfold A_LIM, AT_FL; lia].
Qed.
Lemma oy_d_E_atoms : forall cx E, d_E cx E ->
  ew E AT_A = Z_to_bv 64 (d_A cx) /\ ew E AT_F = Z_to_bv 64 (d_FB cx) /\
  ew E AT_SH = Z_to_bv 64 (shadow_addr (d_FB cx)) /\ ew E 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros cx E (_ & H32 & _ & HA & HF & HS). repeat split; assumption. Qed.
Lemma oy_val_mem_pt : forall (m m' : word -> option byte) a n v, (forall x, m' x = m x) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v Hpt H kk Hk. pose proof (H kk Hk) as H1. unfold mbyte in H1 |- *. rewrite Hpt. exact H1. Qed.
Lemma oy_garr8_pt : forall (m m' : word -> option byte) a l, (forall x, m' x = m x) ->
  garr8 SEGS m a l -> garr8 SEGS m' a l.
Proof. intros m m' a l Hpt H j Hj. destruct (H j Hj) as [H1 H2]. split; [exact (oy_val_mem_pt m m' _ _ _ Hpt H1) | exact H2]. Qed.
Lemma oy_val_mem_keep : forall (W W' : world SEGS) (m m' : word -> option byte) a n v,
  (forall j, (j < n)%nat -> aview SEGS (w_H W') m' (a + Z.of_nat j) = aview SEGS (w_H W) m (a + Z.of_nat j)) ->
  val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W' m') a n v.
Proof. intros W W' m m' a n v Hk H j Hj. rewrite (mbyte_of_aview SEGS _ _ _ _ _ (Hk j Hj)). exact (H j Hj). Qed.
Lemma oy_garr8_keep : forall (W W' : world SEGS) (m m' : word -> option byte) a l,
  (forall j, (j < length l)%nat -> aview SEGS (w_H W') m' (a + Z.of_nat j) = aview SEGS (w_H W) m (a + Z.of_nat j)) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W' m') a l.
Proof.
intros W W' m m' a l Hk H j Hj. destruct (H j Hj) as [H1 H2]. split; [|exact H2].
apply (oy_val_mem_keep W W' m m' _ 1 _); [|exact H1].
intros k Hk'. replace (a + Z.of_nat j + Z.of_nat k) with (a + Z.of_nat j) by lia. exact (Hk j Hj).
Qed.
Lemma oy_region_ok_keep : forall E (W W' : world SEGS) (m m' : word -> option byte) r,
  region_ok SEGS E (rd W m) r ->
  (forall c i, In c (YP09.r_chunks r) -> 0 <= i < YP09.c_len c ->
     aview SEGS (w_H W') m' (base_val E (YP09.r_base r) + YP09.c_off c + i) =
     aview SEGS (w_H W) m (base_val E (YP09.r_base r) + YP09.c_off c + i)) ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> apresent (w_H W') m' (base_val E (YP09.r_base r) + o)) ->
  region_ok SEGS E (rd W' m') r.
Proof.
intros E W W' m m' r (H1 & H2 & H3 & H4) Hc Hp. unfold region_ok.
split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. apply (apresent_writable SEGS). apply Hp. exact Ho.
- rewrite Forall_forall in *. intros c Hin i Hi. destruct (H4 c Hin i Hi) as (b & Hb & Hm).
  exists b. split; [exact Hb|]. rewrite (mbyte_of_aview SEGS _ _ _ _ _ (Hc c i Hin Hi)). exact Hm.
Qed.
Lemma oy_rdword_keep : forall (rd rd' : reader) a, (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold rdword.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma oy_aview_present : forall H (m : word -> option byte) a, apresent H m a -> exists b : byte, aview SEGS H m a = Some (bv_unsigned b).
Proof. intros H m a [Hh [b Hb]]. exists b. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity. Qed.
Lemma oy_ex_val_mem8 : forall H (m : word -> option byte) a, (forall j, 0 <= j < 8 -> apresent H m (a + j)) ->
  exists v, val_mem SEGS (mrestrict H m) a 8 v /\ 0 <= v < 2 ^ 64.
Proof.
intros H m a Hp.
destruct (oy_aview_present H m _ (Hp 0 ltac:(lia))) as [b0 E0]. rewrite Z.add_0_r in E0.
destruct (oy_aview_present H m _ (Hp 1 ltac:(lia))) as [b1 E1]. destruct (oy_aview_present H m _ (Hp 2 ltac:(lia))) as [b2 E2].
destruct (oy_aview_present H m _ (Hp 3 ltac:(lia))) as [b3 E3]. destruct (oy_aview_present H m _ (Hp 4 ltac:(lia))) as [b4 E4].
destruct (oy_aview_present H m _ (Hp 5 ltac:(lia))) as [b5 E5]. destruct (oy_aview_present H m _ (Hp 6 ltac:(lia))) as [b6 E6].
destruct (oy_aview_present H m _ (Hp 7 ltac:(lia))) as [b7 E7].
assert (Hr : exists v, rdword (aview SEGS H m) a = Some v) by (unfold rdword; rewrite E0, E1, E2, E3, E4, E5, E6, E7; eexists; reflexivity).
destruct Hr as [v Hr]. exists v. split; [exact (val_mem_of_rdword SEGS H m a v Hr) | exact (oy_rdword_aview_range SEGS H m a v Hr)].
Qed.
Lemma oy_frame_ext : forall cx h shf (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> d_frame cx h shf W m -> d_frame cx h shf W m'.
Proof.
intros cx h shf W m m' HM (E & HE & HR & HFL & V1 & V2 & V3 & V4 & V5 & V6 & V7).
pose proof (oy_mbyte_ext SEGS (w_H W) m m' HM) as MB.
assert (VM : forall a n v, val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W m') a n v)
  by (intros a n v Hv j Hj; rewrite MB; exact (Hv j Hj)).
exists E. split; [exact HE|]. split.
- refine (Forall_impl _ _ HR). intros r Hr. exact (oy_rok_ext SEGS E _ _ r (oy_mrestrict_ext (w_H W) m m' HM) Hr).
- split.
  + rewrite (rdword_ext (aview SEGS (w_H W) m) (aview SEGS (w_H W) m')); [exact HFL|].
    intros j _. apply oy_aview_ext. exact HM.
  + exact (conj (VM _ _ _ V1) (conj (VM _ _ _ V2) (conj (VM _ _ _ V3) (conj (VM _ _ _ V4)
      (conj (VM _ _ _ V5) (conj (VM _ _ _ V6) (VM _ _ _ V7))))))).
Qed.
Lemma oy_shadow_ext : forall cx shf (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> d_shadow cx shf W m -> d_shadow cx shf W m'.
Proof. intros cx shf W m m' HM Hs j Hj. rewrite (oy_aview_ext SEGS (w_H W) m m' HM). exact (Hs j Hj). Qed.
Lemma oy_d_shadow_keep : forall cx shf (W W' : world SEGS) (m m' : word -> option byte),
  d_shadow cx shf W m ->
  (forall k, 0 <= k < DFRAME_SH -> aview SEGS (w_H W') m' (shadow_addr (d_FB cx) + k) = aview SEGS (w_H W) m (shadow_addr (d_FB cx) + k)) ->
  d_shadow cx shf W' m'.
Proof. intros cx shf W W' m m' H Hk k Hkk. rewrite (Hk k Hkk). exact (H k Hkk). Qed.
Lemma oy_ra_frame : forall cx shf (W : world SEGS) (m : word -> option byte) lo len,
  d_shadow cx shf W m -> d_FB cx mod 8 = 0 -> 0 <= lo -> 0 <= len -> lo + len <= 3072 ->
  (forall k, lo / 8 <= k < (lo + len + 7) / 8 -> shf k = 0) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (d_FB cx + lo) len.
Proof.
intros cx shf W m lo len Hsh HF8 Hlo Hlen Hhi Hz x Hx. exists 0. split; [|left; reflexivity].
assert (Hq : shadow_of_addr SHADOW_OFF x = shadow_addr (d_FB cx) + (x - d_FB cx) / 8).
{ rewrite <- oy_shadow_addr_off by exact HF8. replace (d_FB cx + (x - d_FB cx)) with x by lia. reflexivity. }
rewrite Hq. rewrite (Hsh ((x - d_FB cx) / 8)).
- rewrite Hz; [reflexivity|]. split; [apply Z.div_le_mono; lia|].
  apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.mod_pos_bound (lo + len + 7) 8 ltac:(lia)).
  pose proof (Z.div_mod (lo + len + 7) 8 ltac:(lia)). lia.
- unfold DFRAME_SH. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
Lemma oy_hull_frame : forall cx shf (W : world SEGS) (m : word -> option byte) lo len,
  d_shadow cx shf W m -> d_FB cx mod 8 = 0 -> 64 <= lo -> 0 < len -> lo + len <= 3016 ->
  shadow_hull_vis (aview SEGS (w_H W) m) (d_FB cx + lo) len.
Proof.
intros cx shf W m lo len Hsh HF8 Hlo Hlen Hhi s Hs.
assert (E1 : shadow_addr (d_FB cx + lo) = shadow_addr (d_FB cx) + lo / 8) by (apply oy_shadow_addr_off; exact HF8).
assert (E2 : shadow_addr (d_FB cx + lo + len - 1) = shadow_addr (d_FB cx) + (lo + len - 1) / 8).
{ replace (d_FB cx + lo + len - 1) with (d_FB cx + (lo + len - 1)) by lia. apply oy_shadow_addr_off; exact HF8. }
rewrite E1, E2 in Hs.
pose proof (Z.div_mod (shadow_addr (d_FB cx) + lo / 8) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (shadow_addr (d_FB cx) + lo / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (shadow_addr (d_FB cx) + (lo + len - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (shadow_addr (d_FB cx) + (lo + len - 1) / 8) 8 ltac:(lia)) as M2.
assert (Lb : 8 <= lo / 8) by (apply Z.div_le_lower_bound; lia).
assert (Ub : (lo + len - 1) / 8 < 377) by (apply Z.div_lt_upper_bound; lia).
replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by lia.
rewrite (Hsh (s - shadow_addr (d_FB cx))); [discriminate|]. unfold DFRAME_SH. lia.
Qed.
Lemma oy_d_A_range : forall cx, 0 <= d_S cx - MFRAME ->
  d_S cx - MFRAME - 31 <= d_A cx <= d_S cx - MFRAME /\ d_A cx mod 32 = 0.
Proof.
  intros cx Hs. unfold d_A. pose proof (Z.div_mod (d_S cx - MFRAME) 32 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (d_S cx - MFRAME) 32 ltac:(lia)) as Hmp.
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).

Definition oc (cx : dcx) (h i n now op nb fr len : Z) (Sg T : list byte) (regs : bvmap 5 word)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\ (op mod 4 = 0 \/ op mod 4 = 1) /\ 0 <= op < 256 /\
  d_rL B cx regs /\ d_sp0 cx i now W3 mem3 /\ d_frm cx nb fr len W3 mem3 /\
  length Sg = 24%nat /\ garr8 SEGS (rd W3 mem3) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) Sg) /\
  sighting_facts Sg (firstn 50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) (our_of (c_pl cx)) len 0 /\
  d_spREC cx nb fr len W3 mem3 /\ len <= nb /\ nb - len <= Z.max 0 (c_n cx - 7) /\
  length T = 400%nat /\ garr8 SEGS (rd W3 mem3) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T) /\
  disco_table_c.table_ok T /\
  d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W3 mem3.
Definition ob_sp22 (cx : dcx) (T : list byte) (ai : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  val_mem SEGS (rd W m) (d_A cx + 64) 8 (u64 (16 * ai)) /\ val_mem SEGS (rd W m) (d_A cx + 56) 8 (u64 (64 * ai)) /\
  val_mem SEGS (rd W m) (d_A cx + 352) 8 (u64 (oldv ai (role_of_e T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 192) 8 (u64 (oldv ai (hd_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 104) 8 (u64 (oldv ai (din_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 96) 8 (u64 (oldv ai (dout_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 88) 8 (u64 (oldv ai (reac_disco_table_observe_c.fam_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 80) 8 (u64 (oldv ai (reac_disco_table_observe_c.slots_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 296) 8 (u64 (oldv ai (s32_at T (48 * ai + 20)))) /\
  val_mem SEGS (rd W m) (d_A cx + 72) 8 (u64 (oldv ai (owned_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 48) 8 (u64 (oldv ai (u_at T (48 * ai + 32) 8))).
Definition obT (cx : dcx) (now : Z) (Sg T T' : list byte) (ai ow ret : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  length T = 400%nat /\ disco_table_c.table_ok T /\ find_res T (s_mac Sg) ai /\ (ow = 0 \/ ow = 1) /\
  ob_sp22 cx T ai W m /\ val_mem SEGS (rd W m) (d_A cx + 360) 8 ow /\
  reac_disco_table_observe_c.observe_model T Sg ow now T' ret.
Definition ob_rT (T : list byte) (ai : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 25 = w64 (n_of T) /\ getr regs 26 = w64 ai.
Definition ob_sp24 (cx : dcx) (T Sg : list byte) (ai ow ret : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  val_mem SEGS (rd W m) (d_A cx + 352) 8 (u64 (oldv ai (role_of_e T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 192) 8 (u64 (oldv ai (hd_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 104) 8 (u64 (oldv ai (din_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 96) 8 (u64 (oldv ai (dout_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 88) 8 (u64 (oldv ai (reac_disco_table_observe_c.fam_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 80) 8 (u64 (oldv ai (reac_disco_table_observe_c.slots_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 296) 8 (u64 (oldv ai (s32_at T (48 * ai + 20)))) /\
  val_mem SEGS (rd W m) (d_A cx + 72) 8 (u64 (oldv ai (owned_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 48) 8 (u64 (oldv ai (u_at T (48 * ai + 32) 8))) /\
  val_mem SEGS (rd W m) (d_A cx + 64) 8
    (u64 (if s_role Sg =? 0 then role_of_e T ai
          else if (role_of_e T ai =? 1) && (s_role Sg =? 2) then 1 else s_role Sg)) /\
  val_mem SEGS (rd W m) (d_A cx + 56) 8 (if ow =? 0 then u64 (owned_of T ai) else 1) /\
  val_mem SEGS (rd W m) (d_A cx + 360) 8 ret /\
  val_mem SEGS (rd W m) (d_A cx + 8) 8
    (bv_swrap 32 (if reac_disco_table_observe_c.ch_of T ai <? s_ch Sg then s_ch Sg
                  else reac_disco_table_observe_c.ch_of T ai)) /\
  val_mem SEGS (rd W m) (d_A cx + 0) 8 (bv_swrap 32 (s_ch Sg)).
Definition ob_r24 (cx : dcx) (T Sg : list byte) (ai : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 10 = w64 0 /\
  getr regs 24 = w64 (if s_hd Sg =? 0 then hd_of T ai else 1) /\
  getr regs 21 = w64 (if s_hd Sg =? 0 then din_of T ai else s_din Sg) /\
  getr regs 25 = w64 (if s_hd Sg =? 0 then dout_of T ai else s_dout Sg) /\
  getr regs 23 = w64 (if s_slots Sg =? 0 then reac_disco_table_observe_c.slots_of T ai else s_slots Sg) /\
  getr regs 22 = w64 (if s_fam Sg =? 0 then reac_disco_table_observe_c.fam_of T ai else s_fam Sg) /\
  getr regs 26 = w64 (d_obj cx OT + 48 * ai).

Definition ob_c0 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx OBS_OFF kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T,
    oc cx h i n now op nb fr len Sg T regs ly3 S3 W3 mem3 /\ val_mem SEGS (rd W3 mem3) (d_A cx + 360) 8 op).
Definition ob_c1 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx AF_both3_find_entry kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T,
    oc cx h i n now op nb fr len Sg T regs ly3 S3 W3 mem3 /\ val_mem SEGS (rd W3 mem3) (d_A cx + 360) 8 op /\
    getr regs 1 = w64 (BASE + OB_FE_RET) /\ getr regs 10 = w64 (d_obj cx OT) /\
    getr regs 11 = w64 (d_obj cx OS) /\ getr regs 23 = w64 (d_obj cx OS)).
Definition ob_c2 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx OB_FE_RET kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T ai,
    oc cx h i n now op nb fr len Sg T regs ly3 S3 W3 mem3 /\ val_mem SEGS (rd W3 mem3) (d_A cx + 360) 8 op /\
    getr regs 23 = w64 (d_obj cx OS) /\ getr regs 10 = w64 ai /\ find_res T (s_mac Sg) ai).
Definition ob_c3 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx AF_both3_reac_disco_table_observe kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T ai ow,
    oc cx h i n now op nb fr len Sg T regs ly3 S3 W3 mem3 /\
    find_res T (s_mac Sg) ai /\ (ow = 0 \/ ow = 1) /\ ob_sp22 cx T ai W3 mem3 /\
    val_mem SEGS (rd W3 mem3) (d_A cx + 360) 8 ow /\
    getr regs 1 = w64 (BASE + OB_TO_RET) /\ getr regs 10 = w64 (d_obj cx OT) /\ getr regs 11 = w64 (d_obj cx OS) /\
    getr regs 12 = w64 ow /\ getr regs 13 = w64 now /\ ob_rT T ai regs /\ getr regs 22 = w64 (ov_of T) /\
    getr regs 21 = w64 (s32_at T 392)).
Definition ob_c4 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx OB_TO_RET kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ obT cx now Sg T T' ai ow ret W3 mem3 /\
    ob_rT T ai regs /\ getr regs 10 = w64 ret /\ getr regs 22 = w64 (ov_of T) /\ getr regs 21 = w64 (s32_at T 392)).
Definition ob_c5 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx AF_both3_check_table kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ obT cx now Sg T T' ai ow ret W3 mem3 /\
    ob_rT T ai regs /\ getr regs 1 = w64 (BASE + OB_CT_RET) /\ getr regs 10 = w64 (d_obj cx OT) /\
    getr regs 23 = w64 ret /\ getr regs 24 = w64 (d_obj cx OT) /\
    getr regs 22 = w64 (ov_of T) /\ getr regs 21 = w64 (s32_at T 392)).
Definition ob_c6 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx OB_CT_RET kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ obT cx now Sg T T' ai ow ret W3 mem3 /\
    ob_rT T ai regs /\ getr regs 23 = w64 ret /\ getr regs 24 = w64 (d_obj cx OT) /\
    getr regs 22 = w64 (ov_of T) /\ getr regs 21 = w64 (s32_at T 392)).
Definition ob_c7 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx AF_both3_role_of kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ obT cx now Sg T T' ai ow ret W3 mem3 /\
    ob_rT T ai regs /\ getr regs 23 = w64 ret /\ 0 <= ai /\ role_of_e T ai = 1 /\
    getr regs 1 = w64 (BASE + OB_RO_RET) /\ getr regs 10 = w64 (d_obj cx OT) /\ getr regs 11 = w64 (d_obj cx OS)).
Definition ob_c8 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx OB_RO_RET kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret r v,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ obT cx now Sg T T' ai ow ret W3 mem3 /\
    ob_rT T ai regs /\ getr regs 23 = w64 ret /\ 0 <= ai /\ role_of_e T ai = 1 /\
    getr regs 10 = w64 v /\ find_res T' (s_mac Sg) r /\ v = (if r <? 0 then -1 else role_of_e T' r)).
Definition ob_c9 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx OB_C9 kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ obT cx now Sg T T' ai ow ret W3 mem3 /\
    getr regs 25 = w64 (n_of T) /\ getr regs 23 = w64 ret /\ 0 <= ai).
Definition ob_c10 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx OB_C10 kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ obT cx now Sg T T' ai ow ret W3 mem3 /\
    getr regs 25 = w64 (n_of T) /\ getr regs 23 = w64 ret /\ ai < 0).
Definition ob_c11 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx OB_BC_RET kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\
    length T = 400%nat /\ disco_table_c.table_ok T /\ find_res T (s_mac Sg) ai /\ 0 <= ai < n_of T /\
    (ow = 0 \/ ow = 1) /\ reac_disco_table_observe_c.observe_model T Sg ow now T' ret /\
    ob_sp24 cx T Sg ai ow ret W3 mem3 /\ ob_r24 cx T Sg ai regs).
Definition ob_r9m (T Sg : list byte) (ai ow ret : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 26 = w64 (48 * ai) /\
  getr regs 16 = w64 (if s_role Sg =? 0 then role_of_e T ai
                      else if (role_of_e T ai =? 1) && (s_role Sg =? 2) then 1 else s_role Sg) /\
  getr regs 24 = w64 (if s_hd Sg =? 0 then hd_of T ai else 1) /\
  getr regs 21 = w64 (if s_hd Sg =? 0 then din_of T ai else s_din Sg) /\
  getr regs 14 = w64 (if s_hd Sg =? 0 then dout_of T ai else s_dout Sg) /\
  getr regs 5 = w64 (if s_slots Sg =? 0 then reac_disco_table_observe_c.slots_of T ai else s_slots Sg) /\
  getr regs 22 = w64 (if s_fam Sg =? 0 then reac_disco_table_observe_c.fam_of T ai else s_fam Sg) /\
  getr regs 7 = w64 (if ow =? 0 then u64 (owned_of T ai) else 1) /\
  getr regs 25 = w64 (n_of T) /\ getr regs 23 = w64 ret.
Definition ob_c9m (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx OB_C9M kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ obT cx now Sg T T' ai ow ret W3 mem3 /\
    0 <= ai < n_of T /\
    val_mem SEGS (rd W3 mem3) (d_A cx + 8) 8
      (bv_swrap 32 (if reac_disco_table_observe_c.ch_of T ai <? s_ch Sg then s_ch Sg
                    else reac_disco_table_observe_c.ch_of T ai)) /\
    val_mem SEGS (rd W3 mem3) (d_A cx + 0) 8 (bv_swrap 32 (s_ch Sg)) /\
    ob_r9m T Sg ai ow ret regs).
Definition ob_r12 (cx : dcx) (T Sg : list byte) (ai ow ret : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 26 = w64 (d_obj cx OT + 48 * ai) /\
  getr regs 24 = w64 (if s_hd Sg =? 0 then hd_of T ai else 1) /\
  getr regs 21 = w64 (if s_hd Sg =? 0 then din_of T ai else s_din Sg) /\
  getr regs 14 = w64 (if s_hd Sg =? 0 then dout_of T ai else s_dout Sg) /\
  getr regs 23 = w64 (if s_slots Sg =? 0 then reac_disco_table_observe_c.slots_of T ai else s_slots Sg) /\
  getr regs 22 = w64 (if s_fam Sg =? 0 then reac_disco_table_observe_c.fam_of T ai else s_fam Sg) /\
  getr regs 15 = w64 (u64 (if s_role Sg =? 0 then role_of_e T ai
                          else if (role_of_e T ai =? 1) && (s_role Sg =? 2) then 1 else s_role Sg)) /\
  getr regs 7 = w64 (if ow =? 0 then u64 (owned_of T ai) else 1) /\
  getr regs 5 = w64 ret.
Definition ob_c12 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx OB_C12 kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\
    length T = 400%nat /\ disco_table_c.table_ok T /\ find_res T (s_mac Sg) ai /\ 0 <= ai < n_of T /\
    (ow = 0 \/ ow = 1) /\ reac_disco_table_observe_c.observe_model T Sg ow now T' ret /\
    ob_sp24 cx T Sg ai ow ret W3 mem3 /\ ob_r12 cx T Sg ai ow ret regs).

Definition ob_seg01 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c0 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c1 cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg12 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c1 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c2 cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg23 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c2 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c3 cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg34 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c3 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c4 cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg45 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c4 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c5 cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg56 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c5 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c6 cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg67 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c6 cx h i n now op nb fr len Sg kmax accmax W c ->
  SRr SEGS W c (fun W' c' => ob_c7 cx h i n now op nb fr len Sg kmax accmax W' c' \/
    ob_c9 cx h i n now op nb fr len Sg kmax accmax W' c' \/ ob_c10 cx h i n now op nb fr len Sg kmax accmax W' c').
Definition ob_seg78 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c7 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c8 cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg89 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c8 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c9 cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg9a : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c9 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c11 cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg9b : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (W : world SEGS) (c : config),
  ob_c11 cx h i n now op nb fr len Sg (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) W c ->
  SRr SEGS W c (r27_in B MT XM_LIB RLO RHI tfib_K cx h i (nb - len) now nb fr len).
Definition ob_seg9a1 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c9 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c9m cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg9a2 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c9m cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c11 cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg9b1 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c11 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c12 cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg9b2 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (W : world SEGS) (c : config),
  ob_c12 cx h i n now op nb fr len Sg (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) W c ->
  SRr SEGS W c (r27_in B MT XM_LIB RLO RHI tfib_K cx h i (nb - len) now nb fr len).
Definition ob_seg10r : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (W : world SEGS) (c : config),
  ob_c10 cx h i n now op nb fr len Sg (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) W c ->
  SRr SEGS W c (r27_in B MT XM_LIB RLO RHI tfib_K cx h i (nb - len) now nb fr len).

Lemma oy_A_range : forall cx ly3 S3 W3 mem3 md3 k,
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W3 mem3 md3 k ->
  alloc_ceiling + LLVMF_STK <= d_S cx <= 2 ^ 47 /\ d_S cx mod 16 = 0 /\
  d_S cx - 607 <= d_A cx <= d_S cx - 576 /\ d_A cx mod 32 = 0.
Proof.
intros cx ly3 S3 W3 mem3 md3 k HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
unfold d_A. pose proof (Z.div_mod (d_S cx - MFRAME) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (d_S cx - MFRAME) 32 ltac:(lia)) as M.
unfold MFRAME in *. split; [lia|]. split; [exact Hal|]. split; [lia|rewrite Z.mul_comm; apply Z_mod_mult].
Qed.

Lemma oy_geom : AR_laws SEGS B -> forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k,
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

Lemma regs_ok_obs : forall cx E regs, d_E cx E -> d_rL B cx regs -> 0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (obs_vals regs)) obs_sr regs.
Proof.
intros cx E regs HE HL HA.
pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
pose proof HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
assert (D60 : sv_denot (d_env cx E (obs_vals regs)) (SOff 60 0) = w64 (d_A cx))
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); exact E60).
assert (D2 : sv_denot (d_env cx E (obs_vals regs)) (SOff 2 0) = w64 (d_S cx))
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
      unfold w64, d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (D32 : sv_denot (d_env cx E (obs_vals regs)) (SOff 32 0) = w64 SHADOW_OFF)
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); exact E32).
assert (D529 : sv_denot (d_env cx E (obs_vals regs)) (SOff 529 0) = w64 (shadow_addr (d_FB cx)))
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); exact ESH).
assert (DX : forall j q, q = (AT_X + j)%nat -> (j < 32)%nat ->
  sv_denot (d_env cx E (obs_vals regs)) (SOff q 0) = nth j (obs_vals regs) (Z_to_bv 64 0))
  by (intros j q -> Hj; rewrite sv_denot_SOff0; apply oy_d_env_x; unfold obs_vals; rewrite length_map, length_seq; exact Hj).
apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
repeat (destruct Hz as [<-|Hz];
  [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
      let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
    lazymatch goal with
    | |- _ = sv_denot _ (SLit 0) => rewrite getr_zero; reflexivity
    | |- _ = sv_denot _ (SLit _) => cbn [sv_denot]; first [ exact H18 | exact H20 ]
    | |- _ = sv_denot _ (SOff 60 0) => rewrite D60;
        first [ exact H9 | unfold w64; rewrite <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned ]
    | |- _ = sv_denot _ (SOff 2 0) => rewrite D2; exact H8
    | |- _ = sv_denot _ (SOff 32 0) => rewrite D32; exact H19
    | |- _ = sv_denot _ (SOff 529 0) => rewrite D529; exact H27
    | |- _ = sv_denot _ (SOff ?q 0) =>
        let j := eval vm_compute in (q - 531)%nat in
        rewrite (DX j q eq_refl ltac:(lia)); unfold obs_vals; cbn [nth map seq];
        f_equal; vm_compute; reflexivity
    end
  | ]).
destruct Hz.
Qed.

Lemma oy_land : forall (fq : YK11.FPState) (cx : dcx) (h : Z) (shf : Z -> Z) ly3 S3 (W3 : world SEGS) md3 k
    (E : env) (ss : sstate) (ms : machine_state),
  AR_laws SEGS B ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 (ms_mem ms) md3 k ->
  d_E cx E -> ew E AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  0 <= flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx) < 2 ^ 64 ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W3) ms) ->
  d_land_chk shf (ss_mem ss) = true ->
  val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 184) 8 h ->
  val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 120) 8 (h + 440) ->
  val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 136) 8 0 ->
  val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 376) 8 (dnot (d_obj cx OG)) ->
  val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 280) 8 (dnot (d_obj cx OT)) ->
  val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 232) 8 (dnot (d_obj cx OO)) ->
  val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 264) 8 (dnot (d_obj cx OUSED)) ->
  d_frame cx h shf W3 (ms_mem ms) /\ d_shadow cx shf W3 (ms_mem ms).
Proof.
  intros fq cx h shf ly3 S3 W3 md3 k E ss ms LAWS HC HE HE530 HFLr HS Hchk V1 V2 V3 V4 V5 V6 V7.
  destruct (oy_geom LAWS _ _ _ _ _ _ _ HC)
    as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
  pose proof asan_consts as (Hac & _).
  pose proof (oy_d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
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
  pose proof (oy_sh_region_bytes _ _ _ shf r4 Hc4 R4) as HSB. rewrite Hb4, U529 in HSB.
  assert (FR : region_ok SEGS E (rd W3 (ms_mem ms))
    (YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 DFRAME_SIZE dfhdr_chunks)).
  { apply (oy_region_cover_ok _ _ _ _ _ _ _ _ _ r3 Hc3 R3). rewrite U516. intros o Ho.
    apply (apresent_writable SEGS). apply HFpres. unfold DFRAME_SIZE in Ho. lia. }
  destruct FR as (_ & _ & _ & FC). cbn [YP09.r_base YP09.r_chunks] in FC. rewrite U516 in FC.
  unfold dfhdr_chunks in FC.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail FC)))) as CFL.
  pose proof (val_of_chunk_ok SEGS E _ (d_FB cx) 4088 8%N (SOff AT_FL 0) (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx))
    CFL ltac:(cbn [sv_denot]; rewrite HE530, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(cbn [Z.of_N]; change (8 * 8) with 64; lia) ltac:(cbn [Z.of_N]; lia)) as VFL.
  split.
  - exists E. split; [exact HE|]. split; [|split; [|exact (conj V1 (conj V2 (conj V3 (conj V4 (conj V5 (conj V6 V7))))))]].
    + unfold d_regions. repeat apply Forall_cons; try apply Forall_nil.
      * apply (oy_region_cover_ok _ _ _ _ _ _ _ _ _ r1 Hc1 R1). intros o Ho. lia.
      * apply (oy_region_cover_ok _ _ _ _ _ _ _ _ _ r2 Hc2 R2). rewrite U60. intros o Ho.
        apply (apresent_writable SEGS). apply HWpres. unfold MFRAME, LLVMF_STK in *. lia.
      * pose proof (oy_region_cover_ok _ _ _ _ _ _ 0 DFRAME_SIZE _ r3 Hc3 R3) as FR.
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
        -- apply oy_dsh_chunks_ok. exact HSB.
    + change (fs_frame_bytes DFRAME_CLASS) with 4096. replace (d_FB cx + 4096 - 8) with (d_FB cx + 4088) by lia.
      apply rdword_of_val_mem; [exact VFL | lia].
  - intros kk Hk. destruct (HSB kk Hk) as (Hr & Hm). unfold aview. rewrite Hm. cbn [option_map].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. f_equal. apply Z.mod_small. exact Hr.
Qed.

Lemma oy_frame_keep : forall cx h shf (W W' : world SEGS) (m m' : word -> option byte) ly3 S3 md3 k,
  AR_laws SEGS B ->
  d_frame cx h shf W m -> d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W' m' md3 k ->
  (forall a, (d_A cx <= a < d_S cx \/ d_FB cx <= a < d_FB cx + 24 \/ d_FB cx + 4088 <= a < d_FB cx + 4096 \/
              shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  d_frame cx h shf W' m'.
Proof.
intros cx h shf W W' m m' ly3 S3 md3 k LAWS (E & HE & Hregs & Hflag & V1 & V2 & V3 & V4 & V5 & V6 & V7) Hctx Hkeep.
destruct (oy_geom LAWS cx ly3 S3 W' m' md3 k Hctx)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (oy_d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof HE as (HER & H32 & HI & HA & HF & HSH).
assert (B2 : bv_unsigned (ew E AT_STK) = d_S cx) by (change AT_STK with 2%nat; rewrite (HER 2%nat 2%bv eq_refl); reflexivity).
assert (BA : bv_unsigned (ew E AT_A) = d_A cx) by (rewrite HA; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
assert (BF : bv_unsigned (ew E AT_F) = d_FB cx) by (rewrite HF; apply unsigned_lit_small; lia).
assert (BSH : bv_unsigned (ew E AT_SH) = shadow_addr (d_FB cx)).
{ rewrite HSH; apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF.
  split; [|apply Z.lt_le_trans with (2147450880 + 2 ^ 47 / 8 + 1); [|lia]];
  pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia) ltac:(lia)); [lia|]. assert (d_FB cx / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). lia. }
change (fs_frame_bytes DFRAME_CLASS) with 4096 in *.
assert (VK : forall a v, d_A cx <= a -> a + 8 <= d_S cx ->
  val_mem SEGS (rd W m) a 8 v -> val_mem SEGS (rd W' m') a 8 v).
{ intros a v Ha1 Ha2 Hv. apply (oy_val_mem_keep W W' m m' _ 8 _); [|exact Hv]. intros j Hj. apply Hkeep. left. lia. }
exists E. split; [exact HE|]. split; [|split; [|split]].
- unfold d_regions in *. rewrite !Forall_cons_iff in Hregs. destruct Hregs as (R1 & R2 & R3 & R4 & _).
  repeat (apply Forall_cons); [| | | | apply Forall_nil].
  + apply (oy_region_ok_keep E W W' m m' _ R1).
    * intros c i Hin Hi. cbn [YP09.r_chunks YP09.r_base base_val] in *. rewrite B2.
      unfold dsave_chunks in Hin. apply in_map_iff in Hin as (j & <- & Hj). apply in_seq in Hj.
      cbn [length dsave_regs] in Hj. cbn [YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N] in *.
      apply Hkeep. left. lia.
    * cbn. intros o Ho. lia.
  + apply (oy_region_ok_keep E W W' m m' _ R2).
    * intros c i Hin Hi. cbn [YP09.r_chunks YP09.r_base base_val] in *. rewrite BA.
      unfold dslot_chunks in Hin. apply in_map_iff in Hin as (kv & <- & Hkv).
      assert (Hkv' : 0 <= fst kv <= 416) by (cbn [In] in Hkv; repeat destruct Hkv as [<-|Hkv]; cbn; lia).
      cbn [YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N] in *. apply Hkeep. left. lia.
    * cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val]. rewrite BA. intros o Ho. apply HStk. unfold LLVMF_STK. lia.
  + apply (oy_region_ok_keep E W W' m m' _ R3).
    * intros c i Hin Hi. cbn [YP09.r_chunks YP09.r_base base_val] in *. rewrite BF.
      cbn [In] in Hin. repeat destruct Hin as [<-|Hin]; [..|destruct Hin]; cbn [YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N] in *;
      apply Hkeep; right; left; lia.
    * cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val]. rewrite BF. intros o Ho. apply HFp. unfold DFRAME_SIZE in Ho. lia.
  + apply (oy_region_ok_keep E W W' m m' _ R4).
    * intros c i Hin Hi. cbn [YP09.r_chunks YP09.r_base base_val fshadow_region] in *. rewrite BSH.
      unfold dsh_chunks in Hin. apply in_map_iff in Hin as (j & <- & Hj). apply in_seq in Hj.
      cbn [YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N] in *. unfold DFRAME_SH in Hj.
      apply Hkeep. right; right; right. lia.
    * cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val fshadow_region]. rewrite BSH. intros o Ho. apply HSp. unfold DFRAME_SH in Ho. lia.
- rewrite (oy_rdword_keep (aview SEGS (w_H W) m) (aview SEGS (w_H W') m')); [exact Hflag|].
  intros j Hj. apply Hkeep. right; right; left. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
- apply VK; [lia | lia | exact V1].
- split; [apply VK; [lia | lia | exact V2]|]. split; [apply VK; [lia | lia | exact V3]|].
  split; [apply VK; [lia | lia | exact V4]|]. split; [apply VK; [lia | lia | exact V5]|].
  split; [apply VK; [lia | lia | exact V6]|]. apply VK; [lia | lia | exact V7].
Qed.

Lemma oy_rL_pres : forall cx regs regs', aregs_preserved regs regs' -> d_rL B cx regs -> d_rL B cx regs'.
Proof.
intros cx regs regs' HP (H2 & H3 & H4 & H8 & H9 & H19 & H18 & H20 & H27). unfold d_rL.
split; [unfold spZ in *; rewrite <- H2; f_equal; exact (HP 2 ltac:(unfold acallee_saved; lia))|].
split; [transitivity (getr regs 3%bv); [exact (HP 3 ltac:(unfold acallee_saved; lia)) | exact H3]|].
split; [transitivity (getr regs 4%bv); [exact (HP 4 ltac:(unfold acallee_saved; lia)) | exact H4]|].
split; [transitivity (getr regs 8%bv); [exact (HP 8 ltac:(unfold acallee_saved; lia)) | exact H8]|].
split; [transitivity (getr regs 9%bv); [exact (HP 9 ltac:(unfold acallee_saved; lia)) | exact H9]|].
split; [transitivity (getr regs 19%bv); [exact (HP 19 ltac:(unfold acallee_saved; lia)) | exact H19]|].
split; [transitivity (getr regs 18%bv); [exact (HP 18 ltac:(unfold acallee_saved; lia)) | exact H18]|].
split; [transitivity (getr regs 20%bv); [exact (HP 20 ltac:(unfold acallee_saved; lia)) | exact H20]|].
transitivity (getr regs 27%bv); [exact (HP 27 ltac:(unfold acallee_saved; lia)) | exact H27].
Qed.

Lemma oy_pre8 : forall cx regs ly3 S3 (W : world SEGS) mem3 md3 k STK ret,
  AR_laws SEGS B ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k -> d_rL B cx regs -> getr regs 1 = w64 (BASE + ret) ->
  0 <= ret < 2 ^ 40 -> ret mod 2 = 0 -> 0 <= STK -> STK + 640 <= LLVMF_STK ->
  afn_pre SEGS B STK ly3 S3 W (regupd regs 8 (Z_to_bv 64 0)) mem3 md3 [].
Proof.
intros cx regs ly3 S3 W mem3 md3 k STK ret LAWS Hc HrL Hra Hr0 Hr2 HS0 HS1.
pose proof Hc as (_ & HJ & _).
destruct (oy_geom LAWS cx ly3 S3 W mem3 md3 k Hc) as (HS16 & HSlo & HShi & _).
destruct (oy_d_A_range cx ltac:(pose proof alloc_ceiling_val; unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32).
unfold MFRAME in HAr.
pose proof pa_base_lo as HBlo. pose proof pa_B_ok as HB. pose proof alloc_ceiling_val as Hac.
pose proof HrL as (Hsp & Hgp & Htp & _).
set (regs8 := regupd regs 8 (Z_to_bv 64 0)).
assert (G8 : forall r : bv 5, r <> 8%bv -> getr regs8 r = getr regs r).
{ intros r Hr. unfold regs8, getr. destruct (bv_eqb r 0); [reflexivity|]. exact (regupd_other regs 8 _ r Hr). }
assert (G88 : getr regs8 8%bv = Z_to_bv 64 0) by (unfold regs8, getr; rewrite regupd_same; destruct (bv_eqb _ _); reflexivity).
assert (Hsp8 : spZ regs8 = d_A cx) by (unfold spZ; rewrite G8 by (let X := fresh in intros X; apply (f_equal bv_unsigned) in X; discriminate X); exact Hsp).
apply (afn_pre_at SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)]
  ly3 S3 W mem3 md3 k regs8 STK (d_A cx - d_S cx) [] HJ).
- rewrite Hsp8. lia.
- lia.
- lia.
- exact HS0.
- unfold LLVMF_STK in *. lia.
- rewrite G8 by (let X := fresh in intros X; apply (f_equal bv_unsigned) in X; discriminate X). rewrite Hra. unfold w64. apply ret_ok_codeptr_v; assumption.
- unfold raZ. rewrite G8 by (let X := fresh in intros X; apply (f_equal bv_unsigned) in X; discriminate X). rewrite Hra. unfold w64. rewrite unsigned_lit_small by lia.
  unfold IMG_LO in HBlo. lia.
- rewrite G8 by (let X := fresh in intros X; apply (f_equal bv_unsigned) in X; discriminate X). exact Hgp.
- rewrite G8 by (let X := fresh in intros X; apply (f_equal bv_unsigned) in X; discriminate X). exact Htp.
- unfold s0Z. rewrite G88, unsigned_lit_small by lia. apply achain_low. lia.
Qed.

Lemma oy_post : forall cx ly3 S3 (W : world SEGS) mem3 md3 k STK ly4 S4 W2 mem4 md4,
  AR_laws SEGS B ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k -> 0 <= STK -> STK + 640 <= LLVMF_STK ->
  ajournal SEGS B STK (d_A cx) [] ly3 S3 W mem3 md3 [] ly4 S4 W2 mem4 md4 0 ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 (k + 0).
Proof.
intros cx ly3 S3 W mem3 md3 k STK ly4 S4 W2 mem4 md4 LAWS Hc HS0 HS1 HJ1.
destruct (oy_geom LAWS cx ly3 S3 W mem3 md3 k Hc) as (HS16 & HSlo & HShi & _).
pose proof alloc_ceiling_val as Hac0.
destruct (oy_d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
destruct Hc as (Hbase & HJ & Hfrs).
split; [exact Hbase|]. split.
- change [(DFRAME_CLASS, c_fpos cx)] with ([] ++ [(DFRAME_CLASS, c_fpos cx)]).
  eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | unfold LLVMF_STK in *; lia | lia |
    intros a (rg & [] & _)].
- pose proof HJ1 as (_ & _ & _ & _ & _ & Hf1 & _). rewrite Hf1, Hfrs. reflexivity.
Qed.

Lemma oy_dat : forall cx pc kmax accmax
  (P : bvmap 5 word -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop)
  (fq : YK11.FPState) ly4 S4 regs4 mem4 md4 k acc (W2 : world SEGS),
  MT = ameter_triv -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 k -> 0 <= k <= kmax -> acc <= accmax ->
  P regs4 ly4 S4 W2 mem4 md4 ->
  DAT cx pc kmax accmax P W2 (cfg_at (fx := fq) SEGS (BASE + pc) regs4 mem4 md4).
Proof.
intros cx pc kmax accmax P fq ly4 S4 regs4 mem4 md4 k acc W2 MT_TRIV HFRM0 (Hbase & HJ & Hfrs) Hk Hacc HP.
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
unfold d_at. exists fq, ly4, S4, regs4, mem4, md4, k, acc.
split; [reflexivity|]. split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [lia|]. split; [lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|]. exact HP.
Qed.

Lemma oy_oc_pt : forall cx h i n now op nb fr len Sg T regs regs' ly3 S3 (W : world SEGS) (m m' : word -> option byte),
  d_body_rt_stmt B ->
  (forall x, m' x = m x) -> d_rL B cx regs' ->
  oc cx h i n now op nb fr len Sg T regs ly3 S3 W m -> oc cx h i n now op nb fr len Sg T regs' ly3 S3 W m'.
Proof.
intros cx h i n now op nb fr len Sg T regs regs' ly3 S3 W m m' DBRT HM HrL'
  (Hi & Hn & Hnow & Hop & Hop2 & HrL & (S1 & S2) & (F1 & F2 & F0 & F3) & HSgl & HSg & HSf & (R1 & R2 & R3 & R4) &
   Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof (oy_mrestrict_ext (w_H W) m m' HM) as Hpt.
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & _).
refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj HrL' (conj _ (conj _ (conj HSgl (conj _ (conj HSf
  (conj _ (conj Hlen (conj Hnb (conj HTl (conj _ (conj HTok _))))))))))))))))).
- exact (conj (oy_val_mem_pt _ _ _ _ _ Hpt S1) (oy_val_mem_pt _ _ _ _ _ Hpt S2)).
- exact (conj F1 (conj F2 (conj F0 (oy_garr8_pt _ _ _ _ Hpt F3)))).
- exact (oy_garr8_pt _ _ _ _ Hpt HSg).
- exact (conj (oy_val_mem_pt _ _ _ _ _ Hpt R1) (conj (oy_val_mem_pt _ _ _ _ _ Hpt R2)
    (conj (oy_val_mem_pt _ _ _ _ _ Hpt R3) (oy_val_mem_pt _ _ _ _ _ Hpt R4)))).
- exact (oy_garr8_pt _ _ _ _ Hpt HT).
- apply (DBRT cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W m m' (d_S cx) (d_S cx) (fun _ => False) Hbody).
  + unfold LLVMF_STK. lia.
  + lia.
  + intros a [].
  + intros a _ _. apply oy_aview_ext. exact HM.
  + intros a _ [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite HM. exact Hb.
  + exact (oy_frame_ext cx h dsh_rec W m m' HM Hframe).
  + exact (oy_shadow_ext cx dsh_rec W m m' HM Hshadow).
  + lia.
Qed.

Lemma oy_oc_call_keep : forall cx h i n now op nb fr len Sg T regs ly3 S3 W3 m3 md3 k3 regs' ly4 S4 W4 m4 md4 k4 STK,
  AR_laws SEGS B -> d_body_call_keep_stmt B MT XM_LIB RLO RHI tfib_K ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 m3 md3 k3 ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W4 m4 md4 k4 ->
  oc cx h i n now op nb fr len Sg T regs ly3 S3 W3 m3 ->
  0 <= STK -> STK + 640 <= LLVMF_STK ->
  d_kept (fun a => d_A cx - STK <= a < d_A cx) W3 m3 W4 m4 ->
  Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  aregs_preserved regs regs' ->
  oc cx h i n now op nb fr len Sg T regs' ly4 S4 W4 m4.
Proof.
intros cx h i n now op nb fr len Sg T regs ly3 S3 W3 m3 md3 k3 regs' ly4 S4 W4 m4 md4 k4 STK LAWS DBCK Hc3 Hc4 HOC HS0 HS1 HK HPm HP.
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & _).
destruct (oy_geom LAWS cx ly3 S3 W3 m3 md3 k3 Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
destruct (oy_d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof alloc_ceiling_val as Hac.
assert (Hlo : d_S cx - LLVMF_STK <= d_A cx - STK) by lia.
assert (HKA : forall a nn v, d_A cx <= a -> a + Z.of_nat nn <= d_S cx ->
  val_mem SEGS (rd W3 m3) a nn v -> val_mem SEGS (rd W4 m4) a nn v).
{ intros a nn v H1 H2. apply (oy_val_mem_keep W3 W4 m3 m4). intros j Hj. apply HK; lia. }
assert (HKF : forall a l, d_FB cx <= a -> a + Z.of_nat (length l) <= d_FB cx + 4096 ->
  garr8 SEGS (rd W3 m3) a l -> garr8 SEGS (rd W4 m4) a l).
{ intros a l H1 H2. apply (oy_garr8_keep W3 W4 m3 m4). intros j Hj. apply HK; lia. }
unfold oc.
refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj _ (conj _ (conj HSgl (conj _ (conj HSf
  (conj _ (conj Hlen (conj Hnb (conj HTl (conj _ (conj HTok _))))))))))))))))).
- exact (oy_rL_pres cx regs regs' HP HrL).
- destruct Hsp0 as (S1 & S2). split; apply HKA; try exact S1; try exact S2; cbn; lia.
- destruct Hfrm as (F1 & F2 & F0 & F3). split; [exact F1|]. split; [exact F2|]. split; [exact F0|].
  destruct (Z.eq_dec fr 0) as [E0|E0].
  + rewrite (F2 E0). exact (garr8_nil SEGS _ _).
  + assert (Hin : In (fr, len) (ablocks B ly3 S3)).
    { destruct Hblocks as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)). unfold dxb.
      rewrite (proj2 (Z.eqb_neq fr 0) E0). left. reflexivity. }
    destruct (al_blocks _ _ LAWS ly3 S3 W3 m3 md3 fr len HAR Hin) as (_ & Hfr4 & Hfrc & _).
    assert (Hrq : len <= req_size len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
    assert (HL : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)))) <= len)
      by (rewrite length_map, length_firstn; lia).
    apply (oy_garr8_keep W3 W4 m3 m4); [|exact F3]. intros j Hj. apply HK; lia.
- apply HKF; [unfold d_obj, dobj_off; lia | rewrite length_map, HSgl; unfold d_obj, dobj_off; cbn; lia | exact HSg].
- destruct HREC as (R1 & R2 & R3 & R4).
  split; [apply HKA; [lia | cbn; lia | exact R1]|]. split; [apply HKA; [lia | cbn; lia | exact R2]|].
  split; [apply HKA; [lia | cbn; lia | exact R3]|]. apply HKA; [lia | cbn; lia | exact R4].
- apply HKF; [unfold d_obj, dobj_off; lia | rewrite length_map, HTl; unfold d_obj, dobj_off; cbn; lia | exact HT].
- assert (Hjr : d_jr B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W4 m4 md4 k4) by exact (conj (proj1 Hc4) (proj1 (proj2 Hc4))).
  apply (DBCK LAWS cx h n (dxb fr len) dsh_rec dsh_rec ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 (d_A cx - STK) (d_A cx) Hbody Hjr Hlo
    ltac:(lia) HK HPm).
  + apply (oy_frame_keep cx h dsh_rec W3 W4 m3 m4 ly4 S4 md4 k4 LAWS Hframe Hc4). intros a Ha. apply HK.
    * unfold shadow_addr, SHADOW_OFF in Ha. lia.
    * unfold shadow_addr, SHADOW_OFF in Ha. lia.
  + apply (oy_d_shadow_keep cx dsh_rec W3 W4 m3 m4 Hshadow). intros kk Hkk. apply HK; unfold shadow_addr, SHADOW_OFF, DFRAME_SH in *; lia.
Qed.

Lemma oy_obT_keep : forall cx now Sg T T' ai ow ret (W3 W4 : world SEGS) m3 m4 STK,
  d_kept (fun a => d_A cx - STK <= a < d_A cx) W3 m3 W4 m4 -> 640 <= d_S cx -> d_S cx <= 2 ^ 47 ->
  obT cx now Sg T T' ai ow ret W3 m3 -> obT cx now Sg T T' ai ow ret W4 m4.
Proof.
intros cx now Sg T T' ai ow ret W3 W4 m3 m4 STK HK H0 H1
  (L & Ok & F & Ow & (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11) & V12 & M).
destruct (oy_d_A_range cx ltac:(unfold MFRAME; lia)) as (HAr & _). unfold MFRAME in HAr.
assert (KA : forall a nn v, 0 <= a -> a + Z.of_nat nn <= 448 ->
  val_mem SEGS (rd W3 m3) (d_A cx + a) nn v -> val_mem SEGS (rd W4 m4) (d_A cx + a) nn v).
{ intros a nn v Ha Hb Hv. apply (oy_val_mem_keep W3 W4 m3 m4); [|exact Hv]. intros j Hj. apply HK; lia. }
unfold obT, ob_sp22.
refine (conj L (conj Ok (conj F (conj Ow (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
  (conj _ _)))))))))) (conj _ M)))))); apply KA; try assumption; cbn; lia.
Qed.

End h.
End f.
End d.
Ltac ro_base HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

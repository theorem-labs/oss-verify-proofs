(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths, module names and numbers changed; 283 of its 776 lines of code are new or changed and 167 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0p YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f YC8g YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YC88 YCkd YC1i YCbf YCj1 YCjr YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SetShadowDef ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh SbDec ReacBoxName ReacBoxNameCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Definition rbn10_chunks : list YP09.chunk :=
  [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
   YP09.mkChunk (-104) (CVal 8 (SOff 45 0))].
Definition rbn10_regions : smem :=
  [ YP09.mkRegion (Some 19%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 23%nat) 504 512 0 0 [YP09.mkChunk 504 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 8%nat) (-104) 0 0 0 rbn10_chunks ].
Definition rbn10_facts : facts := mkFacts [ (23%nat, mkAF 4096 (2 ^ 47) 0) ] [] [].
Definition ss_rbn10 : sstate := mkSS (AF_both3_reac_box_name + RBN_P10) sr_atoms rbn10_regions None rbn10_facts.
Definition rbn10_flag_region : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Lemma rbn10_kept_frame : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' P HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma rbn10_tk_len : forall l seen, (length (bn_tk seen l) <= length l)%nat.
Proof.
induction l as [|c l IH]; intros seen; cbn [bn_tk length]; [lia|].
destruct ((c =? 45) && negb seen)%bool; cbn [length]; [specialize (IH true); lia | specialize (IH seen); lia].
Qed.
Lemma rbn10_dec_len : forall x, bn_ok x = true -> (length (bn_dec x 1) <= 2)%nat.
Proof.
intros x Hx. apply bn_ok_in in Hx. unfold bn_oks in Hx. cbn [map seq] in Hx.
repeat (destruct Hx as [<- | Hx]; [vm_compute; lia|]). destruct Hx.
Qed.
Lemma rbn10_acc_lens : forall f sd i o name name_len token token_len display display_len,
  reac_box_name_c.bn_accept f sd i o name name_len token token_len display display_len = true ->
  reac_box_name_c.bn_args_ok name name_len token token_len display display_len i o = true /\
  Z.of_nat (length (bn_NM f sd i o)) + 1 <= Z.min name_len 24 /\
  Z.of_nat (length (bn_TK (bn_NM f sd i o))) + 1 <= Z.min token_len 24 /\
  Z.of_nat (length (bn_DP (bn_NM f sd i o) i o)) + 1 <= Z.min display_len 48.
Proof.
intros f sd i o name name_len token token_len display display_len H.
unfold reac_box_name_c.bn_accept in H.
apply andb_prop in H as [H Hd]. apply andb_prop in H as [H Ht]. apply andb_prop in H as [H Hn].
apply andb_prop in H as [Ha Hr].
apply Z.ltb_lt in Hd. apply Z.ltb_lt in Ht. apply Z.ltb_lt in Hn. apply Z.eqb_eq in Hr.
assert (H23 : Z.of_nat (length (bn_NM f sd i o)) <= 23).
{ unfold bn_ret in Hr.
  match type of Hr with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [_ Hc]. apply Z.leb_le in Hc. exact Hc. }
pose proof Ha as Ha'. unfold reac_box_name_c.bn_args_ok in Ha'.
apply andb_prop in Ha' as [Ha' _]. apply andb_prop in Ha' as [Ha' Hbo]. apply andb_prop in Ha' as [_ Hbi].
pose proof (rbn10_tk_len (bn_NM f sd i o) false) as Htk.
pose proof (rbn10_dec_len i Hbi) as Hdi. pose proof (rbn10_dec_len o Hbo) as Hdo.
split; [exact Ha|].
unfold bn_TK in *. unfold bn_DP in *. rewrite !length_app in *. cbn [length] in *. lia.
Qed.
Definition rbn10_extra (X : rbn_in) (pos : Z) : list word :=
  Z_to_bv 64 (rbn_FL X pos) :: map (fun r => getr (ri_regs X) (Z_to_bv 5 r)) rbn_saved_regs.
Lemma rbn10_ew_saved : forall X pos (regs : bvmap 5 word) j r, nth_error rbn_saved_regs j = Some r ->
  ew (Eimg (Ereg regs (rbn10_extra X pos))) (33 + j) = getr (ri_regs X) (Z_to_bv 5 r).
Proof.
intros X pos regs j r Hj.
assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
rewrite Eimg_low by (cbn [length rbn_saved_regs] in Hj13; unfold A_TEXT; lia).
replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra. unfold rbn10_extra. cbn [nth].
rewrite (nth_indep _ _ (getr (ri_regs X) (Z_to_bv 5 0))) by (rewrite length_map; exact Hj13).
rewrite (map_nth (fun r0 => getr (ri_regs X) (Z_to_bv 5 r0)) rbn_saved_regs 0 j).
rewrite (nth_error_nth rbn_saved_regs j 0 Hj). reflexivity.
Qed.
Lemma rbn10_chunks_ok : forall X pos (regs : bvmap 5 word) (m : word -> option byte),
  rbn_frame X m -> Forall (YP09.chunk_ok SEGS (Eimg (Ereg regs (rbn10_extra X pos))) m (rbn_SP X)) rbn10_chunks.
Proof.
intros X pos regs m Hfr.
assert (K : forall j r off n, nth_error rbn_saved_regs j = Some r -> off = -8 - 8 * Z.of_nat j -> n = (33 + j)%nat ->
  YP09.chunk_ok SEGS (Eimg (Ereg regs (rbn10_extra X pos))) m (rbn_SP X) (YP09.mkChunk off (CVal 8 (SOff n 0)))).
{ intros j r off n Hj -> ->.
  apply (chunk_ok_val SEGS _ m (rbn_SP X) _ 8 _ (bv_unsigned (getr (ri_regs X) (Z_to_bv 5 r)))).
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (rbn10_ew_saved X pos regs j r Hj).
    symmetry. apply Z_to_bv_bv_unsigned.
  - pose proof (bv_unsigned_in_range 64 (getr (ri_regs X) (Z_to_bv 5 r))) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia.
  - change (N.to_nat 8) with 8%nat.
    replace (rbn_SP X + (-8 - 8 * Z.of_nat j)) with (rbn_SP X - 8 - 8 * Z.of_nat j) by lia. exact (Hfr j r Hj). }
unfold rbn10_chunks.
apply Forall_cons; [apply (K 0%nat 1); reflexivity|]. apply Forall_cons; [apply (K 1%nat 8); reflexivity|].
apply Forall_cons; [apply (K 2%nat 9); reflexivity|]. apply Forall_cons; [apply (K 3%nat 18); reflexivity|].
apply Forall_cons; [apply (K 4%nat 19); reflexivity|]. apply Forall_cons; [apply (K 5%nat 20); reflexivity|].
apply Forall_cons; [apply (K 6%nat 21); reflexivity|]. apply Forall_cons; [apply (K 7%nat 22); reflexivity|].
apply Forall_cons; [apply (K 8%nat 23); reflexivity|]. apply Forall_cons; [apply (K 9%nat 24); reflexivity|].
apply Forall_cons; [apply (K 10%nat 25); reflexivity|]. apply Forall_cons; [apply (K 11%nat 26); reflexivity|].
apply Forall_cons; [apply (K 12%nat 27); reflexivity|]. apply Forall_nil.
Qed.
Lemma rbn10_entry : forall (fq : YK11.FPState) X pos (regs : bvmap 5 word) (W : world SEGS) (m : word -> option byte),
  bv_unsigned (getr regs 19) = rbn_F X pos -> bv_unsigned (getr regs 23) = rbn_F X pos ->
  bv_unsigned (getr regs 8) = rbn_SP X ->
  4096 <= rbn_F X pos <= 2 ^ 47 -> rbn_F X pos + 512 <= rbn_SP X - 104 -> 0 <= rbn_FL X pos < 2 ^ 64 ->
  (forall o, 0 <= o < 8 -> apresent (w_H W) m (rbn_F X pos + o)) ->
  val_mem SEGS (mrestrict (w_H W) m) (rbn_F X pos + 504) 8 (rbn_FL X pos) ->
  rbn_frame X (mrestrict (w_H W) m) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (rbn10_extra X pos))) ss_rbn10
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_P10))) m (seg_rom SEGS))).
Proof.
intros fq X pos regs W m H19 H23 H8 HF4 HFsp HFL Hpres Hfl Hfr.
rewrite restrict_mkst_fx.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs (rbn10_extra X pos))) n = getr regs r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E19 : bv_unsigned (ew (Eimg (Ereg regs (rbn10_extra X pos))) 19) = rbn_F X pos)
  by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
assert (E23 : bv_unsigned (ew (Eimg (Ereg regs (rbn10_extra X pos))) 23) = rbn_F X pos)
  by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
assert (E8 : bv_unsigned (ew (Eimg (Ereg regs (rbn10_extra X pos))) 8) = rbn_SP X)
  by (rewrite (EE 8%nat 8%bv eq_refl); exact H8).
assert (E32 : ew (Eimg (Ereg regs (rbn10_extra X pos))) 32 = Z_to_bv 64 (rbn_FL X pos))
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R8. change (bv_modulus 64) with (2 ^ 64) in R8.
unfold ss_rbn10, rbn10_regions. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E19. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite E23. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (rbn_F X pos) 504 8 (SOff 32 0) (rbn_FL X pos));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Hfl].
  + rewrite E8. split; [rewrite <- H8 in HFsp; lia|]. split; [rewrite <- H8; lia|]. split; [intros o Ho; lia|].
    apply rbn10_chunks_ok. exact Hfr.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E19, E23, E8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- unfold rbn10_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok].
  split; [|exact I]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E23, Z.pow_0_r, Z.mod_1_r. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASSF5 : forall fq : YK11.FPState,
  aset_shadow_realizes (fx := fq) SEGS B (SIGMA AS___asan_set_shadow_f5) 0xf5.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Lemma rbn10_ajw : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
  ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H Wc) memc' a) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  AR SEGS B lyc Sc Wc memc' mdc' ->
  ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr HJ Heqw Hpr Hsame HW HAR'.
pose proof pa_segs_low as segs_low.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWw : forall a, Wr a ->
  ~ aowned B lyc Sc a /\
  ((alloc_ceiling <= a /\ sp0 - STK <= a < sp0) \/
   (app_addr a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n /\
      (inFP FP a \/ ~ In (b, n) (ablocks B ly S))) \/
   (exists cid pos, In (cid, pos) own /\
     ((app_addr a /\ in_zr a (frame_rng lyc (cid, pos))) \/
      (kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)))))).
{ intros a Ha. exact (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (HW a Ha)). }
split; [exact HAR'|].
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split.
{ intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply Heqw; [zlia|]. intros HWa.
  destruct (HWw a HWa) as (_ & [[_ Hs'] | [[[_ Hlow] _] | (cid & pos & _ & [[[_ Hlow] _] | [[_ Hlow] _]])]]);
  [exact (Hs Hs') | zlia | zlia | zlia]. }
split.
{ intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & [Hh1 Hh2] & _ & _).
  apply Heqw; [zlia|]. intros HWa.
  destruct (HWw _ HWa) as (_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & [Hfp | Hnot]) |
    (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]).
  - zlia.
  - exact (Hnf Hfp).
  - assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
    pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin H2 Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
  - assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
    pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p n cid pos HAR H2 Hin') as Hd.
    unfold zdisjoint, in_zr, frame_rng in *. cbn [fst snd] in Hd, Hr. zlia.
  - zlia. }
split.
{ intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). pose proof (segs_low a Hi) as Hal'.
  apply Heqw; [zlia|]. intros HWa.
  destruct (HWw a HWa) as (_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) |
    (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]).
  - zlia.
  - exact (blk_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
  - assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
    unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (frm_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hin' Hr Hi).
  - zlia. }
split.
{ intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
  assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
  assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  assert (Hx1 : 0 <= frame_addr lyc cid pos < kHighMemEnd) by (pose proof (fs_frame_bytes_nonneg cid); zlia).
  assert (Hx2 : 0 <= frame_addr lyc cid pos + fs_frame_bytes cid < kHighMemEnd) by (pose proof (fs_frame_bytes_nonneg cid); zlia).
  pose proof (shadow_addr_bounds _ Hx1) as Hsb1. pose proof (shadow_addr_bounds _ Hx2) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
  apply Heqw; [zlia|]. intros HWa.
  destruct (HWw _ HWa) as (_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | (c' & p' & Hown & Hr')]]).
  - zlia.
  - destruct Hr as [Hr | Hr]; [|zlia].
    pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
  - apply in_split in Hown as (o1 & o2 & Eo). apply in_split in Hin as (g1 & g2 & Eg).
    assert (Hd : zdisjoint (frame_rng lyc (c', p')) (frame_rng lyc (cid, pos))).
    { eapply (sep_frames_pos SEGS B LAWS lyc Sc Wc memc mdc _ _ o1 (o2 ++ g1) g2 HAR).
      rewrite Hfrs, Eo, Eg. repeat (rewrite <- app_assoc; cbn). reflexivity. }
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
    destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc c' p' HAR
      ltac:(rewrite Hfrs; apply in_or_app; left; rewrite Eo; apply in_or_app; right; left; reflexivity))
      as (Hf0' & Hfc' & Hfh').
    pose proof (shadow_range_end (frame_addr lyc c' p') (fs_frame_bytes c') (fs_frame_bytes_nonneg c')) as Hse'.
    pose proof (fs_frame_bytes_nonneg c') as Hnn'.
    destruct Hr' as [[[Hlo0' Hlo'] Hr'] | [[Hlo1' Hhi'] Hr']]; unfold in_zr, frame_rng in Hr'; cbn [fst snd] in Hr'.
    + destruct Hr as [Hr | Hr]; [zlia | zlia].
    + destruct Hr as [Hr | Hr]; [zlia |].
      destruct Hd as [Hd | Hd].
      * pose proof (shadow_mono _ _ Hd). zlia.
      * pose proof (shadow_mono _ _ Hd). zlia. }
split; [exact Hgone|].
split; [exact Hpr|].
split; [exact Hstatic|]. split; [|exact HQT].
intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (AR_extra_law_ok SEGS B lyc Sc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
apply Heqw; [exact Ha64|]. intros HWa. exfalso.
destruct (HWw a HWa) as (_ & [[Hc' Hs'] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] Hr]])]]).
- apply Xs. rewrite Eslo, Eshi. zlia.
- exact (Xb b m Hbin Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (proj1 (Xf cid pos Hin') Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  unfold in_zr in Hr; cbn [fst snd] in Hr. exact (proj2 (Xf cid pos Hin') Hr).
Qed.
Lemma rbn10_set_shadow : forall (fq : YK11.FPState) pc v, aset_shadow_realizes (fx := fq) SEGS B pc v ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  In (cid, pos) own ->
  getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
  shadow_addr (frame_addr lyc cid pos) <= q -> q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
      c2 = mkCfg (mkst (fx := fq) regs2 raw mem2 (seg_rom SEGS)) md2 /\
      ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
      aregs_preserved regsT regs2 /\
      (forall i, 0 <= i < n -> aview SEGS (w_H W) mem2 (q + i) = Some v) /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros fq pc v ASS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n o raw
  HJ Hown Ha0 Ha1 Hn Hq1 Hq2 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof pa_segs_low as segs_low.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption.
  rewrite Hra. exact Hraw. }
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
eapply SRr_mono.
{ exact (ASS lyc Sc W regsT memT mdc cid pos q n HPRE Hin Ha0 Ha1 Hn Hq1 Hq2). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Heff & Hfr & Hpres2 & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
destruct (frames_bounds SEGS B LAWS lyc Sc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
assert (Hx1 : 0 <= frame_addr lyc cid pos < kHighMemEnd) by (pose proof (fs_frame_bytes_nonneg cid); zlia).
assert (Hx2 : 0 <= frame_addr lyc cid pos + fs_frame_bytes cid < kHighMemEnd) by (pose proof (fs_frame_bytes_nonneg cid); zlia).
pose proof (shadow_addr_bounds _ Hx1) as Hsb1. pose proof (shadow_addr_bounds _ Hx2) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (rbn10_ajw STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2 (fun a => q <= a < q + n) HJ).
  - intros a Ha Hna. exact (Hfr a Ha Hna).
  - intros a Ha.
    destruct (Z_lt_ge_dec a (spZ regsT - ESTACK)) as [Hlt|Hge]; [|destruct (Z_lt_ge_dec a (spZ regsT)) as [Hlt2|Hge2]].
    + eapply (apresent_transfer SEGS); [zlia | intros Hi; pose proof (segs_low a Hi); zlia | apply Hfr; zlia | exact (Hpres a Ha)].
    + apply Hpres2. zlia.
    + eapply (apresent_transfer SEGS); [zlia | intros Hi; pose proof (segs_low a Hi); zlia | apply Hfr; zlia | exact (Hpres a Ha)].
  - exact Hsame.
  - intros a Ha. right. right. right. exists cid, pos. split; [exact Hown|]. right. unfold in_zr. cbn [fst snd]. zlia.
  - exact HAR2. }
split; [exact HP|]. split; [exact Heff | exact Hfr].
Qed.
Definition rbn10_W (ly : alayout) (pos a : Z) : Prop :=
  (frame_addr ly 3 pos <= a < frame_addr ly 3 pos + 8) \/
  (shadow_addr (frame_addr ly 3 pos) <= a < shadow_addr (frame_addr ly 3 pos) + 64) \/
  a = flag_addr ly 3 pos.
Lemma rbn10_avoid_hi : forall ly S W m md pos a,
  AR SEGS B ly S W m md -> In (3, pos) (frames S) -> alloc_ceiling <= a -> ~ rbn10_W ly pos a.
Proof.
intros ly S W m md pos a HAR Hin Ha.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR Hin) as (H4 & Hc & _).
destruct (FFL _ _ _ _ _ 3 pos HAR Hin) as (_ & _ & _ & (_ & _ & Hfc)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfb : fs_frame_bytes 3 = 512) by reflexivity. rewrite Hfb in Hc.
assert (Hx : 0 <= frame_addr ly 3 pos + 512 < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds _ Hx) as Hsb.
assert (Hse : shadow_addr (frame_addr ly 3 pos) + 64 <= shadow_addr (frame_addr ly 3 pos + 512))
  by exact (shadow_range_end (frame_addr ly 3 pos) 512 ltac:(lia)).
unfold rbn10_W. lia.
Qed.
Lemma rbn10_avoid_img : forall ly S W m md pos a,
  AR SEGS B ly S W m md -> In (3, pos) (frames S) -> in_img SEGS a -> ~ rbn10_W ly pos a.
Proof.
intros ly S W m md pos a HAR Hin Hi.
pose proof (pa_segs_low a Hi) as Hlow.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR Hin) as (H4 & Hc & _).
destruct (FFL _ _ _ _ _ 3 pos HAR Hin) as (_ & _ & (_ & Hfi) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfb : fs_frame_bytes 3 = 512) by reflexivity. rewrite Hfb in Hc.
assert (Hx : 0 <= frame_addr ly 3 pos < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds _ Hx) as Hsb.
unfold rbn10_W. intros [Hr | [Hr | ->]].
- assert (Hr' : frame_addr ly 3 pos <= a < frame_addr ly 3 pos + fs_frame_bytes 3) by (rewrite Hfb; lia).
  exact (frm_img SEGS B LAWS _ _ _ _ _ 3 pos a HAR Hin Hr' Hi).
- lia.
- exact (Hfi Hi).
Qed.
Lemma rbn10_avoid_blk : forall ly S W m md pos b n a,
  AR SEGS B ly S W m md -> In (3, pos) (frames S) -> In (b, n) (ablocks B ly S) -> b <= a < b + req_size n ->
  ~ rbn10_W ly pos a.
Proof.
intros ly S W m md pos b n a HAR Hin Hb Ha.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR Hin) as (H4 & Hc & _).
destruct (FFL _ _ _ _ _ 3 pos HAR Hin) as (_ & Hfo & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & Hb4 & Hbc & Happ & Hbp & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b n 3 pos HAR Hb Hin) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfb : fs_frame_bytes 3 = 512) by reflexivity. rewrite Hfb in Hc, Hd.
assert (Hx : 0 <= frame_addr ly 3 pos + 512 < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds _ Hx) as Hsb2.
assert (Hx1 : 0 <= frame_addr ly 3 pos < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds _ Hx1) as Hsb1.
assert (Hse : shadow_addr (frame_addr ly 3 pos) + 64 <= shadow_addr (frame_addr ly 3 pos + 512))
  by exact (shadow_range_end (frame_addr ly 3 pos) 512 ltac:(lia)).
unfold rbn10_W. intros [Hr | [Hr | ->]].
- lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia.
- exact (proj2 (Hbp _ Ha) Hfo).
Qed.
Lemma rbn10_avoid_frm : forall ly S W m md pos rest c p a,
  AR SEGS B ly S W m md -> frames S = (3, pos) :: rest -> In (c, p) rest ->
  (in_zr a (frame_rng ly (c, p)) \/ in_zr a (shadow_addr (frame_addr ly c p), fs_frame_bytes c / 8)) ->
  ~ rbn10_W ly pos a.
Proof.
intros ly S W m md pos rest c p a HAR Hfrs Hcp Ha.
assert (Hin : In (3, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (Hin' : In (c, p) (frames S)) by (rewrite Hfrs; right; exact Hcp).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR Hin) as (H4 & Hc & Happ).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c p HAR Hin') as (H4' & Hc' & Happ').
destruct (FFL _ _ _ _ _ 3 pos HAR Hin) as (_ & Hfo & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ c p HAR Hin') as (_ & _ & Hfb' & Hfsh').
apply in_split in Hcp as (l1 & l2 & El).
assert (Hd : zdisjoint (frame_rng ly (3, pos)) (frame_rng ly (c, p))).
{ apply (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (c, p) [] l1 l2 HAR). rewrite Hfrs, El. reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fs_frame_bytes_nonneg c) as Hnn.
assert (Hfb : fs_frame_bytes 3 = 512) by reflexivity. rewrite Hfb in Hc, Hd, Happ.
assert (Hx1 : 0 <= frame_addr ly 3 pos < kHighMemEnd) by (rewrite C4; lia).
assert (Hx2 : 0 <= frame_addr ly 3 pos + 512 < kHighMemEnd) by (rewrite C4; lia).
assert (Hx3 : 0 <= frame_addr ly c p < kHighMemEnd) by (rewrite C4; lia).
assert (Hx4 : 0 <= frame_addr ly c p + fs_frame_bytes c < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds _ Hx1) as Hsb1. pose proof (shadow_addr_bounds _ Hx2) as Hsb2.
pose proof (shadow_addr_bounds _ Hx3) as Hsb3. pose proof (shadow_addr_bounds _ Hx4) as Hsb4.
assert (Hse : shadow_addr (frame_addr ly 3 pos) + 64 <= shadow_addr (frame_addr ly 3 pos + 512))
  by exact (shadow_range_end (frame_addr ly 3 pos) 512 ltac:(lia)).
pose proof (shadow_range_end (frame_addr ly c p) (fs_frame_bytes c) Hnn) as Hse'.
unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, Happ'.
unfold rbn10_W. intros [Hr | [Hr | ->]].
- destruct Ha as [Ha | Ha]; lia.
- destruct Ha as [Ha | Ha]; [lia|].
  destruct Hd as [Hd | Hd]; pose proof (shadow_mono _ _ Hd); lia.
- destruct Ha as [Ha | Ha].
  + exact (proj2 (Hfb' _ Ha) Hfo).
  + specialize (Hfsh' (flag_addr ly 3 pos - shadow_addr (frame_addr ly c p)) ltac:(lia)).
    replace (shadow_addr (frame_addr ly c p) + (flag_addr ly 3 pos - shadow_addr (frame_addr ly c p)))
      with (flag_addr ly 3 pos) in Hfsh' by lia.
    exact (proj2 Hfsh' Hfo).
Qed.
Lemma rbn10_avoid_buf : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly1 S1 W1 m1 md1 pos a,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  AR SEGS B ly1 S1 W1 m1 md1 -> frames S1 = (3, pos) :: frames Sc ->
  Permutation (ablocks B ly1 S1) (ablocks B lyc Sc) ->
  (forall c p, frame_addr ly1 c p = frame_addr lyc c p) ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  ~ rbn10_W ly1 pos a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly1 S1 W1 m1 md1 pos a HJ HAR1 Hfrs1 Hperm Efa Hw.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (3, pos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw)
  as (_ & [[Hc _] | [(_ & b & n & Hb & Hr & _) | (c & p & Hcp & Hr)]]).
- exact (rbn10_avoid_hi _ _ _ _ _ pos a HAR1 Hin Hc).
- exact (rbn10_avoid_blk _ _ _ _ _ pos b n a HAR1 Hin (Permutation_in _ (Permutation_sym Hperm) Hb) Hr).
- apply (rbn10_avoid_frm _ _ _ _ _ pos (frames Sc) c p a HAR1 Hfrs1).
  + rewrite Hfrs. apply in_or_app. left. exact Hcp.
  + unfold frame_rng. cbn [fst snd]. rewrite !Efa. unfold frame_rng in Hr. cbn [fst snd] in Hr.
    destruct Hr as [[_ Hr] | [_ Hr]]; [left | right]; exact Hr.
Qed.
Lemma rbn10_post : forall X pos lyc1 Sc1 W1 memc1 mdc1 regsF memF mdF,
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X) (ri_own X)
    (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X) (ri_k X) ->
  ri_sp0 X - ri_STK X <= spZ (ri_regs X) - REAC_BOX_NAME_STK ->
  (rbm_args X ->
     rbn_said B (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (spZ (ri_regs X)) (ri_sp0 X) (ri_said X) (ri_sd X) /\
     rbn_bufs B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_own X) (ri_lyc X) (ri_Sc X) (ri_W X)
       (ri_memc X) (spZ (ri_regs X)) (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X) (ri_display X)
       (ri_display_len X)) ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 mdc1 (ri_k X) ->
  frames Sc1 = (3, pos) :: frames (ri_Sc X) ->
  Permutation (ablocks B lyc1 Sc1) (ablocks B (ri_lyc X) (ri_Sc X)) ->
  rbn_kept B X W1 memc1
    (rbn_wr (ri_f X) (ri_sd X) (ri_i X) (ri_o X) (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X)
       (ri_display X) (ri_display_len X)) ->
  (rbm_acc X = true ->
     garr8 SEGS (mrestrict (w_H W1) memc1) (ri_name X) (rbm_NM X ++ [0]) /\
     garr8 SEGS (mrestrict (w_H W1) memc1) (ri_token X) (bn_TK (rbm_NM X) ++ [0]) /\
     garr8 SEGS (mrestrict (w_H W1) memc1) (ri_display X) (bn_DP (rbm_NM X) (ri_i X) (ri_o X) ++ [0])) ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    (ri_own X) lyc1 (stack_free_state 3 pos Sc1) W1 memF mdF (ri_k X) ->
  aregs_preserved (ri_regs X) regsF ->
  getr regsF 10 = w64 (if rbm_acc X then 0 else -1) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ rbn10_W lyc1 pos a -> aview SEGS (w_H W1) memF a = aview SEGS (w_H W1) memc1 a) ->
  rbn_post B X W1 (mkCfg (mkst (fx := ri_fq X) regsF (getr (ri_regs X) 1) memF (seg_rom SEGS)) mdF).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 regsF memF mdF HJ Hstk Hargs HJ1 Hfrs1 Hperm HK Hacc HJF HP H10F KK.
pose proof HJ as (_ & Hly0 & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _ & _).
pose proof HJ1 as (AR1 & Hly1 & _).
pose proof HJF as (_ & _ & _ & _ & _ & HfrsF & _).
pose proof Hstatic as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (bv_unsigned_in_range 64 (getr (ri_regs X) 2)) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
assert (Efa : forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p).
{ destruct Hly0 as (_ & _ & _ & _ & _ & EF0 & _). destruct Hly1 as (_ & _ & _ & _ & _ & EF1 & _).
  intros c p. unfold frame_addr. rewrite EF0, EF1. reflexivity. }
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs1; left; reflexivity).
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6). unfold rbn_SP in K1, K5, K6. unfold spZ in Hstk, K1, K5, K6.
unfold rbn_post, treac_box_name_post.
exists lyc1, (stack_free_state 3 pos Sc1), regsF, memF, mdF.
split; [reflexivity|]. split; [exact HJF|]. split; [exact HP|].
split; [rewrite HfrsF, Hfrs0; reflexivity|].
split; [unfold ablocks; rewrite blocks_stack_free_state; exact Hperm|].
split; [exact H10F|].
split.
{ intros a Ha Hn Hw. unfold spZ in Hn.
  rewrite (KK a ltac:(lia) (rbn10_avoid_hi _ _ _ _ _ pos a AR1 Hin3 ltac:(lia))). exact (K1 a Ha Hn Hw). }
split.
{ intros b m j Hb Hj Hw.
  assert (Hb1 : In (b, m) (ablocks B lyc1 Sc1))
    by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m AR1 Hb1) as (_ & Hb4 & Hbc & _).
  rewrite (KK (b + j) ltac:(lia) (rbn10_avoid_blk _ _ _ _ _ pos b m (b + j) AR1 Hin3 Hb1 ltac:(lia))).
  exact (K2 b m j Hb Hj Hw). }
split.
{ intros a Hi Ho He. pose proof (pa_segs_low a Hi) as Hlow.
  rewrite (KK a ltac:(lia) (rbn10_avoid_img _ _ _ _ _ pos a AR1 Hin3 Hi)). exact (K3 a Hi Ho He). }
split.
{ intros cid p a Hcp Ha Hw.
  assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite Hfrs1; right; exact Hcp).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p AR1 Hcp1) as (Hc4 & Hcc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  assert (Ha' : in_zr a (frame_rng lyc1 (cid, p)) \/ in_zr a (shadow_addr (frame_addr lyc1 cid p), fs_frame_bytes cid / 8)).
  { unfold frame_rng in *. cbn [fst snd] in *. rewrite !Efa. exact Ha. }
  assert (Hx : 0 <= frame_addr lyc1 cid p + fs_frame_bytes cid < kHighMemEnd) by (rewrite C4; lia).
  pose proof (shadow_addr_bounds _ Hx) as Hsb.
  pose proof (shadow_range_end (frame_addr lyc1 cid p) (fs_frame_bytes cid) Hnn) as Hse.
  assert (Hx0 : 0 <= frame_addr lyc1 cid p < kHighMemEnd) by (rewrite C4; lia).
  pose proof (shadow_addr_bounds _ Hx0) as Hsb0.
  assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold in_zr, frame_rng in Ha'; cbn [fst snd] in Ha'; lia).
  rewrite (KK a Ha64 (rbn10_avoid_frm _ _ _ _ _ pos (frames (ri_Sc X)) cid p a AR1 Hfrs1 Hcp Ha')).
  exact (K4 cid p a Hcp Ha Hw). }
split.
{ intros a Ha Hn Hp. unfold spZ in Hn.
  apply (apresent_transfer SEGS (w_H W1) (w_H W1) memc1 memF a);
    [lia | intros Hi; pose proof (pa_segs_low a Hi); lia | | exact (K5 a Ha Hn Hp)].
  apply KK; [lia | exact (rbn10_avoid_hi _ _ _ _ _ pos a AR1 Hin3 ltac:(lia))]. }
split.
{ intros a Ha. unfold spZ in Ha.
  apply (apresent_transfer SEGS (w_H W1) (w_H W1) memc1 memF a);
    [lia | intros Hi; pose proof (pa_segs_low a Hi); lia | | exact (K6 a Ha)].
  apply KK; [lia | exact (rbn10_avoid_hi _ _ _ _ _ pos a AR1 Hin3 ltac:(lia))]. }
intros Hacc'.
destruct (Hacc Hacc') as (G1 & G2 & G3).
destruct (rbn10_acc_lens _ _ _ _ _ _ _ _ _ _ Hacc') as (Hargs' & L1 & L2 & L3).
destruct (Hargs Hargs') as (_ & (B1 & B2 & B3 & _)).
assert (KB : forall b n, rbn_buf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_own X) (ri_lyc X) (ri_Sc X)
  (ri_W X) (ri_memc X) (spZ (ri_regs X)) b n ->
  forall a, b <= a < b + n -> aview SEGS (w_H W1) memF a = aview SEGS (w_H W1) memc1 a).
{ intros b n (Hb0 & Hb63 & _ & _ & _ & _ & Hbw) a Ha. destruct (Hbw a Ha) as (Hw & _).
  apply KK; [lia|].
  exact (rbn10_avoid_buf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lyc1 Sc1 W1 memc1 mdc1 pos a HJ AR1 Hfrs1 Hperm Efa Hw). }
unfold rbm_NM in *.
split; [|split].
- eapply (garr8_aview_kept SEGS); [|exact G1].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply (KB _ _ B1). lia.
- eapply (garr8_aview_kept SEGS); [|exact G2].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply (KB _ _ B2). lia.
- eapply (garr8_aview_kept SEGS); [|exact G3].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply (KB _ _ B3). lia.
Qed.
Theorem rbn_seg10 : rbn_seg10_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H10.
pose proof HX as (HJ & _ & _ & Hra & _ & Hgp & Htp & _ & Hal & Hstk & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hargs).
destruct H10 as ((HJ1 & Hfrs1 & Hperm & _ & HK & Hfr & Hfl & _) & (G2 & G3 & G4 & G8 & G9 & G19 & G23) &
  G18 & G20 & Hacc).
pose proof HJ1 as HJ1m.
pose proof HJ as (_ & Hly0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _ & _).
pose proof HJ1 as (HAR1 & Hly1 & _).
pose proof Hstatic as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Efa : forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p).
{ destruct Hly0 as (_ & _ & _ & _ & _ & EF0 & _). destruct Hly1 as (_ & _ & _ & _ & _ & EF1 & _).
  intros c p. unfold frame_addr. rewrite EF0, EF1. reflexivity. }
assert (Ela : flag_addr lyc1 3 pos = rbn_FL X pos).
{ destruct Hly0 as (_ & _ & _ & _ & _ & EF0 & _). destruct Hly1 as (_ & _ & _ & _ & _ & EF1 & _).
  unfold rbn_FL, flag_addr. rewrite EF0, EF1. reflexivity. }
assert (EF : frame_addr lyc1 3 pos = rbn_F X pos) by (unfold rbn_F; apply Efa).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HF4 & HFc & HFapp).
destruct (FFL _ _ _ _ _ 3 pos HAR1 Hin3) as (_ & HFLo & _ & (HFL4 & _ & HFLc)).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (_ & _ & HFb & _).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
rewrite Hfb3, EF in HFc, HFb, HFapp. rewrite EF in HF4. rewrite Ela in HFLo, HFL4, HFLc.
assert (HFLnf : ~ (rbn_F X pos <= rbn_FL X pos < rbn_F X pos + 512)) by (intros Hr; exact (proj2 (HFb _ Hr) HFLo)).
pose proof (bv_unsigned_in_range 64 (getr (ri_regs X) 2)) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
assert (HSPc : alloc_ceiling + 8816 <= rbn_SP X) by (unfold rbn_SP, spZ in *; lia).
assert (HSPt : rbn_SP X + 16 <= 2 ^ 47) by (unfold rbn_SP, spZ in *; lia).
assert (ESP : rbn_SP X = spZ (ri_regs X)) by reflexivity.
assert (Hx1 : 0 <= rbn_F X pos < kHighMemEnd) by (rewrite C4; lia).
assert (Hx2 : 0 <= rbn_F X pos + 512 < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds _ Hx1) as Hsb1. pose proof (shadow_addr_bounds _ Hx2) as Hsb2.
assert (Hse : rbn_SH X pos + 64 <= shadow_addr (rbn_F X pos + 512))
  by (unfold rbn_SH; exact (shadow_range_end (rbn_F X pos) 512 ltac:(lia))).
change (shadow_addr (rbn_F X pos)) with (rbn_SH X pos) in Hsb1.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (H19u : bv_unsigned (getr regs1 19) = rbn_F X pos) by (rewrite G19; unfold w64; apply unsigned_lit_small; lia).
assert (H23u : bv_unsigned (getr regs1 23) = rbn_F X pos) by (rewrite G23; unfold w64; apply unsigned_lit_small; lia).
assert (H8u : bv_unsigned (getr regs1 8) = rbn_SP X)
  by (rewrite G8; unfold w64, rbn_SP, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (rbn10_entry (ri_fq X) X pos regs1 W1 memc1 H19u H23u H8u ltac:(lia) ltac:(lia) ltac:(lia)
  (fun o Ho => proj1 (HFb (rbn_F X pos + o) ltac:(lia))) Hfl Hfr) as HS.
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_both3_reac_box_name + RBN_P10) with (BASE + (AF_both3_reac_box_name + RBN_P10)) by lia.
set (fq := ri_fq X) in *.
pose proof (@SRr_run_pi_AJ fq _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call fq _ _ _ _ _ B LAWS) as RUNC.
pose proof (@aj_flag_store_pi fq _ _ _ _ _ B LAWS ML ASF FFL) as RUNF.
remember (Eimg (Ereg regs1 (rbn10_extra X pos))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (rbn_FL X pos))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (ES : forall j r, nth_error rbn_saved_regs j = Some r -> ew E (33 + j) = getr (ri_regs X) (Z_to_bv 5 r))
  by (intros j r Hj; subst E; apply rbn10_ew_saved; exact Hj).
assert (E19 : bv_unsigned (ew E 19) = rbn_F X pos) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19u).
assert (E23 : bv_unsigned (ew E 23) = rbn_F X pos) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23u).
assert (E8 : bv_unsigned (ew E 8) = rbn_SP X) by (rewrite (EE 8%nat 8%bv eq_refl); exact H8u).
clear HE.
paj_run_shc RUNP RUNC HS HJ1.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply awr_ok_cons_gen; [reflexivity | exact E19 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    right. right. right. exists 3, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EF, Hfb3. lia.
  - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_F X pos <= a < rbn_F X pos + 8) ->
  aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) memc1 a).
{ apply (rbn10_kept_frame E (ss_mem ss_rbn10) (w_H W1) memc1 (ms_mem ms)
    (fun a => rbn_F X pos <= a < rbn_F X pos + 8) HFr).
  intros a (r & Hr & Hw). unfold ss_rbn10, rbn10_regions in Hr. cbn [ss_mem In] in Hr.
  repeat destruct Hr as [<- | Hr]; try destruct Hr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?E19, ?E23, ?E8 in Hw; lia. }
clear HF HFr.
set (A := rbn_A X) in *.
assert (HA : rbn_SP X - 351 <= A <= rbn_SP X - 320 /\ A mod 32 = 0).
{ unfold A, rbn_A. pose proof (Z.div_mod (rbn_SP X - 320) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (rbn_SP X - 320) 32 ltac:(lia)) as M.
  split; [lia|]. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
pmkst HS.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (1%bv : bv 5) R1.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite (EE 18%nat 18%bv eq_refl), G18 in R10. rewrite (EE 2%nat 2%bv eq_refl), G2 in R2.
rewrite (EE 3%nat 3%bv eq_refl), G3 in R3. rewrite (EE 4%nat 4%bv eq_refl), G4 in R4.
eapply SRr_bind.
{ eapply (rbn10_set_shadow fq (SIGMA AS___asan_set_shadow_f5) 0xf5 (ASSF5 fq) W1 (ms_regs ms) (ms_mem ms)
    _ _ _ _ _ _ _ _ _ _ _ _ _ 3 pos (rbn_SH X pos) 64 (A - ri_sp0 X) _ HJ1).
  - left; reflexivity.
  - exact R10.
  - unfold w64. exact R11.
  - lia.
  - rewrite EF. unfold rbn_SH. lia.
  - rewrite EF, Hfb3. change (512 / 8) with 64. unfold rbn_SH. lia.
  - unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - destruct HA as (_ & HA32). apply Z.mod_divide in HA32; [|lia]. pose proof Hsp0al as H16.
    apply Z.mod_divide in H16; [|lia]. destruct HA32 as (q1 & Hq1). destruct H16 as (q2 & Hq2).
    replace (A - ri_sp0 X) with ((2 * q1 - q2) * 16) by lia. apply Z.mod_mul. lia.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hf5 & K2).
jafter_call_keep_pi HS 46%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst].
  destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos (proj1 HJ2) Hin3) as (_ & _ & HFb2 & _).
  rewrite Hfb3, EF in HFb2.
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_SH X pos <= a < rbn_SH X pos + 64) ->
     mbyte SEGS (mrestrict (w_H W1) mem2) a = mbyte SEGS (mrestrict (w_H W1) (ms_mem ms)) a)
    by (intros a Ha Hn; apply (mbyte_of_aview SEGS); exact (K2 a Ha Hn)).
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?E19, ?E23, ?E8; intros a Ha.
  - apply KR; lia.
  - intros _. apply (apresent_writable SEGS). exact (proj1 (HFb2 a ltac:(lia))).
  - apply KR; lia.
  - lia.
  - apply KR; lia.
  - lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 46 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall n, (n < 46)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply ew_havoc_old; exact Hn).
clear HE2.
assert (E232 : bv_unsigned (ew E2 32) = rbn_FL X pos) by (rewrite OLD, E32 by lia; apply unsigned_lit_small; lia).
assert (E219 : bv_unsigned (ew E2 19) = rbn_F X pos) by (rewrite OLD by lia; exact E19).
assert (E223 : bv_unsigned (ew E2 23) = rbn_F X pos) by (rewrite OLD by lia; exact E23).
assert (E28 : bv_unsigned (ew E2 8) = rbn_SP X) by (rewrite OLD by lia; exact E8).
destruct (FFL _ _ _ _ _ 3 pos (proj1 HJ2) Hin3) as (HFLp2 & _). rewrite Ela in HFLp2.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  assert (HRo : region_ok SEGS E2 (ms_mem msx) rbn10_flag_region);
  [| assert (HDj : all_disjoint E2 rbn10_flag_region (ss_mem ssx));
     [| pose proof (st_ok_pi_add_region E2 ssx msx rbn10_flag_region HS eq_refl HRo HDj) as HS3]] end.
{ unfold region_ok, rbn10_flag_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  rewrite E232. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. replace (rbn_FL X pos + o) with (rbn_FL X pos) by lia. apply (apresent_writable SEGS). exact HFLp2. }
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, rbn10_flag_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E232, E219, E223, E28. repeat split; lia. }
clear HS HRo HDj. norm_ss HS3. rename HS3 into HS.
paj_run_flag_sh RUNF HS HJ2.
- lia.
- intros a (r & Hr & Hw). cbn [ss_mem In] in Hr.
  repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
  + right. rewrite Ela. rewrite E232 in Hw. lia.
  + left. right. right. right. exists 3, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EF, Hfb3. rewrite E219 in Hw. lia.
  + rewrite E223 in Hw. lia.
  + rewrite E28 in Hw. lia.
- intros msr HSr.
  pose proof (st_ok_pi_region_nth E2 _ msr 0 _ HSr eq_refl) as HR.
  pose proof (field_of_region E2 (ms_mem msr) 32 (rbn_FL X pos) _ _ _ _ _ 0 1%N (SLit 0) 0 HR E232
    ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite Ela. specialize (V 0%nat ltac:(cbn; lia)). cbn [Z.of_nat] in V. rewrite !Z.add_0_r in V. exact V.
- match goal with |- context [mkCfg ?msF _] => rename msF into msZ end.
  match goal with H : frame_of _ _ _ (mrestrict _ (ms_mem msZ)) |- _ => rename H into HFr3 end.
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (a = rbn_FL X pos \/ rbn_F X pos <= a < rbn_F X pos + 8) ->
    aview SEGS (w_H W1) (ms_mem msZ) a = aview SEGS (w_H W1) mem2 a).
  { lazymatch type of HFr3 with frame_of _ ?rsx _ _ =>
    apply (rbn10_kept_frame E2 rsx (w_H W1) mem2 (ms_mem msZ)
      (fun a => a = rbn_FL X pos \/ rbn_F X pos <= a < rbn_F X pos + 8) HFr3) end.
    intros a (r & Hr & Hw). cbn [ss_mem In] in Hr.
    repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
    rewrite ?E232, ?E219, ?E223, ?E28 in Hw; lia. }
  assert (KK : forall a, 0 <= a < 2 ^ 64 -> ~ rbn10_W lyc1 pos a ->
    aview SEGS (w_H W1) (ms_mem msZ) a = aview SEGS (w_H W1) memc1 a).
  { intros a Ha HW. unfold rbn10_W in HW. rewrite EF, Ela in HW.
    change (shadow_addr (rbn_F X pos)) with (rbn_SH X pos) in HW.
    rewrite (K3 a Ha ltac:(tauto)), (K2 a Ha ltac:(tauto)), (K1 a Ha ltac:(tauto)). reflexivity. }
  eapply (@paj_ret_at fq _ _ _ _ W1 E2 _ msZ _ _ HS); [vm_compute; reflexivity | vm_compute; reflexivity |].
  intros mat3.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  assert (EPC : v_jalr (getr (ms_regs msZ) 1) 0 = getr (ri_regs X) 1).
  { rewrite Q1, OLD by lia. pose proof (ES 0%nat 1 eq_refl) as S1. cbn [Nat.add] in S1. rewrite S1.
    change (Z_to_bv 5 1) with (Z_to_bv 5 (bv_unsigned (1%bv : bv 5))). rewrite Z_to_bv_bv_unsigned. exact Hra. }
  assert (H10F : getr (ms_regs msZ) 10 = w64 (if rbm_acc X then 0 else -1)).
  { rewrite Q10, OLD by lia. rewrite (EE 20%nat 20%bv eq_refl). exact G20. }
  assert (HPF : aregs_preserved (ri_regs X) (ms_regs msZ)).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    destruct Hr' as [-> | [-> | [-> | Hr']]].
    - prreg HS (Z_to_bv 5 2) Q. rewrite Q, OLD by lia. rewrite (EE 8%nat 8%bv eq_refl), G8.
      change (Z_to_bv 5 2) with (Z_to_bv 5 (bv_unsigned (2%bv : bv 5))).
      unfold w64, rbn_SP, spZ. rewrite !Z_to_bv_bv_unsigned. reflexivity.
    - prreg HS (Z_to_bv 5 3) Q. rewrite Q, OLD by lia. rewrite (EE 3%nat 3%bv eq_refl), G3.
      change (Z_to_bv 5 3) with (Z_to_bv 5 (bv_unsigned (3%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      symmetry. exact Hgp.
    - prreg HS (Z_to_bv 5 4) Q. rewrite Q, OLD by lia. rewrite (EE 4%nat 4%bv eq_refl), G4.
      change (Z_to_bv 5 4) with (Z_to_bv 5 (bv_unsigned (4%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      symmetry. exact Htp.
    - destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]].
      + prreg HS (Z_to_bv 5 8) Q. rewrite Q, OLD by lia. exact (ES 1%nat 8 eq_refl).
      + prreg HS (Z_to_bv 5 9) Q. rewrite Q, OLD by lia. exact (ES 2%nat 9 eq_refl).
      + prreg HS (Z_to_bv 5 18) Q. rewrite Q, OLD by lia. exact (ES 3%nat 18 eq_refl).
      + prreg HS (Z_to_bv 5 19) Q. rewrite Q, OLD by lia. exact (ES 4%nat 19 eq_refl).
      + prreg HS (Z_to_bv 5 20) Q. rewrite Q, OLD by lia. exact (ES 5%nat 20 eq_refl).
      + prreg HS (Z_to_bv 5 21) Q. rewrite Q, OLD by lia. exact (ES 6%nat 21 eq_refl).
      + prreg HS (Z_to_bv 5 22) Q. rewrite Q, OLD by lia. exact (ES 7%nat 22 eq_refl).
      + prreg HS (Z_to_bv 5 23) Q. rewrite Q, OLD by lia. exact (ES 8%nat 23 eq_refl).
      + prreg HS (Z_to_bv 5 24) Q. rewrite Q, OLD by lia. exact (ES 9%nat 24 eq_refl).
      + prreg HS (Z_to_bv 5 25) Q. rewrite Q, OLD by lia. exact (ES 10%nat 25 eq_refl).
      + prreg HS (Z_to_bv 5 26) Q. rewrite Q, OLD by lia. exact (ES 11%nat 26 eq_refl).
      + prreg HS (Z_to_bv 5 27) Q. rewrite Q, OLD by lia. exact (ES 12%nat 27 eq_refl). }
  rewrite EPC.
  apply (rbn10_post X pos lyc1 Sc1 W1 memc1 mdc1 (ms_regs msZ) (ms_mem msZ) _ HJ Hstk Hargs HJ1m Hfrs1 Hperm HK Hacc);
    [| exact HPF | exact H10F | exact KK].
  exact (ajournal_materialize SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ2).
Qed.
End h.
End f.
End d.

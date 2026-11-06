(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 167 of its 196 lines of code are new or changed and 516 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacBoxName.v, with its module paths and module names changed; 358 of its 401 lines of code are new or changed and 153 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC81 YC45 YC85 YCkd YC1i YCjr YCbf YCj1 YCja YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh SbDec SbDecCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Definition sbe_stk_chunk (j : nat) : YP09.chunk := YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0)).
Definition sbe_stack : YP09.region := YP09.mkRegion (Some 8%nat) (-96) 0 0 0 (map sbe_stk_chunk (seq 0 12)).
Definition sbe_frame : YP09.region := YP09.mkRegion (Some 23%nat) 0 64 0 8 [YP09.mkChunk 56 (CVal 8 (SOff 44 0))].
Definition sbe_shadow : YP09.region := YP09.mkRegion (Some 24%nat) 0 8 0 8 [].
Definition sbe_flag : YP09.region := YP09.mkRegion (Some 44%nat) 0 1 0 1 [].
Definition sbe_regions : smem := [sbe_stack; sbe_frame; sbe_shadow; sbe_flag].
Definition sbe_facts : facts :=
  mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (23%nat, HPTR 6); (24%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3);
           (44%nat, HPTR 0)] [] [].
Definition sbe_sr : list sv := sr_set sr_atoms 18%bv (SOff 23 0).
Definition ss_sbE : sstate := mkSS (AF_both3_sb_dec + SBD_PE) sbe_sr sbe_regions None sbe_facts.
Definition sbe_W (F FL a : Z) : Prop := F <= a < F + 8 \/ shadow_addr F <= a < shadow_addr F + 8 \/ a = FL.
Lemma sbe_ly_eq : forall n m ly ly1 ly2, layout_le n ly ly1 -> layout_le m ly ly2 ->
  (forall c p, frame_addr ly1 c p = frame_addr ly2 c p) /\ (forall c p, flag_addr ly1 c p = flag_addr ly2 c p).
Proof.
intros n m ly ly1 ly2 (_ & _ & _ & _ & _ & H1 & _) (_ & _ & _ & _ & _ & H2 & _).
split; intros c p; unfold frame_addr, flag_addr; rewrite H1, H2; reflexivity.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Definition sbe_extra (X : sbd_in) (pos : Z) : list word :=
  map (fun r => getr (si_regs X) (Z_to_bv 5 r)) sbd_saved_regs ++ [Z_to_bv 64 (sbd_FL X pos)].
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Lemma sbe_sep : forall ly S (W : world SEGS) m md pos frs,
  AR SEGS B ly S W m md -> frames S = (0, pos) :: frs ->
  (forall a, alloc_ceiling <= a -> ~ sbe_W (frame_addr ly 0 pos) (flag_addr ly 0 pos) a) /\
  (forall a, in_img SEGS a -> ~ sbe_W (frame_addr ly 0 pos) (flag_addr ly 0 pos) a) /\
  (forall b n i, In (b, n) (ablocks B ly S) -> 0 <= i < req_size n ->
     ~ sbe_W (frame_addr ly 0 pos) (flag_addr ly 0 pos) (b + i)) /\
  (forall cid p a, In (cid, p) frs ->
     (in_zr a (frame_rng ly (cid, p)) \/ in_zr a (shadow_addr (frame_addr ly cid p), fs_frame_bytes cid / 8)) ->
     ~ sbe_W (frame_addr ly 0 pos) (flag_addr ly 0 pos) a).
Proof.
intros ly S W m md pos frs HAR Hfrs.
assert (Hin : In (0, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR Hin) as (_ & Happ & Hfb & Hfsh).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR Hin) as (HF4 & HFc & _).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 pos HAR Hin) as (Hal & _ & _).
destruct (FFL ly S W m md 0 pos HAR Hin) as (_ & HFLo & (_ & HFLimg) & (HFL4 & (_ & HFLz) & HFLc)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
change (fs_frame_bytes 0) with 64 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
split.
{ intros a Ha [Hw | [Hw | Hw]]; unfold shadow_addr, SHADOW_OFF in *; lia. }
split.
{ intros a Him [Hw | [Hw | Hw]].
  - refine (proj2 (al_client_img _ _ LAWS ly S W m md a HAR _) Him).
    right; left. exists 0, pos. split; [exact Hin|]. change (fs_frame_bytes 0) with 64. lia.
  - pose proof (pa_segs_low a Him) as Hl. unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
  - subst a. exact (HFLimg Him). }
split.
{ intros b n i Hb Hi Hw.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & Hb4 & Hbc & Hbapp & Hbown & _ & _).
  pose proof (sep_block_frame SEGS B LAWS ly S W m md b n 0 pos HAR Hb Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  destruct Hw as [Hw | [Hw | Hw]].
  - lia.
  - unfold shadow_addr, SHADOW_OFF in Hw. lia.
  - apply (proj2 (Hbown (b + i) ltac:(lia))). rewrite Hw. exact HFLo. }
intros cid p a Hcp Ha Hw.
assert (Hin2 : In (cid, p) (frames S)) by (rewrite Hfrs; right; exact Hcp).
destruct (in_split _ _ Hcp) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS ly S W m md (0, pos) (cid, p) [] l2 l3 HAR
  ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid p HAR Hin2) as (_ & Happ2 & Hfb2 & Hfsh2).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR Hin2) as (HG4 & HGc & _).
destruct (frame_al64 SEGS B _ _ _ _ _ cid p HAR Hin2) as (Hal2 & Hbs2 & H642).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ2.
destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha.
- destruct Hw as [Hw | [Hw | Hw]].
  + lia.
  + unfold shadow_addr, SHADOW_OFF in Hw. lia.
  + apply (proj2 (Hfb2 a Ha)). rewrite Hw. exact HFLo.
- destruct Hw as [Hw | [Hw | Hw]].
  + unfold shadow_addr, SHADOW_OFF in Ha. lia.
  + unfold shadow_addr, SHADOW_OFF in Ha, Hw. lia.
  + apply (proj2 (Hfsh2 (a - shadow_addr (frame_addr ly cid p)) ltac:(lia))).
    replace (shadow_addr (frame_addr ly cid p) + (a - shadow_addr (frame_addr ly cid p))) with a by lia.
    rewrite Hw. exact HFLo.
Qed.
Lemma sbe_awr : forall STK sp0 FP bl0 lyc Sc own F FL a,
  alloc_ceiling <= sp0 - STK ->
  (forall c p, In (c, p) own -> In (c, p) (frames Sc)) ->
  (forall a, alloc_ceiling <= a -> ~ sbe_W F FL a) ->
  (forall b n i, In (b, n) (ablocks B lyc Sc) -> 0 <= i < req_size n -> ~ sbe_W F FL (b + i)) ->
  (forall cid p a, In (cid, p) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, p)) \/ in_zr a (shadow_addr (frame_addr lyc cid p), fs_frame_bytes cid / 8)) ->
     ~ sbe_W F FL a) ->
  awr_byte STK sp0 FP bl0 (ablocks B lyc Sc) lyc own a -> ~ sbe_W F FL a.
Proof.
intros STK sp0 FP bl0 lyc Sc own F FL a Hst Hown K1 K2 K4
  [Ha | [(_ & b & n & Hb & Ha) | [(b & n & Hb & _ & Ha) | (cid & p & Hcp & Ha)]]].
- apply K1. lia.
- replace a with (b + (a - b)) by lia. apply (K2 b n); [exact Hb | lia].
- replace a with (b + (a - b)) by lia. apply (K2 b n); [exact Hb | lia].
- apply (K4 cid p a (Hown cid p Hcp)). unfold frame_rng. cbn [fst snd]. exact Ha.
Qed.
Lemma sbe_entry : forall (fq : YK11.FPState) X pos regs1 lyc1 Sc1 W1 memc1 mdc1,
  sbd_cx B X -> sbd_stE B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 (sbe_extra X pos))) ss_sbE
    (restrict (w_H W1) (mkst (fx := fq) regs1 (Z_to_bv 64 (BASE + (AF_both3_sb_dec + SBD_PE))) memc1 (seg_rom SEGS))).
Proof.
intros fq X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HE.
destruct HE as ((HJ1 & Hfrs1 & _ & _ & _ & Hfr & HFLv & _ & _) & _ &
  (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R24 & R25 & R26 & R27) & _).
destruct HX as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hstk & Hsp & _).
pose proof HJ as (_ & Hly0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof HJ1 as (HAR1 & Hly1 & _).
destruct (sbe_ly_eq _ _ _ _ _ Hly1 Hly0) as (EF & EFL).
assert (Hin : In (0, pos) (frames Sc1)) by (rewrite Hfrs1; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR1 Hin) as (_ & Happ & Hfb & Hfsh).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR1 Hin) as (HF4 & HFc & _).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 pos HAR1 Hin) as (Hal & _ & _).
destruct (FFL _ _ _ _ _ 0 pos HAR1 Hin) as (HFLp & HFLo & _ & (HFL4 & (_ & HFLz) & HFLc)).
rewrite (EF 0 pos) in Happ, Hfb, Hfsh, HF4, HFc, Hal.
rewrite (EFL 0 pos) in HFLp, HFLo, HFL4, HFLz, HFLc.
assert (HFLnf : ~ (frame_addr (si_lyc X) 0 pos <= flag_addr (si_lyc X) 0 pos < frame_addr (si_lyc X) 0 pos + fs_frame_bytes 0)).
{ intros H. apply (proj2 (Hfb _ H)). exact HFLo. }
change (frame_addr (si_lyc X) 0 pos) with (sbd_F X pos) in *.
change (flag_addr (si_lyc X) 0 pos) with (sbd_FL X pos) in *.
change (fs_frame_bytes 0) with 64 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSB : SB_DEC_STK = 4256) by reflexivity.
remember (Eimg (Ereg regs1 (sbe_extra X pos))) as E eqn:HEd.
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (sbe_extra X pos) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E8 : ew E 8 = Z_to_bv 64 (sbd_SP X)) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E23 : ew E 23 = Z_to_bv 64 (sbd_F X pos)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = Z_to_bv 64 (sbd_SH X pos)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (E44 : ew E 44 = Z_to_bv 64 (sbd_FL X pos)) by (exact (EX 12%nat ltac:(lia))).
unfold sbd_SH in E24.
remember (sbd_SP X) as SP eqn:HSPd. remember (sbd_F X pos) as F eqn:HFd. remember (sbd_FL X pos) as FL eqn:HFLd.
assert (HSP1 : alloc_ceiling + 4256 <= SP) by lia.
assert (HSP2 : SP <= 2 ^ 47) by lia.
rewrite restrict_mkst_fx. unfold ss_sbE. apply pa_entry_st_ok_full.
- unfold sbe_sr. apply regs_ok_rereg.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 23%nat 23%bv eq_refl), R18, R23. reflexivity.
- vm_compute. reflexivity.
- unfold sbe_regions. repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok, sbe_stack.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E8, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
    destruct (nth_error sbd_saved_regs j) as [r|] eqn:Hr; [| apply nth_error_None in Hr; cbn in Hr; lia].
    assert (Hn : nth_error (sbe_extra X pos) j = Some (getr (si_regs X) (Z_to_bv 5 r))).
    { unfold sbe_extra. rewrite nth_error_app1 by (rewrite length_map; cbn; lia). rewrite nth_error_map, Hr. reflexivity. }
    unfold sbe_stk_chunk.
    pose proof (bv_unsigned_in_range 64 (getr (si_regs X) (Z_to_bv 5 r))) as Hb.
    change (bv_modulus 64) with (2 ^ 64) in Hb.
    apply (chunk_ok_val SEGS E _ SP (-8 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0) (bv_unsigned (getr (si_regs X) (Z_to_bv 5 r)))).
    * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EX j) by lia.
      rewrite (nth_error_nth _ _ _ Hn). symmetry. apply Z_to_bv_bv_unsigned.
    * zside.
    * zside.
    * replace (SP + (-8 - 8 * Z.of_nat j)) with (SP - 8 - 8 * Z.of_nat j) by lia. subst SP. exact (Hfr j r Hr).
  + unfold region_ok, sbe_frame.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E23, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hfb (F + o) ltac:(lia))).
    * constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ F 56 8 (SOff 44 0) FL);
        [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | subst F FL; exact HFLv].
  + unfold region_ok, sbe_shadow.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E24, unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia). unfold shadow_addr, SHADOW_OFF in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hfsh o ltac:(lia))).
  + unfold region_ok, sbe_flag.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E44, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). replace (FL + o) with FL by lia. exact HFLp.
- apply pairwise_disjoint_of_extents.
  unfold sbe_regions, sbe_stack, sbe_frame, sbe_shadow, sbe_flag, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E8, E23, E24, E44, !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold shadow_addr, SHADOW_OFF in *. repeat split; lia.
- split; [|split; exact I].
  cbn [sbe_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
  rewrite E8, E23, E24, E44, !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
  unfold shadow_addr, SHADOW_OFF in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
Qed.
Theorem sbd_segE : sbd_segE_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HE.
pose proof pa_segs_low as Hsegs.
pose proof (sbe_entry (si_fq X) X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HE) as HS.
destruct HE as ((HJ1 & Hfrs1 & Hbl1 & _ & Hkept & _ & _ & _ & _) & _ &
  (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R24 & R25 & R26 & R27) & Hrec).
destruct HX as (HJ & _ & Hra & _ & Hgp & Htp & _ & _ & _ & Hal16 & Hstk & Hsp & _ & _ & _ & HA0 & _ & HA63 &
  _ & _ & _ & _ & _ & Hn0 & _ & _ & _ & HrecP & Hout).
pose proof HJ as (_ & Hly0 & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ &
  (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof HJ1 as (HAR1 & Hly1 & _).
destruct (sbe_ly_eq _ _ _ _ _ Hly1 Hly0) as (EF & EFL).
destruct (sbe_sep lyc1 Sc1 W1 memc1 mdc1 pos (frames (si_Sc X)) HAR1 Hfrs1) as (S1 & S2 & S3 & S4).
rewrite (EF 0 pos), (EFL 0 pos) in S1, S2, S3, S4.
rewrite Hbl1 in S3.
assert (S4' : forall cid p a, In (cid, p) (frames (si_Sc X)) ->
  (in_zr a (frame_rng (si_lyc X) (cid, p)) \/ in_zr a (shadow_addr (frame_addr (si_lyc X) cid p), fs_frame_bytes cid / 8)) ->
  ~ sbe_W (frame_addr (si_lyc X) 0 pos) (flag_addr (si_lyc X) 0 pos) a).
{ intros cid p a H1 H2. apply (S4 cid p a H1). unfold frame_rng in *. cbn [fst snd] in *. rewrite !EF. exact H2. }
assert (Hst : alloc_ceiling <= si_sp0 X - si_STK X) by lia.
assert (Hown : forall c p, In (c, p) (si_own X) -> In (c, p) (frames (si_Sc X)))
  by (intros c p H; rewrite Hfrs0; apply in_or_app; left; exact H).
assert (NAW : forall a, awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X))
    (ablocks B (si_lyc X) (si_Sc X)) (si_lyc X) (si_own X) a ->
  ~ sbe_W (frame_addr (si_lyc X) 0 pos) (flag_addr (si_lyc X) 0 pos) a)
  by (intros a Ha; exact (sbe_awr _ _ _ _ _ _ _ _ _ a Hst Hown S1 S3 S4' Ha)).
assert (Hin : In (0, pos) (frames Sc1)) by (rewrite Hfrs1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR1 Hin) as (HF4 & HFc & _).
destruct (FFL _ _ _ _ _ 0 pos HAR1 Hin) as (_ & _ & _ & (HFL4 & _ & HFLc)).
rewrite (EF 0 pos) in HF4, HFc. rewrite (EFL 0 pos) in HFL4, HFLc.
change (fs_frame_bytes 0) with 64 in HFc.
change (frame_addr (si_lyc X) 0 pos) with (sbd_F X pos) in *.
change (flag_addr (si_lyc X) 0 pos) with (sbd_FL X pos) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold sbd_cfg, cfg_at.
replace (BASE + AF_both3_sb_dec + SBD_PE) with (BASE + (AF_both3_sb_dec + SBD_PE)) by lia.
change (w64 (BASE + (AF_both3_sb_dec + SBD_PE))) with (Z_to_bv 64 (BASE + (AF_both3_sb_dec + SBD_PE))).
remember (Eimg (Ereg regs1 (sbe_extra X pos))) as E eqn:HEd.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (sbe_extra X pos) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E23 : ew E 23 = Z_to_bv 64 (sbd_F X pos)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = Z_to_bv 64 (sbd_SH X pos)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (E44 : ew E 44 = Z_to_bv 64 (sbd_FL X pos)) by (exact (EX 12%nat ltac:(lia))).
assert (XR : forall j r, nth_error sbd_saved_regs j = Some r -> ew E (32 + j) = getr (si_regs X) (Z_to_bv 5 r)).
{ intros j r Hr.
  assert (Hj : (j < length sbd_saved_regs)%nat) by (apply nth_error_Some; rewrite Hr; discriminate).
  cbn [length sbd_saved_regs] in Hj.
  rewrite (EX j) by lia. unfold sbe_extra. rewrite app_nth1 by (rewrite length_map; cbn; lia).
  apply nth_error_nth. rewrite nth_error_map, Hr. reflexivity. }
unfold sbd_SH in E24.
clear HEd.
pose proof (@aj_flag_store_pi (si_fq X) _ _ _ _ _ B LAWS ML ASF FFL) as RUNF.
paj_run_flag_sh RUNF HS HJ1.
- lia.
- intros a (r & Hr & Ha). cbn [ss_mem ss_sbE sbe_regions In] in Hr.
  repeat destruct Hr as [<- | Hr]; try destruct Hr;
    unfold sbe_stack, sbe_frame, sbe_shadow, sbe_flag in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  + lia.
  + left. right; right; right. exists 0, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite (EF 0 pos). change (frame_addr (si_lyc X) 0 pos) with (sbd_F X pos). change (fs_frame_bytes 0) with 64.
    rewrite E23, unsigned_lit_small in Ha by lia. lia.
  + left. right; right; right. exists 0, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite (EF 0 pos). change (frame_addr (si_lyc X) 0 pos) with (sbd_F X pos). change (fs_frame_bytes 0 / 8) with 8.
    rewrite E24, unsigned_lit_small in Ha by (unfold shadow_addr, SHADOW_OFF; lia). lia.
  + right. rewrite (EFL 0 pos). change (flag_addr (si_lyc X) 0 pos) with (sbd_FL X pos).
    rewrite E44, unsigned_lit_small in Ha by lia. lia.
- intros msr HSr.
  pose proof (st_ok_pi_region_nth E _ msr 3 _ HSr eq_refl) as HR3.
  pose proof (YCjr.field_of_region E (ms_mem msr) 44 (flag_addr lyc1 0 pos) _ 0 1 0 1 0 1 (SLit 0) 0 HR3
    ltac:(rewrite E44, unsigned_lit_small by lia; rewrite (EFL 0 pos); reflexivity)
    ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  specialize (V 0%nat ltac:(cbn; lia)). cbn [Z.of_nat] in V. rewrite !Z.add_0_r in V. rewrite V. reflexivity.
- cbn [ms_mem mkst] in HF, HFr, HG, HJ1.
  prreg HS (1%bv : bv 5) G1. prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4.
  prreg HS (8%bv : bv 5) G8. prreg HS (9%bv : bv 5) G9. prreg HS (18%bv : bv 5) G18. prreg HS (19%bv : bv 5) G19.
  prreg HS (20%bv : bv 5) G20. prreg HS (21%bv : bv 5) G21. prreg HS (22%bv : bv 5) G22. prreg HS (23%bv : bv 5) G23.
  prreg HS (24%bv : bv 5) G24. prreg HS (25%bv : bv 5) G25. prreg HS (26%bv : bv 5) G26. prreg HS (27%bv : bv 5) G27.
  assert (G1' : getr (ms_regs ms) 1 = getr (si_regs X) 1) by (rewrite G1; exact (XR 0%nat 1 eq_refl)).
  assert (AP : aregs_preserved (si_regs X) (ms_regs ms)).
  { apply aregs_preserved_eqs.
    - rewrite G2, (EE 8%nat 8%bv eq_refl), R8. unfold w64, sbd_SP, spZ. apply Z_to_bv_bv_unsigned.
    - rewrite G3, (EE 3%nat 3%bv eq_refl), R3, Hgp. reflexivity.
    - rewrite G4, (EE 4%nat 4%bv eq_refl), R4, Htp. reflexivity.
    - rewrite G8. exact (XR 1%nat 8 eq_refl).
    - rewrite G9. exact (XR 2%nat 9 eq_refl).
    - rewrite G18. exact (XR 3%nat 18 eq_refl).
    - rewrite G19. exact (XR 4%nat 19 eq_refl).
    - rewrite G20. exact (XR 5%nat 20 eq_refl).
    - rewrite G21. exact (XR 6%nat 21 eq_refl).
    - rewrite G22. exact (XR 7%nat 22 eq_refl).
    - rewrite G23. exact (XR 8%nat 23 eq_refl).
    - rewrite G24. exact (XR 9%nat 24 eq_refl).
    - rewrite G25. exact (XR 10%nat 25 eq_refl).
    - rewrite G26. exact (XR 11%nat 26 eq_refl).
    - rewrite G27, (EE 27%nat 27%bv eq_refl), R27. reflexivity. }
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ sbe_W (sbd_F X pos) (sbd_FL X pos) a ->
    aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) memc1 a).
  { intros a Ha Hn. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
    intros (r & Hr & Hw). apply Hn. cbn [ss_mem ss_sbE sbe_regions In] in Hr. unfold sbe_W.
    repeat destruct Hr as [<- | Hr]; try destruct Hr;
      unfold sbe_stack, sbe_frame, sbe_shadow, sbe_flag in Hw;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
    - lia.
    - left. rewrite E23, unsigned_lit_small in Hw by lia. lia.
    - right; left. rewrite E24, unsigned_lit_small in Hw by (unfold shadow_addr, SHADOW_OFF; lia). lia.
    - right; right. rewrite E44, unsigned_lit_small in Hw by lia. lia. }
  pose (RET := paj_ret_at (fx := si_fq X) (PL := PL_both3_0) (PI := PI)).
  eapply (RET W1 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold sbd_post, tsb_dec_post.
  eexists lyc1, (stack_free_state 0 pos Sc1), _, _, _.
  split; [rewrite G1', Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ1|].
  split; [exact AP|].
  split.
  { unfold frames, stack_free_state. cbn [st_fs set_fs fs_live]. unfold frames in Hfrs1. rewrite Hfrs1.
    cbn [del_pos]. rewrite !Z.eqb_refl. reflexivity. }
  split.
  { assert (Eb : ablocks B lyc1 (stack_free_state 0 pos Sc1) = ablocks B lyc1 Sc1)
      by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
    rewrite Eb, Hbl1. apply Permutation_refl. }
  destruct Hkept as (K1 & K2 & K3 & K4 & K5 & K6).
  split.
  { intros a Ha Hs HA16 Hpn. rewrite (KR a) by (first [lia | apply S1; lia]).
    apply K1; [exact Ha | exact Hs | intros [H | H]; [exact (HA16 H) | exact (Hpn H)]]. }
  split.
  { intros b m i Hb Hi HA16 Hpn.
    assert (Hb1 : In (b, m) (ablocks B lyc1 Sc1)) by (rewrite Hbl1; exact Hb).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR1 Hb1) as (_ & Hb4 & Hbc & _).
    rewrite (KR (b + i)) by (first [lia | exact (S3 b m i Hb Hi)]).
    apply (K2 b m i Hb Hi). intros [H | H]; [exact (HA16 H) | exact (Hpn H)]. }
  split.
  { intros a Him Hns Herr. pose proof (Hsegs a Him) as Hl. unfold kLowMemEnd in Hl.
    rewrite (KR a) by (first [lia | exact (S2 a Him)]). apply K3; assumption. }
  split.
  { intros cid p a Hcp Hz HA16 Hpn.
    assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite Hfrs1; right; exact Hcp).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp1) as (Hf1 & Hf2 & _).
    rewrite (EF cid p) in Hf1, Hf2.
    assert (Hac : 0 <= a < alloc_ceiling).
    { pose proof (fs_frame_bytes_nonneg cid).
      destruct Hz as [Hz | Hz]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hz; cbn [fst snd] in Hz; lia. }
    rewrite (KR a) by (first [lia | exact (S4' cid p a Hcp Hz)]).
    apply (K4 cid p a Hcp Hz). intros [H | H]; [exact (HA16 H) | exact (Hpn H)]. }
  split.
  { intros a Ha Hs Hp. apply (apresent_grows _ _ _ _ HG). exact (K5 a Ha Hs Hp). }
  split.
  { intros a Ha. apply (apresent_grows _ _ _ _ HG). exact (K6 a Ha). }
  destruct Hrec as (V0 & V8 & V16 & V24 & Vg).
  destruct HrecP as (_ & _ & HAw).
  assert (NA : forall a, si_A X <= a < si_A X + 28 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) memc1 a).
  { intros a Ha. apply KR; [lia|]. apply NAW. exact (proj1 (HAw a Ha)). }
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 (ms_mem ms)); [intros k Hk; apply NA; lia | exact V0]|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 (ms_mem ms)); [intros k Hk; apply NA; lia | exact V8]|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 (ms_mem ms)); [intros k Hk; apply NA; lia | exact V16]|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 (ms_mem ms)); [intros k Hk; apply NA; lia | exact V24]|].
  intros Hroom.
  destruct (Hout Hroom) as (Hp0 & Hpn63 & _ & _ & _ & _ & (_ & _ & HPw)).
  unfold sbd_acc in HPw, Hpn63.
  apply (garr8_aview_kept SEGS (w_H W1) (w_H W1) memc1 (ms_mem ms)); [| exact (Vg Hroom)].
  intros a Ha. rewrite length_firstn in Ha.
  assert (Ha' : si_p X + si_n X <= a < si_p X + si_n X + sb_dec_c.sb_dec_acc (si_v X) (si_md X) (si_cap X) (si_n X)) by lia.
  apply KR. { clear - Ha' Hp0 Hpn63 Hn0. lia. }
  apply NAW. exact (proj1 (HPw a Ha')).
Qed.
End h.
End f.
End d.

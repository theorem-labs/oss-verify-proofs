(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8c.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AE2d.v, proofs/cgif/cgif_file_fuzzer/lib/UI2d.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on image B (fuzz_grant.asan-ubsan, bin fde52226dc48, 0x8363c = BASE + 0x2c00, 367 slots), ported from lib/A/Prog/CtrlBuildGrantSweep.v at a working branch 5aae1e8a0ce (its Require closure: 196 files, 0 Admitted / admit / Axiom / Parameter), with the steps of the class-6 side-stack frame adapted from lib/A/Prog/CtrlStampHeadamp.v at the same commit (whose own cgif sources are proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, ACam.v, ACbf.v, ACf6.v, AChd.v); every address, constant and byte is image B's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlBuildGrantSweep.v, with its module paths and module names changed; 296 of its 328 lines of code are new or changed and 3978 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YE00 YE01 YC5d YO09 YCbp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoSites DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoRo DiscoEntRecCut DiscoEntRec DiscoEntRec2Kit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma cm_kept : forall (E : env) (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

Lemma cm_dE : forall (cx : dcx) E j ws, d_E cx E -> (530 <= j)%nat -> d_E cx (havoc E j ws).
Proof.
intros cx E j ws (H1 & H32 & HI & H60 & H516 & H529) Hj.
split; [|split; [|split; [|split; [|split]]]].
- intros nn r Hr. pose proof (bv_unsigned_in_range 5 r) as Hb. change (bv_modulus 5) with 32 in Hb.
  rewrite ew_havoc_old by lia. exact (H1 nn r Hr).
- rewrite ew_havoc_old by lia. exact H32.
- apply img_env_havoc_hi; [exact HI | unfold A_LIM; lia].
- rewrite ew_havoc_old by (unfold AT_A; lia). exact H60.
- rewrite ew_havoc_old by (unfold AT_F; lia). exact H516.
- rewrite ew_havoc_old by (unfold AT_SH; lia). exact H529.
Qed.

Lemma cm_regs_ok : forall (cx : dcx) (E : env) (R : bvmap 5 word) (ret : Z),
  img_env VAL A_LIM E -> getr R 1 = Z_to_bv 64 (BASE + ret) ->
  regs_ok (d_env cx E (map (getr R) (tl all_regs))) (SLit 0 :: SOff A_TEXT ret :: atom_regs 532 30) R.
Proof.
intros cx E R ret HEI H1.
assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr R) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEI | unfold AT_FL, A_LIM; lia]).
regs_ok_cases_pre ltac:(first [ rewrite getr_zero; reflexivity
                             | rewrite H1; symmetry; exact (codeptr_val _ ret HEId) ]).
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis AIL : asink_img_laws SEGS B tfib_K.
Hypothesis KCAN : ak_canary tfib_K = AE2k.FF_canary.
Hypothesis DUNIV : duniv_ok B.
Hypothesis AMALLOC : forall fq : YK11.FPState, amalloc_realizes (fx := fq) SEGS B.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBMAL : d_body_malloc_stmt B MT XM_LIB RLO RHI tfib_K.

Lemma cm_save : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k E shf,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k -> d_E cx E ->
  Forall (region_ok SEGS E (rd W3 mem3)) (d_regions cx shf) ->
  rdword (aview SEGS (w_H W3) mem3) (d_S cx - 8) = Some RA_LLVMF /\
  rdword (aview SEGS (w_H W3) mem3) (d_S cx - 16) = Some (s0Z (c_regs cx)) /\
  (bad_next (d_S cx) (ly_top ly3) (s0Z (c_regs cx)) = true \/
   fpchain (rdword (aview SEGS (w_H W3) mem3)) (s0Z (c_regs cx)) (ly_top ly3) []).
Proof.
intros cx ly3 S3 W3 mem3 md3 k E shf HC HE HREG.
pose proof HC as (HB & HJ & HFR).
pose proof HB as ((HPRE & HRA & _) & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 mem3 md3 k HC)
  as (GS16 & GSlo & GShi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof alloc_ceiling_value as Hceil0.
unfold LLVMF_STK in GSlo.
change (spZ (c_regs cx)) with (d_S cx) in Hch, Hal16, Hslo, Hshi, Hbot, Htop.
pose proof HE as (EE & _).
pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hs0r. change (bv_modulus 64) with (2 ^ 64) in Hs0r.
split.
{ apply (rdword_of_val_mem SEGS); [|unfold RA_LLVMF; lia].
  replace (d_S cx - 8) with (d_S cx + -8) by lia.
  apply (slot_of_region E (rd W3 mem3) (d_S cx) dsave_chunks (-104) 0 0 0 (-8) (SOff 1 0) RA_LLVMF).
  - exact (Forall_inv HREG).
  - rewrite (EE 2%nat 2%bv eq_refl). reflexivity.
  - vm_compute. left. reflexivity.
  - cbn [sv_denot]. rewrite (EE 1%nat 1%bv eq_refl). rewrite Z.add_0_r. unfold raZ in HRA. rewrite HRA. reflexivity.
  - unfold RA_LLVMF. lia. }
split.
{ apply (rdword_of_val_mem SEGS); [|unfold s0Z; lia].
  replace (d_S cx - 16) with (d_S cx + -16) by lia.
  apply (slot_of_region E (rd W3 mem3) (d_S cx) dsave_chunks (-104) 0 0 0 (-16) (SOff 8 0) (s0Z (c_regs cx))).
  - exact (Forall_inv HREG).
  - rewrite (EE 2%nat 2%bv eq_refl). reflexivity.
  - vm_compute. right. left. reflexivity.
  - cbn [sv_denot]. rewrite (EE 8%nat 8%bv eq_refl). rewrite Z.add_0_r. reflexivity.
  - unfold s0Z. lia. }
rewrite Etop.
destruct Hch as [([Hc | [Hc | Hc]] & _) | (H1 & H2 & H3 & H4 & H5)].
- left. unfold bad_next. replace (s0Z (c_regs cx) <=? d_S cx) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
- left. unfold bad_next. replace (ly_top (c_ly cx) - 16 <=? s0Z (c_regs cx)) with true by (symmetry; apply Z.leb_le; lia).
  rewrite Bool.orb_true_r. reflexivity.
- left. unfold bad_next. replace (s0Z (c_regs cx) mod 8 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hc).
  cbn. rewrite !Bool.orb_true_r. reflexivity.
- right. apply (fpchain_ext (rdword (aview SEGS (w_H (c_W cx)) (c_mem cx))) (rdword (aview SEGS (w_H W3) mem3))
    (s0Z (c_regs cx)) (ly_top (c_ly cx)) []); [| lia | exact H4].
  intros a Ha1 Ha2. apply rdword_ext. intros kk Hkk.
  apply (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
Qed.

Theorem r2_cm : r2_cm_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W c HST.
unfold p_mal, r2_st, d_at in HST.
destruct HST as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc &
  Hi & Hn & Hnow & HRL & (R1 & R10 & R27 & HRK) & (HPURE & HMEM) & HSP0 & HBODY).
pose proof HRK as (R24 & R23 & R19 & R22 & R26).
pose proof HMEM as (M408 & M248 & M392).
pose proof HSP0 as (M232 & M344).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HBODY as (T & G & Lk & Hbb0 & HFRM & _ & _ & HBLK & _).
pose proof HFRM as (E & HE & HREG & HFLAG & H216 & H152).
pose proof HBLK as (_ & _ & Hbb & _).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & _ & _ & _ & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBASE as ((_ & _ & _ & _ & _ & _ & _ & _ & HEV0 & HBB0 & _) & _).
pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
assert (SpR : spZ regs = d_A cx) by exact Rsp.
assert (HEIE : img_env VAL A_LIM E) by exact (proj1 (proj2 (proj2 HE))).
assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr regs) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEIE | unfold AT_FL, A_LIM; lia]).
assert (Hlen : 0 <= r2_len cx n < 65536).
{ pose proof (bv_unsigned_in_range 8 (nth 0 (rest_of (c_pl cx) n) (Z_to_bv 8 0))) as Hb0.
  pose proof (bv_unsigned_in_range 8 (nth 1 (rest_of (c_pl cx) n) (Z_to_bv 8 0))) as Hb1.
  change (bv_modulus 8) with 256 in Hb0, Hb1.
  unfold r2_len, rec_len, rec_rem, rec_take, rec_want, rdb. lia. }
pose proof (pal_rt_below B TL) as (_ & Hpc0).
assert (Hra : raZ regs = BASE + RA_MAL)
  by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; unfold RA_MAL; lia).
assert (Hs0 : s0Z regs = d_S cx) by (unfold s0Z; rewrite Rs0; unfold w64; apply unsigned_lit_small; lia).
destruct (cm_save cx ly3 S3 W mem3 md3 k E dsh_loop HCTX HE HREG) as (Hw8 & Hw16 & Hv0).
destruct (d_call_chain B MT XM_LIB RLO RHI tfib_K (pc_malloc_ra0 (as_code B)) RA_MAL cx ly3 S3 W mem3 md3 k regs
  (s0Z (c_regs cx)) HCTX Hpc0 ltac:(unfold RA_MAL; lia) ltac:(unfold RA_MAL; lia)
  ltac:(apply DUNIV; cbn [d_sites In]; do 8 right; left; reflexivity)
  ltac:(apply DUNIV; cbn [d_sites In]; do 2 right; left; reflexivity)
  Rsp Hs0 ltac:(lia) Hra Hw8 Hw16 Hv0) as (ch & Hcp & Htr).
pose proof (DSEAT LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E (SIGMA DS___interceptor_trampoline_malloc - BASE)
  (SLit 0 :: SOff A_TEXT RA_MAL :: atom_regs 532 30) (map (getr regs) (tl all_regs)) [] [] [] (d_facts [] [])
  HCTX HE HREG HFLAG (cm_regs_ok cx E regs RA_MAL HEIE R1)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (map (getr regs) (tl all_regs)) [] [] HCTX HE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS1.
replace (BASE + (SIGMA DS___interceptor_trampoline_malloc - BASE)) with (pc_wrap_malloc (as_code B))
  by (rewrite (pal_malloc B TL); lia).
unfold cfg_at, w64.
eapply SRr_mono.
{ apply (aj_malloc_at04 (fx := fq) SEGS B LAWS pa_segs_low (pal_env B TL) ML (AMALLOC fq) W regs mem3 LLVMF_STK
    (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md3 k
    (r2_len cx n) (d_A cx - d_S cx) (getr regs 1) ch HJ).
  - exact R10.
  - unfold MALLOC_MAX. lia.
  - cbn [fold_right] in Hbb. unfold LIVE_MAX. unfold LIVE_LIB, LIVE_MAX in HBB0. unfold HUNT_SIZE in Hbb. lia.
  - rewrite SpR. lia.
  - pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DA. pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)) as DS.
    rewrite GA32 in DA. rewrite GS16 in DS.
    replace (d_A cx - d_S cx) with ((2 * (d_A cx / 32) - d_S cx / 16) * 16) by lia. apply Z_mod_mult.
  - lia.
  - unfold ASTACK, LLVMF_STK. lia.
  - exact Rgp.
  - exact Rtp.
  - reflexivity.
  - rewrite R1. unfold w64. apply ret_ok_codeptr_v; [unfold RA_MAL; lia | reflexivity].
  - clear - Hk Hnev HEV0 Hi. unfold EV_HEAD, EV_PRO, EV_ITER, EV_LIB, EV_MAX, MAX_OPS in *. lia.
  - exact Hcp.
  - exact Htr. }
cbv beta. intros W2 c2 HW2 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP & Hres & Hfrs & H4096 & Eab & HK).
assert (HFR4 : frames S4 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite Hfrs; exact HFR).
assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 (k + 1)) by exact (conj HBASE (conj HJ4 HFR4)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly4 S4 W2 mem4 md4 (k + 1) HCTX4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & HAR4 & HFin4 & EFA4 & _).
assert (Hnew : In (res, r2_len cx n) (ablocks B ly4 S4)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR4 Hnew) as (Hr16 & _ & Hrceil & Hrapp & _ & _ & _).
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (KA : forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply K1; [lia | unfold ASTACK; lia]. }
assert (KFR : forall a, d_FB cx <= a < d_FB cx + 4096 -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a HFin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
  - intros Hfp.
    pose proof (sep_block_frame SEGS B LAWS ly4 S4 W2 mem4 md4 res (r2_len cx n) DFRAME_CLASS (c_fpos cx)
      HAR4 Hnew HFin4) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA4 in Hd.
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hd. lia. }
assert (KSH : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 ->
  aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a HFin3).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
  - intros Hfp.
    apply (fshadow_not_app (d_FB cx) 512 res (req_size (r2_len cx n)) a); [lia | lia | exact Hrapp | | lia].
    unfold shadow_addr, SHADOW_OFF in Ha. lia. }
assert (ES2 : bv_unsigned (ew E 2) = d_S cx) by (rewrite (proj1 HE 2%nat 2%bv eq_refl); reflexivity).
assert (EA : ew E 60 = w64 (d_A cx)) by exact (proj1 (proj2 (proj2 (proj2 HE)))).
assert (EF : ew E 516 = w64 (d_FB cx)) by exact (proj1 (proj2 (proj2 (proj2 (proj2 HE))))).
assert (ESH : ew E 529 = w64 (shadow_addr (d_FB cx))) by exact (proj2 (proj2 (proj2 (proj2 (proj2 HE))))).
jafter_call_keep_hi HS1 562%nat regs4 (mrestrict (w_H W2) mem4) HP [0;1;2;3]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (cm_kept _ (w_H W) (w_H W2) mem3 mem4 _ (d_S cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). exact ES2.
    + intros a Ha. apply KA. lia.
    + intros a Ha. lia.
  - eapply (cm_kept _ (w_H W) (w_H W2) mem3 mem4 _ (d_A cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite EA. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. apply KA. lia.
    + intros a Ha. apply GSTK4. unfold LLVMF_STK. lia.
  - eapply (cm_kept _ (w_H W) (w_H W2) mem3 mem4 _ (d_FB cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite EF. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. apply KFR. lia.
    + intros a Ha. apply GFpres4. lia.
  - eapply (cm_kept _ (w_H W) (w_H W2) mem3 mem4 _ (shadow_addr (d_FB cx))).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite ESH. unfold w64. apply unsigned_lit_small.
      unfold shadow_addr, SHADOW_OFF. lia.
    + intros a Ha. apply KSH. lia.
    + intros a Ha. replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia.
      apply GFsh4. lia. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2.
assert (HE2 : d_E cx (havoc (d_env cx E (map (getr regs) (tl all_regs))) 562 (map (getr regs4) CLOB)))
  by (apply cm_dE; [apply d_E_env; exact HE | lia]).
assert (HFL2 : ew (havoc (d_env cx E (map (getr regs) (tl all_regs))) 562 (map (getr regs4) CLOB)) AT_FL =
  Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
  by (rewrite ew_havoc_old by (unfold AT_FL; lia); apply d_env_fl).
assert (KV : forall off v, 0 <= off <= 464 -> val_mem SEGS (mrestrict (w_H W) mem3) (d_A cx + off) 8 v ->
  val_mem SEGS (mrestrict (w_H W2) mem4) (d_A cx + off) 8 v).
{ intros off v Hoff Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W2) mem3 mem4); [|exact Hv].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KA. lia. }
pose proof (DLAND LAWS FFL fq cx h dsh_loop ly4 S4 W2 md4 (k + 1) _ _
  (YK11.mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + RA_MAL)) mem4 (YK11.seg_rom SEGS))
  HCTX4 HE2 HFL2 HS2 ltac:(vm_compute; reflexivity) (KV 216 h ltac:(lia) H216) (KV 152 (h + 440) ltac:(lia) H152))
  as (HFRM4 & HSHD4).
pose proof (DBMAL LAWS (conj DRO (conj GM HV)) (conj AIL KCAN) cx h n [] dsh_loop dsh_loop ly3 S3 W mem3 md3 k
  ly4 S4 W2 mem4 md4 (k + 1) (d_S cx + (d_A cx - d_S cx) - ASTACK) (d_S cx + (d_A cx - d_S cx))
  [(res, r2_len cx n)]
  HBODY (conj HBASE HJ) (conj HBASE HJ4) ltac:(cbn; lia) ltac:(unfold ASTACK, LLVMF_STK; lia) ltac:(lia) Eab
  ltac:(constructor; [exact (blk_off_imgP B ly4 S4 W2 mem4 md4 res (r2_len cx n) HAR4 Hnew) | constructor])
  ltac:(eapply acall_kept_mono_E;
        [exact HK | intros a Ha; exists res, (r2_len cx n); split; [left; reflexivity | exact Ha]])
  HFRM4 HSHD4) as HBODY4.
cbn [app] in HBODY4.
assert (PR : forall rr : Z, acallee_saved rr -> getr regs4 (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)) by exact HP.
assert (P2 : getr regs4 2 = getr regs 2) by exact (PR 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs4 3 = getr regs 3) by exact (PR 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs4 4 = getr regs 4) by exact (PR 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs4 8 = getr regs 8) by exact (PR 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs4 9 = getr regs 9) by exact (PR 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs4 18 = getr regs 18) by exact (PR 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs4 19 = getr regs 19) by exact (PR 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs4 20 = getr regs 20) by exact (PR 20 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs4 22 = getr regs 22) by exact (PR 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs4 23 = getr regs 23) by exact (PR 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs4 24 = getr regs 24) by exact (PR 24 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs4 25 = getr regs 25) by exact (PR 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs4 26 = getr regs 26) by exact (PR 26 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs4 27 = getr regs 27) by exact (PR 27 ltac:(unfold acallee_saved; lia)).
exists res.
unfold q_mal, r2_st, d_at.
exists fq, ly4, S4, regs4, mem4, md4, (k + 1), acc.
split; [unfold cfg_at, w64; rewrite R1; reflexivity|]. split; [exact HFRM0|].
split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR4|].
split; [lia|].
split; [pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite P2; exact Rsp|].
  split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|]. split; [rewrite P8; exact Rs0|].
  split; [rewrite P9; exact Rs1|]. split; [rewrite P18; exact Rs2|]. split; [rewrite P20; exact Rs4|].
  rewrite P25; exact Rs9. }
split.
{ split; [exact Hres|]. split; [rewrite P27; exact R27|].
  split; [rewrite P24; exact R24|]. split; [rewrite P23; exact R23|]. split; [rewrite P19; exact R19|].
  split; [rewrite P22; exact R22|]. rewrite P26; exact R26. }
split.
{ split; [exact H4096|]. split; [exact HPURE|].
  split; [apply KV; [lia | exact M408]|]. split; [apply KV; [lia | exact M248]|].
  apply KV; [lia | exact M392]. }
split.
{ split; [apply KV; [lia | exact M232] | apply KV; [lia | exact M344]]. }
exact HBODY4.
Qed.

End h.
End f.
End d.

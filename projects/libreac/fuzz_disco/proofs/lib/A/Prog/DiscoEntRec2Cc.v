(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8c.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AE2d.v, proofs/cgif/cgif_file_fuzzer/lib/UI2d.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on image B (fuzz_grant.asan-ubsan, bin fde52226dc48, 0x8363c = BASE + 0x2c00, 367 slots), ported from lib/A/Prog/CtrlBuildGrantSweep.v at a working branch 5aae1e8a0ce (its Require closure: 196 files, 0 Admitted / admit / Axiom / Parameter), with the steps of the class-6 side-stack frame adapted from lib/A/Prog/CtrlStampHeadamp.v at the same commit (whose own cgif sources are proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, ACam.v, ACbf.v, ACf6.v, AChd.v); every address, constant and byte is image B's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlBuildGrantSweep.v, with its module paths and module names changed; 254 of its 285 lines of code are new or changed and 3979 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YE00 YC5d YO09 YCbp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntRecCut DiscoEntRec2Kit.
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

Lemma rcc_kept : forall (E : env) (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
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

Lemma rcc_dE : forall (cx : dcx) E j ws, d_E cx E -> (530 <= j)%nat -> d_E cx (havoc E j ws).
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

Lemma rcc_regs_ok : forall (cx : dcx) (E : env) (R : bvmap 5 word) (ret : Z),
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
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBHCALL : d_body_hcall_stmt B MT XM_LIB RLO RHI tfib_K.

Theorem r2_cc : r2_cc_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op fr W c HST.
unfold p_cpy, r2_st, d_at in HST.
destruct HST as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc &
  Hi & Hn & Hnow & HRL & (R1 & R10 & R11 & R12 & R27 & HRK) & (H4096 & Hlen0 & Hpure & HMEM) & HSP0 & HBODY).
pose proof HRK as (R24 & R23 & R19 & R22 & R26).
pose proof HMEM as (M408 & M248 & M392).
pose proof HSP0 as (S232 & S344).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HBODY as (T & G & Lk & HL & HFRM & HSHD & HOBJ & HBLK & HINP & HROD & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & H216 & H152).
pose proof HBLK as (HPerm0 & HNot0 & Hbb & HOFFb).
pose proof HINP as (Hnrng & Hgin & Hpoff).
pose proof HGEO as (GFB0 & GFBc & Gh0 & Ghc & Gceil & Glen & Ghfb & Ginp).
pose proof HBASE as (HPRE & _ & _).
pose proof HPRE as (_ & _ & _ & _ & HPN & _).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & _ & _ & _ & HAR3 & HFin3 & EFA3 & EFL3).
pose proof asan_consts as (CA & _).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
assert (Hlr : r2_len cx n <= rec_rem n) by (unfold r2_len, rec_len; lia).
assert (Hrr : rec_rem n = n - 2 /\ 2 < n) by (unfold rec_rem, rec_take in *; lia).
destruct HPN as [(Hcn0 & _) | (Hcn26 & Hinp0)]; [lia|].
assert (Hcn : n <= c_n cx - 7) by lia.
assert (Hinfr : In (fr, r2_len cx n) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym HPerm0)); cbn [app]; left; reflexivity).
assert (Hinp : In (c_p cx, c_n cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym HPerm0)); cbn [app]; right; right; exact Hinp0).
assert (Hnotfr : ~ In (fr, r2_len cx n) (ablocks B (c_ly cx) (c_S cx)))
  by exact (Forall_inv (Forall_inv_tail HNot0)).
assert (Hne : (fr, r2_len cx n) <> (c_p cx, c_n cx)) by (intros Eq; apply Hnotfr; rewrite Eq; exact Hinp0).
pose proof (sep_blocks SEGS B LAWS ly3 S3 W mem3 md3 fr (r2_len cx n) (c_p cx) (c_n cx) HAR3 Hinfr Hinp Hne) as Hdisj.
unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj.
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinfr) as (_ & Hf4096 & Hfceil & Hfapp & Hfpres & _ & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinp) as (_ & Hp4096 & Hpceil & Hpapp & Hppres & _ & _).
assert (RqL : req_size (r2_len cx n) = r2_len cx n) by (unfold req_size; destruct (Z.eqb_spec (r2_len cx n) 0); lia).
assert (RqP : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
rewrite RqL in Hdisj, Hfceil. rewrite RqP in Hdisj, Hpceil, Hppres.
assert (SpR : spZ regs = d_A cx) by exact Rsp.
assert (HEIE : img_env VAL A_LIM E) by exact (proj1 (proj2 (proj2 HE))).
assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr regs) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEIE | unfold AT_FL, A_LIM; lia]).
pose proof (DSEAT LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E (SIGMA DS___asan_memcpy - BASE)
  (SLit 0 :: SOff A_TEXT RA_CPY :: atom_regs 532 30) (map (getr regs) (tl all_regs)) [] [] [] (d_facts [] [])
  HCTX HE HREG HFLAG (rcc_regs_ok cx E regs RA_CPY HEIE R1)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (map (getr regs) (tl all_regs)) [] [] HCTX HE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS1.
replace (BASE + (SIGMA DS___asan_memcpy - BASE)) with (SIGMA DS___asan_memcpy) by lia.
unfold cfg_at, w64.
eapply SRr_mono.
{ apply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA DS___asan_memcpy) (AMEMCPY fq) W regs mem3
    LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md3 k
    fr (d_cur cx (rec_rem n)) (r2_len cx n) (d_A cx - d_S cx) (getr regs 1) HJ).
  - exact R10.
  - exact R11.
  - exact R12.
  - lia.
  - lia.
  - lia.
  - rewrite SpR. lia.
  - pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DA. pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)) as DS.
    rewrite GA32 in DA. rewrite GS16 in DS.
    replace (d_A cx - d_S cx) with ((2 * (d_A cx / 32) - d_S cx / 16) * 16) by lia. apply Z_mod_mult.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact Rgp.
  - exact Rtp.
  - reflexivity.
  - rewrite R1. unfold w64. apply ret_ok_codeptr_v; [unfold RA_CPY; lia | reflexivity].
  - intros a Ha. split.
    + right. right. left. exists fr, (r2_len cx n). split; [exact Hinfr|]. split; [exact Hnotfr | rewrite RqL; lia].
    + unfold ESTACK. lia.
  - apply (amem_range_of_block SEGS B LAWS ly3 S3 W mem3 md3 fr (r2_len cx n) fr (r2_len cx n) HAR3 Hinfr);
      rewrite ?RqL; lia.
  - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W mem3 md3 fr (r2_len cx n) fr (r2_len cx n) HAR3 Hinfr);
      rewrite ?RqL; lia.
  - intros Hpos. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W mem3 md3 fr (r2_len cx n) fr (r2_len cx n)
      HAR3 Hinfr); rewrite ?RqL; lia.
  - unfold d_cur. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - apply aview_some_of_apresent. exact (proj1 (Hppres a ltac:(lia))).
      - rewrite SpR. unfold ESTACK. lia. }
    split; [lia|]. split.
    { apply (amem_range_of_block SEGS B LAWS ly3 S3 W mem3 md3 (c_p cx) (c_n cx) _ _ HAR3 Hinp); rewrite ?RqP; lia. }
    split.
    { apply (range_addressable_of_block SEGS B LAWS ly3 S3 W mem3 md3 (c_p cx) (c_n cx) _ _ HAR3 Hinp);
        rewrite ?RqP; lia. }
    intros Hpos. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W mem3 md3 (c_p cx) (c_n cx) _ _ HAR3 Hinp);
      rewrite ?RqP; lia. }
cbv beta. intros W2 c2 HW2 (-> & regs4 & mem4 & md4 & -> & HJ4 & HP & Hres & Heff & Hfr & Hpres & Hsame).
assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem4 md4 k) by exact (conj HBASE (conj HJ4 HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem4 md4 k HCTX4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
assert (KK : forall a, 0 <= a < 2 ^ 64 -> ~ (fr <= a < fr + r2_len cx n) -> ~ (d_A cx - ESTACK <= a < d_A cx) ->
  aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha H1 H2. apply Hfr; [exact Ha | exact H1 | intros Hx; apply H2; lia]. }
assert (KA : forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply KK; [lia | lia | lia]. }
assert (KFR : forall a, d_FB cx <= a < d_FB cx + 4096 -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha.
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 fr (r2_len cx n) DFRAME_CLASS (c_fpos cx) HAR3 Hinfr HFin3)
    as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA3, RqL in Hd.
  replace (fs_frame_bytes DFRAME_CLASS) with 4096 in Hd by reflexivity.
  apply KK; [lia | lia | unfold ESTACK; lia]. }
assert (KSH : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 ->
  aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. unfold shadow_addr, SHADOW_OFF in Ha. apply KK; [lia | | unfold ESTACK; lia].
  intros Hx. apply (fshadow_not_app (d_FB cx) 512 fr (req_size (r2_len cx n)) a); [lia | lia | exact Hfapp | lia |].
  rewrite RqL. exact Hx. }
assert (ES2 : bv_unsigned (ew E 2) = d_S cx) by (rewrite (proj1 HE 2%nat 2%bv eq_refl); reflexivity).
assert (EA : ew E 60 = w64 (d_A cx)) by exact (proj1 (proj2 (proj2 (proj2 HE)))).
assert (EF : ew E 516 = w64 (d_FB cx)) by exact (proj1 (proj2 (proj2 (proj2 (proj2 HE))))).
assert (ESH : ew E 529 = w64 (shadow_addr (d_FB cx))) by exact (proj2 (proj2 (proj2 (proj2 (proj2 HE))))).
jafter_call_keep_hi HS1 562%nat regs4 (mrestrict (w_H W) mem4) HP [0;1;2;3]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (rcc_kept _ (w_H W) (w_H W) mem3 mem4 _ (d_S cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). exact ES2.
    + intros a Ha. apply KA. lia.
    + intros a Ha. lia.
  - eapply (rcc_kept _ (w_H W) (w_H W) mem3 mem4 _ (d_A cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite EA. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. apply KA. lia.
    + intros a Ha. apply GSTK4. unfold LLVMF_STK. lia.
  - eapply (rcc_kept _ (w_H W) (w_H W) mem3 mem4 _ (d_FB cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite EF. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. apply KFR. lia.
    + intros a Ha. apply GFpres4. lia.
  - eapply (rcc_kept _ (w_H W) (w_H W) mem3 mem4 _ (shadow_addr (d_FB cx))).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite ESH. unfold w64. apply unsigned_lit_small.
      unfold shadow_addr, SHADOW_OFF. lia.
    + intros a Ha. apply KSH. lia.
    + intros a Ha. replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia.
      apply GFsh4. lia. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2.
assert (HE2 : d_E cx (havoc (d_env cx E (map (getr regs) (tl all_regs))) 562 (map (getr regs4) CLOB)))
  by (apply rcc_dE; [apply d_E_env; exact HE | lia]).
assert (HFL2 : ew (havoc (d_env cx E (map (getr regs) (tl all_regs))) 562 (map (getr regs4) CLOB)) AT_FL = r2_flag cx)
  by (unfold r2_flag; rewrite ew_havoc_old by (unfold AT_FL; lia); apply d_env_fl).
assert (KV : forall off v, 0 <= off <= 464 -> val_mem SEGS (rd W mem3) (d_A cx + off) 8 v ->
  val_mem SEGS (rd W mem4) (d_A cx + off) 8 v).
{ intros off v Hoff Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact Hv].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KA. lia. }
assert (HFRAME : r2_frame cx n fr W mem4).
{ unfold r2_frame.
  apply (garr8_aview SEGS (w_H W) (w_H W) mem3 mem4 (d_cur cx (rec_rem n)) fr).
  - intros j Hj. unfold rest_of in Hj. rewrite length_map, length_firstn, length_skipn in Hj.
    exact (Heff j ltac:(lia)).
  - pose proof (garr8_sub_x SEGS _ _ _ (length (c_pl cx) - Z.to_nat (rec_rem n)) (Z.to_nat (r2_len cx n)) Hgin
      ltac:(rewrite length_map; lia)) as HX.
    rewrite skipn_map, firstn_map in HX. unfold rest_of.
    replace (d_cur cx (rec_rem n)) with (c_p cx + Z.of_nat (length (c_pl cx) - Z.to_nat (rec_rem n)))
      by (unfold d_cur; lia).
    exact HX. }
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
unfold q_cpy. rewrite R1. unfold w64.
eapply (r2_land B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND fq cx RA_CPY (EV_HEAD i + 1) h i n now
  [(fr, r2_len cx n)] _ _ W ly3 S3 md4 k acc _ _ (YK11.mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + RA_CPY)) mem4
  (YK11.seg_rom SEGS)) HFRM0 HBASE HJ4 HFR Hk Hnev HMO Hacc Hi Hn Hnow HS2).
- reflexivity.
- reflexivity.
- exact HE2.
- exact HFL2.
- vm_compute. reflexivity.
- exact (KV 216 h ltac:(lia) H216).
- exact (KV 152 (h + 440) ltac:(lia) H152).
- intros Hfr4 Hsh4.
  apply (DBHCALL LAWS cx h n [(fr, r2_len cx n)] dsh_loop dsh_loop ly3 S3 W mem3 ly3 S3 W mem4 md4 k
    (d_A cx - ESTACK) (d_A cx) HBODY (conj HBASE HJ4)); [unfold ESTACK, LLVMF_STK; lia | lia | | apply Permutation_refl
    | exact Hfr4 | exact Hsh4].
  intros a Ha Hna. apply KK; [exact Ha | | intros Hx; apply Hna; left; exact Hx].
  intros Hx. apply Hna. right. exists fr, (r2_len cx n). split; [left; reflexivity | rewrite RqL; lia].
- cbn [ms_regs mkst]. unfold d_rL, spZ in *.
  split; [rewrite P2; exact Rsp|]. split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|].
  split; [rewrite P8; exact Rs0|]. split; [rewrite P9; exact Rs1|]. split; [rewrite P18; exact Rs2|].
  split; [rewrite P20; exact Rs4|]. rewrite P25; exact Rs9.
- cbn [ms_regs mkst]. split; [rewrite P27; exact R27|]. unfold r2_rk.
  rewrite P24, P23, P19, P22, P26. exact HRK.
- cbn [ms_mem mkst]. split; [exact H4096|]. split; [exact Hpure|]. split; [|exact HFRAME].
  split; [apply KV; [lia | exact M408]|]. split; [apply KV; [lia | exact M248] | apply KV; [lia | exact M392]].
- cbn [ms_mem mkst]. split; [apply KV; [lia | exact S232] | apply KV; [lia | exact S344]].
Qed.

End h.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-158;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 287-290,
   358-363, for libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 104-107. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_family_of.v, with its module paths and module names changed; 4197 of its 4280 lines of code are new or changed and 764 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacArbitrate.v, with its module paths and module names changed; 1046 of its 1212 lines of code are new or changed and 4114 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YA0q YCbm YK06 YI0m YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i YXcalls YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd YCbf YCj1 YCja YCjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacFrameCleanLen.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_classify_c disco_table_c hunt_c reac_disco_table_observe_c reac_frame_clean_len_c reac_hunt_observe_c
HuntObsFacts HuntObsLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacHuntObserveCore.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing}.
Context {PW : PAWinImg lib_both3_0_listing}.
Context {PV : PAObjVal lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis ASM1 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TCOS : treac_disco_classify_on_segment_spec B.
Hypothesis TOBS : treac_disco_table_observe_spec B.
Hypothesis HRO : YRo.tfib_ro_unowned B.
#[local] Notation EHO := (@ReacHuntObserveCore.EHO rc PI).
#[local] Notation ho_shent_gen := (@ReacHuntObserveCore.ho_shent_gen rc PI).
#[local] Notation hoC := (@ReacHuntObserveCore.hoC rc PI).
#[local] Notation ho_pre := (@ReacHuntObserveCore.ho_pre rc SK PI B).
#[local] Notation ho_post := (@ReacHuntObserveCore.ho_post rc SK PI B).
#[local] Notation ho_fsh := (@ReacHuntObserveCore.ho_fsh rc PI).
#[local] Notation ho_regs_mid := (@ReacHuntObserveCore.ho_regs_mid rc PI B).
#[local] Notation ho_cfg := (@ReacHuntObserveCore.ho_cfg rc PI).
#[local] Notation ho_base := (@ReacHuntObserveCore.ho_base rc SK PI B).
#[local] Notation EHOm := (@ReacHuntObserveCore.EHOm rc PI B).
#[local] Notation ho_seg_G_stmt := (@ReacHuntObserveCore.ho_seg_G_stmt rc SK PI B).
#[local] Notation ho_seg_T_stmt := (@ReacHuntObserveCore.ho_seg_T_stmt rc SK PI B).
#[local] Notation hoG_pre := (@ReacHuntObserveCore.hoG_pre rc SK PI B).
#[local] Notation hoG_head_stmt := (@ReacHuntObserveCore.hoG_head_stmt rc SK PI B).
#[local] Notation hoG_ret_stmt := (@ReacHuntObserveCore.hoG_ret_stmt rc SK PI B).
Hypothesis ho_entry : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs : bvmap 5 word) (h n hb hn : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 h ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_HUNT_OBSERVE_STK -> spZ regs <= sp0 ->
  In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn ->
  0 < h -> h mod 8 = 0 -> 0 <= n <= 8 ->
  val_mem SEGS (mrestrict (w_H W) memc) (h + 384) 4 n ->
  st_ok_pi SEGS VAL (EHO regs n (as_uar_cell B)) ss_ho
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_both3_reac_hunt_observe)) memc (seg_rom SEGS))) /\
  sh_ok SEGS HOBx ho_SH (EHO regs n (as_uar_cell B)) (mrestrict (w_H W) memc).
Hypothesis ho_mid_entry : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F SH (wo : bool) af,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  ho_fsh W2 mem2 F SH -> length SH = 16%nat -> Forall (fun z : Z => 0 <= z < 256) SH ->
  (wo = true -> c_out c <> 0 /\ getr regs2 19 = w64 (c_out c)) ->
  st_ok_pi (fx := c_fq c) SEGS VAL (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) (ss_hoM SH wo af)
    (restrict (w_H W2) (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + af)) mem2 (seg_rom SEGS)))
  /\ img_env VAL A_LIM (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)).
Hypothesis ho_shokM : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F (wo : bool),
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  (wo = true -> c_out c <> 0 /\ getr regs2 19 = w64 (c_out c)) ->
  sh_ok SEGS HOBx (ho_SHM wo) (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) (mrestrict (w_H W2) mem2).
Hypothesis ho_segT : ho_seg_T_stmt.

Lemma tho_model_mono : forall (Hh FB O : list byte) (len now out r : Z) (H' : list byte)
    (OUT OUT2 : list byte -> Prop),
  (forall A, OUT A -> OUT2 A) -> tho_model Hh FB O len now out r H' OUT ->
  tho_model Hh FB O len now out r H' OUT2.
Proof.
  intros Hh FB O len now out r H' OUT OUT2 HM HT. unfold tho_model in HT |- *. cbv zeta in HT |- *.
  destruct HT as [F1 F2]. split.
  - intros X. destruct (F1 X) as (E1 & E2 & E3). split; [exact E1|]. split; [exact E2|].
    intros Ho. apply HM. apply E3. exact Ho.
  - intros X. destruct (F2 X) as (T' & c & OM & E1 & E2 & E3). exists T', c.
    split; [exact OM|]. split; [exact E1|]. split; [exact E2|].
    intros Ho. destruct (E3 Ho) as (A & HA & OA & FA). exists A.
    split; [exact HA|]. split; [apply HM; exact OA | exact FA].
Qed.

Lemma hoG_rdword_kept : forall (rd rd' : Z -> option Z) a v,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof.
intros rd rd' a v H Hv. unfold rdword in *.
pose proof (H 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0.
rewrite E0, (H 1 ltac:(lia)), (H 2 ltac:(lia)), (H 3 ltac:(lia)), (H 4 ltac:(lia)), (H 5 ltac:(lia)),
  (H 6 ltac:(lia)), (H 7 ltac:(lia)). exact Hv.
Qed.

Lemma hoG_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(s & Hs & _ & Hr) | Hrel]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hrel)].
Qed.

Lemma hoG_rod_kept : forall (Wa Wb : world SEGS) ma mb,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wa) ma) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H Wb) mb a = aview SEGS (w_H Wa) ma a) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wb) mb).
Proof.
intros Wa Wb ma mb HR HK a Hro Ho He.
rewrite (HK a (hoG_ro_img a Hro) Ho He). exact (HR a Hro Ho He).
Qed.

Lemma hoG_base_frame : forall (c : hoC) fpos ly2 S2 W2 memA mdA k2 H2 regsA sp1 F memB mdB regsB (Zw : Z -> Prop),
  ho_base c fpos ly2 S2 W2 memA mdA k2 H2 regsA sp1 F ->
  ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly2 S2 W2 memB mdB k2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zw a -> aview SEGS (w_H W2) memB a = aview SEGS (w_H W2) memA a) ->
  (forall a, apresent (w_H W2) memA a -> apresent (w_H W2) memB a) ->
  (forall a, Zw a -> (spZ (c_regs c) - REAC_HUNT_OBSERVE_STK <= a < sp1) \/
                    (c_out c <> 0 /\ c_out c <= a < c_out c + 24)) ->
  (forall a, Zw a -> c_out c <= a < c_out c + 24 ->
     ~ in_img SEGS a /\ ~ (c_h c <= a < c_h c + 480) /\ ~ (F + 120 <= a < F + 128)) ->
  ho_regs_mid c regsB sp1 F ->
  ho_base c fpos ly2 S2 W2 memB mdB k2 H2 regsB sp1 F.
Proof.
intros c fpos ly2 S2 W2 memA mdA k2 H2 regsA sp1 F memB mdB regsB Zw HB HJB HZ HP HZ1 HZ2 HRB.
destruct HB as (HPRE & HMID & HSP1 & HF & HRA & HSV).
destruct HMID as (HJ & HFRS & HFA & HPERM & HKEPT & HROD & HG & HL & HFL & HKK).
pose proof HPRE as ((mdc & HJ0) & _ & _ & _ & _ & _ & Hal16 & Hwin & Hsp & _ & _ & _ & Hout0 & Hh0 & Hh8 & Hhin & Hhb & Hhe & _ & _ & _ & _ & _ & HOUT & _).
pose proof HJ0 as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof HSP1 as (_ & Hsp1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfr : REAC_HUNT_OBSERVE_STK = REAC_HUNT_OBSERVE_FRAME + CLS_STK) by reflexivity.
assert (Hcls : 0 <= CLS_STK)
by (unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK; lia).
assert (Hfr0 : REAC_HUNT_OBSERVE_FRAME = 176) by reflexivity.
assert (KS : forall a, spZ (c_regs c) - REAC_HUNT_OBSERVE_STK <= a -> YM05.alloc_ceiling <= a) by (intros a Ha; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hhin) as (_ & _ & Hhceil & _).
assert (KOUT : c_out c <> 0 -> forall a, c_out c <= a < c_out c + 24 ->
  ~ (spZ (c_regs c) - REAC_HUNT_OBSERVE_STK <= a < spZ (c_regs c))).
{ intros Ho a Ha. destruct (HOUT Ho) as ((_ & _ & _ & Hsep & _) & _). lia. }
assert (KF : 4096 <= F /\ F + 128 <= YM05.alloc_ceiling).
{ assert (Hin2 : In (1, fpos) (frames S2)) by (rewrite HFRS; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos (proj1 HJ) Hin2) as (HF4 & HFc & _).
  rewrite HFA in HF4, HFc. change (fs_frame_bytes 1) with 128 in HFc. subst F. split; [exact HF4 | exact HFc]. }
assert (Zcase : forall a, Zw a -> (spZ (c_regs c) - REAC_HUNT_OBSERVE_STK <= a < sp1) \/
   (c_out c <> 0 /\ c_out c <= a < c_out c + 24 /\ ~ in_img SEGS a /\ ~ (c_h c <= a < c_h c + 480) /\
    ~ (F + 120 <= a < F + 128))).
{ intros a Hz. destruct (HZ1 a Hz) as [Hs | (Ho & Ha)]; [left; exact Hs | right].
  destruct (HZ2 a Hz Ha) as (N1 & N2 & N3).
  split; [exact Ho|]. split; [exact Ha|]. split; [exact N1|]. split; [exact N2 | exact N3]. }
clear HZ1 HZ2.
assert (Kimg : forall a, in_img SEGS a -> ~ Zw a).
{ intros a Ha Hz. pose proof (pa_segs_low a Ha) as Hl. destruct (Zcase a Hz) as [Hs | (_ & _ & Hn & _)];
  [pose proof (KS a ltac:(lia)); lia | exact (Hn Ha)]. }
split; [exact HPRE|]. split; [|split; [exact HSP1|]; split; [exact HF|]; split; [exact HRB|]].
- split; [exact HJB|]. split; [exact HFRS|]. split; [exact HFA|]. split; [exact HPERM|].
  split; [|split; [|split; [|split; [exact HL|]]]].
  + destruct HKEPT as (K1 & K2 & K3 & K4 & K5 & K6).
    split; [|split; [|split; [|split; [|split]]]].
    * intros a Ha Hns Hnw. rewrite HZ by first [lia | intros Hz; destruct (Zcase a Hz) as [Hs | (Ho & Ha' & _)];
        [apply Hns; lia | apply Hnw; right; split; assumption]].
      apply K1; assumption.
    * intros b m i Hin Hi Hnw.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin) as (_ & Hb4096 & Hbc & _).
      rewrite HZ by first [lia | intros Hz; destruct (Zcase (b + i) Hz) as [Hs | (Ho & Ha' & _)];
        [pose proof (KS (b + i) ltac:(lia)); lia | apply Hnw; right; split; assumption]].
      exact (K2 b m i Hin Hi Hnw).
    * intros a Ha Ho He. rewrite HZ by (try (pose proof (pa_segs_low a Ha); lia); exact (Kimg a Ha)).
      apply K3; assumption.
    * intros cid pos a Hin Hr Hnw.
      destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR0 Hin) as (Hf4096 & Hfc & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfb.
      assert (Hra : 0 <= a < YM05.alloc_ceiling).
      { unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hr. cbn [fst snd] in Hr.
        destruct Hr as [Hr | Hr]; [lia|].
        assert (frame_addr (c_lyc c) cid pos / 8 <= YM05.alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
        assert (fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (apply Z.div_le_upper_bound; lia).
        assert (0 <= frame_addr (c_lyc c) cid pos / 8) by (apply Z.div_pos; lia). lia. }
      rewrite HZ by first [lia | intros Hz; destruct (Zcase a Hz) as [Hs | (Ho & Ha' & _)];
        [pose proof (KS a ltac:(lia)); lia | apply Hnw; right; split; assumption]].
      exact (K4 cid pos a Hin Hr Hnw).
    * intros a Ha Hns Hp. apply HP. apply K5; assumption.
    * intros a Ha. apply HP. apply K6. exact Ha.
  + apply (hoG_rod_kept W2 W2 memA memB HROD). intros a Ha Ho He.
    apply HZ; [pose proof (pa_segs_low a Ha); lia | exact (Kimg a Ha)].
  + apply (garr8_aview_kept SEGS (w_H W2) (w_H W2) memA memB); [|exact HG].
    rewrite length_map, HL. intros a Ha.
    apply HZ; [lia|]. intros Hz. destruct (Zcase a Hz) as [Hs | (_ & _ & _ & Hn & _)];
    [pose proof (KS a ltac:(lia)); lia | apply Hn; lia].
  + split; [|exact HKK]. apply (hoG_rdword_kept (aview SEGS (w_H W2) memA)); [|exact HFL].
    intros i Hi. rewrite HFA, <- HF.
    apply HZ; [lia|]. intros Hz. destruct (Zcase (F + 120 + i) Hz) as [Hs | (_ & _ & _ & _ & Hn)];
    [pose proof (KS (F + 120 + i) ltac:(lia)); lia | apply Hn; lia].
- intros j Hj. apply (val_mem_aview_kept_x SEGS (w_H W2) (w_H W2) memA memB); [|exact (HSV j Hj)].
  intros a Ha. apply HZ; [lia|]. intros Hz. destruct (Zcase a Hz) as [Hs | (Ho & Ha' & _)]; [lia|].
  exact (KOUT Ho a Ha' ltac:(lia)).
Qed.

Lemma hoG_swap : forall (fq : YK11.FPState) E ss (H : word -> bool) regs regs' pc m (r : bv 5) e,
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict H (mkst (fx := fq) regs pc m (seg_rom SEGS))) ->
  bv_eqb r 0 = false -> sv_denot E e = getr regs' r ->
  (forall r', r' <> r -> getr regs' r' = getr regs r') ->
  st_ok_pi (fx := fq) SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss))
    (restrict H (mkst (fx := fq) regs' pc m (seg_rom SEGS))).
Proof.
intros fq E ss H regs regs' pc m r e HS Hr0 He Ho.
destruct ss as [p0 r0 f0 m0 v0 g0].
unfold st_ok_pi, st_ok, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
cbn [restrict mkst ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem] in *.
repeat (split; [assumption|]). split; [|split; assumption].
intros r'. destruct (bv_eq_dec _ r' r) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. symmetry. exact He.
- rewrite sr_get_set_other by exact Hne. rewrite (Ho r' Hne). apply S7.
Qed.

Lemma hoG_getr_upd_other : forall (regs : bvmap 5 word) (r r' : bv 5) v, r' <> r -> getr (regupd regs r v) r' = getr regs r'.
Proof. intros regs r r' v H. unfold getr. destruct (bv_eqb r' 0); [reflexivity|]. apply regupd_other. exact H. Qed.

Lemma hoG_getr_upd_same : forall (regs : bvmap 5 word) (r : bv 5) v, bv_eqb r 0 = false -> getr (regupd regs r v) r = v.
Proof. intros regs r v H. unfold getr. rewrite H. apply regupd_same. Qed.

Ltac hoG_bvne := let H := fresh in intros H; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H.

Lemma hoG_regs_mid_upd : forall (c : hoC) regs sp1 F (r : bv 5) v,
  r <> 2%bv -> r <> 3%bv -> r <> 4%bv -> r <> 8%bv -> r <> 9%bv -> r <> 18%bv -> r <> 21%bv -> r <> 24%bv -> r <> 25%bv ->
  ho_regs_mid c regs sp1 F -> ho_regs_mid c (regupd regs r v) sp1 F.
Proof.
intros c regs sp1 F r v N2 N3 N4 N8 N9 N18 N21 N24 N25 (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R24 & R25).
unfold ho_regs_mid. rewrite !hoG_getr_upd_other by congruence.
split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
split; [exact R18|]. split; [exact R21|]. split; [exact R24 | exact R25].
Qed.

Lemma hoG_ble_cons : forall (b : byte) bs,
  bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
intros b bs. cbn [bytes_le_to_Z].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hr.
assert (HTb : forall i, 8 <= i -> Z.testbit (bv_unsigned b) i = false).
{ intros i Hi. destruct (Z.eq_dec (bv_unsigned b) 0) as [E0|E0]; [rewrite E0; apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|].
  assert (Z.log2 (bv_unsigned b) < 8) by (apply (proj1 (Z.log2_lt_pow2 (bv_unsigned b) 8 ltac:(lia))); change (2 ^ 8) with 256; lia). lia. }
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite <- Z.lxor_lor.
- rewrite Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (HTb i Hi8). reflexivity.
- apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (HTb i Hi8). reflexivity.
Qed.

Lemma hoG_le_byte_ble : forall (bs : list byte) j, (j < length bs)%nat ->
  YO0f.le_byte (bytes_le_to_Z bs) (length bs) j = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b bs IH]; intros j Hj; cbn [length] in Hj; [lia|].
pose proof (bytes_le_to_Z_nonneg bs) as N0. pose proof (bytes_le_to_Z_bound bs) as N1.
pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
rewrite hoG_ble_cons. unfold YO0f.le_byte. cbn [length].
assert (HX : 0 <= bv_unsigned b + bytes_le_to_Z bs * 256 < 2 ^ (8 * Z.of_nat (S (length bs)))).
{ replace (8 * Z.of_nat (S (length bs))) with (8 * Z.of_nat (length bs) + 8) by lia. rewrite Z.pow_add_r by lia.
  change (2 ^ 8) with 256. set (X := 2 ^ (8 * Z.of_nat (length bs))) in *. nia. }
rewrite (Z.mod_small _ _ HX).
destruct j as [|j].
- cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
- cbn [nth]. rewrite <- (IH j ltac:(lia)). unfold YO0f.le_byte. rewrite (Z.mod_small (bytes_le_to_Z bs)) by lia.
  replace (8 * Z.of_nat (S j)) with (8 + 8 * Z.of_nat j) by lia. rewrite <- Z.shiftr_shiftr by lia.
  replace (Z.shiftr (bv_unsigned b + bytes_le_to_Z bs * 256) 8) with (bytes_le_to_Z bs). reflexivity.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma hoG_val_mem_sub : forall (m : word -> option byte) a (T : list byte) k (n : nat),
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) T) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length T) ->
  val_mem SEGS m (a + k) n (bytes_le_to_Z (disco_table_c.sub T k n)).
Proof.
intros m a T k n HG Hk Hkn j Hj.
assert (Hl : length (disco_table_c.sub T k n) = n).
{ unfold disco_table_c.sub. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
rewrite <- Hl at 2. rewrite hoG_le_byte_ble by lia.
assert (Hj2 : (Z.to_nat k + j < length (map (fun b : byte => bv_unsigned b) T))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte SEGS m a _ _ HG Hj2) as Hb.
replace (a + k + Z.of_nat j) with (a + Z.of_nat (Z.to_nat k + j)) by lia. rewrite Hb. f_equal.
unfold disco_table_c.sub. rewrite nth_firstn. replace ((j <? n)%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_skipn.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
rewrite map_nth. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma hoG_chunk_row : forall E (m : word -> option byte) hb (Hh : list byte) base off (n : N) (a : nat),
  garr8 SEGS m hb (map (fun b : byte => bv_unsigned b) Hh) ->
  ew E a = Z_to_bv 64 (bytes_le_to_Z (disco_table_c.sub Hh (base - hb + off) (N.to_nat n))) ->
  0 <= base - hb + off -> base - hb + off + Z.of_N n <= Z.of_nat (length Hh) -> 1 <= Z.of_N n <= 8 ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal n (SOff a 0))).
Proof.
intros E m hb Hh base off n a HG Ha Hk Hkn Hn.
assert (HL : length (disco_table_c.sub Hh (base - hb + off) (N.to_nat n)) = N.to_nat n)
  by (apply HuntObsLib.len_sub; lia).
apply (chunk_ok_val SEGS E m base off n (SOff a 0) (bytes_le_to_Z (disco_table_c.sub Hh (base - hb + off) (N.to_nat n)))).
- rewrite sv_denot_SOff0. exact Ha.
- pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub Hh (base - hb + off) (N.to_nat n))).
  pose proof (bytes_le_to_Z_bound (disco_table_c.sub Hh (base - hb + off) (N.to_nat n))). rewrite HL in *. lia.
- lia.
- replace (base + off) with (hb + (base - hb + off)) by lia. apply hoG_val_mem_sub; [exact HG | lia | lia].
Qed.

Lemma hoG_chunk_rd : forall E (H : word -> bool) (m : word -> option byte) base off (a : nat) v,
  ew E a = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H m) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H m) base (YP09.mkChunk off (CVal 8 (SOff a 0))).
Proof.
intros E H m base off a v Ha Hv Hr.
apply (chunk_ok_val SEGS E _ base off 8 (SOff a 0) v).
- rewrite sv_denot_SOff0. exact Ha.
- cbn. lia.
- lia.
- exact (val_mem_of_rdword SEGS H m _ v Hr).
Qed.

Lemma hoG_awr_mono : forall STK sp0 FP bl0 blc blc' ly ly' own (x : Z * Z) a,
  awr_byte STK sp0 FP bl0 blc ly own a -> Permutation blc' blc ->
  (forall cid p, frame_addr ly' cid p = frame_addr ly cid p) ->
  awr_byte STK sp0 FP bl0 blc' ly' (x :: own) a.
Proof.
intros STK sp0 FP bl0 blc blc' ly ly' own x a
  [H | [(Hf & b & n & Hin & Hr) | [(b & n & Hin & Hn & Hr) | (cid & pos & Hin & Hr)]]] HP HF.
- left; exact H.
- right; left. split; [exact Hf|]. exists b, n. split; [exact (Permutation_in _ (Permutation_sym HP) Hin) | exact Hr].
- right; right; left. exists b, n. split; [exact (Permutation_in _ (Permutation_sym HP) Hin)|]. split; [exact Hn | exact Hr].
- right; right; right. exists cid, pos. split; [right; exact Hin|]. rewrite HF. exact Hr.
Qed.

Lemma hoG_aview_fr : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 ->
  ~ in_wrange E rs a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a HF Ha Hn. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; exact Hn)). reflexivity.
Qed.

Lemma hoG_vm_chunk : forall E (m : word -> option byte) base off (n : N) e,
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal n e)) -> Z.of_N n <= 8 ->
  val_mem SEGS m (base + off) (N.to_nat n) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N n)).
Proof.
intros E m base off n e Hc Hn k Hk.
assert (Hk' : 0 <= Z.of_nat k < YP09.c_len (YP09.mkChunk off (CVal n e)))
  by (unfold YP09.c_len; cbn [YP09.c_val YP09.cv_len]; lia).
destruct (Hc (Z.of_nat k) Hk') as (b & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. injection Hb1 as Hb1. subst b.
rewrite Hb2. f_equal. unfold YP09.byte_of_word, YO0f.le_byte.
pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as HU.
set (U := bv_unsigned (sv_denot E e)) in *.
replace (8 * Z.of_N n) with (8 * Z.of_nat (N.to_nat n)) by lia.
rewrite Z.mod_mod by (apply Z.pow_nonzero; lia).
transitivity (Z_to_bv 8 (Z.shiftr (U mod 2 ^ (8 * Z.of_nat (N.to_nat n))) (8 * Z.of_nat k))).
- symmetry. apply low_byte_mod; [unfold bv_modulus in HU; lia | exact Hk].
- apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma hoG_sext_mod : forall E e, bv_unsigned (sv_denot E (SExt true 32 e)) mod 2 ^ 32 = bv_unsigned (sv_denot E e) mod 2 ^ 32.
Proof.
intros E e. cbn [sv_denot]. rewrite sext32_unsigned, bv_extract_unsigned.
generalize (bv_unsigned (sv_denot E e)). intros x.
unfold bv_swrap. replace (bv_half_modulus 32) with 2147483648 by reflexivity.
unfold bv_wrap. replace (bv_modulus 64) with 18446744073709551616 by reflexivity.
replace (bv_modulus 32) with 4294967296 by reflexivity.
change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 32) with 4294967296.
Z.div_mod_to_equations. lia.
Qed.

Lemma hoG_garr8_val_mem : forall (m : word -> option byte) a (bs : list byte) v,
  val_mem SEGS m a (length bs) v -> v mod 2 ^ (8 * Z.of_nat (length bs)) = bytes_le_to_Z bs ->
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) bs).
Proof.
intros m a bs v HV Hv j Hj. rewrite length_map in Hj.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia). rewrite map_nth.
pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
split; [|lia].
intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r.
rewrite (HV j Hj). f_equal. f_equal.
transitivity (bv_unsigned (nth j bs (Z_to_bv 8 0))).
- rewrite <- (hoG_le_byte_ble bs j Hj), <- Hv. unfold YO0f.le_byte. rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
- unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  rewrite (Z.mod_small (bv_unsigned (nth j bs (Z_to_bv 8 0))) 256) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma hoG_piece : forall (fq : YK11.FPState) E ss (H : word -> bool) ms i r off (w : N) e (bs : list byte),
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) -> 1 <= Z.of_N w <= 8 ->
  length bs = N.to_nat w ->
  bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w) = bytes_le_to_Z bs ->
  garr8 SEGS (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (map (fun b : byte => bv_unsigned b) bs).
Proof.
intros fq E ss H ms i r off w e bs HS Hi Hin Hw Hl Hv.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) i r HS Hi) as (_ & _ & _ & Hcs).
pose proof (hoG_vm_chunk E _ _ off w e (proj1 (Forall_forall _ _) Hcs _ Hin) ltac:(lia)) as HV.
cbn [ms_mem restrict] in HV.
apply (hoG_garr8_val_mem _ _ bs (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w))).
- rewrite Hl. exact HV.
- rewrite Hl. replace (8 * Z.of_nat (N.to_nat w)) with (8 * Z.of_N w) by lia.
  rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). exact Hv.
Qed.

Lemma hoG_firstn_add : forall (a b : nat) (l : list byte), firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
induction a as [|a IH]; intros b l; [reflexivity|].
destruct l as [|x l]; [cbn; rewrite firstn_nil; reflexivity|].
cbn [Nat.add firstn skipn app]. f_equal. apply IH.
Qed.

Lemma hoG_sub_split : forall (L : list byte) k (a b : nat), 0 <= k ->
  disco_table_c.sub L k (a + b) = disco_table_c.sub L k a ++ disco_table_c.sub L (k + Z.of_nat a) b.
Proof.
intros L k a b Hk. unfold disco_table_c.sub. rewrite hoG_firstn_add, skipn_skipn.
replace (a + Z.to_nat k)%nat with (Z.to_nat (k + Z.of_nat a)) by lia. reflexivity.
Qed.

Lemma hoG_garr8_cat : forall m p q (LA LB : list byte),
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) LA) -> q = p + Z.of_nat (length LA) ->
  garr8 SEGS m q (map (fun b : byte => bv_unsigned b) LB) ->
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) (LA ++ LB)).
Proof.
intros m p q LA LB HA Hq HB. rewrite map_app. apply garr8_app. split; [exact HA|]. rewrite length_map, <- Hq. exact HB.
Qed.

Lemma hoG_garr8_subL : forall m p (L : list byte) (a n : nat),
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L) -> (a + n <= length L)%nat ->
  garr8 SEGS m (p + Z.of_nat a) (map (fun b : byte => bv_unsigned b) (disco_table_c.sub L (Z.of_nat a) n)).
Proof.
intros m p L a n HG Hle. unfold disco_table_c.sub. rewrite Nat2Z.id.
replace (map (fun b : byte => bv_unsigned b) (firstn n (skipn a L)))
  with (firstn n (skipn a (map (fun b : byte => bv_unsigned b) L))) by (rewrite skipn_map, firstn_map; reflexivity).
apply garr8_sub_x; [exact HG | rewrite length_map; exact Hle].
Qed.

Lemma hoG_entry_garr8 : forall m out (G T : list byte) i,
  length G = 24%nat -> length T = 400%nat -> 0 <= i <= 7 ->
  garr8 SEGS m out (map (fun b : byte => bv_unsigned b) (disco_table_c.sub G 0 8)) ->
  garr8 SEGS m (out + 8) (map (fun b : byte => bv_unsigned b) (disco_table_c.sub T (48 * i + 8) 4)) ->
  garr8 SEGS m (out + 12) (map (fun b : byte => bv_unsigned b) (disco_table_c.sub T (48 * i + 12) 1)) ->
  garr8 SEGS m (out + 13) (map (fun b : byte => bv_unsigned b) (disco_table_c.sub T (48 * i + 13) 1)) ->
  garr8 SEGS m (out + 14) (map (fun b : byte => bv_unsigned b) (disco_table_c.sub T (48 * i + 14) 1)) ->
  garr8 SEGS m (out + 15) (map (fun b : byte => bv_unsigned b) (disco_table_c.sub T (48 * i + 15) 1)) ->
  garr8 SEGS m (out + 16) (map (fun b : byte => bv_unsigned b) (disco_table_c.sub T (48 * i + 16) 1)) ->
  garr8 SEGS m (out + 17) (map (fun b : byte => bv_unsigned b) (disco_table_c.sub G 17 3)) ->
  garr8 SEGS m (out + 20) (map (fun b : byte => bv_unsigned b) (disco_table_c.sub T (48 * i + 20) 4)) ->
  garr8 SEGS m out (map (fun b : byte => bv_unsigned b) (reac_hunt_observe_c.ho_entry T G i)).
Proof.
intros m out G T i LG LT Hi G0 T8 T12 T13 T14 T15 T16 G17 T20.
unfold reac_hunt_observe_c.ho_entry.
replace 9%nat with (4 + (1 + (1 + (1 + (1 + 1)))))%nat by reflexivity.
rewrite (hoG_sub_split T (48 * i + 8) 4) by lia.
rewrite (hoG_sub_split T (48 * i + 8 + Z.of_nat 4) 1) by lia.
rewrite (hoG_sub_split T (48 * i + 8 + Z.of_nat 4 + Z.of_nat 1) 1) by lia.
rewrite (hoG_sub_split T (48 * i + 8 + Z.of_nat 4 + Z.of_nat 1 + Z.of_nat 1) 1) by lia.
rewrite (hoG_sub_split T (48 * i + 8 + Z.of_nat 4 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1) 1) by lia.
replace (48 * i + 8 + Z.of_nat 4) with (48 * i + 12) by lia.
replace (48 * i + 12 + Z.of_nat 1) with (48 * i + 13) by lia.
replace (48 * i + 13 + Z.of_nat 1) with (48 * i + 14) by lia.
replace (48 * i + 14 + Z.of_nat 1) with (48 * i + 15) by lia.
replace (48 * i + 15 + Z.of_nat 1) with (48 * i + 16) by lia.
rewrite <- !app_assoc.
assert (LS : forall (L : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length L) ->
  length (disco_table_c.sub L k n) = n) by (intros; apply HuntObsLib.len_sub; lia).
apply (hoG_garr8_cat _ _ (out + 8)); [exact G0 | rewrite LS by lia; lia|].
apply (hoG_garr8_cat _ _ (out + 12)); [exact T8 | rewrite LS by lia; lia|].
apply (hoG_garr8_cat _ _ (out + 13)); [exact T12 | rewrite LS by lia; lia|].
apply (hoG_garr8_cat _ _ (out + 14)); [exact T13 | rewrite LS by lia; lia|].
apply (hoG_garr8_cat _ _ (out + 15)); [exact T14 | rewrite LS by lia; lia|].
apply (hoG_garr8_cat _ _ (out + 16)); [exact T15 | rewrite LS by lia; lia|].
apply (hoG_garr8_cat _ _ (out + 17)); [exact T16 | rewrite LS by lia; lia|].
apply (hoG_garr8_cat _ _ (out + 20)); [exact G17 | rewrite LS by lia; lia|].
exact T20.
Qed.

Lemma hoG_out_noimg : forall (c : hoC), ho_pre c -> c_out c <> 0 ->
  forall a, c_out c <= a < c_out c + 24 -> ~ in_img SEGS a.
Proof.
intros c HPRE Ho a Ha Himg.
destruct HPRE as ((mdc & HJ0) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOUT & _).
destruct (HOUT Ho) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl) & _).
pose proof (pa_img_range a Himg) as Hr. destruct HJ0 as (HAR0 & _).
destruct Hpl as [(cid & pos & Hin & H1 & H2) | (b & m & Hin & H1 & H2)].
- pose proof (frm_off_imgP _ _ _ _ _ _ cid pos HAR0 Hin) as Ho'. unfold off_img in Ho'. clear - Ho' Hr Ha H1 H2. lia.
- pose proof (blk_off_imgP _ _ _ _ _ _ b m HAR0 Hin) as Ho'. unfold off_img in Ho'. clear - Ho' Hr Ha H1 H2. lia.
Qed.

Ltac hoG_kr HS KR rr n Q := prreg HS rr Q; rewrite (KR rr n eq_refl ltac:(lia) ltac:(hoG_bvne)) in Q.

Lemma hoG_ble_rng : forall (L : list byte) k (n : nat), 0 <= k -> k + Z.of_nat n <= Z.of_nat (length L) ->
  0 <= bytes_le_to_Z (disco_table_c.sub L k n) < 2 ^ (8 * Z.of_nat n).
Proof.
intros L k n Hk Hkn. pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub L k n)) as B0.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub L k n)) as B1.
rewrite (HuntObsLib.len_sub L k n Hk Hkn) in B1. lia.
Qed.

Lemma hoG_val1 : forall E (a : nat) (L : list byte) k, ew E a = w64 (bytes_le_to_Z (disco_table_c.sub L k 1)) ->
  0 <= k -> k + 1 <= Z.of_nat (length L) ->
  bv_unsigned (sv_denot E (SOff a 0)) mod 2 ^ (8 * Z.of_N 1) = bytes_le_to_Z (disco_table_c.sub L k 1).
Proof.
intros E a L k Ha Hk Hkn. pose proof (hoG_ble_rng L k 1 Hk Hkn) as R. cbn in R.
rewrite sv_denot_SOff0, Ha. unfold w64. rewrite unsigned_lit_small by lia. change (2 ^ (8 * Z.of_N 1)) with 256.
apply Z.mod_small. lia.
Qed.

Lemma hoG_val4 : forall E (a : nat) (L : list byte) k, ew E a = w64 (bytes_le_to_Z (disco_table_c.sub L k 4)) ->
  0 <= k -> k + 4 <= Z.of_nat (length L) ->
  bv_unsigned (sv_denot E (SExt true 32 (SOff a 0))) mod 2 ^ (8 * Z.of_N 4) = bytes_le_to_Z (disco_table_c.sub L k 4).
Proof.
intros E a L k Ha Hk Hkn. pose proof (hoG_ble_rng L k 4 Hk Hkn) as R. cbn in R.
change (8 * Z.of_N 4) with 32. rewrite hoG_sext_mod, sv_denot_SOff0, Ha. unfold w64.
rewrite unsigned_lit_small by lia. apply Z.mod_small. lia.
Qed.

Ltac hoG_nowin := let rr := fresh "rr" in let Hin := fresh "Hin" in let Hrng := fresh "Hrng" in
  intros (rr & Hin & Hrng); cbn in Hin; destruct Hin as [<- | []]; try unfold hoG_sp1R in Hrng; cbn in Hrng;
  clear - Hrng; lia.

Ltac hoG_mid5 HS KR HRM :=
  let Q2 := fresh "Q" in let Q3 := fresh "Q" in let Q4 := fresh "Q" in let Q8 := fresh "Q" in let Q9 := fresh "Q" in
  let Q18 := fresh "Q" in let Q21 := fresh "Q" in let Q24 := fresh "Q" in let Q25 := fresh "Q" in
  hoG_kr HS KR (2%bv : bv 5) 2%nat Q2; hoG_kr HS KR (3%bv : bv 5) 3%nat Q3; hoG_kr HS KR (4%bv : bv 5) 4%nat Q4;
  hoG_kr HS KR (8%bv : bv 5) 8%nat Q8; hoG_kr HS KR (9%bv : bv 5) 9%nat Q9; hoG_kr HS KR (18%bv : bv 5) 18%nat Q18;
  hoG_kr HS KR (21%bv : bv 5) 21%nat Q21; hoG_kr HS KR (24%bv : bv 5) 24%nat Q24; hoG_kr HS KR (25%bv : bv 5) 25%nat Q25;
  unfold ho_regs_mid; rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q21, Q24, Q25; exact HRM.

Lemma hoGH_fr0 : forall E (H : word -> bool) (m m' : word -> option byte),
  frame_of E [] (mrestrict H m) (mrestrict H m') ->
  (forall a, aview SEGS H m' a = aview SEGS H m a) /\ (forall a, apresent H m a -> apresent H m' a).
Proof.
intros E H m m' HF.
assert (X : forall w, mrestrict H m' w = mrestrict H m w).
{ intros w. apply HF. intros (r & Hr & _). exact (False_ind _ Hr). }
split.
- intros a. unfold aview, mbyte. rewrite X. reflexivity.
- intros a (Ha & b & Hb). split; [exact Ha|]. exists b.
  pose proof (X (Z_to_bv 64 a)) as Y. unfold mrestrict in Y. rewrite Ha in Y. rewrite Y. exact Hb.
Qed.

Lemma hoGH_sub_nth : forall (T : list byte) (j w k : nat), (k < w)%nat ->
  nth_error (disco_table_c.sub T (Z.of_nat j) w) k = nth_error T (j + k).
Proof. intros T j w k Hk. unfold disco_table_c.sub. rewrite Nat2Z.id, nth_error_firstn. destruct (Nat.ltb_spec k w); [|lia]. apply nth_error_skipn. Qed.

Lemma hoGH_garr8_nth : forall (m : word -> option byte) base (L : list byte) j b,
  garr8 SEGS m base (map (fun b0 : byte => bv_unsigned b0) L) -> nth_error L j = Some b ->
  mbyte SEGS m (base + Z.of_nat j) = Some b.
Proof.
intros m base L j b G Hj.
assert (Hl : (j < length L)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
rewrite (garr8_mbyte SEGS m base _ j G) by (rewrite length_map; exact Hl).
f_equal. rewrite (nth_error_nth (map (fun b0 : byte => bv_unsigned b0) L) j 0 (map_nth_error _ j L Hj)). apply Z_to_bv_bv_unsigned.
Qed.

Lemma hoGH_aview_nth : forall H (m : word -> option byte) base (L : list byte) j b,
  garr8 SEGS (mrestrict H m) base (map (fun b0 : byte => bv_unsigned b0) L) -> nth_error L j = Some b ->
  aview SEGS H m (base + Z.of_nat j) = Some (bv_unsigned b).
Proof. intros H m base L j b G Hj. unfold aview. rewrite (hoGH_garr8_nth _ base L j b G Hj). reflexivity. Qed.

Lemma hoGH_mac : forall H (m : word -> option byte) t p (T P : list byte) i,
  length T = 400%nat -> length P = 6%nat -> 0 <= i <= 7 ->
  garr8 SEGS (mrestrict H m) t (map (fun b0 : byte => bv_unsigned b0) T) ->
  garr8 SEGS (mrestrict H m) p (map (fun b0 : byte => bv_unsigned b0) P) ->
  ((forall i0, 0 <= i0 < 6 -> aview SEGS H m (t + 48 * i + i0) = aview SEGS H m (p + i0)) <->
   disco_table_c.mac_of T i = P).
Proof.
intros H m t p T P i LT LP Ri GT GP. unfold disco_table_c.mac_of.
assert (NT : forall k, (k < 6)%nat -> nth_error (disco_table_c.sub T (48 * i) 6) k = nth_error T (Z.to_nat (48 * i) + k)).
{ intros k Hk. replace (48 * i) with (Z.of_nat (Z.to_nat (48 * i))) at 1 by lia. apply hoGH_sub_nth. exact Hk. }
assert (VT : forall k b, nth_error T (Z.to_nat (48 * i) + k) = Some b -> aview SEGS H m (t + 48 * i + Z.of_nat k) = Some (bv_unsigned b)).
{ intros k b Hb. replace (t + 48 * i + Z.of_nat k) with (t + Z.of_nat (Z.to_nat (48 * i) + k)) by lia. exact (hoGH_aview_nth H m t T _ b GT Hb). }
assert (VP : forall k b, nth_error P k = Some b -> aview SEGS H m (p + Z.of_nat k) = Some (bv_unsigned b)).
{ intros k b Hb. exact (hoGH_aview_nth H m p P k b GP Hb). }
split.
- intros HE. apply nth_error_ext. intros k. destruct (Nat.lt_ge_cases k 6) as [Hk|Hk].
  + rewrite (NT k Hk).
    destruct (nth_error T (Z.to_nat (48 * i) + k)) as [b1|] eqn:E1; [|apply nth_error_None in E1; lia].
    destruct (nth_error P k) as [b2|] eqn:E2; [|apply nth_error_None in E2; lia].
    pose proof (HE (Z.of_nat k) ltac:(lia)) as Hq. rewrite (VT k b1 E1), (VP k b2 E2) in Hq.
    injection Hq as Hq. f_equal. apply bv_eq. exact Hq.
  + assert (LS : length (disco_table_c.sub T (48 * i) 6) = 6%nat) by (unfold disco_table_c.sub; rewrite length_firstn, length_skipn, LT; lia).
    rewrite (proj2 (nth_error_None (disco_table_c.sub T (48 * i) 6) k) ltac:(lia)), (proj2 (nth_error_None P k) ltac:(lia)). reflexivity.
- intros HE i0 Hi0. pose proof (NT (Z.to_nat i0) ltac:(lia)) as Hn. rewrite HE in Hn.
  destruct (nth_error P (Z.to_nat i0)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  replace i0 with (Z.of_nat (Z.to_nat i0)) by lia. rewrite (VP _ b Eb). symmetry in Hn. rewrite (VT _ b Hn). reflexivity.
Qed.

Lemma hoGH_add : forall E a b, ew E 21 = w64 a -> ew E 27 = w64 b -> 0 <= a -> 0 <= b -> a + b < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff 21 0) (SOff 27 0)) = w64 (a + b).
Proof.
intros E a b Ha Hb A0 B0 AB.
rewrite denot_lit_U, U_SAlu, !U_SOff, Ha, Hb. unfold w64. rewrite !unsigned_lit_small by lia.
cbn [zalu_raw]. rewrite !Z.add_0_r.
rewrite (zcanon_id a), (zcanon_id b), (zcanon_id (a + b)) by (unfold M64; lia). reflexivity.
Qed.

Ltac hoGH_rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in
      change (sr_get (ss_regs ss) r) with e in Hr
  end.

Ltac hoGH_q HS EE r n Q := prreg HS r Q; rewrite (EE n r eq_refl) in Q.

Ltac hoGH_k KP r z Q :=
  rewrite (KP r z ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)), Q.

Lemma hoG_head : hoG_head_stmt.
Proof.
intros c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G r nn ii HPRE0 K.
pose proof HPRE0 as (HB & R19 & R20 & R23 & R26 & R27 & HFSH & HOK & HSPL & LT' & Hnn_def & Hii & Hnn & Hr &
  RD8 & RD16 & RD24 & GF & LG & HGs & HMM & Hout & GO & HANS).
pose proof (ho_mid_entry c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ho_shC false 0x7448 HB HFSH eq_refl
  ltac:(unfold ho_shC; repeat constructor; lia) ltac:(discriminate)) as [HS HEI].
pose proof (ho_shokM c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F false HB ltac:(discriminate)) as SHOK.
cbn [ho_SHM app] in SHOK.
pose proof HB as (HPRE & HMID & HSP1 & HF & HRM & HSV).
pose proof HMID as (HJ & HFRS & HFA & HPERM & HKEPT & HROD & HG2 & HL2 & HFLAG).
pose proof HPRE as ((mdc & HJ0) & _ & _ & _ & _ & _ & Hal16 & Hwin & Hsp & _ & _ & _ & Hout0 & Hh0 & Hh8 & Hhin & Hhb & Hhe &
  _ & _ & _ & _ & _ & HOUT & _).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _) & _).
pose proof HSP1 as (_ & Hsp1 & Hsp1al).
pose proof HRM as (G2 & G3 & G4 & G8 & G9 & G18 & G21 & G24 & G25).
assert (HSTK : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
destruct (HOUT Hout) as ((_ & Ho63 & _ & Hsep & _) & _).
assert (Hin2 : In (c_hb c, c_hn c) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HPERM) Hhin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hin2) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
pose proof (st_ok_pi_submem _ _ _ [] HS (submem_nil _) eq_refl) as HS2. clear HS. rename HS2 into HS.
cbn [ss_pc ss_regs ss_resv ss_facts ss_hoM] in HS.
set (E := EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) in *.
assert (EE : forall (n : nat) (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr).
{ intros n rr Hn. unfold E, EHOm. apply ew_Eimg_Ereg_nat. exact Hn. }
assert (E27 : ew E 27 = w64 (48 * ii)) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (E26 : ew E 26 = w64 432) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (E20 : ew E 20 = w64 (2 ^ 64 - 1 - c_h c)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = w64 (c_h c)) by (rewrite (EE 21%nat 21%bv eq_refl); exact G21).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KSPZ : YM05.alloc_ceiling + 8688 <= spZ (c_regs c) <= 2 ^ 47) by lia.
assert (KSP1 : YM05.alloc_ceiling + 8512 <= sp1 <= 2 ^ 47 - 160) by lia.
assert (Hii7 : 0 <= ii <= 7) by lia.
ra_join_fact HS 27%nat (mkAF 0 336 4) ltac:(rewrite E27; unfold w64; rewrite unsigned_lit_small by lia; lia).
ra_join_fact HS 26%nat (mkAF 432 432 0) ltac:(rewrite E26; unfold w64; rewrite unsigned_lit_small by lia; lia).
ra_join_fact HS 20%nat (mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0) ltac:(rewrite E20; unfold w64; rewrite unsigned_lit_small by lia; lia).
norm_ss HS.
pose (RUN := paj_run (fx := c_fq c) B LAWS). pose (BR := paj_branch (fx := c_fq c) (PI := PI)).
unfold ho_cfg.
paj_run_tok RUN HS HJ SHOK HOspan.
{ apply awr_ok_nil. }
pose proof (hoGH_fr0 E (w_H W2) mem2 (ms_mem ms) HFr) as (MEQ & MPR).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hin2) as (_ & _ & _ & _ & HtP & _).
assert (Hf1 : In (1, fpos) (frames S2)) by (rewrite HFRS; left; reflexivity).
assert (HFe : frame_addr ly2 1 fpos = F) by (rewrite (HFA 1 fpos); symmetry; exact HF).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ) Hf1) as (Hal32 & Happ & HFpres & HFspres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos (proj1 HJ) Hf1) as (HF4096 & HFceil & _).
assert (Hfb : fs_frame_bytes 1 = 128) by reflexivity.
rewrite HFe in Hal32, Happ, HFpres, HFspres, HF4096, HFceil. rewrite Hfb in Happ, HFpres, HFspres, HFceil.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
hoGH_rreg HS (10%bv : bv 5) Ra0.
hoGH_rreg HS (22%bv : bv 5) Ra22.
prreg HS (11%bv : bv 5) Ra1. rewrite (EE 23%nat 23%bv eq_refl) in Ra1.
prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra.
hoGH_q HS EE (2%bv : bv 5) 2%nat Q2.
hoGH_q HS EE (3%bv : bv 5) 3%nat Q3.
hoGH_q HS EE (4%bv : bv 5) 4%nat Q4.
hoGH_q HS EE (8%bv : bv 5) 8%nat Q8.
hoGH_q HS EE (9%bv : bv 5) 9%nat Q9.
hoGH_q HS EE (18%bv : bv 5) 18%nat Q18.
hoGH_q HS EE (19%bv : bv 5) 19%nat Q19.
hoGH_q HS EE (20%bv : bv 5) 20%nat Q20.
hoGH_q HS EE (21%bv : bv 5) 21%nat Q21.
hoGH_q HS EE (23%bv : bv 5) 23%nat Q23.
hoGH_q HS EE (24%bv : bv 5) 24%nat Q24.
hoGH_q HS EE (25%bv : bv 5) 25%nat Q25.
hoGH_q HS EE (26%bv : bv 5) 26%nat Q26.
hoGH_q HS EE (27%bv : bv 5) 27%nat Q27.
assert (ADDV : sv_denot E (SAlu ALU_ADD (SOff 21 0) (SOff 27 0)) = w64 (c_h c + 48 * ii))
  by (apply hoGH_add; [exact E21 | exact E27 | lia | lia | lia]).
assert (HspM : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite Q2, G2; unfold w64; apply unsigned_lit_small; lia).
assert (A1 : getr (ms_regs ms) 10 = w64 (c_h c + 48 * ii)) by (rewrite Ra0; exact ADDV).
assert (A2 : getr (ms_regs ms) 11 = w64 (F + 32)) by (rewrite Ra1; exact R23).
assert (A3 : getr (ms_regs ms) 12 = w64 6) by (rewrite Ra2; reflexivity).
assert (A4 : 0 <= 6 < 2 ^ 32) by lia.
assert (A5 : 0 <= c_h c + 48 * ii) by lia.
assert (A6 : c_h c + 48 * ii + 6 <= 2 ^ 63) by lia.
assert (A7 : 0 <= F + 32) by lia.
assert (A8 : F + 32 + 6 <= 2 ^ 63) by lia.
assert (A9 : spZ (ms_regs ms) = c_sp0 c + (sp1 - c_sp0 c)) by (rewrite HspM; lia).
assert (A10 : (sp1 - c_sp0 c) mod 16 = 0) by lia.
assert (A11 : sp1 - c_sp0 c <= 0) by lia.
assert (A12 : 2 * ESTACK - (sp1 - c_sp0 c) <= c_STK c) by (unfold ESTACK; lia).
assert (A13 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3; exact G3).
assert (A14 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4; exact G4).
assert (A16 : YK0s.ret_ok (Z_to_bv 64 (BASE + 29796))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (A17 : src_ok SEGS W2 (ms_regs ms) (ms_mem ms) (c_h c + 48 * ii) 6).
{ intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (HtP a ltac:(lia))) | rewrite HspM; unfold ESTACK; lia]. }
assert (A18 : src_ok SEGS W2 (ms_regs ms) (ms_mem ms) (F + 32) 6).
{ intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (HFpres a ltac:(lia))) | rewrite HspM; unfold ESTACK; lia]. }
assert (A19 : forall a, c_h c + 48 * ii <= a < c_h c + 48 * ii + 6 ->
  ~ (c_sp0 c + (sp1 - c_sp0 c) - 2 * ESTACK <= a < c_sp0 c + (sp1 - c_sp0 c))) by (intros a Ha; unfold ESTACK; lia).
assert (A20 : forall a, F + 32 <= a < F + 32 + 6 ->
  ~ (c_sp0 c + (sp1 - c_sp0 c) - 2 * ESTACK <= a < c_sp0 c + (sp1 - c_sp0 c))) by (intros a Ha; unfold ESTACK; lia).
assert (A21 : amem_range (c_h c + 48 * ii) 6)
  by (apply (amem_range_of_block SEGS B LAWS _ _ _ _ _ (c_hb c) (c_hn c) _ 6 (proj1 HJ) Hin2); lia).
assert (A22 : amem_range (F + 32) 6) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia).
assert (A23 : range_addressable (aview SEGS (w_H W2) (ms_mem ms)) SHADOW_OFF (c_h c + 48 * ii) 6)
  by (apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ (c_hb c) (c_hn c) _ 6 (proj1 HJ) Hin2); lia).
assert (A24 : 0 < 6 -> shadow_hull_vis (aview SEGS (w_H W2) (ms_mem ms)) (c_h c + 48 * ii) 6)
  by (intros _; apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ (c_hb c) (c_hn c) _ 6 (proj1 HJ) Hin2); lia).
assert (A25 : range_addressable (aview SEGS (w_H W2) (ms_mem ms)) SHADOW_OFF (F + 32) 6).
{ unfold range_addressable. intros a Ha. exists 0. split; [|left; reflexivity].
  rewrite MEQ. unfold shadow_of_addr.
  replace (SHADOW_OFF + a / 8) with (SB + F / 8 + 4) by (unfold SB, SHADOW_OFF; lia).
  exact (HFSH 4 ltac:(lia)). }
assert (A26 : 0 < 6 -> shadow_hull_vis (aview SEGS (w_H W2) (ms_mem ms)) (F + 32) 6).
{ intros _ s Hs. unfold shadow_addr in Hs.
  replace s with (shadow_addr F + (s - shadow_addr F)) by lia.
  apply (aview_some_of_apresent SEGS). apply (proj1 (HFspres (s - shadow_addr F) ltac:(unfold shadow_addr, SHADOW_OFF in *; lia))). }
pmkst HS.
eapply SRr_bind.
{ exact (aj_bcmp_at (fx := c_fq c) SEGS B LAWS pa_segs_low (SIGMA AS___interceptor_trampoline_bcmp) (ABCMP (c_fq c))
    W2 (ms_regs ms) (ms_mem ms) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly2 S2 _ k2 (c_h c + 48 * ii) (F + 32) 6 (sp1 - c_sp0 c) _ HJ
    A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 Rra A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26). }
intros W' c2 _ HPost. cbv beta in HPost.
destruct HPost as (-> & regs4 & mem4 & md4 & v & -> & HJ4 & HP4 & Hv & Hcmp & Hfr4 & Hpres4).
assert (KP : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> acallee_saved z -> getr regs4 rr = getr (ms_regs ms) rr)
  by (intros rr z -> Hz; exact (HP4 z Hz)).
assert (AV4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 8192 <= a < sp1) ->
  aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hz. rewrite (Hfr4 a Ha) by (unfold ESTACK; lia). apply MEQ. }
assert (PR4 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem4 a)
  by (intros a Ha; apply Hpres4; apply MPR; exact Ha).
assert (HRB : ho_regs_mid c regs4 sp1 F).
{ unfold ho_regs_mid.
  split; [hoGH_k KP (2%bv : bv 5) 2 Q2; exact G2|].
  split; [hoGH_k KP (3%bv : bv 5) 3 Q3; exact G3|].
  split; [hoGH_k KP (4%bv : bv 5) 4 Q4; exact G4|].
  split; [hoGH_k KP (8%bv : bv 5) 8 Q8; exact G8|].
  split; [hoGH_k KP (9%bv : bv 5) 9 Q9; exact G9|].
  split; [hoGH_k KP (18%bv : bv 5) 18 Q18; exact G18|].
  split; [hoGH_k KP (21%bv : bv 5) 21 Q21; exact G21|].
  split; [hoGH_k KP (24%bv : bv 5) 24 Q24; exact G24|].
  hoGH_k KP (25%bv : bv 5) 25 Q25; exact G25. }
assert (HB4 : ho_base c fpos ly2 S2 W2 mem4 md4 k2 H2 regs4 sp1 F).
{ apply (hoG_base_frame c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F mem4 md4 regs4
    (fun a => sp1 - 8192 <= a < sp1) HB HJ4).
  - intros a Ha Hz. exact (AV4 a Ha Hz).
  - exact PR4.
  - intros a Ha. left. cbv beta in Ha. lia.
  - intros a Ha Ho. exfalso. cbv beta in Ha. lia.
  - exact HRB. }
assert (P19 : getr regs4 19 = w64 (48 * nn)) by (hoGH_k KP (19%bv : bv 5) 19 Q19; exact R19).
assert (P20 : getr regs4 20 = w64 (2 ^ 64 - 1 - c_h c)) by (hoGH_k KP (20%bv : bv 5) 20 Q20; exact R20).
assert (P23 : getr regs4 23 = w64 (F + 32)) by (hoGH_k KP (23%bv : bv 5) 23 Q23; exact R23).
assert (P26 : getr regs4 26 = w64 432) by (hoGH_k KP (26%bv : bv 5) 26 Q26; exact R26).
assert (P27 : getr regs4 27 = w64 (48 * ii)) by (hoGH_k KP (27%bv : bv 5) 27 Q27; exact R27).
assert (P22 : getr regs4 22 = w64 (c_h c + 48 * ii)) by (hoGH_k KP (22%bv : bv 5) 22 Ra22; exact ADDV).
assert (FSH4 : ho_fsh W2 mem4 F ho_shC).
{ intros i Hi. rewrite AV4 by (unfold SB; lia). exact (HFSH i Hi). }
assert (RD8' : rdword (aview SEGS (w_H W2) mem4) (sp1 + 8) = Some SB).
{ apply (hoG_rdword_kept (aview SEGS (w_H W2) mem2)); [|exact RD8]. intros i Hi. apply AV4; lia. }
assert (RD16' : rdword (aview SEGS (w_H W2) mem4) (sp1 + 16) = Some (c_out c)).
{ apply (hoG_rdword_kept (aview SEGS (w_H W2) mem2)); [|exact RD16]. intros i Hi. apply AV4; lia. }
assert (RD24' : rdword (aview SEGS (w_H W2) mem4) (sp1 + 24) = Some r).
{ apply (hoG_rdword_kept (aview SEGS (w_H W2) mem2)); [|exact RD24]. intros i Hi. apply AV4; lia. }
assert (GF4 : garr8 SEGS (mrestrict (w_H W2) mem4) (F + 32) (map (fun b : byte => bv_unsigned b) G)).
{ apply (garr8_aview_kept SEGS (w_H W2) (w_H W2) mem2 mem4); [|exact GF].
  rewrite length_map, LG. intros a Ha. apply AV4; lia. }
assert (GO4 : garr8 SEGS (mrestrict (w_H W2) mem4) (c_out c) (map (fun b : byte => bv_unsigned b) G)).
{ apply (garr8_aview_kept SEGS (w_H W2) (w_H W2) mem2 mem4); [|exact GO].
  rewrite length_map, LG. intros a Ha. apply AV4; lia. }
assert (LSM : length (disco_table_c.s_mac G) = 6%nat).
{ unfold disco_table_c.s_mac, disco_table_c.sub. rewrite length_firstn, length_skipn, LG. reflexivity. }
assert (GT : garr8 SEGS (mrestrict (w_H W2) (ms_mem ms)) (c_h c) (map (fun b : byte => bv_unsigned b) T')).
{ apply (garr8_aview_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms)); [intros a _; apply MEQ|].
  pose proof HG2 as X. rewrite HSPL, map_app in X. apply garr8_app in X. exact (proj1 X). }
assert (GS : garr8 SEGS (mrestrict (w_H W2) (ms_mem ms)) (F + 32)
  (map (fun b : byte => bv_unsigned b) (disco_table_c.s_mac G))).
{ apply (garr8_aview_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms)); [intros a _; apply MEQ|].
  pose proof (garr8_sub_x SEGS _ (F + 32) _ 0%nat 6%nat GF ltac:(rewrite length_map, LG; lia)) as X.
  rewrite skipn_map, firstn_map in X. replace (F + 32 + Z.of_nat 0) with (F + 32) in X by lia. exact X. }
assert (XC : v = w64 0 <-> disco_table_c.mac_of T' ii = disco_table_c.s_mac G)
  by exact (iff_trans Hcmp (hoGH_mac (w_H W2) (ms_mem ms) (c_h c) (F + 32) T' (disco_table_c.s_mac G) ii LT' LSM Hii7 GT GS)).
assert (HPRE4 : hoG_pre c fpos ly2 S2 W2 mem4 md4 k2 regs4 sp1 F H2 T' G r nn ii).
{ unfold hoG_pre. split; [exact HB4|]. split; [exact P19|]. split; [exact P20|]. split; [exact P23|].
  split; [exact P26|]. split; [exact P27|]. split; [exact FSH4|]. split; [exact HOK|]. split; [exact HSPL|].
  split; [exact LT'|]. split; [exact Hnn_def|]. split; [exact Hii|]. split; [exact Hnn|]. split; [exact Hr|].
  split; [exact RD8'|]. split; [exact RD16'|]. split; [exact RD24'|]. split; [exact GF4|]. split; [exact LG|].
  split; [exact HGs|]. split; [exact HMM|]. split; [exact Hout|]. split; [exact GO4 | exact HANS]. }
exact (K regs4 mem4 md4 v HPRE4 Hv XC P22).
Qed.

Lemma hoG_ret : ho_seg_T_stmt -> hoG_ret_stmt.
Proof.
intros HTs. unfold hoG_ret_stmt.
intros c fpos ly2 S2 W2 mem4 md4 k2 regs4 sp1 F H2 T' G r nn ii v HP Hv XC H22 IH.
unfold hoG_pre in HP.
destruct HP as (HB & R19 & R20 & R23 & R26 & R27 & HFSH & HOK2 & HT2 & LT & Hnn & Hii & Hnn8 & Hr & S8 & S16 & S24 & GG & LG & HGs & HNM & Hout & GO & HANS).
set (regs4' := regupd regs4 (19%bv : bv 5) (w64 (c_out c))).
assert (HB' : ho_base c fpos ly2 S2 W2 mem4 md4 k2 H2 regs4' sp1 F).
{ destruct HB as (B1 & B2 & B3 & B4 & B5 & B6). split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
  split; [exact B4|]. split; [|exact B6].
  apply hoG_regs_mid_upd; [hoG_bvne .. | exact B5]. }
assert (R19' : getr regs4' 19 = w64 (c_out c)) by (apply hoG_getr_upd_same; reflexivity).
pose proof (ho_mid_entry c fpos ly2 S2 W2 mem4 md4 k2 H2 regs4' sp1 F ho_shC true 0x7464 HB' HFSH eq_refl
  ltac:(unfold ho_shC; repeat constructor; lia) (fun _ => conj Hout R19')) as [HS HEI].
pose proof (ho_shokM c fpos ly2 S2 W2 mem4 md4 k2 H2 regs4' sp1 F true HB' (fun _ => conj Hout R19')) as SHOK.
cbn [ho_SHM app] in SHOK.
set (FL := flag_addr (c_lyc c) 1 fpos) in *.
set (E0 := EHOm c regs4' FL) in *.
pose proof HB as (HPRE & HMID & HSP1 & HF & HRM & HSV).
pose proof HMID as (HJ & HFRS & HFA & HPERM & HKEPT & HROD & HG2 & HL2 & HFLAG).
pose proof HPRE as ((mdc & HJ0) & _ & _ & _ & _ & _ & Hal16 & Hwin & Hsp & _ & _ & _ & Hout0 & Hh0 & Hh8 & Hhin & Hhb & Hhe & _ & _ & _ & _ & _ & HOUT & _).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof HRM as (M2 & M3 & M4 & M8 & M9 & M18 & M21 & M24 & M25).
pose proof HSP1 as (_ & Hsp1 & Hsp1al).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HhinS : In (c_hb c, c_hn c) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HPERM) Hhin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) HhinS) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
assert (Hin2 : In (1, fpos) (frames S2)) by (rewrite HFRS; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos (proj1 HJ) Hin2) as (HF4 & HFc & _).
rewrite HFA in HF4, HFc. change (fs_frame_bytes 1) with 128 in HFc. rewrite <- HF in HF4, HFc.
destruct (HOUT Hout) as ((Ho8 & Ho63 & Hoam & Hosep & _ & Hora & _ & Howr & _) & Hoh & _).
assert (Hspr : 0 <= spZ (c_regs c) < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
assert (ESTK : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
assert (EV : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = getr regs4' rr)
  by (intros n rr Hn; unfold E0, EHOm; exact (ew_Eimg_Ereg_nat regs4' _ n rr Hn)).
assert (U2 : bv_unsigned (ew E0 2) = sp1) by (rewrite (EV 2%nat 2%bv eq_refl); unfold regs4'; rewrite hoG_getr_upd_other by hoG_bvne; rewrite M2; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E0 9) = sp1) by (rewrite (EV 9%nat 9%bv eq_refl); unfold regs4'; rewrite hoG_getr_upd_other by hoG_bvne; rewrite M9; unfold w64; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E0 8) = spZ (c_regs c)) by (rewrite (EV 8%nat 8%bv eq_refl); unfold regs4'; rewrite hoG_getr_upd_other by hoG_bvne; rewrite M8; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E0 18) = F) by (rewrite (EV 18%nat 18%bv eq_refl); unfold regs4'; rewrite hoG_getr_upd_other by hoG_bvne; rewrite M18; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E0 19) = c_out c) by (rewrite (EV 19%nat 19%bv eq_refl), R19'; unfold w64; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E0 21) = c_h c) by (rewrite (EV 21%nat 21%bv eq_refl); unfold regs4'; rewrite hoG_getr_upd_other by hoG_bvne; rewrite M21; unfold w64; apply unsigned_lit_small; lia).
assert (HF8 : 0 <= F / 8 <= F) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (U24 : bv_unsigned (ew E0 24) = SB + F / 8) by (rewrite (EV 24%nat 24%bv eq_refl); unfold regs4'; rewrite hoG_getr_upd_other by hoG_bvne; rewrite M24; unfold w64; apply unsigned_lit_small; unfold SB; lia).
pose proof HS as HS0. unfold st_ok_pi, st_ok in HS0.
destruct HS0 as (_ & _ & _ & _ & _ & _ & _ & (_ & HROK & HPD) & _).
cbn [ss_mem ss_facts abs_ss setpc ss_hoM ho_regionsM app] in HROK, HPD.
cbn [pairwise_disjoint all_disjoint] in HPD. unfold extent_disjoint in HPD.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val ho_outreg ho_sp1_region ho_saved_region got_regionP bcell_regionP
  uar_got_regionP uar_cell_regionP ho_frame_region ho_fshadow_region ho_hregM] in HPD.
rewrite U2, U8, U18, U19, U21, U24 in HPD.
destruct HPD as ((D1 & D2 & _ & _ & _ & _ & D7 & D8 & D9 & _) & (_ & _ & _ & _ & _ & _ & _ & D10 & _) & _).
assert (Rr : 0 <= r < 2 ^ 64) by (clear - Hr; lia).
assert (HDJ : hoG_box ((c_out c + 24 <= sp1 \/ sp1 + 56 <= c_out c) /\ (c_out c + 24 <= F \/ F + 128 <= c_out c) /\
  (c_out c + 24 <= SB + F / 8 \/ SB + F / 8 + 16 <= c_out c) /\ (sp1 + 56 <= c_h c \/ c_h c + 480 <= sp1) /\
  (c_out c + 24 <= c_h c \/ c_h c + 480 <= c_out c))).
{ unfold hoG_box. split; [destruct D1 as [X|X]; [left|right]; clear - X; lia|].
  split; [destruct D7 as [X|X]; [left|right]; clear - X; lia|].
  split; [destruct D8 as [X|X]; [left|right]; clear - X; lia|].
  split; [destruct D10 as [X|X]; [left|right]; clear - X; lia | exact Hoh]. }
assert (HrB : hoG_box (r = 0 \/ r = 1)) by exact Hr.
clear D1 D2 D7 D8 D9 D10 Hoh Hosep Hr.
apply Forall_inv in HROK. unfold region_ok in HROK. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ho_outreg] in HROK.
rewrite U19 in HROK. destruct HROK as (_ & _ & HOW & _).
assert (E32 : ew E0 32 = Z_to_bv 64 SB)
  by (unfold E0, EHOm; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4' _ 0)).
assert (U22 : bv_unsigned (ew E0 22) = c_h c + 48 * ii)
  by (rewrite (EV 22%nat 22%bv eq_refl); unfold regs4'; rewrite hoG_getr_upd_other by hoG_bvne; rewrite H22; unfold w64; apply unsigned_lit_small; lia).
assert (EW19 : ew E0 19 = Z_to_bv 64 (c_out c)) by (rewrite (EV 19%nat 19%bv eq_refl); exact R19').
assert (EW22 : ew E0 22 = Z_to_bv 64 (c_h c + 48 * ii))
  by (rewrite (EV 22%nat 22%bv eq_refl); unfold regs4'; rewrite hoG_getr_upd_other by hoG_bvne; exact H22).
pose proof (st_ok_pi_havoc 60 E0 _ _ (hoG_ws nn r ii H2) HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia)) as HS1.
pose proof (img_env_havoc E0 60 (hoG_ws nn r ii H2) HEI ltac:(vm_compute; lia)) as HEI1.
clear HS.
assert (AG1 : forall n, (n < 60)%nat -> ew (havoc E0 60 (hoG_ws nn r ii H2)) n = ew E0 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (E60 : ew (havoc E0 60 (hoG_ws nn r ii H2)) 60 = w64 (48 * nn))
  by exact (ew_havoc_new E0 60 (hoG_ws nn r ii H2) 0 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E61 : ew (havoc E0 60 (hoG_ws nn r ii H2)) 61 = w64 r)
  by exact (ew_havoc_new E0 60 (hoG_ws nn r ii H2) 1 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E62 : ew (havoc E0 60 (hoG_ws nn r ii H2)) 62 = w64 (bytes_le_to_Z (disco_table_c.sub H2 (48 * ii + 8) 4)))
  by exact (ew_havoc_new E0 60 (hoG_ws nn r ii H2) 2 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E63 : ew (havoc E0 60 (hoG_ws nn r ii H2)) 63 = w64 (bytes_le_to_Z (disco_table_c.sub H2 (48 * ii + 12) 1)))
  by exact (ew_havoc_new E0 60 (hoG_ws nn r ii H2) 3 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E64 : ew (havoc E0 60 (hoG_ws nn r ii H2)) 64 = w64 (bytes_le_to_Z (disco_table_c.sub H2 (48 * ii + 13) 1)))
  by exact (ew_havoc_new E0 60 (hoG_ws nn r ii H2) 4 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E65 : ew (havoc E0 60 (hoG_ws nn r ii H2)) 65 = w64 (bytes_le_to_Z (disco_table_c.sub H2 (48 * ii + 14) 1)))
  by exact (ew_havoc_new E0 60 (hoG_ws nn r ii H2) 5 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E66 : ew (havoc E0 60 (hoG_ws nn r ii H2)) 66 = w64 (bytes_le_to_Z (disco_table_c.sub H2 (48 * ii + 15) 1)))
  by exact (ew_havoc_new E0 60 (hoG_ws nn r ii H2) 6 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E67 : ew (havoc E0 60 (hoG_ws nn r ii H2)) 67 = w64 (bytes_le_to_Z (disco_table_c.sub H2 (48 * ii + 16) 1)))
  by exact (ew_havoc_new E0 60 (hoG_ws nn r ii H2) 7 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E68 : ew (havoc E0 60 (hoG_ws nn r ii H2)) 68 = w64 (bytes_le_to_Z (disco_table_c.sub H2 (48 * ii + 20) 4)))
  by exact (ew_havoc_new E0 60 (hoG_ws nn r ii H2) 8 (Z_to_bv 64 0) ltac:(cbn; lia)).
set (E1 := havoc E0 60 (hoG_ws nn r ii H2)) in *.
pose proof (hoG_swap (c_fq c) E1 _ (w_H W2) regs4' regs4 (Z_to_bv 64 (BASE + 0x7464)) mem4 (19%bv : bv 5) (SOff 60 0) HS1
  eq_refl ltac:(rewrite sv_denot_SOff0, E60; symmetry; exact R19)
  ltac:(intros r' Hr'; unfold regs4'; symmetry; apply hoG_getr_upd_other; exact Hr')) as HS2.
clear HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_hoM] in HS2.
pose proof (st_ok_pi_submem _ _ _ [] HS2 (submem_nil _) eq_refl) as HS3. clear HS2.
cbn [ss_pc ss_regs ss_resv ss_facts] in HS3.
assert (OKsp : region_ok SEGS E1 (mrestrict (w_H W2) mem4) hoG_sp1R).
{ unfold region_ok, hoG_sp1R. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite (AG1 9%nat ltac:(lia)), U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - apply (hoG_chunk_rd E1 (w_H W2) mem4 sp1 8 32 SB); [rewrite AG1 by lia; exact E32 | unfold SB; lia | exact S8].
  - apply (hoG_chunk_rd E1 (w_H W2) mem4 sp1 16 19 (c_out c)); [rewrite AG1 by lia; exact EW19 | lia | exact S16].
  - apply (hoG_chunk_rd E1 (w_H W2) mem4 sp1 24 61 r); [exact E61 | lia | exact S24]. }
assert (OKrow : region_ok SEGS E1 (mrestrict (w_H W2) mem4) hoG_rowR).
{ unfold region_ok, hoG_rowR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite (AG1 22%nat ltac:(lia)), U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil;
  (apply (hoG_chunk_row E1 _ (c_h c) H2); [exact HG2 | | lia | rewrite HL2; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]);
  first [ rewrite E62 | rewrite E63 | rewrite E64 | rewrite E65 | rewrite E66 | rewrite E67 | rewrite E68 ];
  do 4 f_equal; lia. }
assert (OKoA : region_ok SEGS E1 (mrestrict (w_H W2) mem4) hoG_outA).
{ unfold region_ok, hoG_outA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite (AG1 19%nat ltac:(lia)), U19. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HOW; lia | apply Forall_nil]. }
assert (OKoB : region_ok SEGS E1 (mrestrict (w_H W2) mem4) hoG_outB).
{ unfold region_ok, hoG_outB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite (AG1 19%nat ltac:(lia)), U19. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HOW; lia | apply Forall_nil]. }
assert (B2 : base_val E1 (Some 9%nat) = sp1) by (cbn [base_val]; rewrite AG1 by lia; exact U9).
assert (B19 : base_val E1 (Some 19%nat) = c_out c) by (cbn [base_val]; rewrite AG1 by lia; exact U19).
assert (B22 : base_val E1 (Some 22%nat) = c_h c + 48 * ii) by (cbn [base_val]; rewrite AG1 by lia; exact U22).
pose proof (st_ok_pi_add_region _ _ _ hoG_sp1R HS3 eq_refl OKsp I) as HS4. clear HS3.
assert (DJ1 : all_disjoint E1 hoG_rowR [hoG_sp1R]).
{ cbn [all_disjoint]. unfold extent_disjoint, hoG_rowR, hoG_sp1R. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite B22, B2. split; [|exact I]. pose proof HDJ as Q; unfold hoG_box in Q; destruct Q as (_ & _ & _ & Q & _).
  clear - Q Hii Hnn8. lia. }
assert (DJ2 : all_disjoint E1 hoG_outA [hoG_rowR; hoG_sp1R]).
{ cbn [all_disjoint]. unfold extent_disjoint, hoG_rowR, hoG_sp1R, hoG_outA. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite B22, B2, B19. pose proof HDJ as Q; unfold hoG_box in Q; destruct Q as (Q1 & _ & _ & _ & Q5).
  split; [clear - Q5 Hii Hnn8; lia|]. split; [clear - Q1; lia | exact I]. }
assert (DJ3 : all_disjoint E1 hoG_outB [hoG_outA; hoG_rowR; hoG_sp1R]).
{ cbn [all_disjoint]. unfold extent_disjoint, hoG_rowR, hoG_sp1R, hoG_outA, hoG_outB. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite B22, B2, B19. pose proof HDJ as Q; unfold hoG_box in Q; destruct Q as (Q1 & _ & _ & _ & Q5).
  split; [clear; lia|]. split; [clear - Q5 Hii Hnn8; lia|]. split; [clear - Q1; lia | exact I]. }
pose proof (st_ok_pi_add_region _ _ _ hoG_rowR HS4 eq_refl OKrow DJ1) as HS5. clear HS4.
pose proof (st_ok_pi_add_region _ _ _ hoG_outA HS5 eq_refl OKoA DJ2) as HS6. clear HS5.
pose proof (st_ok_pi_add_region _ _ _ hoG_outB HS6 eq_refl OKoB DJ3) as HS. clear HS6.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
ra_join_fact HS 22%nat (mkAF 4096 140737479966720 3)
  ltac:(rewrite (AG1 22%nat ltac:(lia)), U22; change (2 ^ 3) with 8; lia).
norm_ss HS.
assert (UB0 : U E0 HOBx = SHADOW_OFF).
{ unfold HOBx. rewrite U_SOff, E32, unsigned_lit_small by (unfold SB; lia). rewrite Z.add_0_r.
  apply zcanon_id. unfold SB, SHADOW_OFF, M64; lia. }
assert (UO0 : U E0 (SOff 19 0) = c_out c) by (apply U_atom; [exact EW19 | lia]).
pose proof (Forall_inv SHOK) as SH19. unfold shent_ok in SH19. cbn [she_m she_lo she_hi] in SH19.
destruct SH19 as [RA19 _]. rewrite UB0, UO0 in RA19.
assert (SHOK2 : sh_ok SEGS HOBx [mkSHE 19 0 24; mkSHE 22 8 24] E1 (mrestrict (w_H W2) mem4)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (ho_shent_gen E1 (w_H W2) mem4 19 (c_out c) 0 24);
    [ rewrite AG1 by lia; exact E32 | rewrite AG1 by lia; exact EW19 | lia | lia
    | replace (c_out c + 0) with (c_out c) by lia; replace (24 - 0) with 24 by lia; exact Hoam
    | rewrite aview_rd_of; exact RA19 ].
  - apply (ho_shent_gen E1 (w_H W2) mem4 22 (c_h c + 48 * ii) 8 24);
    [ rewrite AG1 by lia; exact E32 | rewrite AG1 by lia; exact EW22 | lia | lia
    | apply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) HhinS); lia
    | apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) HhinS); lia ]. }
clear SHOK. rename SHOK2 into SHOK.
pose (RUN := paj_run (fx := c_fq c) B LAWS). pose (RUNTO := paj_run_to (fx := c_fq c) B LAWS).
pose (BR := paj_branch (fx := c_fq c) (PI := PI)).
assert (EW10 : ew E1 10 = v)
  by (rewrite AG1 by lia; rewrite (EV 10%nat 10%bv eq_refl); unfold regs4'; rewrite hoG_getr_upd_other by hoG_bvne; exact Hv).
pose proof (bv_unsigned_in_range 64 v) as Hvr. unfold bv_modulus in Hvr. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hvr.
assert (U10 : U E1 (SOff 10 0) = bv_unsigned v)
  by (apply U_atom; [rewrite EW10; symmetry; apply Z_to_bv_bv_unsigned | exact Hvr]).
assert (HspR : spZ (c_regs c) - REAC_HUNT_OBSERVE_STK <= sp1 < spZ (c_regs c)) by lia.
assert (BR1 : forall k, 0 <= k -> k + 1 <= 480 -> 0 <= bytes_le_to_Z (disco_table_c.sub H2 k 1) < 256).
{ intros k Hk0 Hk1. pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub H2 k 1)) as Bq0.
  pose proof (bytes_le_to_Z_bound (disco_table_c.sub H2 k 1)) as Bq1.
  rewrite (HuntObsLib.len_sub H2 k 1) in Bq1 by (try rewrite HL2; lia). cbn in Bq1. lia. }
ra_join_fact HS 63%nat (mkAF 0 255 0) ltac:(rewrite E63; unfold w64; rewrite unsigned_lit_small by (pose proof (BR1 (48 * ii + 12)); lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; pose proof (BR1 (48 * ii + 12)); lia).
ra_join_fact HS 64%nat (mkAF 0 255 0) ltac:(rewrite E64; unfold w64; rewrite unsigned_lit_small by (pose proof (BR1 (48 * ii + 13)); lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; pose proof (BR1 (48 * ii + 13)); lia).
ra_join_fact HS 65%nat (mkAF 0 255 0) ltac:(rewrite E65; unfold w64; rewrite unsigned_lit_small by (pose proof (BR1 (48 * ii + 14)); lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; pose proof (BR1 (48 * ii + 14)); lia).
ra_join_fact HS 66%nat (mkAF 0 255 0) ltac:(rewrite E66; unfold w64; rewrite unsigned_lit_small by (pose proof (BR1 (48 * ii + 15)); lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; pose proof (BR1 (48 * ii + 15)); lia).
ra_join_fact HS 67%nat (mkAF 0 255 0) ltac:(rewrite E67; unfold w64; rewrite unsigned_lit_small by (pose proof (BR1 (48 * ii + 16)); lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; pose proof (BR1 (48 * ii + 16)); lia).
norm_ss HS.
assert (KR : forall (rr : bv 5) (n : nat), Z.of_nat n = bv_unsigned rr -> (n < 32)%nat -> rr <> 19%bv -> ew E1 n = getr regs4 rr).
{ intros rr n Hn Hn32 Hne. rewrite AG1 by lia. rewrite (EV n rr Hn). unfold regs4'. apply hoG_getr_upd_other. exact Hne. }
assert (KB : 4096 <= sp1 /\ sp1 + 56 <= 2 ^ 47 /\ 4096 <= F /\ F + 128 <= 2 ^ 47 /\ 0 <= c_h c /\ c_h c + 480 <= 2 ^ 47 /\
  0 <= c_out c /\ c_out c + 24 <= 2 ^ 63) by lia.
assert (SUBT : forall k (n : nat), 0 <= k -> k + Z.of_nat n <= 400 -> disco_table_c.sub H2 k n = disco_table_c.sub T' k n).
{ intros k n Hk Hkn. rewrite HT2 at 1. apply HuntObsLib.sub_app_l; [exact Hk | rewrite LT; lia]. }
assert (HSF : forall i, 0 <= i < 16 -> 0 <= SB + F / 8 + i < 2 ^ 64) by (intros i Hi; unfold SB; lia).
unfold ho_cfg.
psrr_branch_tok RUN BR HS SHOK HOspan.
- rewrite branch_eq_U, U10, YI04.U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  assert (HM : disco_table_c.mac_of T' ii = disco_table_c.s_mac G)
    by (apply XC; apply bv_eq; rewrite Hc; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK HOspan 29508.
  { intros a (rr & Hin & Hrng). cbn [ss_mem add_cond In] in Hin.
    destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hrng;
    rewrite ?B19, ?B22, ?B2 in Hrng; try lia;
    (apply (hoG_awr_mono (c_STK c) (c_sp0 c) (c_FP c) (ablocks B (c_ly c) (c_S c)) (ablocks B (c_lyc c) (c_Sc c))
      (ablocks B ly2 S2) (c_lyc c) ly2 (c_own c) (1, fpos) a); [exact (proj1 (Howr a ltac:(lia))) | exact HPERM | exact HFA]). }
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst (ms_regs ?m5) _ _ _; cfg_model := ?md5 |} _ =>
  lazymatch goal with
  | HFy : frame_of _ _ (mrestrict _ mem4) (mrestrict _ (ms_mem m5)),
    HGy : mem_grows (mrestrict _ mem4) (mrestrict _ (ms_mem m5)),
    HJ5 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem m5) _ _ |- _ =>
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (c_out c + 8 <= a < c_out c + 17 \/ c_out c + 20 <= a < c_out c + 24) ->
    aview SEGS (w_H W2) (ms_mem m5) a = aview SEGS (w_H W2) mem4 a);
  [ intros a Ha HnZ; apply (hoG_aview_fr _ _ _ _ _ a HFy Ha); intros (rr & Hin & Hrng); apply HnZ;
    cbn in Hin; destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hrng;
    rewrite ?B19, ?B22, ?B2 in Hrng; clear - Hrng; lia | ];
  assert (PRES : forall a, apresent (w_H W2) mem4 a -> apresent (w_H W2) (ms_mem m5) a)
    by (intros a Hp; eapply apresent_grows; [exact HGy | exact Hp]);
  assert (HRM5 : ho_regs_mid c (ms_regs m5) sp1 F) by (hoG_mid5 HS KR HRM);
  pose proof (hoG_base_frame c fpos ly2 S2 W2 mem4 md4 k2 H2 regs4 sp1 F (ms_mem m5) md5 (ms_regs m5)
    (fun a => c_out c + 8 <= a < c_out c + 17 \/ c_out c + 20 <= a < c_out c + 24) HB HJ5 MEQ PRES
    ltac:(intros a Hz; cbv beta in Hz; right; split; [exact Hout | clear - Hz; lia])
    ltac:(intros a Hz Ha; split; [exact (hoG_out_noimg c HPRE Hout a Ha)|];
          pose proof HDJ as Q; unfold hoG_box in Q; destruct Q as (_ & Q2 & _ & _ & Q5); split; clear - Q2 Q5 Ha; lia)
    HRM5) as HB5;
  assert (P8 : garr8 SEGS (mrestrict (w_H W2) (ms_mem m5)) (c_out c + 8)
     (map (fun b : byte => bv_unsigned b) (disco_table_c.sub H2 (48 * ii + 8) 4)));
  [ let X := fresh "X" in
    pose proof (hoG_piece (c_fq c) _ _ (w_H W2) m5 1 _ 8 4 (SExt true 32 (SOff 62 0)) (disco_table_c.sub H2 (48 * ii + 8) 4) HS eq_refl
      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)
      ltac:(apply HuntObsLib.len_sub; [lia | rewrite HL2; lia])
      ltac:(apply hoG_val4; [rewrite ?ew_ewset_other by lia; exact E62 | lia | rewrite HL2; lia])) as X;
    cbn [YP09.r_base base_val] in X; rewrite ?ew_ewset_other in X by lia; rewrite (AG1 19%nat ltac:(lia)), U19 in X; exact X | ];
  assert (P20 : garr8 SEGS (mrestrict (w_H W2) (ms_mem m5)) (c_out c + 20)
     (map (fun b : byte => bv_unsigned b) (disco_table_c.sub H2 (48 * ii + 20) 4)));
  [ let X := fresh "X" in
    pose proof (hoG_piece (c_fq c) _ _ (w_H W2) m5 0 _ 20 4 (SExt true 32 (SOff 68 0)) (disco_table_c.sub H2 (48 * ii + 20) 4) HS eq_refl
      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)
      ltac:(apply HuntObsLib.len_sub; [lia | rewrite HL2; lia])
      ltac:(apply hoG_val4; [rewrite ?ew_ewset_other by lia; exact E68 | lia | rewrite HL2; lia])) as X;
    cbn [YP09.r_base base_val] in X; rewrite ?ew_ewset_other in X by lia; rewrite (AG1 19%nat ltac:(lia)), U19 in X; exact X | ];
  assert (P12 : garr8 SEGS (mrestrict (w_H W2) (ms_mem m5)) (c_out c + 12)
     (map (fun b : byte => bv_unsigned b) (disco_table_c.sub H2 (48 * ii + 12) 1)));
  [ let X := fresh "X" in
    pose proof (hoG_piece (c_fq c) _ _ (w_H W2) m5 1 _ 12 1 (SOff 63 0) (disco_table_c.sub H2 (48 * ii + 12) 1) HS eq_refl
      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)
      ltac:(apply HuntObsLib.len_sub; [lia | rewrite HL2; lia])
      ltac:(apply hoG_val1; [rewrite ?ew_ewset_other by lia; exact E63 | lia | rewrite HL2; lia])) as X;
    cbn [YP09.r_base base_val] in X; rewrite ?ew_ewset_other in X by lia; rewrite (AG1 19%nat ltac:(lia)), U19 in X; exact X | ];
  assert (P13 : garr8 SEGS (mrestrict (w_H W2) (ms_mem m5)) (c_out c + 13)
     (map (fun b : byte => bv_unsigned b) (disco_table_c.sub H2 (48 * ii + 13) 1)));
  [ let X := fresh "X" in
    pose proof (hoG_piece (c_fq c) _ _ (w_H W2) m5 1 _ 13 1 (SOff 64 0) (disco_table_c.sub H2 (48 * ii + 13) 1) HS eq_refl
      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)
      ltac:(apply HuntObsLib.len_sub; [lia | rewrite HL2; lia])
      ltac:(apply hoG_val1; [rewrite ?ew_ewset_other by lia; exact E64 | lia | rewrite HL2; lia])) as X;
    cbn [YP09.r_base base_val] in X; rewrite ?ew_ewset_other in X by lia; rewrite (AG1 19%nat ltac:(lia)), U19 in X; exact X | ];
  assert (P14 : garr8 SEGS (mrestrict (w_H W2) (ms_mem m5)) (c_out c + 14)
     (map (fun b : byte => bv_unsigned b) (disco_table_c.sub H2 (48 * ii + 14) 1)));
  [ let X := fresh "X" in
    pose proof (hoG_piece (c_fq c) _ _ (w_H W2) m5 1 _ 14 1 (SOff 65 0) (disco_table_c.sub H2 (48 * ii + 14) 1) HS eq_refl
      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)
      ltac:(apply HuntObsLib.len_sub; [lia | rewrite HL2; lia])
      ltac:(apply hoG_val1; [rewrite ?ew_ewset_other by lia; exact E65 | lia | rewrite HL2; lia])) as X;
    cbn [YP09.r_base base_val] in X; rewrite ?ew_ewset_other in X by lia; rewrite (AG1 19%nat ltac:(lia)), U19 in X; exact X | ];
  assert (P15 : garr8 SEGS (mrestrict (w_H W2) (ms_mem m5)) (c_out c + 15)
     (map (fun b : byte => bv_unsigned b) (disco_table_c.sub H2 (48 * ii + 15) 1)));
  [ let X := fresh "X" in
    pose proof (hoG_piece (c_fq c) _ _ (w_H W2) m5 1 _ 15 1 (SOff 66 0) (disco_table_c.sub H2 (48 * ii + 15) 1) HS eq_refl
      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)
      ltac:(apply HuntObsLib.len_sub; [lia | rewrite HL2; lia])
      ltac:(apply hoG_val1; [rewrite ?ew_ewset_other by lia; exact E66 | lia | rewrite HL2; lia])) as X;
    cbn [YP09.r_base base_val] in X; rewrite ?ew_ewset_other in X by lia; rewrite (AG1 19%nat ltac:(lia)), U19 in X; exact X | ];
  assert (P16 : garr8 SEGS (mrestrict (w_H W2) (ms_mem m5)) (c_out c + 16)
     (map (fun b : byte => bv_unsigned b) (disco_table_c.sub H2 (48 * ii + 16) 1)));
  [ let X := fresh "X" in
    pose proof (hoG_piece (c_fq c) _ _ (w_H W2) m5 1 _ 16 1 (SOff 67 0) (disco_table_c.sub H2 (48 * ii + 16) 1) HS eq_refl
      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)
      ltac:(apply HuntObsLib.len_sub; [lia | rewrite HL2; lia])
      ltac:(apply hoG_val1; [rewrite ?ew_ewset_other by lia; exact E67 | lia | rewrite HL2; lia])) as X;
    cbn [YP09.r_base base_val] in X; rewrite ?ew_ewset_other in X by lia; rewrite (AG1 19%nat ltac:(lia)), U19 in X; exact X | ];
  assert (PG0 : garr8 SEGS (mrestrict (w_H W2) (ms_mem m5)) (c_out c) (map (fun b : byte => bv_unsigned b) (disco_table_c.sub G 0 8)));
  [ pose proof (hoG_garr8_subL _ _ G 0 8 GO ltac:(lia)) as X; cbn [Z.of_nat] in X; rewrite Z.add_0_r in X;
    apply (garr8_aview_kept SEGS (w_H W2) (w_H W2) mem4 (ms_mem m5)); [|exact X];
    rewrite length_map, (HuntObsLib.len_sub G 0 8) by (try rewrite LG; lia); intros a Ha; apply MEQ; clear - Ha KB; lia | ];
  assert (PG17 : garr8 SEGS (mrestrict (w_H W2) (ms_mem m5)) (c_out c + 17) (map (fun b : byte => bv_unsigned b) (disco_table_c.sub G 17 3)));
  [ pose proof (hoG_garr8_subL _ _ G 17 3 GO ltac:(lia)) as X; change (Z.of_nat 17) with 17 in X;
    apply (garr8_aview_kept SEGS (w_H W2) (w_H W2) mem4 (ms_mem m5)); [|exact X];
    rewrite length_map, (HuntObsLib.len_sub G 17 3) by (try rewrite LG; lia); intros a Ha; apply MEQ; clear - Ha KB; lia | ];
  assert (GE : garr8 SEGS (mrestrict (w_H W2) (ms_mem m5)) (c_out c)
     (map (fun b : byte => bv_unsigned b) (reac_hunt_observe_c.ho_entry T' G ii)));
  [ apply (hoG_entry_garr8 _ _ G T' ii LG LT ltac:(lia) PG0);
    [ rewrite <- (SUBT (48 * ii + 8) 4%nat) by lia; exact P8
    | rewrite <- (SUBT (48 * ii + 12) 1%nat) by lia; exact P12
    | rewrite <- (SUBT (48 * ii + 13) 1%nat) by lia; exact P13
    | rewrite <- (SUBT (48 * ii + 14) 1%nat) by lia; exact P14
    | rewrite <- (SUBT (48 * ii + 15) 1%nat) by lia; exact P15
    | rewrite <- (SUBT (48 * ii + 16) 1%nat) by lia; exact P16
    | exact PG17
    | rewrite <- (SUBT (48 * ii + 20) 4%nat) by lia; exact P20 ] | ];
  apply (HTs c fpos ly2 S2 W2 (ms_mem m5) md5 k2 (ms_regs m5) sp1 F H2 r HB5);
  [ let Q := fresh "Q" in prreg HS (20%bv : bv 5) Q; rewrite Q; exact E61
  | pose proof HrB as Q; unfold hoG_box in Q; clear - Q; lia
  | intros i Hi; rewrite MEQ; [exact (HFSH i Hi) | exact (HSF i Hi) |];
    pose proof HDJ as Q; unfold hoG_box in Q; destruct Q as (_ & _ & Q3 & _); clear - Q3 Hi KB; lia
  | exact HOK2
  | apply (tho_model_mono (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) r H2
      (fun A' => A' = reac_hunt_observe_c.ho_entry T' G ii));
    [ intros A ->; exact GE
    | apply HANS; exists ii; split;
      [ right; split; [rewrite <- Hnn; lia|]; split; [exact HM | exact HNM]
      | rewrite (proj2 (Z.ltb_ge ii 0)) by lia; reflexivity ] ] ]
  end end.
- rewrite branch_eq_U, U10, YI04.U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  assert (HM : disco_table_c.mac_of T' ii <> disco_table_c.s_mac G)
    by (intros X; apply Hc; apply XC in X; rewrite X; reflexivity).
  pose proof (st_ok_pi_submem _ _ _ [hoG_sp1R] HS ltac:(cbn [ss_mem add_cond]; submem_tac) eq_refl) as HSn.
  clear HS. rename HSn into HS. cbn [ss_pc ss_regs ss_resv ss_facts add_cond] in HS.
  paj_run_tok RUN HS HJ SHOK HOspan.
  { intros a (rr & Hin & Hrng). cbn [ss_mem In] in Hin.
    destruct Hin as [<- | []]; unfold hoG_sp1R in Hrng; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hrng; lia. }
  assert (EW27 : ew E1 27 = Z_to_bv 64 (48 * ii))
    by (rewrite AG1 by lia; rewrite (EV 27%nat 27%bv eq_refl); unfold regs4'; rewrite hoG_getr_upd_other by hoG_bvne; exact R27).
  assert (U60 : U E1 (SOff 60 0) = 48 * nn) by (apply U_atom; [exact E60 | lia]).
  assert (U27 : U E1 (SOff 27 48) = 48 * ii + 48) by (apply U_atom_off; [exact EW27 | lia | lia]).
  psrr_branch_tok RUN BR HS SHOK HOspan.
  + rewrite branch_ne_U, U60, U27 in Hc0. apply negb_true_iff, Z.eqb_neq in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK HOspan 29768.
    { intros a (rr & Hin & Hrng). cbn [ss_mem add_cond In] in Hin.
      destruct Hin as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hrng; lia. }
    clear U60 U27.
    pmkst HS.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst (ms_regs ?m5) _ _ _; cfg_model := ?md5 |} _ =>
    lazymatch goal with
    | HFy : frame_of _ _ (mrestrict _ mem4) (mrestrict _ (ms_mem ?m1)),
      HFx : frame_of _ _ (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem m5)),
      HGy : mem_grows (mrestrict _ mem4) (mrestrict _ (ms_mem ?m1)),
      HGx : mem_grows (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem m5)),
      HJ5 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem m5) _ _ |- _ =>
    assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview SEGS (w_H W2) (ms_mem m5) a = aview SEGS (w_H W2) mem4 a);
    [ intros a Ha _; rewrite (hoG_aview_fr _ _ _ _ _ a HFx Ha) by hoG_nowin;
      rewrite (hoG_aview_fr _ _ _ _ _ a HFy Ha) by hoG_nowin; reflexivity | ];
    assert (PRES : forall a, apresent (w_H W2) mem4 a -> apresent (w_H W2) (ms_mem m5) a)
      by (intros a Hp; eapply apresent_grows; [exact HGx|]; eapply apresent_grows; [exact HGy | exact Hp]);
    assert (HRM5 : ho_regs_mid c (ms_regs m5) sp1 F) by (hoG_mid5 HS KR HRM);
    pose proof (hoG_base_frame c fpos ly2 S2 W2 mem4 md4 k2 H2 regs4 sp1 F (ms_mem m5) md5 (ms_regs m5)
      (fun _ => False) HB HJ5 MEQ PRES (fun a f => False_ind _ f) (fun a f _ => False_ind _ f) HRM5) as HB5;
    assert (FSH5 : ho_fsh W2 (ms_mem m5) F ho_shC)
      by (intros i Hi; rewrite MEQ; [exact (HFSH i Hi) | exact (HSF i Hi) | tauto]);
    assert (GO5 : garr8 SEGS (mrestrict (w_H W2) (ms_mem m5)) (c_out c) (map (fun b : byte => bv_unsigned b) G))
      by (apply (garr8_aview_kept SEGS (w_H W2) (w_H W2) mem4 (ms_mem m5)); [|exact GO];
          rewrite length_map, LG; intros a Ha; apply MEQ; [clear - Ha KB; lia | tauto]);
    apply (IH ltac:(clear - Hc0 Hii; lia) (ms_regs m5) (ms_mem m5) md5);
    unfold hoG_pre;
    split; [exact HB5|];
    split; [let Q := fresh "Q" in prreg HS (19%bv : bv 5) Q; rewrite Q; exact E60|];
    split; [let Q := fresh "Q" in hoG_kr HS KR (20%bv : bv 5) 20%nat Q; rewrite Q; exact R20|];
    split; [let Q := fresh "Q" in hoG_kr HS KR (23%bv : bv 5) 23%nat Q; rewrite Q; exact R23|];
    split; [let Q := fresh "Q" in hoG_kr HS KR (26%bv : bv 5) 26%nat Q; rewrite Q; exact R26|];
    split; [let Q := fresh "Q" in prreg HS (27%bv : bv 5) Q; rewrite Q, EW27, unsigned_lit_small by lia; unfold w64; f_equal; lia|];
    split; [exact FSH5|]; split; [exact HOK2|]; split; [exact HT2|]; split; [exact LT|]; split; [exact Hnn|];
    split; [clear - Hc0 Hii; lia|]; split; [exact Hnn8|]; split; [exact HrB|];
    split; [apply (hoG_rdword_kept (aview SEGS (w_H W2) mem4)); [intros i Hi; apply MEQ; [clear - Hi KB; lia | tauto] | exact S8]|];
    split; [apply (hoG_rdword_kept (aview SEGS (w_H W2) mem4)); [intros i Hi; apply MEQ; [clear - Hi KB; lia | tauto] | exact S16]|];
    split; [apply (hoG_rdword_kept (aview SEGS (w_H W2) mem4)); [intros i Hi; apply MEQ; [clear - Hi KB; lia | tauto] | exact S24]|];
    split; [apply (garr8_aview_kept SEGS (w_H W2) (w_H W2) mem4 (ms_mem m5)); [|exact GG];
            rewrite length_map, LG; intros a Ha; apply MEQ; [clear - Ha KB; lia | tauto]|];
    split; [exact LG|]; split; [exact HGs|];
    split; [intros j Hj; destruct (Z.eq_dec j ii) as [->|Hne]; [exact HM | apply HNM; clear - Hj Hne; lia]|];
    split; [exact Hout|]; split; [exact GO5 | exact HANS]
    end end.
  + rewrite branch_ne_U, U60, U27 in Hc0. apply negb_false_iff, Z.eqb_eq in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK HOspan 29508.
    { intros a (rr & Hin & Hrng). cbn [ss_mem add_cond In] in Hin.
      destruct Hin as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hrng; lia. }
    pmkst HS.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst (ms_regs ?m5) _ _ _; cfg_model := ?md5 |} _ =>
    lazymatch goal with
    | HFy : frame_of _ _ (mrestrict _ mem4) (mrestrict _ (ms_mem ?m1)),
      HFx : frame_of _ _ (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem m5)),
      HGy : mem_grows (mrestrict _ mem4) (mrestrict _ (ms_mem ?m1)),
      HGx : mem_grows (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem m5)),
      HJ5 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem m5) _ _ |- _ =>
    assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview SEGS (w_H W2) (ms_mem m5) a = aview SEGS (w_H W2) mem4 a);
    [ intros a Ha _; rewrite (hoG_aview_fr _ _ _ _ _ a HFx Ha) by hoG_nowin;
      rewrite (hoG_aview_fr _ _ _ _ _ a HFy Ha) by hoG_nowin; reflexivity | ];
    assert (PRES : forall a, apresent (w_H W2) mem4 a -> apresent (w_H W2) (ms_mem m5) a)
      by (intros a Hp; eapply apresent_grows; [exact HGx|]; eapply apresent_grows; [exact HGy | exact Hp]);
    assert (HRM5 : ho_regs_mid c (ms_regs m5) sp1 F) by (hoG_mid5 HS KR HRM);
    pose proof (hoG_base_frame c fpos ly2 S2 W2 mem4 md4 k2 H2 regs4 sp1 F (ms_mem m5) md5 (ms_regs m5)
      (fun _ => False) HB HJ5 MEQ PRES (fun a f => False_ind _ f) (fun a f _ => False_ind _ f) HRM5) as HB5;
    assert (FSH5 : ho_fsh W2 (ms_mem m5) F ho_shC)
      by (intros i Hi; rewrite MEQ; [exact (HFSH i Hi) | exact (HSF i Hi) | tauto]);
    assert (GO5 : garr8 SEGS (mrestrict (w_H W2) (ms_mem m5)) (c_out c) (map (fun b : byte => bv_unsigned b) G))
      by (apply (garr8_aview_kept SEGS (w_H W2) (w_H W2) mem4 (ms_mem m5)); [|exact GO];
          rewrite length_map, LG; intros a Ha; apply MEQ; [clear - Ha KB; lia | tauto]);
    apply (HTs c fpos ly2 S2 W2 (ms_mem m5) md5 k2 (ms_regs m5) sp1 F H2 r HB5);
    [ let Q := fresh "Q" in prreg HS (20%bv : bv 5) Q; rewrite Q; exact E61
    | pose proof HrB as Q; unfold hoG_box in Q; clear - Q; lia
    | exact FSH5
    | exact HOK2
    | apply (tho_model_mono (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) r H2 (fun A' => A' = G));
      [ intros A ->; exact GO5
      | apply HANS; exists (-1); split;
        [ left; split; [reflexivity|]; intros j Hj; destruct (Z.eq_dec j ii) as [->|Hne];
          [exact HM | apply HNM; rewrite <- Hnn in Hj; clear - Hj Hne Hc0; lia]
        | reflexivity ] ] ]
    end end.
Qed.

Lemma hoG_loop : hoG_head_stmt -> hoG_ret_stmt ->
  forall (d : nat) (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G r nn ii,
  Z.of_nat d = nn - ii ->
  hoG_pre c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G r nn ii ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x7448) (ho_post c).
Proof.
intros HH HR d. induction d as [|d IH]; intros c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G r nn ii Hd HP.
- exfalso. pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hii & _). lia.
- apply (HH c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G r nn ii HP).
  intros regs4 mem4 md4 v HP4 Hv XC H22.
  apply (HR c fpos ly2 S2 W2 mem4 md4 k2 regs4 sp1 F H2 T' G r nn ii v HP4 Hv XC H22).
  intros Hlt regs5 mem5 md5 HP5.
  apply (IH c fpos ly2 S2 W2 mem5 md5 k2 regs5 sp1 F H2 T' G r nn (ii + 1)); [lia | exact HP5].
Qed.

Lemma ho_segG_of : hoG_head_stmt -> hoG_ret_stmt -> ho_seg_G_stmt.
Proof.
intros HH HR. unfold ho_seg_G_stmt.
intros c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G r nn ii HB R19 R20 R23 R26 R27 HFSH HOK HT2 LT Hnn Hii Hnn8 Hr
  S8 S16 S24 GG LG HGs HNM Hout GO HANS.
apply (hoG_loop HH HR (Z.to_nat (nn - ii)) c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G r nn ii); [lia|].
unfold hoG_pre. repeat (split; [assumption|]). assumption.
Qed.

Lemma ho_segG : ho_seg_G_stmt.
Proof. exact (ho_segG_of hoG_head (hoG_ret ho_segT)). Qed.

End h.
End f.
End d.

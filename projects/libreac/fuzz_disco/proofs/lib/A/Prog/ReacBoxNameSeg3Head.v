(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg7.v, with its module paths and numbers changed; 856 of its 971 lines of code are new or changed and 976 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
SbDec DiscoRo ReacBoxName ReacBoxNameCut ReacBoxNameSeg3Mid.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition R3H_B : Z := 0x218.
Definition r3h_Bx : sv := SOff 22 0.
Definition r3h_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition r3h_regl : list (bv 5) :=
  [(2%bv : bv 5); 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 13%bv; 14%bv; 15%bv; 16%bv; 18%bv; 19%bv; 22%bv; 23%bv; 24%bv;
   26%bv; 27%bv].
Definition r3h_same (regs1 regs2 : bvmap 5 word) : Prop :=
  forall r, In r r3h_regl -> getr regs2 r = getr regs1 r.
Ltac r3in := cbn [In r3h_regl]; repeat (first [left; reflexivity | right]).
Lemma r3h_globs : forall q sz, In (q, sz) disco_globs -> 0x20f80 <= q /\ q + sz <= 0xa0358 /\ q mod 8 = 0 /\ 0 < sz.
Proof.
intros q sz H.
assert (A : forallb (fun p => (0x20f80 <=? fst p) && (fst p + snd p <=? 0xa0358) && (fst p mod 8 =? 0) && (0 <? snd p))
  disco_globs = true) by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A (q, sz) H). cbn [fst snd] in A.
apply andb_true_iff in A as [A A4]. apply andb_true_iff in A as [A A3]. apply andb_true_iff in A as [A1 A2].
apply Z.leb_le in A1, A2. apply Z.eqb_eq in A3. apply Z.ltb_lt in A4. lia.
Qed.
Lemma r3h_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma r3h_sh_band : forall x n j, 4096 <= x -> 0 <= n -> x + n <= alloc_ceiling -> 0 <= j < n / 8 ->
  kLowShadowBeg <= shadow_addr x + j < kHighMemBeg.
Proof.
intros x n j H1 H2 H3 H4.
pose proof (shadow_range_end x n H2) as E1.
pose proof (shadow_mono (x + n) alloc_ceiling H3) as E2.
pose proof (shadow_mono 4096 x H1) as E3.
pose proof asan_consts as (C1 & _).
assert (E4 : alloc_ceiling / 8 <= 0xfffffff0000) by (apply Z.div_le_upper_bound; lia).
assert (E5 : shadow_addr 4096 = SHADOW_OFF + 512) by reflexivity.
assert (E6 : shadow_addr alloc_ceiling = SHADOW_OFF + alloc_ceiling / 8) by reflexivity.
unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma r3h_ok_rng : forall X, rbm_args X -> 0 <= ri_i X <= 40 /\ 0 <= ri_o X <= 40.
Proof.
intros X HA. unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [_ Hi].
apply bn_ok_in in Hi. apply bn_ok_in in Ho.
assert (Hb : forall x, In x bn_oks -> 0 <= x <= 40)
  by (intros x Hx; vm_compute in Hx; repeat (destruct Hx as [<- | Hx]; [lia|]); destruct Hx).
split; [exact (Hb _ Hi) | exact (Hb _ Ho)].
Qed.
Lemma r3h_kept : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' P HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma r3h_roimg : forall q sz x, In (q, sz) disco_ro_ranges -> q <= x < q + sz -> in_img SEGS x.
Proof.
intros q sz x Hin Hx.
assert (Hin' : In (q, sz) disco_ro_all) by (unfold disco_ro_all; apply in_or_app; left; exact Hin).
destruct (disco_ro_in_ro (PI := PI) q sz x Hin' Hx) as [(sg & Hsg & _ & Hr) | Hr];
  [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img x Hr)].
Qed.
Lemma r3h_cfg : forall X off regs mem md q, q = BASE + AF_reac_box_name + off ->
  rbn_cfg X off regs mem md = mkCfg (mkst (fx := ri_fq X) regs (Z_to_bv 64 q) mem (seg_rom SEGS)) md.
Proof. intros X off regs mem md q ->. reflexivity. Qed.
Definition r3h_rT : YP09.region := YP09.mkRegion (Some (A_OBJ 26)) 0 24 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0))].
Definition r3h_fB : facts := mkFacts [ (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (A_OBJ 26, mkAF IMG_LO IMG_TOP 3) ] [] [].
Definition r3h_ssB : sstate := mkSS (AF_reac_box_name + R3H_B) sr_atoms [r3h_rT] None r3h_fB.
Definition r3h_SHB : list shent := [ mkSHE (A_OBJ 26) 0 24 ].
Definition r3h_EB (regs : bvmap 5 word) (t1 t2 t3 : Z) : env :=
  Eimg (Ereg regs [Z_to_bv 64 t1; Z_to_bv 64 t2; Z_to_bv 64 t3]).
Lemma r3h_eB : forall (fq : YK11.FPState) (regs : bvmap 5 word) (W : world SEGS) memc t1 t2 t3,
  getr regs 22 = w64 SHADOW_OFF -> 0 <= t1 < 2 ^ 64 -> 0 <= t2 < 2 ^ 64 -> 0 <= t3 < 2 ^ 64 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (VAL (A_OBJ 26)) 24 ->
  val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 26)) 8 t1 ->
  val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 26) + 8) 8 t2 ->
  val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 26) + 16) 8 t3 ->
  st_ok_pi SEGS VAL (r3h_EB regs t1 t2 t3) r3h_ssB
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + R3H_B))) memc (seg_rom SEGS)))
  /\ sh_ok SEGS r3h_Bx r3h_SHB (r3h_EB regs t1 t2 t3) (mrestrict (w_H W) memc).
Proof.
intros fq regs W memc t1 t2 t3 R22 Ht1 Ht2 Ht3 HRA M0 M1 M2.
pose proof (pa_obj_val 26 ltac:(vm_compute; lia)) as V26. change (disco_obj 26) with 0xa0300 in V26.
rewrite restrict_mkst_fx.
set (E := r3h_EB regs t1 t2 t3).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 t1; Z_to_bv 64 t2; Z_to_bv 64 t3]) n)
  by (intros n Hn; subst E; unfold r3h_EB; apply Eimg_low; exact Hn).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22).
assert (E32 : ew E 32 = Z_to_bv 64 t1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 t2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 t3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Etab : ew E (A_OBJ 26) = Z_to_bv 64 (VAL (A_OBJ 26)))
  by (subst E; unfold r3h_EB; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w)
  by (intros n w Hn Hw; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hw).
assert (HRO : regs_ok E sr_atoms regs) by (unfold E, r3h_EB; apply regs_ok_Eimg_Ereg).
rewrite V26 in HRA, M0, M1, M2, Etab. clearbody E.
split.
- unfold r3h_ssB. apply pa_entry_st_ok_full.
  + exact HRO.
  + vm_compute. reflexivity.
  + unfold r3h_rT. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB (A_OBJ 26) 0xa0300 Etab) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (chunk_ok_val SEGS E _ 0xa0300 0 8 (SOff 32 0) t1);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact M0.
    * apply (chunk_ok_val SEGS E _ 0xa0300 8 8 (SOff 33 0) t2);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M1].
    * apply (chunk_ok_val SEGS E _ 0xa0300 16 8 (SOff 34 0) t3);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M2].
  + cbn [pairwise_disjoint all_disjoint]. split; exact I.
  + split; [|split; exact I].
    cbn [r3h_fB f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E22, Etab, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF, IMG_LO, IMG_TOP. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- unfold sh_ok, r3h_SHB. apply Forall_cons; [|apply Forall_nil].
  eapply shent_ok_of_range.
  + exact HRA.
  + unfold U, r3h_Bx. cbn [sv_denot]. rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite Etab, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.
Lemma r3h_bad : forall E v, ew E 25 = Z_to_bv 64 v -> -2 ^ 31 <= v < 2 ^ 31 ->
  branch_taken BC_LTU (sv_denot E (SLit 2)) (sv_denot E (SAluw ALU_ADD (SOff 25 0) (SLit (-1)))) = false ->
  v = 1 \/ v = 2 \/ v = 3.
Proof.
intros E v H25 Hv Hc. rewrite branch_ltu_U in Hc. apply Z.ltb_ge in Hc.
rewrite (U_of_S E (SAluw ALU_ADD (SOff 25 0) (SLit (-1)))), S_SAluw, !U_SLit, U_SOff, H25 in Hc. cbn [zalu_raw] in Hc.
rewrite Z_to_bv_unsigned in Hc.
assert (W64 : forall z, bv_wrap 64 z = z mod 18446744073709551616) by (intros z; reflexivity).
assert (S32 : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648) by (intros z; reflexivity).
rewrite !W64, S32 in Hc. unfold zcanon, M64 in Hc.
change (2 ^ 64) with 18446744073709551616 in Hc. change (2 ^ 32) with 4294967296 in Hc.
change (2 ^ 31) with 2147483648 in Hv.
Z.div_mod_to_equations. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Lemma r3h_fa : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM c p.
destruct HX as ((_ & L0 & _) & _). destruct HM as ((_ & L1 & _) & _).
destruct L0 as (_ & _ & _ & _ & _ & F0 & _). destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F0, F1. reflexivity.
Qed.
Lemma r3h_A_rng : forall X, rbn_cx B X ->
  alloc_ceiling + 8784 <= rbn_SP X /\ rbn_SP X - 319 <= rbn_A X /\ rbn_A X + 288 <= rbn_SP X /\
  rbn_SP X + 16 <= 2 ^ 47 /\ ri_sp0 X - ri_STK X <= rbn_SP X - 8784 /\ rbn_SP X + 16 <= ri_sp0 X /\
  rbn_A X mod 32 = 0 /\ ri_sp0 X mod 16 = 0.
Proof.
intros X HX. destruct HX as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (H16 & _ & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
unfold rbn_A, rbn_SP.
pose proof (Z.div_mod (spZ (ri_regs X) - 288) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 288) 32 ltac:(lia)) as M1.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact H16].
rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.
Lemma r3h_F_facts : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh m md,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh -> AR SEGS B lyc1 Sc1 W1 m md ->
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 32 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) m a /\ ~ in_img SEGS a) /\
  (forall i, 0 <= i < 64 -> apresent (w_H W1) m (rbn_SH X pos + i)).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh m md HX HM HAR.
pose proof (r3h_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM 3 pos) as FA.
destruct HM as (_ & Hfrs & _).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR Hin3) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR Hin3) as (Hal & Happ & Hpr & Hspr).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
unfold rbn_SH, rbn_F. rewrite <- FA. rewrite Hfb3 in *.
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact Hal|]. split; [exact Happ|]. split.
- intros a Ha. split; [exact (proj1 (Hpr a Ha))|].
  refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR _)). right; left. exists 3, pos.
  split; [exact Hin3|]. rewrite Hfb3. exact Ha.
- intros i Hi. exact (proj1 (Hspr i ltac:(change (512 / 8) with 64; lia))).
Qed.
Lemma r3h_mid : forall X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2 sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 mem2 md2 (ri_k X) ->
  Z.of_nat (length sh) <= 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 8 <= a < rbn_A X + 184) ->
     aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  rbn_mid B X pos lyc1 Sc1 W1 mem2 md2 (fun _ => False) sh.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2 sh HX HM HJ2 Hsh HN.
pose proof (r3h_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as FA.
pose proof HM as (HJ1 & Hfrs & Hperm & Hro & HK & Hfr & Hfl & Hsh0).
pose proof (proj1 HJ1) as HAR1.
destruct (r3h_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ memc1 mdc1 HX HM HAR1) as (HF4096 & HFceil & _).
destruct (r3h_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
assert (HLO : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a)
  by (intros a Ha; apply HN; lia).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
split; [exact HJ2|]. split; [exact Hfrs|]. split; [exact Hperm|].
split.
{ intros a Hro0 Ho He.
  assert (Hia : in_img SEGS a)
    by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
  pose proof (pa_segs_low a Hia) as Hlow.
  rewrite (HLO a) by lia. exact (Hro a Hro0 Ho He). }
split.
{ destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn' He. rewrite (HN a) by (unfold rbn_SP in *; lia). exact (K1 a Ha Hn' He).
  - intros b m j Hb Hj He.
    assert (Hb1 : In (b, m) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hb).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR1 Hb1) as (_ & Hb4 & Hbc & _).
    rewrite (HLO (b + j)) by lia. exact (K2 b m j Hb Hj He).
  - intros a Hia Ho He. pose proof (pa_segs_low a Hia) as Hlow.
    rewrite (HLO a) by lia. exact (K3 a Hia Ho He).
  - intros cid p a Hcp Ha He.
    assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite Hfrs; right; exact Hcp).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp1) as (Hc4096 & Hcceil & _).
    rewrite FA in Hc4096, Hcceil.
    pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
    destruct Ha as [Ha | Ha].
    + unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha.
      rewrite (HLO a) by lia. exact (K4 cid p a Hcp (or_introl Ha) He).
    + unfold in_zr in Ha. cbn [fst snd] in Ha.
      pose proof (r3h_sh_band (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid)
        (a - shadow_addr (frame_addr (ri_lyc X) cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
      rewrite (HLO a) by (unfold kLowShadowBeg in Hb; lia). exact (K4 cid p a Hcp (or_intror Ha) He).
  - intros a Ha Hn' Hp.
    apply (apresent_transfer SEGS (w_H W1) (w_H W1) memc1 mem2 a);
      [lia | | apply HN; unfold rbn_SP in *; lia | exact (K5 a Ha Hn' Hp)].
    intros Hi. pose proof (pa_segs_low a Hi). lia.
  - intros a Ha. apply Hpres2. unfold rbn_SP in *. lia. }
split.
{ unfold rbn_frame. intros j r Hj.
  assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length rbn_saved_regs) with 13%nat in Hj13.
  apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact (Hfr j r Hj)].
  intros k Hk. apply HN; unfold rbn_SP in *; lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact Hfl].
  intros k Hk. apply HLO. lia. }
unfold rbn_shadow_at. intros j Hj.
pose proof (r3h_sh_band (rbn_F X pos) 512 j HF4096 ltac:(lia) HFceil ltac:(change (512 / 8) with 64; lia)) as Hb.
change (shadow_addr (rbn_F X pos)) with (rbn_SH X pos) in Hb.
rewrite (HLO (rbn_SH X pos + j)) by (unfold kLowShadowBeg in Hb; lia). exact (Hsh0 j Hj).
Qed.
Lemma r3h_kro : forall X pos lyc1 Sc1 W1 m1 md1 sh q sz x,
  rbn_mid B X pos lyc1 Sc1 W1 m1 md1 (fun _ => False) sh -> In (q, sz) disco_ro_ranges -> q <= x < q + sz ->
  aview SEGS (w_H W1) m1 x = aview SEGS (w_H (ri_W X)) (ri_memc X) x.
Proof.
intros X pos lyc1 Sc1 W1 m1 md1 sh q sz x HM Hin Hx.
pose proof HM as (_ & _ & _ & _ & (_ & _ & K3 & _) & _).
destruct (disco_ro_unowned_at B q sz DRO Hin x Hx) as [U1 U2].
exact (K3 x (r3h_roimg q sz x Hin Hx) U1 U2).
Qed.
Lemma r3h_str_img : forall X pos lyc1 Sc1 W1 m1 md1 sh q sz a s,
  rbn_mid B X pos lyc1 Sc1 W1 m1 md1 (fun _ => False) sh ->
  rbn_ro q sz -> q <= a -> a + Z.of_nat (length s) + 1 <= q + sz ->
  rbn_str (ri_W X) (ri_memc X) a s -> rbn_str W1 m1 a s.
Proof.
intros X pos lyc1 Sc1 W1 m1 md1 sh q sz a s HM (Hq & Htl) Hqa Haq (Hf & Hg & Ha0 & Ha1 & Hl & Ham & Hra & Hhv & Htr).
pose proof HM as (HJ1 & _).
pose proof (proj1 HJ1) as HAR1.
destruct (r3h_globs q sz Hq) as (G1 & G2 & G3 & G4).
assert (Hqr : In (q, sz) disco_ro_ranges) by (unfold disco_ro_ranges; apply in_or_app; left; exact Hq).
split; [exact Hf|]. split.
{ apply (garr8_frame SEGS (mrestrict (w_H (ri_W X)) (ri_memc X))); [exact Hg|].
  intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
  apply (mbyte_of_aview SEGS). apply (r3h_kro X pos lyc1 Sc1 W1 m1 md1 sh q sz x HM Hqr). lia. }
split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Hl|]. split; [exact Ham|]. split.
{ eapply ro_usable_glob; [exact GM | exact Hq | exact HAR1 | lia | lia]. }
split.
{ eapply ro_hull; [exact HV | exact HAR1 | lia | unfold IMG_LO; lia | unfold IMG_TOP; lia]. }
intros x Hx.
set (L := a + Z.of_nat (length s)) in *.
pose proof (Z.div_mod L 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as M1.
pose proof (Z.div_mod sz 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as M2.
pose proof (Z.div_mod q 8 ltac:(lia)) as D3. rewrite G3, Z.add_0_r in D3.
assert (Hx' : x < q + sz \/ (sz mod 8 <> 0 /\ q + sz <= x < q + sz + (8 - sz mod 8))).
{ destruct (Z.eq_dec (sz mod 8) 0) as [Z0 | Z0]; [left | ].
  - assert (L / 8 < q / 8 + sz / 8) by lia. lia.
  - destruct (Z_lt_le_dec x (q + sz)) as [Hlt | Hge]; [left; exact Hlt | right].
    assert (L / 8 <= q / 8 + sz / 8) by lia. lia. }
destruct Hx' as [Hx' | (Hz & Hx')].
- intros Hnone. apply (Htr x Hx).
  rewrite <- (r3h_kro X pos lyc1 Sc1 W1 m1 md1 sh q sz x HM Hqr ltac:(lia)). exact Hnone.
- destruct Htl as [Htl | Htl]; [exfalso; exact (Hz Htl)|].
  assert (Htl' : In (q + sz, 8 - sz mod 8) disco_ro_all)
    by (unfold disco_ro_all; apply in_or_app; right; exact Htl).
  exact (disco_ro_view (w_H W1) m1 (q + sz) (8 - sz mod 8) x Htl' ltac:(lia)).
Qed.
Definition r3h_sok (X : rbn_in) (pos a : Z) (s : list Z) : Prop :=
  forall lyc1 Sc1 (W1 : world SEGS) m1 md1 sh, rbn_mid B X pos lyc1 Sc1 W1 m1 md1 (fun _ => False) sh ->
    rbn_str W1 m1 a s /\
    (forall x, a <= x < a + Z.of_nat (length s) + 1 ->
       ~ (rbn_SP X - REAC_BOX_NAME_STK <= x < rbn_SP X) /\ ~ (rbn_F X pos <= x < rbn_F X pos + 512)).
Lemma r3h_sok_ro : forall X pos q sz a s,
  rbn_cx B X -> rbn_ro q sz -> q <= a -> a + Z.of_nat (length s) + 1 <= q + sz ->
  rbn_str (ri_W X) (ri_memc X) a s -> 4096 <= a /\ r3h_sok X pos a s.
Proof.
intros X pos q sz a s HX Hro Hqa Haq Hs.
destruct (r3h_globs q sz (proj1 Hro)) as (G1 & _).
split; [lia|].
intros lyc1 Sc1 W1 m1 md1 sh HM.
split; [exact (r3h_str_img X pos lyc1 Sc1 W1 m1 md1 sh q sz a s HM Hro Hqa Haq Hs)|].
intros x Hx.
destruct Hro as (Hq & _).
assert (Hqr : In (q, sz) disco_ro_ranges) by (unfold disco_ro_ranges; apply in_or_app; left; exact Hq).
pose proof (r3h_roimg q sz x Hqr ltac:(lia)) as Hix.
pose proof (pa_segs_low x Hix) as Hlow.
destruct (r3h_A_rng X HX) as (AR1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (r3h_F_facts X pos lyc1 Sc1 W1 m1 md1 _ _ m1 md1 HX HM (proj1 (proj1 HM))) as (_ & _ & _ & _ & HFpr & _).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
split; [lia|]. intros Hf. exact (proj2 (HFpr x Hf) Hix).
Qed.
Lemma r3h_pk_img : forall X pos q sz a,
  rbn_cx B X -> rbn_ro q sz -> q <= a -> a + Z.of_nat (length (rbm_stem X)) + 1 <= q + sz ->
  rbn_str (ri_W X) (ri_memc X) a (rbm_stem X) -> rbn3_pk B X pos a.
Proof.
intros X pos q sz a HX Hro Hqa Haq Hs lyc1 Sc1 W1 m1 md1 sh HM.
exact (proj2 (r3h_sok_ro X pos q sz a _ HX Hro Hqa Haq Hs) lyc1 Sc1 W1 m1 md1 sh HM).
Qed.
Lemma r3h_fin : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 mem2 md2 P,
  rbn_cx B X -> rbn_st3 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 mem2 md2 (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 80 <= a < rbn_A X + 96) ->
     aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  val_mem SEGS (mrestrict (w_H W1) mem2) (rbn_A X + 80) 8 (ri_i X) ->
  val_mem SEGS (mrestrict (w_H W1) mem2) (rbn_A X + 88) 8 (ri_o X) ->
  r3h_same regs1 regs2 -> getr regs2 20 = w64 P ->
  4096 <= P -> P <= 2 ^ 47 - 2 -> rbn3_pk B X pos P ->
  rbn3_mid B X W1 (rbn_cfg X RBN_T3 regs2 mem2 md2).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 mem2 md2 P HX H3 HJ2 HN M80 M88 HSm R20 HP0 HP1 HPK.
destruct H3 as (HM & (B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R26 & _ & R23 & R24 & _ & R27 & R12 & R13 &
  R14 & R15 & R16 & HA).
destruct (r3h_ok_rng X HA) as (Ri & Ro).
exists pos, P, regs2, lyc1, Sc1, mem2, md2.
split; [reflexivity|].
split.
{ apply (r3h_mid X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2 _ HX HM HJ2); [rewrite r3h_sh_len; lia|].
  intros a Ha Hn. apply HN; [exact Ha | lia]. }
split.
{ unfold rbn3_regs.
  repeat split;
    first [ exact R20
          | lazymatch goal with |- getr regs2 ?r = _ => rewrite (HSm r ltac:(r3in)); assumption end ]. }
split; [exact HP0|]. split; [exact HP1|]. split; [lia|]. split; [lia|].
split; [exact M80|]. split; [exact M88|]. split; [exact HPK | exact HA].
Qed.
Ltac r3h_awr :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac r3h_kr HFr Kr :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (Kr : forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m2 a = aview SEGS H m1 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    apply (r3h_kept _ _ _ _ _ (fun _ => False) HFr); [ | exact Ha | tauto];
    let a' := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hw := fresh "Hw" in
    intros a' (r & Hin & Hw);
    lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; lia|]); destruct Hin
  | ] end.
Ltac r3h_post HS :=
  apply SRr_ret; pmkst HS;
  lazymatch goal with |- rbn3_mid _ ?X _ (mkCfg (mkst (ms_regs ?m) (Z_to_bv 64 ?q) (ms_mem ?m) _) ?md) =>
    rewrite <- (r3h_cfg X RBN_T3 (ms_regs m) (ms_mem m) md q ltac:(unfold AF_reac_box_name, RBN_T3; lia)) end.
Ltac r3h_toB HS X :=
  pmkst HS;
  lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?m) (Z_to_bv 64 ?q) (ms_mem ?m) _) ?md) _ =>
    rewrite <- (r3h_cfg X R3H_B (ms_regs m) (ms_mem m) md q ltac:(unfold AF_reac_box_name, R3H_B; lia)) end.
Ltac r3h_krA HFr Kr P U9 :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (Kr : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m2 a = aview SEGS H m1 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn;
    apply (r3h_kept _ _ _ _ _ P HFr); [ | exact Ha | exact Hn];
    let a' := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hw := fresh "Hw" in
    intros a' (r & Hin & Hw); cbv beta;
    lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; cbn [extK ewset ew Nat.eqb] in Hw;
       rewrite ?U9 in Hw; lia|]);
    destruct Hin
  | ] end.
Ltac r3h_same_tac HS EE HSm :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In r3h_regl] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr _ ?r0 = getr ?regs1 _ =>
        let R := fresh "R" in prreg HS r0 R; rewrite R;
        lazymatch type of EE with forall n r, _ -> ew _ n = getr ?regs2 r =>
          transitivity (getr regs2 r0); [apply EE; reflexivity | apply HSm; r3in] end end
    | ]);
  destruct Hr.
Lemma r3h_B : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 mem2 md2,
  rbn_cx B X -> rbn_st3 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 -> ri_sd X = [] ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 mem2 md2 (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 80 <= a < rbn_A X + 96) ->
     aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  val_mem SEGS (mrestrict (w_H W1) mem2) (rbn_A X + 80) 8 (ri_i X) ->
  val_mem SEGS (mrestrict (w_H W1) mem2) (rbn_A X + 88) 8 (ri_o X) ->
  r3h_same regs1 regs2 -> getr regs2 25 = w64 (ri_f X) ->
  SRr SEGS W1 (rbn_cfg X R3H_B regs2 mem2 md2) (rbn3_mid B X).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 mem2 md2 HX H3 Hsd HJ2 HN M80 M88 HSm R25.
pose proof H3 as (HM & (B2 & B3 & B4 & B8 & B9 & B19 & B22) & _).
pose proof HX as (HJ0 & Hrod0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Himg & _).
destruct Himg as (t1 & t2 & t3 & _ & _ & _ & MT1 & MT2 & MT3 & S1 & S2 & S3 & S0 & _ & _ & _ & RT & R1 & R2 & R3 & R0 & _).
pose proof (pa_obj_val 26 ltac:(vm_compute; lia)) as V26. change (disco_obj 26) with 0xa0300 in V26.
pose proof (pa_obj_val 27 ltac:(vm_compute; lia)) as V27. change (disco_obj 27) with 0x21220 in V27.
rewrite V26 in MT1, MT2, MT3, RT. rewrite V27 in S0, R0.
destruct (r3h_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct RT as (RTg & _).
assert (RTr : In (0xa0300, 24) disco_ro_ranges) by (unfold disco_ro_ranges; apply in_or_app; left; exact RTg).
assert (KT : forall x, 0xa0300 <= x < 0xa0300 + 24 ->
  aview SEGS (w_H W1) mem2 x = aview SEGS (w_H (ri_W X)) (ri_memc X) x).
{ intros x Hx. pose proof (pa_segs_low x (r3h_roimg _ _ x RTr Hx)) as Hl.
  rewrite (HN x) by lia. exact (r3h_kro X pos lyc1 Sc1 W1 memc1 mdc1 _ _ _ x HM RTr Hx). }
assert (MT1' : val_mem SEGS (mrestrict (w_H W1) mem2) 0xa0300 8 t1)
  by (apply (val_mem_kept SEGS (w_H (ri_W X)) (w_H W1) (ri_memc X) mem2); [intros k Hk; apply KT; lia | exact MT1]).
assert (MT2' : val_mem SEGS (mrestrict (w_H W1) mem2) (0xa0300 + 8) 8 t2)
  by (apply (val_mem_kept SEGS (w_H (ri_W X)) (w_H W1) (ri_memc X) mem2); [intros k Hk; apply KT; lia | exact MT2]).
assert (MT3' : val_mem SEGS (mrestrict (w_H W1) mem2) (0xa0300 + 16) 8 t3)
  by (apply (val_mem_kept SEGS (w_H (ri_W X)) (w_H W1) (ri_memc X) mem2); [intros k Hk; apply KT; lia | exact MT3]).
assert (HRA2 : range_addressable (aview SEGS (w_H W1) mem2) SHADOW_OFF 0xa0300 24)
  by (eapply ro_usable_glob; [exact GM | exact RTg | exact (proj1 HJ2) | lia | lia]).
destruct (r3h_globs _ _ (proj1 R1)) as (T1a & T1b & _).
destruct (r3h_globs _ _ (proj1 R2)) as (T2a & T2b & _).
destruct (r3h_globs _ _ (proj1 R3)) as (T3a & T3b & _).
assert (R22 : getr regs2 22 = w64 SHADOW_OFF) by (rewrite (HSm 22%bv ltac:(r3in)); exact B22).
destruct (r3h_eB (ri_fq X) regs2 W1 mem2 t1 t2 t3 R22 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(rewrite V26; exact HRA2) ltac:(rewrite V26; exact MT1') ltac:(rewrite V26; exact MT2')
  ltac:(rewrite V26; exact MT3')) as [HS0 SHOK].
set (E := r3h_EB regs2 t1 t2 t3) in HS0, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold r3h_EB; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; subst E; unfold r3h_EB; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j [Z_to_bv 64 t1; Z_to_bv 64 t2; Z_to_bv 64 t3] (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold r3h_EB; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth] in E32, E33, E34. clear EX.
assert (E25 : ew E 25 = Z_to_bv 64 (ri_f X)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E27 : ew E (A_OBJ 27) = Z_to_bv 64 0x21220)
  by (subst E; unfold r3h_EB; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V27; reflexivity).
clearbody E.
pose proof (paj_run_to (fx := ri_fq X) B LAWS) as RUNTO.
pose proof (paj_branch (fx := ri_fq X) (L := disco_listing) (PI := PI)) as BR.
assert (NE25 : (25%bv : bv 5) <> 0%bv) by (intro Z; apply (f_equal bv_unsigned) in Z; vm_compute in Z; discriminate Z).
unfold rbn_cfg, cfg_at. change (w64 (BASE + AF_reac_box_name + R3H_B)) with (Z_to_bv 64 (BASE + AF_reac_box_name + R3H_B)).
rewrite <- Z.add_assoc.
assert (Hcase : ri_f X = 1 \/ ri_f X = 2 \/ ri_f X = 3 \/ (ri_f X <> 1 /\ ri_f X <> 2 /\ ri_f X <> 3)) by lia.
destruct Hcase as [Hf1 | [Hf2 | [Hf3 | (N1 & N2 & N3)]]].
- rewrite Hf1 in R25.
  pose proof (st_ok_pi_set_reg (fx := ri_fq X) E r3h_ssB _ (25%bv : bv 5) (SLit 1) HS0 NE25 R25) as HS. clear HS0.
  paj_run_to_tok RUNTO HS HJ2 SHOK r3h_span (AF_reac_box_name + RBN_T3). { r3h_awr. }
  r3h_kr HFr Kr. r3h_post HS.
  assert (HST : rbm_stem X = bn_STEM 1) by (unfold rbm_stem; rewrite Hsd, Hf1; reflexivity).
  apply (r3h_fin X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ _ _ t1 HX H3 HJ2).
  + intros a Ha Hn. rewrite (Kr a Ha). exact (HN a Ha Hn).
  + apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem2 _); [intros k Hk; apply Kr; lia | exact M80].
  + apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem2 _); [intros k Hk; apply Kr; lia | exact M88].
  + r3h_same_tac HS EE HSm.
  + let R := fresh "R" in prreg HS (20%bv : bv 5) R; rewrite R; exact E32.
  + lia.
  + lia.
  + apply (r3h_pk_img X pos t1 7 t1 HX R1); [lia | rewrite HST; cbn; lia | rewrite HST; exact (proj1 S1)].
- rewrite Hf2 in R25.
  pose proof (st_ok_pi_set_reg (fx := ri_fq X) E r3h_ssB _ (25%bv : bv 5) (SLit 2) HS0 NE25 R25) as HS. clear HS0.
  paj_run_to_tok RUNTO HS HJ2 SHOK r3h_span (AF_reac_box_name + RBN_T3). { r3h_awr. }
  r3h_kr HFr Kr. r3h_post HS.
  assert (HST : rbm_stem X = bn_STEM 2) by (unfold rbm_stem; rewrite Hsd, Hf2; reflexivity).
  apply (r3h_fin X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ _ _ t2 HX H3 HJ2).
  + intros a Ha Hn. rewrite (Kr a Ha). exact (HN a Ha Hn).
  + apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem2 _); [intros k Hk; apply Kr; lia | exact M80].
  + apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem2 _); [intros k Hk; apply Kr; lia | exact M88].
  + r3h_same_tac HS EE HSm.
  + let R := fresh "R" in prreg HS (20%bv : bv 5) R; rewrite R; exact E33.
  + lia.
  + lia.
  + apply (r3h_pk_img X pos t2 7 t2 HX R2); [lia | rewrite HST; cbn; lia | rewrite HST; exact (proj1 S2)].
- rewrite Hf3 in R25.
  pose proof (st_ok_pi_set_reg (fx := ri_fq X) E r3h_ssB _ (25%bv : bv 5) (SLit 3) HS0 NE25 R25) as HS. clear HS0.
  paj_run_to_tok RUNTO HS HJ2 SHOK r3h_span (AF_reac_box_name + RBN_T3). { r3h_awr. }
  r3h_kr HFr Kr. r3h_post HS.
  assert (HST : rbm_stem X = bn_STEM 3) by (unfold rbm_stem; rewrite Hsd, Hf3; reflexivity).
  apply (r3h_fin X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ _ _ t3 HX H3 HJ2).
  + intros a Ha Hn. rewrite (Kr a Ha). exact (HN a Ha Hn).
  + apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem2 _); [intros k Hk; apply Kr; lia | exact M80].
  + apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem2 _); [intros k Hk; apply Kr; lia | exact M88].
  + r3h_same_tac HS EE HSm.
  + let R := fresh "R" in prreg HS (20%bv : bv 5) R; rewrite R; exact E34.
  + lia.
  + lia.
  + apply (r3h_pk_img X pos t3 8 t3 HX R3); [lia | rewrite HST; cbn; lia | rewrite HST; exact (proj1 S3)].
- paj_run_to_tok RUNTO HS0 HJ2 SHOK r3h_span (AF_reac_box_name + RBN_T3). { r3h_awr. }
  r3h_kr HFr Kr1. clear HF HFr HG.
  psrr_branch_tok RUNTO BR HS0 SHOK r3h_span.
  + paj_run_to_tok RUNTO HS0 HJ2 SHOK r3h_span (AF_reac_box_name + RBN_T3). { r3h_awr. }
    r3h_kr HFr Kr2. r3h_post HS0.
    assert (HST : rbm_stem X = bn_STEM 0).
    { unfold rbm_stem, bn_stem. rewrite Hsd. unfold bn_STEM.
      rewrite (proj2 (Z.eqb_neq _ 1) N1), (proj2 (Z.eqb_neq _ 2) N2), (proj2 (Z.eqb_neq _ 3) N3). reflexivity. }
    apply (r3h_fin X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ _ _ 0x21220 HX H3 HJ2).
    * intros a Ha Hn. rewrite (Kr2 a Ha), (Kr1 a Ha). exact (HN a Ha Hn).
    * apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem2 _); [intros k Hk; rewrite Kr2, Kr1 by lia; reflexivity | exact M80].
    * apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem2 _); [intros k Hk; rewrite Kr2, Kr1 by lia; reflexivity | exact M88].
    * r3h_same_tac HS0 EE HSm.
    * let R := fresh "R" in prreg HS0 (20%bv : bv 5) R; rewrite R; exact E27.
    * lia.
    * lia.
    * apply (r3h_pk_img X pos 0x21220 5 0x21220 HX R0); [lia | rewrite HST; cbn; lia | rewrite HST; exact (proj1 S0)].
  + exfalso.
    destruct (r3h_bad _ (ri_f X) ltac:(cbn [extK ewset ew Nat.eqb]; exact E25) Hf Hc) as [Q | [Q | Q]]; lia.
Qed.
Definition r3h_rA : YP09.region := YP09.mkRegion (Some 9%nat) 80 96 80 96 [].
Definition r3h_rS (cv : sv) : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 cv)].
Definition r3h_fA : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (20%nat, mkAF 4096 (2 ^ 47 - 2) 0) ] [] [].
Definition r3h_ssA (cv : sv) : sstate := mkSS (AF_reac_box_name + RBN_P3) sr_atoms [r3h_rA; r3h_rS cv] None r3h_fA.
Definition r3h_SHA : list shent := [ mkSHE 20 0 1 ].
Definition r3h_EA (regs : bvmap 5 word) (c : Z) : env := Eimg (Ereg regs [Z_to_bv 64 c]).
Definition r3h_ssA0 : sstate :=
  mkSS (AF_reac_box_name + RBN_P3) sr_atoms [r3h_rA] None (mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5) ] [] []).
Lemma r3h_eA : forall (fq : YK11.FPState) (regs : bvmap 5 word) (W : world SEGS) memc A s c cv,
  getr regs 9 = w64 A -> getr regs 20 = w64 s -> getr regs 22 = w64 SHADOW_OFF ->
  2 ^ 46 <= A -> A + 184 <= 2 ^ 47 -> A mod 32 = 0 ->
  4096 <= s <= 2 ^ 47 - 2 -> (s + 1 <= A + 80 \/ A + 96 <= s) -> 0 <= c < 256 ->
  regions_wf [r3h_rA; r3h_rS cv] = true ->
  sv_denot (r3h_EA regs c) cv = Z_to_bv 64 c ->
  (forall o, 80 <= o < 96 -> apresent (w_H W) memc (A + o)) ->
  val_mem SEGS (mrestrict (w_H W) memc) s 1 c ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s 1 ->
  ~ (SHADOW_OFF <= s < SHADOW_OFF + 17592186044416) ->
  st_ok_pi SEGS VAL (r3h_EA regs c) (r3h_ssA cv)
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_P3))) memc (seg_rom SEGS)))
  /\ sh_ok SEGS r3h_Bx r3h_SHA (r3h_EA regs c) (mrestrict (w_H W) memc).
Proof.
intros fq regs W memc A s c cv R9 R20 R22 HA0 HA1 HA32 Hs Hsd Hc Hwf Hcv PA Vc HRA Hap.
rewrite restrict_mkst_fx.
set (E := r3h_EA regs c) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold r3h_EA; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E20 : ew E 20 = Z_to_bv 64 s) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w)
  by (intros n w Hn Hw; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hw).
assert (HRO : regs_ok E sr_atoms regs) by (unfold E, r3h_EA; apply regs_ok_Eimg_Ereg).
clearbody E.
split.
- unfold r3h_ssA. apply pa_entry_st_ok_full.
  + exact HRO.
  + exact Hwf.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, r3h_rA, r3h_rS;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 9%nat A E9) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply PA; lia | constructor].
    * rewrite (VB 20%nat s E20) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ s 0 1 cv c); [exact Hcv | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat. exact Vc.
  + apply pairwise_disjoint_of_extents. unfold r3h_rA, r3h_rS, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 9%nat A E9), (VB 20%nat s E20) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; try exact I; lia.
  + split; [|split; exact I].
    cbn [r3h_fA f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E20, E22, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- unfold sh_ok, r3h_SHA. apply Forall_cons; [|apply Forall_nil].
  eapply shent_ok_of_range.
  + exact HRA.
  + unfold U, r3h_Bx. cbn [sv_denot]. rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. intros Hb. apply Hap. lia.
Qed.
Lemma r3h_eA0 : forall (fq : YK11.FPState) (regs : bvmap 5 word) (W : world SEGS) memc A,
  getr regs 9 = w64 A -> 2 ^ 46 <= A -> A + 184 <= 2 ^ 47 -> A mod 32 = 0 ->
  (forall o, 80 <= o < 96 -> apresent (w_H W) memc (A + o)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) r3h_ssA0
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_P3))) memc (seg_rom SEGS))).
Proof.
intros fq regs W memc A R9 HA0 HA1 HA32 PA.
rewrite restrict_mkst_fx.
assert (E9 : ew (Eimg (Ereg regs [])) 9 = Z_to_bv 64 A)
  by (rewrite (ew_Eimg_Ereg_nat regs [] 9%nat 9%bv eq_refl); exact R9).
unfold r3h_ssA0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, r3h_rA.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply PA; lia | constructor].
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, unsigned_lit_small by lia. change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
Lemma r3h_str_tr : forall (W W' : world SEGS) (m m' : word -> option byte) a s,
  rbn_str W m a s ->
  (forall x, a <= x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
     aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  range_addressable (aview SEGS (w_H W') m') SHADOW_OFF a (Z.of_nat (length s) + 1) ->
  shadow_hull_vis (aview SEGS (w_H W') m') a (Z.of_nat (length s) + 1) ->
  rbn_str W' m' a s.
Proof.
intros W W' m m' a s (Hf & Hg & Ha0 & Ha1 & Hl & Ham & _ & _ & Htr) HE Hra Hhv.
pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)) as M.
split; [exact Hf|]. split.
{ apply (garr8_frame SEGS (mrestrict (w_H W) m)); [exact Hg|].
  intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
  apply (mbyte_of_aview SEGS). apply HE. lia. }
split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Hl|]. split; [exact Ham|].
split; [exact Hra|]. split; [exact Hhv|].
intros x Hx. rewrite (HE x ltac:(lia)). exact (Htr x Hx).
Qed.
Lemma r3h_zs_vis : forall (rd : Z -> option Z) q L a n,
  q mod 64 = 0 -> L mod 64 = 0 -> 0 <= q -> 0 <= L ->
  zero_shadow rd SHADOW_OFF q L -> q <= a -> 0 < n -> a + n <= q + L ->
  range_addressable rd SHADOW_OFF a n /\ shadow_hull_vis rd a n.
Proof.
intros rd q L a n Hq HL Hq0 HL0 Hz Hqa Hn Hhi.
split.
- assert (HR : range_addressable rd SHADOW_OFF q L) by (apply zero_shadow_range; [lia | lia | exact Hz]).
  eapply range_addressable_sub; [exact HR | lia | lia].
- intros s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
  assert (Hi : 0 <= s - shadow_of_addr SHADOW_OFF q < L / 8) by (unfold shadow_of_addr, SHADOW_OFF; lia).
  replace s with (shadow_of_addr SHADOW_OFF q + (s - shadow_of_addr SHADOW_OFF q)) by lia.
  rewrite (Hz _ Hi). discriminate.
Qed.
Lemma r3h_hull_sub : forall (rd : Z -> option Z) b N a n,
  shadow_hull_vis rd b N -> b <= a -> 0 < n -> a + n <= b + N -> shadow_hull_vis rd a n.
Proof. intros rd b N a n H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *. lia. Qed.
Lemma r3h_frame64 : forall ly cid p, ly_F ly mod 4096 = 0 -> 0 <= cid ->
  frame_addr ly cid p mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0.
Proof.
intros ly cid p HF Hc.
assert (Hb : (64 | fs_frame_bytes cid)).
{ unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia. apply Z.divide_factor_l. }
split; [|apply Z.mod_divide; [lia | exact Hb]].
apply Z.mod_divide; [lia|]. unfold frame_addr, fs_frame_off.
repeat apply Z.divide_add_r;
  first [ apply Z.divide_mul_r; first [exact Hb | exists 16384; reflexivity]
        | apply Z.mod_divide; [lia | reflexivity]
        | apply (Z.divide_trans _ 4096); [exists 64; reflexivity | apply Z.mod_divide; [lia | exact HF]] ].
Qed.
Lemma r3h_sok_stk : forall X pos a s, rbn_cx B X -> rbn_SP X + 16 <= a ->
  a + Z.of_nat (length s) + 1 <= ri_sp0 X -> rbn_str (ri_W X) (ri_memc X) a s ->
  4096 <= a /\ r3h_sok X pos a s.
Proof.
intros X pos a s HX Ha1 Ha2 Hs.
destruct (r3h_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
split; [lia|].
intros lyc1 Sc1 W1 m1 md1 sh HM.
pose proof HM as (HJ1 & _ & _ & _ & (K1 & _) & _).
pose proof HJ1 as (HAR1 & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof (am_layout B lyc1 Sc1 _ (proj1 HAR1)) as HLY.
pose proof (lo_top lyc1 HLY) as (_ & _ & _ & _ & Lplo & Lphi & _). unfold page_aligned in Lplo, Lphi.
rewrite Elo in Lplo. rewrite Ehi in Lphi.
destruct (r3h_F_facts X pos lyc1 Sc1 W1 m1 md1 _ _ m1 md1 HX HM HAR1) as (HF4096 & HFceil & _).
pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)) as M8.
pose proof (Z.div_mod (ri_sp0 X) 16 ltac:(lia)) as D16. rewrite AR8, Z.add_0_r in D16.
assert (HE : forall x, a <= x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
  aview SEGS (w_H W1) m1 x = aview SEGS (w_H (ri_W X)) (ri_memc X) x).
{ intros x Hx. apply K1; [lia | unfold rbn_SP in *; lia | tauto]. }
pose proof (al_zshadow _ _ LAWS lyc1 Sc1 W1 m1 md1 (ly_stk_lo lyc1, ly_stk_hi lyc1 - ly_stk_lo lyc1) HAR1
  (or_introl eq_refl)) as Hz. cbn [fst snd] in Hz. rewrite Elo, Ehi in Hz.
destruct (r3h_zs_vis _ (ly_stk_lo (ri_ly X)) (ly_stk_hi (ri_ly X) - ly_stk_lo (ri_ly X)) a (Z.of_nat (length s) + 1)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hz ltac:(lia) ltac:(lia) ltac:(lia)) as (Hra & Hhv).
split.
- exact (r3h_str_tr (ri_W X) W1 (ri_memc X) m1 a s Hs HE Hra Hhv).
- intros x Hx. split; [unfold rbn_SP in *; lia | lia].
Qed.
Lemma r3h_sok_frame : forall X pos cid p a s, rbn_cx B X -> In (cid, p) (frames (ri_Sc X)) ->
  frame_addr (ri_lyc X) cid p <= a ->
  a + Z.of_nat (length s) + 1 <= frame_addr (ri_lyc X) cid p + fs_frame_bytes cid ->
  rbn_str (ri_W X) (ri_memc X) a s -> 4096 <= a /\ r3h_sok X pos a s.
Proof.
intros X pos cid p a s HX Hcp Ha1 Ha2 Hs.
pose proof HX as ((HAR0 & _) & _).
pose proof (am_wf _ _ _ _ (proj1 HAR0)) as HWF.
assert (HFS : wf_fs (ri_Sc X)) by (eapply wf_fakestack; exact HWF).
destruct HFS as [_ _ HL]. rewrite Forall_forall in HL.
destruct (HL (cid, p) Hcp) as [Hc0 _]. cbn [fst] in Hc0.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR0 Hcp) as (HF0 & HFc & _).
pose proof (lo_F_al (ri_lyc X) (am_layout B (ri_lyc X) (ri_Sc X) _ (proj1 HAR0))) as HLF. unfold page_aligned in HLF.
destruct (r3h_frame64 (ri_lyc X) cid p HLF ltac:(lia)) as (H64 & Hb64).
destruct (r3h_A_rng X HX) as (AR1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
pose proof (fs_frame_bytes_nonneg cid) as Hfn.
split; [lia|].
intros lyc1 Sc1 W1 m1 md1 sh HM.
pose proof (r3h_fa X pos lyc1 Sc1 W1 m1 md1 _ _ HX HM) as FA.
pose proof HM as (HJ1 & Hfrs & _ & _ & (_ & _ & _ & K4 & _) & _).
pose proof (proj1 HJ1) as HAR1.
pose proof Hs as (_ & _ & _ & _ & _ & _ & Hra0 & Hhv0 & _).
pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)) as M8.
assert (KF : forall x, frame_addr (ri_lyc X) cid p <= x < frame_addr (ri_lyc X) cid p + fs_frame_bytes cid ->
  aview SEGS (w_H W1) m1 x = aview SEGS (w_H (ri_W X)) (ri_memc X) x).
{ intros x Hx. apply (K4 cid p x Hcp); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | tauto]. }
assert (KS : forall y, shadow_addr (frame_addr (ri_lyc X) cid p) <= y <
    shadow_addr (frame_addr (ri_lyc X) cid p) + fs_frame_bytes cid / 8 ->
  aview SEGS (w_H W1) m1 y = aview SEGS (w_H (ri_W X)) (ri_memc X) y).
{ intros y Hy. apply (K4 cid p y Hcp); [right; unfold in_zr; cbn [fst snd]; lia | tauto]. }
assert (HE : forall x, a <= x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
  aview SEGS (w_H W1) m1 x = aview SEGS (w_H (ri_W X)) (ri_memc X) x)
  by (intros x Hx; apply KF; lia).
assert (Hra : range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF a (Z.of_nat (length s) + 1)).
{ intros x Hx. destruct (Hra0 x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  rewrite KS; [exact Hsv|]. unfold shadow_of_addr, shadow_addr. lia. }
assert (Hhv : shadow_hull_vis (aview SEGS (w_H W1) m1) a (Z.of_nat (length s) + 1)).
{ intros y Hy. rewrite KS; [exact (Hhv0 y Hy)|]. unfold shadow_addr, SHADOW_OFF in *. lia. }
split; [exact (r3h_str_tr (ri_W X) W1 (ri_memc X) m1 a s Hs HE Hra Hhv)|].
intros x Hx.
destruct (in_split _ _ Hcp) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (cid, p) [] l2 l3 HAR1
  ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !FA in Hd.
change (fs_frame_bytes 3) with 512 in Hd.
split; [unfold rbn_SP in *; lia | unfold rbn_F; lia].
Qed.
Lemma r3h_sok_heap : forall X pos b m a s, rbn_cx B X -> In (b, m) (ablocks B (ri_lyc X) (ri_Sc X)) ->
  b <= a -> a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 <= b + req_size m ->
  rbn_str (ri_W X) (ri_memc X) a s -> 4096 <= a /\ r3h_sok X pos a s.
Proof.
intros X pos b m a s HX Hb Hba Hab Hs.
pose proof HX as ((HAR0 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hb) as (_ & Hb4096 & Hbc & _).
destruct (r3h_A_rng X HX) as (AR1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)) as M8.
split; [lia|].
intros lyc1 Sc1 W1 m1 md1 sh HM.
pose proof (r3h_fa X pos lyc1 Sc1 W1 m1 md1 _ _ HX HM) as FA.
pose proof HM as (HJ1 & Hfrs & Hperm & _ & (_ & K2 & _) & _).
pose proof (proj1 HJ1) as HAR1.
assert (Hb1 : In (b, m) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hb).
destruct (al_shadow _ _ LAWS _ _ _ _ _ b m HAR1 Hb1) as (Hbs & Hbh).
assert (HE : forall x, a <= x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
  aview SEGS (w_H W1) m1 x = aview SEGS (w_H (ri_W X)) (ri_memc X) x).
{ intros x Hx. replace x with (b + (x - b)) by lia. apply (K2 b m (x - b) Hb); [lia | tauto]. }
split.
- apply (r3h_str_tr (ri_W X) W1 (ri_memc X) m1 a s Hs HE).
  + eapply block_shadow_range; [exact Hbs | lia | lia].
  + eapply r3h_hull_sub; [exact Hbh | lia | lia | lia].
- intros x Hx.
  assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 3 pos HAR1 Hb1 Hin3) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite FA in Hd. change (fs_frame_bytes 3) with 512 in Hd.
  split; [unfold rbn_SP in *; lia | unfold rbn_F; lia].
Qed.
Lemma r3h_said_sok : forall X pos, rbn_cx B X -> rbm_args X -> ri_said X <> 0 ->
  4096 <= ri_said X /\ r3h_sok X pos (ri_said X) (ri_sd X).
Proof.
intros X pos HX HA Hsn.
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & HSD).
destruct (HSD HA) as (HSAID & _).
destruct HSAID as [(Hs0 & _) | (_ & Hstr & Hloc)]; [contradiction|].
destruct Hloc as [(b & m & Hb & Hb1 & Hb2) | [(cid & p & Hcp & Hc1 & Hc2) | [(Hk1 & Hk2) | (q & sz & Hro & Hq1 & Hq2)]]].
- exact (r3h_sok_heap X pos b m _ _ HX Hb Hb1 Hb2 Hstr).
- exact (r3h_sok_frame X pos cid p _ _ HX Hcp Hc1 Hc2 Hstr).
- exact (r3h_sok_stk X pos _ _ HX Hk1 Hk2 Hstr).
- exact (r3h_sok_ro X pos q sz _ _ HX Hro Hq1 Hq2 Hstr).
Qed.
Ltac r3h_awrA X EE B9 :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  eapply (awr_ok_cons_stack_off _ _ _ (ri_STK X) (ri_sp0 X) (ri_FP X) _ _ _ _ 9%nat (rbn_A X - ri_sp0 X));
    [reflexivity | rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; rewrite unsigned_lit_small by lia; lia
    | cbn; lia | cbn; lia |];
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Theorem rbn3_head : rbn3_head_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H3.
pose proof H3 as (HM & (B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R26 & R20 & R23 & R24 & R25 & R27 & R12 & R13 &
  R14 & R15 & R16 & HA).
pose proof HX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _ & Hsr & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & HSD).
destruct (HSD HA) as (HSAID & _).
destruct (r3h_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HM as (HJ1 & _).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
assert (PA : forall o, 80 <= o < 96 -> apresent (w_H W1) memc1 (rbn_A X + o)).
{ intros o Ho. pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _).
  apply Hp. unfold rbn_SP in *. lia. }
destruct (r3h_ok_rng X HA) as (Ri & Ro).
assert (HSm0 : r3h_same regs1 regs1) by (intros r _; reflexivity).
assert (VA80 : forall E, ew E 12 = getr regs1 12 -> sv_denot E (SOff 12 0) = Z_to_bv 64 (ri_i X))
  by (intros E HE; cbn [sv_denot]; rewrite HE, R12, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (VA88 : forall E, ew E 13 = getr regs1 13 -> sv_denot E (SOff 13 0) = Z_to_bv 64 (ri_o X))
  by (intros E HE; cbn [sv_denot]; rewrite HE, R13, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (paj_run_to (fx := ri_fq X) B LAWS) as RUNTO.
pose proof (@SRr_run_to_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNTOP.
unfold rbn_cfg, cfg_at.
change (w64 (BASE + AF_reac_box_name + RBN_P3)) with (Z_to_bv 64 (BASE + AF_reac_box_name + RBN_P3)).
rewrite <- Z.add_assoc.
destruct HSAID as [(Hs0 & Hsd0) | (Hsn & _ & _)].
- pose proof (r3h_eA0 (ri_fq X) regs1 W1 memc1 (rbn_A X) B9 ltac:(lia) ltac:(lia) AR7 PA) as HS0.
  rewrite Hs0 in R20.
  pose proof (st_ok_pi_pin_reg' (Eimg (Ereg regs1 [])) _ _ (20%bv : bv 5) 0 HS0 R20 eq_refl) as HS. clear HS0.
  remember (Eimg (Ereg regs1 [])) as E eqn:HEd.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
    by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = rbn_A X)
    by (rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; lia).
  clear HEd.
  paj_run_to_sh RUNTOP HS HJ1 (AF_reac_box_name + R3H_B). { r3h_awrA X EE B9. }
  r3h_krA HFr Kr (fun a => rbn_A X + 80 <= a < rbn_A X + 96) U9.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RA. cbn [ms_mem restrict] in RA.
  r3h_toB HS X.
  apply (r3h_B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ _ _ HX H3 Hsd0 HJ1).
  + exact Kr.
  + apply (field_of_region E _ 9 (rbn_A X) _ 80 96 80 96 80 8 (SOff 12 0) (ri_i X) RA);
      [exact U9 | cbn [In]; tauto | apply VA80; apply EE; reflexivity | cbn; lia | cbn; lia].
  + apply (field_of_region E _ 9 (rbn_A X) _ 80 96 80 96 88 8 (SOff 13 0) (ri_o X) RA);
      [exact U9 | cbn [In]; tauto | apply VA88; apply EE; reflexivity | cbn; lia | cbn; lia].
  + r3h_same_tac HS EE HSm0.
  + let R := fresh "R" in prreg HS (25%bv : bv 5) R; rewrite R, (EE 25%nat 25%bv eq_refl); exact R25.
- destruct (r3h_said_sok X pos HX HA Hsn) as (Hs4096 & Hsok).
  destruct (Hsok _ _ _ _ _ _ HM) as (Hstr1 & Hdis1).
  pose proof Hstr1 as (Hch & Hg & Hp0 & Hp1 & Hl32 & Ham & Hra & _).
  assert (Hsb : ri_said X + Z.of_nat (length (ri_sd X)) + 1 <= 2 ^ 47 - 1) by (unfold amem_range in Ham; lia).
  assert (Hap : ~ (SHADOW_OFF <= ri_said X < SHADOW_OFF + 17592186044416))
    by (unfold amem_range in Ham; unfold SHADOW_OFF; lia).
  assert (Hdj : ri_said X + 1 <= rbn_A X + 80 \/ rbn_A X + 96 <= ri_said X).
  { destruct (Hdis1 (ri_said X) ltac:(lia)) as [Hd1 _]. unfold rbn_SP in *. lia. }
  assert (HRA1 : range_addressable (aview SEGS (w_H W1) memc1) SHADOW_OFF (ri_said X) 1)
    by (eapply range_addressable_sub; [exact Hra | lia | lia]).
  destruct (Hg 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as (V0 & Vr0).
  cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0.
  destruct (ri_sd X) as [|c sd'] eqn:Hsd.
  + cbn [nth app] in V0.
    destruct (r3h_eA (ri_fq X) regs1 W1 memc1 (rbn_A X) (ri_said X) 0 (SLit 0) B9 R20 B22 ltac:(lia) ltac:(lia) AR7
      ltac:(lia) Hdj ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity) PA V0 HRA1 Hap) as [HS SHOK].
    remember (r3h_EA regs1 0) as E eqn:HEd.
    assert (HEI : img_env VAL A_LIM E) by (subst E; unfold r3h_EA; apply Eimg_env).
    assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
      by (intros n r Hn; subst E; unfold r3h_EA; apply ew_Eimg_Ereg_nat; exact Hn).
    assert (U9 : bv_unsigned (ew E 9) = rbn_A X)
      by (rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; lia).
    clear HEd.
    paj_run_to_tok RUNTO HS HJ1 SHOK r3h_span (AF_reac_box_name + R3H_B). { r3h_awrA X EE B9. }
    r3h_krA HFr Kr (fun a => rbn_A X + 80 <= a < rbn_A X + 96) U9.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RA. cbn [ms_mem restrict] in RA.
    r3h_toB HS X.
    apply (r3h_B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ _ _ HX H3 Hsd HJ1).
    * exact Kr.
    * apply (field_of_region _ _ 9 (rbn_A X) _ 80 96 80 96 80 8 (SOff 12 0) (ri_i X) RA);
        [cbn [extK ewset ew Nat.eqb]; exact U9 | cbn [In]; tauto
        | apply VA80; cbn [extK ewset ew Nat.eqb]; apply EE; reflexivity | cbn; lia | cbn; lia].
    * apply (field_of_region _ _ 9 (rbn_A X) _ 80 96 80 96 88 8 (SOff 13 0) (ri_o X) RA);
        [cbn [extK ewset ew Nat.eqb]; exact U9 | cbn [In]; tauto
        | apply VA88; cbn [extK ewset ew Nat.eqb]; apply EE; reflexivity | cbn; lia | cbn; lia].
    * r3h_same_tac HS EE HSm0.
    * let R := fresh "R" in prreg HS (25%bv : bv 5) R; rewrite R, (EE 25%nat 25%bv eq_refl); exact R25.
  + cbn [nth app] in V0, Vr0.
    assert (Hc : 0 < c < 256) by exact (Forall_inv Hch).
    assert (HST : rbm_stem X = ri_sd X) by (unfold rbm_stem, bn_stem; rewrite Hsd; reflexivity).
    remember (r3h_EA regs1 c) as E eqn:HEd.
    assert (E32 : ew E 32 = Z_to_bv 64 c)
      by (subst E; unfold r3h_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
    assert (Hcv : sv_denot E (SOff 32 0) = Z_to_bv 64 c)
      by (cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    subst E.
    destruct (r3h_eA (ri_fq X) regs1 W1 memc1 (rbn_A X) (ri_said X) c (SOff 32 0) B9 R20 B22 ltac:(lia) ltac:(lia) AR7
      ltac:(lia) Hdj ltac:(lia) ltac:(vm_compute; reflexivity) Hcv PA V0 HRA1 Hap) as [HS0 SHOK].
    remember (r3h_EA regs1 c) as E eqn:HEd.
    assert (HEI : img_env VAL A_LIM E) by (subst E; unfold r3h_EA; apply Eimg_env).
    assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
      by (intros n r Hn; subst E; unfold r3h_EA; apply ew_Eimg_Ereg_nat; exact Hn).
    assert (U9 : bv_unsigned (ew E 9) = rbn_A X)
      by (rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; lia).
    clear HEd.
    pose proof (st_ok_pi_add_fact E _ _ 32 (mkAF 1 255 0) HS0
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS. clear HS0.
    paj_run_to_tok RUNTO HS HJ1 SHOK r3h_span (AF_reac_box_name + RBN_T3). { r3h_awrA X EE B9. }
    r3h_krA HFr Kr (fun a => rbn_A X + 80 <= a < rbn_A X + 96) U9.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RA. cbn [ms_mem restrict] in RA.
    r3h_post HS.
    apply (r3h_fin X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ _ _ (ri_said X) HX H3 HJ1).
    * exact Kr.
    * apply (field_of_region _ _ 9 (rbn_A X) _ 80 96 80 96 80 8 (SOff 12 0) (ri_i X) RA);
        [cbn [extK ewset ew Nat.eqb]; exact U9 | cbn [In]; tauto
        | apply VA80; cbn [extK ewset ew Nat.eqb]; apply EE; reflexivity | cbn; lia | cbn; lia].
    * apply (field_of_region _ _ 9 (rbn_A X) _ 80 96 80 96 88 8 (SOff 13 0) (ri_o X) RA);
        [cbn [extK ewset ew Nat.eqb]; exact U9 | cbn [In]; tauto
        | apply VA88; cbn [extK ewset ew Nat.eqb]; apply EE; reflexivity | cbn; lia | cbn; lia].
    * r3h_same_tac HS EE HSm0.
    * let R := fresh "R" in prreg HS (20%bv : bv 5) R; rewrite R, (EE 20%nat 20%bv eq_refl); exact R20.
    * exact Hs4096.
    * lia.
    * intros lyc' Sc' W' m' md' sh' HM'. destruct (Hsok _ _ _ _ _ _ HM') as (Hst & Hdi).
      unfold rbn_stp. rewrite HST, ?Hsd. split; [exact Hst | exact Hdi].
Qed.
End h.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC88.v:61-65, 107-112, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_L1.v, with its module paths changed; 816 of its 892 lines of code are new or changed and 741 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YI0s YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC88 YK0w YC85 YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacBoxNameLoops.
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
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma rbn2_apresent_of_some : forall H (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> aview SEGS H m a <> None -> apresent H m a.
Proof.
intros H m a Ha Hn Hv.
assert (Er : seg_rom SEGS (Z_to_bv 64 a) = None).
{ eapply seg_rom_none; try exact Ha; try exact Hn; try exact pa_segs_low. }
unfold aview, mbyte, mrestrict in Hv. unfold apresent.
destruct (H (Z_to_bv 64 a)) eqn:Eh.
- rewrite Er in Hv. cbn in Hv. exfalso. exact (Hv eq_refl).
- split; [reflexivity|]. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [exists b; reflexivity|].
  rewrite Er in Hv. cbn in Hv. exfalso. exact (Hv eq_refl).
Qed.
Definition rbn2_SB : Z := 0x7fff8000.
Definition rbn2_Bx : sv := SOff 22 0.
Definition rbn2_span : Z * Z := (rbn2_SB, rbn2_SB + 2 ^ 44 - 1).
Definition rbn2_ssA : sstate := mkSS (AF_both3_reac_box_name + RBN_L2) sr_atoms [] None
  (mkFacts [(22%nat, mkAF rbn2_SB rbn2_SB 0)] [] []).
Definition RBN_L2R : Z := 0x3c0.
Definition rbn2_ssB : sstate := mkSS (AF_both3_reac_box_name + RBN_L2R) sr_atoms
  [YP09.mkRegion (Some 20%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 32 0))]] None
  (mkFacts [(20%nat, mkAF 0 (2 ^ 47 - 2) 0); (21%nat, mkAF 1 (2 ^ 47 - 1) 0); (22%nat, mkAF rbn2_SB rbn2_SB 0);
            (32%nat, mkAF 0 255 0)] [] []).
Lemma rbn2_entryA : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) memc,
  getr regs 22 = w64 SHADOW_OFF ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) rbn2_ssA
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L2))) memc (seg_rom SEGS))).
Proof.
intros fq W regs memc H22. rewrite restrict_mkst_fx. unfold rbn2_ssA. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (ew_Eimg_Ereg_nat regs [] 22 22%bv eq_refl), H22. unfold w64.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold rbn2_SB, SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
Lemma rbn2_entryB : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) memc P c1,
  getr regs 22 = w64 SHADOW_OFF -> getr regs 20 = w64 P -> getr regs 21 = w64 (P + 1) ->
  0 <= P <= 2 ^ 47 - 2 ->
  val_mem SEGS (mrestrict (w_H W) memc) (P + 1) 1 c1 -> 0 <= c1 < 256 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 c1])) rbn2_ssB
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L2R))) memc (seg_rom SEGS))).
Proof.
intros fq W regs memc P c1 H22 H20 H21 HP Vc Rc. rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [Z_to_bv 64 c1])).
assert (E20 : ew E 20 = Z_to_bv 64 P) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E21 : ew E 21 = Z_to_bv 64 (P + 1)) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 c1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
unfold rbn2_ssB. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E20, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ P 1 1 (SOff 32 0) c1);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | exact Vc].
- apply pairwise_disjoint_of_extents. cbn [map extent_of_region zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E20, E21, E22, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold rbn2_SB, SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
Lemma rbn2_keep_nowr : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hw a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr). rewrite Forall_forall in Hw. pose proof (Hw r Hin). lia.
Qed.
Ltac rbn2_nowr :=
  apply Forall_forall; let rr := fresh "rr" in let Hrr := fresh "Hrr" in intros rr Hrr;
  lazymatch type of Hrr with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hrr end;
  repeat (destruct Hrr as [<- | Hrr]; [cbn; lia|]); try destruct Hrr.
Lemma rbn2_ra_keep : forall (rd rd' : Z -> option Z) a n,
  (forall s, SHADOW_OFF <= s < kHighShadowEnd -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n HK Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. apply HK. unfold shadow_of_addr, SHADOW_OFF, kHighShadowEnd.
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
change (2 ^ 44) with 17592186044416 in *. lia.
Qed.
Lemma rbn2_shv_keep : forall (rd rd' : Z -> option Z) a n,
  (forall s, SHADOW_OFF <= s < kHighShadowEnd -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof.
intros rd rd' a n HK Ha Han Hn HV s Hs. rewrite HK; [exact (HV s Hs)|]. unfold shadow_addr, SHADOW_OFF, kHighShadowEnd in *.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
assert (Hq : (a + n - 1) / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (Hq2 : (2147450880 + (a + n - 1) / 8) / 8 < 2199291686912) by (apply Z.div_lt_upper_bound; lia).
assert (Hl : 268431360 <= (2147450880 + a / 8) / 8) by (apply Z.div_le_lower_bound; lia).
lia.
Qed.
Lemma rbn2_shv_sub : forall (rd : Z -> option Z) x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + x / 8) (SHADOW_OFF + x' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (x' + n' - 1) / 8) (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
lia.
Qed.
Lemma rbn2_off_img : forall x n a, off_img x n -> x <= a < x + n -> ~ in_img SEGS a.
Proof.
intros x n a Ho Ha Hi. pose proof (pa_img_range a Hi) as Hr. unfold off_img in Ho. lia.
Qed.
Lemma rbn2_vm_some : forall H (m : word -> option byte) a n v k,
  val_mem SEGS (mrestrict H m) a n v -> 0 <= k < Z.of_nat n -> aview SEGS H m (a + k) <> None.
Proof.
intros H m a n v k Hv Hk. unfold aview. replace k with (Z.of_nat (Z.to_nat k)) by lia.
rewrite (Hv (Z.to_nat k) ltac:(lia)). discriminate.
Qed.
Lemma rbn2_ra_ext : forall (rd rd' : Z -> option Z) a n,
  (forall s, rd' s = rd s) -> range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof. intros rd rd' a n HK HR x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. rewrite HK. auto. Qed.
Lemma rbn2_shv_ext : forall (rd rd' : Z -> option Z) a n,
  (forall s, rd' s = rd s) -> shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof. intros rd rd' a n HK HV s Hs. rewrite HK. exact (HV s Hs). Qed.
Lemma rbn2_src_tail : forall (W : world SEGS) (mem : word -> option byte) P c l,
  rbn_lsrc W mem P (c :: l) -> rbn_lsrc W mem (P + 1) l.
Proof.
intros W mem P c l (HG & H0 & H63 & H47 & HRA).
assert (HL : Z.of_nat (length (c :: l)) = Z.of_nat (length l) + 1) by (cbn [length]; lia).
change (c :: l) with ([c] ++ l) in HG.
split; [|split; [lia | split; [lia | split; [lia|]]]].
- pose proof (proj1 (garr8_app SEGS (mrestrict (w_H W) mem) P [c] l) HG) as (_ & HG2).
  cbn [length Z.of_nat] in HG2. exact HG2.
- eapply range_addressable_sub; [exact HRA | lia | lia].
Qed.
Definition rbn2_keptl : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma rbn2_kept_cover : forall r : Z, 0 <= r < 32 -> r <> 10 -> r <> 11 -> r <> 20 -> r <> 21 ->
  r = 0 \/ In (Z_to_bv 5 r) rbn2_keptl.
Proof.
intros r Hr H10 H11 H20 H21.
assert (H32 : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/
  r = 10 \/ r = 11 \/ r = 12 \/ r = 13 \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17 \/ r = 18 \/ r = 19 \/
  r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 28 \/ r = 29 \/
  r = 30 \/ r = 31) by lia.
repeat (destruct H32 as [-> | H32]); try (subst r);
  first [ solve [left; reflexivity]
        | solve [exfalso; lia]
        | solve [right; unfold rbn2_keptl; cbn [In];
                 repeat first [ solve [left; apply bv_eq; vm_compute; reflexivity] | right ]] ].
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TSB : tsb_ch_spec B.
Lemma rbn2_kept_pre : forall lyc Sc (W : world SEGS) (m m' : word -> option byte) W2 m2 sp (Er : Z -> Prop),
  (forall a, aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) -> mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  tsb_ch_kept B lyc Sc W m' W2 m2 sp Er -> tsb_ch_kept B lyc Sc W m W2 m2 sp Er.
Proof.
intros lyc Sc W m m' W2 m2 sp Er HK HG (A1 & A2 & A3 & A4 & A5 & A6).
split; [intros a Ha Hw HE; rewrite <- HK; exact (A1 a Ha Hw HE)|].
split; [intros b mm i Hb Hi HE; rewrite <- HK; exact (A2 b mm i Hb Hi HE)|].
split; [intros a Him Hns Herr; rewrite <- HK; exact (A3 a Him Hns Herr)|].
split; [intros cid pos a Hf Hz HE; rewrite <- HK; exact (A4 cid pos a Hf Hz HE)|].
split; [intros a Ha Hw Hp; apply (A5 a Ha Hw); exact (apresent_grows _ _ _ _ HG Hp)|].
exact A6.
Qed.
Lemma rbn2_kept_post : forall lyc Sc (W : world SEGS) (m : word -> option byte) (W2 : world SEGS) m2 m2' sp (Er : Z -> Prop),
  (forall a, aview SEGS (w_H W2) m2' a = aview SEGS (w_H W2) m2 a) -> mem_grows (mrestrict (w_H W2) m2) (mrestrict (w_H W2) m2') ->
  tsb_ch_kept B lyc Sc W m W2 m2 sp Er -> tsb_ch_kept B lyc Sc W m W2 m2' sp Er.
Proof.
intros lyc Sc W m W2 m2 m2' sp Er HK HG (A1 & A2 & A3 & A4 & A5 & A6).
split; [intros a Ha Hw HE; rewrite HK; exact (A1 a Ha Hw HE)|].
split; [intros b mm i Hb Hi HE; rewrite HK; exact (A2 b mm i Hb Hi HE)|].
split; [intros a Him Hns Herr; rewrite HK; exact (A3 a Him Hns Herr)|].
split; [intros cid pos a Hf Hz HE; rewrite HK; exact (A4 cid pos a Hf Hz HE)|].
split; [intros a Ha Hw Hp; exact (apresent_grows _ _ _ _ HG (A5 a Ha Hw Hp))|].
intros a Ha. exact (apresent_grows _ _ _ _ HG (A6 a Ha)).
Qed.
Lemma rbn2_kept_mono : forall lyc Sc (W : world SEGS) m W2 m2 sp (E1 E2 : Z -> Prop),
  (forall a, E1 a -> E2 a) -> tsb_ch_kept B lyc Sc W m W2 m2 sp E1 -> tsb_ch_kept B lyc Sc W m W2 m2 sp E2.
Proof.
intros lyc Sc W m W2 m2 sp E1 E2 HE (A1 & A2 & A3 & A4 & A5 & A6).
split; [intros a Ha Hw HN; exact (A1 a Ha Hw (fun X => HN (HE a X)))|].
split; [intros b mm i Hb Hi HN; exact (A2 b mm i Hb Hi (fun X => HN (HE _ X)))|].
split; [exact A3|].
split; [intros cid pos a Hf Hz HN; exact (A4 cid pos a Hf Hz (fun X => HN (HE a X)))|].
split; [exact A5 | exact A6].
Qed.
Lemma rbn2_kept_trans : forall lyc Sc (W : world SEGS) m lyc1 Sc1 (W1 : world SEGS) m1 W2 m2 sp (E1 E2 : Z -> Prop),
  (forall cid pos, frame_addr lyc1 cid pos = frame_addr lyc cid pos) -> frames Sc1 = frames Sc ->
  ablocks B lyc1 Sc1 = ablocks B lyc Sc ->
  tsb_ch_kept B lyc Sc W m W1 m1 sp E1 -> tsb_ch_kept B lyc1 Sc1 W1 m1 W2 m2 sp E2 ->
  tsb_ch_kept B lyc Sc W m W2 m2 sp (fun a => E1 a \/ E2 a).
Proof.
intros lyc Sc W m lyc1 Sc1 W1 m1 W2 m2 sp E1 E2 HFA HFR HBL (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6).
split.
{ intros a Ha Hw HE. rewrite (B1 a Ha Hw (fun X => HE (or_intror X))). exact (A1 a Ha Hw (fun X => HE (or_introl X))). }
split.
{ intros b mm i Hb Hi HE. rewrite (B2 b mm i ltac:(rewrite HBL; exact Hb) Hi (fun X => HE (or_intror X))).
  exact (A2 b mm i Hb Hi (fun X => HE (or_introl X))). }
split.
{ intros a Him Hns Herr. rewrite (B3 a Him Hns Herr). exact (A3 a Him Hns Herr). }
split.
{ intros cid pos a Hf Hz HE.
  assert (Hz1 : in_zr a (frame_rng lyc1 (cid, pos)) \/
                in_zr a (shadow_addr (frame_addr lyc1 cid pos), fs_frame_bytes cid / 8))
    by (unfold frame_rng in *; cbn [fst snd] in *; rewrite !HFA; exact Hz).
  rewrite (B4 cid pos a ltac:(rewrite HFR; exact Hf) Hz1 (fun X => HE (or_intror X))).
  exact (A4 cid pos a Hf Hz (fun X => HE (or_introl X))). }
split.
{ intros a Ha Hw Hp. exact (B5 a Ha Hw (A5 a Ha Hw Hp)). }
exact B6.
Qed.
Lemma rbn2_rod_kept : forall lyc Sc (W : world SEGS) m W2 m2 sp (Er : Z -> Prop),
  tsb_ch_kept B lyc Sc W m W2 m2 sp Er ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) m2).
Proof.
intros lyc Sc W m W2 m2 sp Er (_ & _ & K3 & _) HR a Hro Ho He.
rewrite (K3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
exact (pa_relro_img a Hgot).
Qed.
Lemma rbn2_lyF : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md lyc2 Sc2 W2 m2 md2 k k2,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc2 Sc2 W2 m2 md2 k2 ->
  forall cid pos, frame_addr lyc2 cid pos = frame_addr lyc cid pos.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md lyc2 Sc2 W2 m2 md2 k k2 (_ & L1 & _) (_ & L2 & _) cid pos.
destruct L1 as (_ & _ & _ & _ & _ & F1 & _). destruct L2 as (_ & _ & _ & _ & _ & F2 & _).
unfold frame_addr. rewrite F1, F2. reflexivity.
Qed.
Lemma rbn2_awr_tr : forall STK sp0 FP bl0 own lyc Sc lyc2 Sc2 a,
  (forall cid pos, frame_addr lyc2 cid pos = frame_addr lyc cid pos) -> ablocks B lyc2 Sc2 = ablocks B lyc Sc ->
  awr_byte STK sp0 FP bl0 (ablocks B lyc Sc) lyc own a -> awr_byte STK sp0 FP bl0 (ablocks B lyc2 Sc2) lyc2 own a.
Proof.
intros STK sp0 FP bl0 own lyc Sc lyc2 Sc2 a HFA HBL H. rewrite HBL.
destruct H as [H | [H | [H | (cid & pos & Hin & Hz)]]]; [left; exact H | right; left; exact H | right; right; left; exact H|].
right. right. right. exists cid, pos. rewrite !HFA. split; [exact Hin | exact Hz].
Qed.
Definition rbn2_cpost (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc k
  (regs : bvmap 5 word) (D n c : Z) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists lyc1 Sc1 regs1 mem1 md1,
    c1 = cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L2R) regs1 mem1 md1 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 mem1 md1 k /\
    frames Sc1 = frames Sc /\ ablocks B lyc1 Sc1 = ablocks B lyc Sc /\
    aregs_preserved regs regs1 /\
    ((23 <= n /\ val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs + 152 + 24) 4 1 /\
      tsb_ch_kept B lyc Sc W memc W1 mem1 (spZ regs) (fun a => spZ regs + 152 + 24 <= a < spZ regs + 152 + 28)) \/
     (n < 23 /\ val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs + 152 + 16) 8 (n + 1) /\
      val_mem SEGS (mrestrict (w_H W1) mem1) (D + n) 1 c /\
      tsb_ch_kept B lyc Sc W memc W1 mem1 (spZ regs)
        (fun a => spZ regs + 152 + 16 <= a < spZ regs + 152 + 24 \/ a = D + n))).
Lemma rbn2_call : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) D n ov c,
  rbn_lcx B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 152) D 24 n ov ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 152) D 24 ->
  0 <= n <= 23 -> getr regs 10 = w64 c -> 0 <= c < 256 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L2) regs memc mdc)
    (rbn2_cpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs D n c).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n ov c HX HR HD Hn H10 Hc.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. unfold YImgTop.IMG_LO in HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HX as (HJ & HROD & H3 & H4 & H9 & H22 & Hal & Hlo & Hhi).
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof HR as (HR0 & HR8 & HR63 & HRam & HRimg & HRside & HD64 & Hcap64 & Hn0 & Hn64 & Hov &
  VR0 & VR8 & VR16 & VR24 & HRra & HRsv & HRwr).
pose proof HD as (HD0 & HD63 & HDapp & HDam & HDimg & HDside & HDR & HDra & HDsv & HDwr).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
pose proof (rbn2_entryA fq W regs memc H22) as HS.
unfold cfg_at. rewrite <- Z.add_assoc.
change (w64 (BASE + (AF_both3_reac_box_name + RBN_L2))) with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L2))).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Eimg_Ereg_nat regs [] 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Eimg_Ereg_nat regs [] 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Eimg_Ereg_nat regs [] 4 4%bv eq_refl)).
assert (E9 : ew E 9 = getr regs 9) by (subst E; exact (ew_Eimg_Ereg_nat regs [] 9 9%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; exact (ew_Eimg_Ereg_nat regs [] 10 10%bv eq_refl)).
clear HE.
assert (SHOK : sh_ok SEGS rbn2_Bx [] E (mrestrict (w_H W) memc)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
paj_run_tok RUN HS HJ SHOK rbn2_span.
{ awr_ok_tac. }
assert (KEEP0 : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a)
  by (apply (rbn2_keep_nowr E (ss_mem rbn2_ssA) (w_H W) memc (ms_mem ms) HFr); unfold rbn2_ssA; cbn [ss_mem]; constructor).
assert (HPA : aregs_preserved regs (ms_regs ms))
  by exact (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HS HAE ltac:(vm_compute; reflexivity)).
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
assert (Usp : spZ (ms_regs ms) = spZ regs) by (unfold spZ; rewrite R2, E2; reflexivity).
assert (A10 : getr (ms_regs ms) 10 = w64 (spZ regs + 152)) by (rewrite R10, E9, H9; reflexivity).
assert (A11 : getr (ms_regs ms) 11 = w64 c).
{ rewrite R11, E10, H10. cbn [alu64 alu]. unfold w64. apply land_255_small. rewrite unsigned_lit_small by lia. lia. }
pmkst HS. rewrite pa_sigma_sb_ch.
pose proof (fun a => KEEP0 a) as KEEP0'.
assert (HDra0 : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF D 24)
  by exact (rbn2_ra_ext _ _ D 24 KEEP0 HDra).
assert (HDsv0 : shadow_hull_vis (aview SEGS (w_H W) (ms_mem ms)) D 24)
  by exact (rbn2_shv_ext _ _ D 24 KEEP0 HDsv).
eapply SRr_bind.
{ pose proof (TSB fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc) k
    (ms_regs ms) (spZ regs + 152) c D 24 n [] HJ) as CALL.
  unfold cfg_at in CALL. apply CALL; clear CALL.
  - intros a Ha1 Ha2 Ha3. rewrite KEEP0. exact (HROD a Ha1 Ha2 Ha3).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
  - rewrite R3, E3. exact H3.
  - rewrite R4, E4. exact H4.
  - exact A10.
  - exact A11.
  - apply achain_low. unfold s0Z. rewrite getr_same by reg_neq_tac. rewrite unsigned_lit_small by lia. lia.
  - rewrite Usp. exact Hal.
  - rewrite Usp. exact Hlo.
  - rewrite Usp. exact Hhi.
  - lia.
  - exact HR0.
  - exact HR8.
  - exact HR63.
  - exact HRam.
  - rewrite Usp. exact HRside.
  - exact HRimg.
  - lia.
  - lia.
  - lia.
  - apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) memc (ms_mem ms)); [intros x _; apply KEEP0 | exact VR0].
  - apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) memc (ms_mem ms)); [intros x _; apply KEEP0 | exact VR8].
  - apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) memc (ms_mem ms)); [intros x _; apply KEEP0 | exact VR16].
  - exact (rbn2_ra_ext _ _ _ 28 KEEP0 HRra).
  - exact (rbn2_shv_ext _ _ _ 28 KEEP0 HRsv).
  - intros a Ha. destruct (HRwr a Ha) as [Hw Hp]. split; [exact Hw | exact (apresent_grows _ _ _ _ HG Hp)].
  - intros Hlt. destruct (HDwr (D + n) ltac:(lia)) as [Hw Hp].
    split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
    split; [exact (range_addressable_sub _ _ D 24 (D + n) 1 HDra0 ltac:(lia) ltac:(lia))|].
    split; [exact (rbn2_shv_sub _ D 24 (D + n) 1 HDsv0 ltac:(lia) ltac:(lia) ltac:(lia))|].
    split; [rewrite Usp; lia|]. split; [unfold off_img in *; lia|]. split; [lia|].
    split; [exact Hw | exact (apresent_grows _ _ _ _ HG Hp)]. }
cbv beta. intros W1 c1 Hle1 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hfr2 & Hbl2 & Hcase).
apply SRr_ret. unfold rbn2_cpost. exists ly2, S2, regs2, mem2, md2.
split.
{ unfold cfg_at, w64. rewrite R1. do 3 f_equal. unfold RBN_L2R, AF_both3_reac_box_name. lia. }
split; [exact HJ2|]. split; [exact Hfr2|]. split; [exact Hbl2|].
split; [exact (aregs_preserved_trans _ _ _ HPA HP2)|].
rewrite Usp in Hcase.
destruct Hcase as [(Hcap & V24 & HK) | (Hlt & V16 & Vb & HK)].
- left. split; [lia|]. split; [exact V24|].
  exact (rbn2_kept_pre _ _ W memc (ms_mem ms) _ _ _ _ KEEP0 HG HK).
- right. split; [lia|]. split; [exact V16|].
  split; [rewrite Z.mod_small in Vb by lia; exact Vb|].
  exact (rbn2_kept_pre _ _ W memc (ms_mem ms) _ _ _ _ KEEP0 HG HK).
Qed.
Definition rbn2_rpost (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc k
  (regs : bvmap 5 word) (P c1 : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + (if c1 =? 0 then RBN_L2X else RBN_L2)) regs2 mem2 md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
    (forall a, aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
    mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) /\
    (forall r, 0 <= r < 32 -> r <> 10 -> r <> 11 -> r <> 20 -> r <> 21 ->
       getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
    getr regs2 10 = w64 c1 /\ getr regs2 20 = w64 (P + 1) /\ getr regs2 21 = w64 (P + 2).
Ltac rbn2_fin c1 HAE E10v E20v E21v KEEP1 HG0 :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msx), HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HFx : frame_of _ ?rsx (mrestrict _ _) (mrestrict _ (ms_mem ?msx)), HGx : mem_grows _ (mrestrict _ (ms_mem ?msx)) |- _ =>
  let KEEP2 := fresh "KEEP2" in
  assert (KEEP2 : forall a, aview SEGS _ (ms_mem msx) a = aview SEGS _ _ a)
    by (apply (rbn2_keep_nowr _ rsx _ _ _ HFx); rbn2_nowr);
  let HKr := fresh "HKr" in
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ [Z_to_bv 64 c1] rbn2_keptl HS ltac:(env_agree_chain HAE)
    ltac:(vm_compute; reflexivity)) as HKr;
  cbn [ms_regs restrict] in HKr;
  let Q10 := fresh "Q10" in let Q20 := fresh "Q20" in let Q21 := fresh "Q21" in
  prreg HS (10%bv : bv 5) Q10; prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21;
  pmkst HS;
  apply SRr_ret; unfold rbn2_rpost; split; [reflexivity|];
  lazymatch goal with |- context [mkCfg (mkst (ms_regs ?m1) _ _ _) ?md1] => exists (ms_regs m1), (ms_mem m1), md1 end;
  split; [|split; [exact HJx|split; [intros a; rewrite KEEP2; apply KEEP1|split; [exact (mem_grows_trans _ _ _ HG0 HGx)|]]]];
  [|split; [intros r Hr Nq10 Nq11 Nq20 Nq21; destruct (rbn2_kept_cover r Hr Nq10 Nq11 Nq20 Nq21) as [-> | Hin];
     [replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity); rewrite !getr_zero; reflexivity
     | exact (HKr _ Hin)]|]];
  [|split; [rewrite Q10; rewrite ?ew_ewset_other by lia; rewrite E10v; reflexivity|];
    split; [rewrite Q20; rewrite ?ew_ewset_other by lia; rewrite E20v, unsigned_lit_small by lia; unfold w64; f_equal; lia|];
    rewrite Q21; rewrite ?ew_ewset_other by lia; rewrite E21v, unsigned_lit_small by lia; unfold w64; f_equal; lia]
  end.
Lemma rbn2_ret : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) P c1,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 22 = w64 SHADOW_OFF -> getr regs 20 = w64 P -> getr regs 21 = w64 (P + 1) -> getr regs 24 = w64 (-1) ->
  0 <= P <= 2 ^ 47 - 2 ->
  val_mem SEGS (mrestrict (w_H W) memc) (P + 1) 1 c1 -> 0 <= c1 < 256 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (P + 1) 1 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L2R) regs memc mdc)
    (rbn2_rpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs P c1).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P c1 HJ H22 H20 H21 H24 HP Vc Rc HRA.
pose proof (rbn2_entryB fq W regs memc P c1 H22 H20 H21 HP Vc Rc) as HS.
unfold cfg_at. rewrite <- Z.add_assoc.
change (w64 (BASE + (AF_both3_reac_box_name + RBN_L2R))) with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L2R))).
remember (Eimg (Ereg regs [Z_to_bv 64 c1])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 c1]) E)
  by (subst E; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E20 : ew E 20 = Z_to_bv 64 P) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E21 : ew E 21 = Z_to_bv 64 (P + 1)) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E24 : ew E 24 = Z_to_bv 64 (2 ^ 64 - 1))
  by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 24 24%bv eq_refl), H24; apply bv_eq; vm_compute; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 c1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
clear HE.
assert (SHOK : sh_ok SEGS rbn2_Bx [] E (mrestrict (w_H W) memc)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
psrr_branch_tok RUN BR HS SHOK rbn2_span.
{ exfalso. rewrite branch_eq_U, (U_atom E 20 P E20), (U_atom E 24 (2 ^ 64 - 1) E24) in Hc by lia.
  apply Z.eqb_eq in Hc. lia. }
paj_run_tok RUN HS HJ SHOK rbn2_span.
{ cbn [ms_mem mkst]. rewrite (U_atom E 21 (P + 1) E21) by lia.
  apply (obl_of_range SEGS (w_H W) memc E rbn2_Bx (P + 1) 1 (P + 1) 1); [exact HRA | | lia | lia].
  unfold rbn2_Bx. rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia). reflexivity. }
{ awr_ok_tac. }
assert (KEEP1 : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a)
  by (apply (rbn2_keep_nowr _ _ (w_H W) memc (ms_mem ms) HFr); unfold rbn2_ssB; cbn [ss_mem add_cond];
      repeat constructor; cbn; lia).
pose proof HG as HG0. clear HF HFr HG.
lazymatch goal with HS : st_ok_pi _ _ ?E1 _ _ |- _ =>
  assert (F32 : ew E1 32 = Z_to_bv 64 c1) by (rewrite ?ew_ewset_other by lia; exact E32);
  assert (F20 : ew E1 20 = Z_to_bv 64 P) by (rewrite ?ew_ewset_other by lia; exact E20);
  assert (F21 : ew E1 21 = Z_to_bv 64 (P + 1)) by (rewrite ?ew_ewset_other by lia; exact E21) end.
psrr_branch_tok RUN BR HS SHOK rbn2_span.
- rewrite branch_eq_U, (U_atom _ 32 c1 F32), U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
  idtac.
  paj_run_to_tok RUNTO HS HJ SHOK rbn2_span (AF_both3_reac_box_name + RBN_L2X).
  { awr_ok_tac. }
  rbn2_fin c1 HAE E32 E20 E21 KEEP1 HG0.
  unfold cfg_at, w64. rewrite (proj2 (Z.eqb_eq c1 0) Hc0), <- Z.add_assoc. reflexivity.
- rewrite branch_eq_U, (U_atom _ 32 c1 F32), U_lit in Hc0 by lia. apply Z.eqb_neq in Hc0.
  idtac.
  paj_run_to_tok RUNTO HS HJ SHOK rbn2_span (AF_both3_reac_box_name + RBN_L2).
  { awr_ok_tac. }
  rbn2_fin c1 HAE E32 E20 E21 KEEP1 HG0.
  unfold cfg_at, w64. rewrite (proj2 (Z.eqb_neq c1 0) Hc0), <- Z.add_assoc. reflexivity.
Qed.
Lemma rbn2_cl2_cs : forall r : Z, 0 <= r < 32 -> ~ In r rbn_cl2 -> r = 0 \/ acallee_saved r.
Proof.
intros r Hr Hn.
assert (H32 : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/
  r = 10 \/ r = 11 \/ r = 12 \/ r = 13 \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17 \/ r = 18 \/ r = 19 \/
  r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 28 \/ r = 29 \/
  r = 30 \/ r = 31) by lia.
repeat (destruct H32 as [-> | H32]); try (subst r);
  first [ solve [left; reflexivity]
        | solve [right; unfold acallee_saved; lia]
        | solve [exfalso; apply Hn; unfold rbn_cl2, rbn_clc; cbn [app In];
                 repeat first [ solve [left; reflexivity] | right ]] ].
Qed.
Lemma rbn2_sh_kept : forall lyc Sc (W : world SEGS) memc (W1 : world SEGS) mem1 sp R D (Er : Z -> Prop),
  tsb_ch_kept B lyc Sc W memc W1 mem1 sp Er ->
  (forall a, Er a -> R + 16 <= a < R + 28 \/ D <= a < D + 24) ->
  alloc_ceiling <= sp - TSB_CH_STK -> sp <= R -> in_app D 24 ->
  forall s, SHADOW_OFF <= s < kHighShadowEnd -> aview SEGS (w_H W1) mem1 s = aview SEGS (w_H W) memc s.
Proof.
intros lyc Sc W memc W1 mem1 sp R D Er HK HEr Hceil HR Happ s Hs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
pose proof Happ as (Hlo & Hhi). pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR. unfold YG0f.ASAN_CEIL in *.
unfold SHADOW_OFF, kHighShadowEnd, kLowShadowBeg, kHighMemBeg in *.
apply (proj1 HK s); [lia | lia|].
intros HE. destruct (HEr s HE) as [Hc | Hc]; lia.
Qed.
Definition rbn2_pc (s : list Z) : Z := match s with [] => RBN_L2X | _ => RBN_L2 end.
Definition rbn2_n1 (n0 : Z) : Z := Z.min 23 (n0 + 1).
Definition rbn2_ov1 (n0 ov0 : Z) : Z := if 23 <=? n0 then 1 else ov0.
Definition rbn2_wr1 (n0 c : Z) : list Z := if n0 <? 23 then [c] else [].
Definition rbn2_ipost (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc k
  (regs : bvmap 5 word) (P D n0 ov0 c : Z) (s : list Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists lyc2 Sc2 regs2 mem2 md2,
    c2 = cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + rbn2_pc s) regs2 mem2 md2 /\
    rbn_lcx B STK sp0 FP ly S W0 mem0 md0 own lyc2 Sc2 W2 mem2 md2 k regs2 /\
    spZ regs2 = spZ regs /\
    frames Sc2 = frames Sc /\ ablocks B lyc2 Sc2 = ablocks B lyc Sc /\
    (forall cid pos, frame_addr lyc2 cid pos = frame_addr lyc cid pos) /\
    rbn_lrec B STK sp0 FP ly S own lyc2 Sc2 W2 mem2 (spZ regs) (spZ regs + 152) D 24
      (rbn2_n1 n0) (rbn2_ov1 n0 ov0) /\
    rbn_lbuf B STK sp0 FP ly S own lyc2 Sc2 W2 mem2 (spZ regs) (spZ regs + 152) D 24 /\
    rbn_lsrc W2 mem2 (P + 1) (s ++ [0]) /\
    rbn_keep_regs regs regs2 rbn_cl2 /\
    getr regs2 10 = w64 (hd 0 (s ++ [0])) /\ getr regs2 20 = w64 (P + 1) /\ getr regs2 21 = w64 (P + 2) /\
    garr8 SEGS (mrestrict (w_H W2) mem2) (D + n0) (rbn2_wr1 n0 c) /\
    tsb_ch_kept B lyc Sc W memc W2 mem2 (spZ regs)
      (fun a => spZ regs + 152 + 16 <= a < spZ regs + 152 + 28 \/
                D + n0 <= a < D + n0 + Z.of_nat (length (rbn2_wr1 n0 c))).
Ltac rbn2_nin := let HH := fresh "HH" in intros HH; unfold rbn_cl2, rbn_clc in HH; cbn [app In] in HH;
  repeat (destruct HH as [HH | HH]; [lia |]); exact HH.
Ltac rbn2_inl := unfold rbn_cl2, rbn_clc; cbn [app In];
  repeat first [ solve [left; reflexivity] | right ].
Ltac rbn2_wrl := unfold rbn2_wr1;
  match goal with |- context [if ?b then _ else _] =>
    match b with (?x <? ?y)%Z => destruct (Z.ltb_spec x y) end end;
  cbn [length Z.of_nat]; lia.
Lemma rbn2_iter : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) P D n0 ov0 c (s : list Z),
  rbn_lcx B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 152) D 24 n0 ov0 ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 152) D 24 ->
  Forall (fun x => 0 < x < 256) (c :: s) -> rbn_lsrc W memc P ((c :: s) ++ [0]) ->
  rbn_lsep (spZ regs) (spZ regs + 152) D 24 P (Z.of_nat (length (c :: s)) + 1) ->
  0 <= n0 <= 23 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 10 = w64 c -> getr regs 20 = w64 P -> getr regs 21 = w64 (P + 1) -> getr regs 24 = w64 (-1) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L2) regs memc mdc)
    (rbn2_ipost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs P D n0 ov0 c s).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 c s
  HX HR HD Hall HSRC HSEP Hn0 Hov0 H10 H20 H21 H24.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR. unfold YG0f.ASAN_CEIL in CR.
pose proof HX as (HJ & HROD & H3 & H4 & H9 & H22 & Hal & Hlo & Hhi).
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof HR as (HR0 & HR8 & HR63 & HRam & HRimg & HRside & HD64 & Hcap64 & Hn0a & Hn64 & Hov &
  VR0 & VR8 & VR16 & VR24 & HRra & HRsv & HRwr).
pose proof HD as (HDpos & HD63 & HDapp & HDam & HDimg & HDside & HDR & HDra & HDsv & HDwr).
pose proof HSEP as (Hsep1 & Hsep2 & Hsep3).
pose proof HSRC as (HGs & HP0 & HP63 & HP47 & HRAs).
assert (Hlc : Z.of_nat (length (c :: s)) = Z.of_nat (length s) + 1) by (cbn [length]; lia).
pose proof (Zle_0_nat (length s)) as Hls.
assert (Hc : 0 < c < 256) by (inversion Hall; assumption).
assert (Hceil2 : alloc_ceiling <= spZ regs - TSB_CH_STK) by (unfold TSB_CH_STK, ESTACK in *; lia).
assert (Hlen : Z.of_nat (length ((c :: s) ++ [0])) = Z.of_nat (length s) + 2)
  by (rewrite length_app; cbn [length]; lia).
assert (HRam2 : spZ regs + 152 + 28 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HRam; lia).
assert (HDam2 : D + 24 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HDam; lia).
remember (hd 0 (s ++ [0])) as c1 eqn:Hc1e.
assert (Vc1 : val_mem SEGS (mrestrict (w_H W) memc) (P + 1) 1 c1 /\ 0 <= c1 < 256).
{ destruct (garr8_nthZ SEGS (mrestrict (w_H W) memc) P ((c :: s) ++ [0]) 1 HGs ltac:(lia) ltac:(lia))
    as (Hv1 & Hr1).
  replace (nth (Z.to_nat 1) ((c :: s) ++ [0]) 0) with c1 in Hv1, Hr1 by
    (rewrite Hc1e; cbn [app nth Z.to_nat Pos.to_nat Pos.iter_op]; destruct s; reflexivity).
  split; assumption. }
destruct Vc1 as (Vc1 & Rc1).
eapply SRr_bind;
  [exact (rbn2_call fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 c HX HR HD
            ltac:(lia) H10 ltac:(lia))|].
cbv beta. intros W1 cc1 Hle1 (lyc1 & Sc1 & regs1 & mem1 & md1 & -> & HJ1 & Hfr1 & Hbl1 & HP1 & Hcase).
assert (KR1 : forall (z : Z) (r : bv 5), acallee_saved z -> Z_to_bv 5 z = r -> getr regs1 r = getr regs r)
  by (intros z r Hcs <-; exact (HP1 z Hcs)).
assert (Q22 : getr regs1 22 = w64 SHADOW_OFF)
  by (rewrite (KR1 22 22%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)); exact H22).
assert (Q20 : getr regs1 20 = w64 P)
  by (rewrite (KR1 20 20%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)); exact H20).
assert (Q21 : getr regs1 21 = w64 (P + 1))
  by (rewrite (KR1 21 21%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)); exact H21).
assert (Q24 : getr regs1 24 = w64 (-1))
  by (rewrite (KR1 24 24%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)); exact H24).
assert (HKc : tsb_ch_kept B lyc Sc W memc W1 mem1 (spZ regs)
  (fun a => spZ regs + 152 + 16 <= a < spZ regs + 152 + 28 \/
            D + n0 <= a < D + n0 + Z.of_nat (length (rbn2_wr1 n0 c)))).
{ unfold rbn2_wr1. destruct Hcase as [(Hge & V24 & HK) | (Hlt & V16 & Vb & HK)].
  - rewrite (proj2 (Z.ltb_ge n0 23) ltac:(lia)). cbn [length Z.of_nat].
    eapply rbn2_kept_mono; [|exact HK]. intros a Ha. cbv beta in Ha |- *. left. lia.
  - rewrite (proj2 (Z.ltb_lt n0 23) ltac:(lia)). cbn [length Z.of_nat].
    eapply rbn2_kept_mono; [|exact HK]. intros a Ha. cbv beta in Ha |- *.
    destruct Ha as [Ha | Ha]; [left; lia | right; lia]. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
  ~ (spZ regs + 152 + 16 <= a < spZ regs + 152 + 28) ->
  ~ (D + n0 <= a < D + n0 + Z.of_nat (length (rbn2_wr1 n0 c))) ->
  ~ (spZ regs - TSB_CH_STK <= a < spZ regs) ->
  aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) memc a).
{ intros a Ha Na1 Na2 Na3. apply (proj1 HKc a Ha Na3). intros [X | X]; [exact (Na1 X) | exact (Na2 X)]. }
assert (KSH : forall sx, SHADOW_OFF <= sx < kHighShadowEnd -> aview SEGS (w_H W1) mem1 sx = aview SEGS (w_H W) memc sx).
{ apply (rbn2_sh_kept lyc Sc W memc W1 mem1 (spZ regs) (spZ regs + 152) D _ HKc);
    [intros a [Ha | Ha]; [left; lia|]; right; unfold rbn2_wr1 in Ha;
     destruct (n0 <? 23); cbn [length Z.of_nat] in Ha; lia
    | exact Hceil2 | lia | exact HDapp]. }
assert (HRA1 : range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF (P + 1) 1).
{ apply (rbn2_ra_keep _ _ (P + 1) 1 KSH ltac:(lia) ltac:(lia)).
  apply (range_addressable_sub _ _ P (Z.of_nat (length ((c :: s) ++ [0]))) (P + 1) 1 HRAs); lia. }
assert (Vc1' : val_mem SEGS (mrestrict (w_H W1) mem1) (P + 1) 1 c1).
{ apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W1) memc mem1 (P + 1) 1 c1); [|exact Vc1].
  intros x Hx. cbn [Z.of_nat] in Hx. apply KEEP; [lia | lia | rbn2_wrl | lia]. }
eapply SRr_mono.
{ exact (rbn2_ret fq STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 mem1 md1 k regs1 P c1
           HJ1 Q22 Q20 Q21 Q24 ltac:(lia) Vc1' Rc1 HRA1). }
cbv beta. intros W2 c2 Hle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & KEEPr & HGr & HKr & N10 & N20 & N21).
assert (HKEEP : rbn_keep_regs regs regs2 rbn_cl2).
{ intros r Hr Hnin.
  rewrite (HKr r Hr ltac:(intros ->; apply Hnin; rbn2_inl) ltac:(intros ->; apply Hnin; rbn2_inl)
                  ltac:(intros ->; apply Hnin; rbn2_inl) ltac:(intros ->; apply Hnin; rbn2_inl)).
  destruct (rbn2_cl2_cs r Hr Hnin) as [-> | Hcs].
  - replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !getr_zero. reflexivity.
  - exact (HP1 r Hcs). }
assert (KR : forall (z : Z) (r : bv 5), 0 <= z < 32 -> ~ In z rbn_cl2 -> Z_to_bv 5 z = r ->
  getr regs2 r = getr regs r) by (intros z r Hz Hn <-; exact (HKEEP z Hz Hn)).
assert (Esp : spZ regs2 = spZ regs)
  by (unfold spZ; rewrite (KR 2 2%bv ltac:(lia) ltac:(rbn2_nin) ltac:(apply bv_eq; vm_compute; reflexivity)); reflexivity).
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (spZ regs + 152 + 16 <= a < spZ regs + 152 + 28) ->
  ~ (D + n0 <= a < D + n0 + Z.of_nat (length (rbn2_wr1 n0 c))) ->
  ~ (spZ regs - TSB_CH_STK <= a < spZ regs) ->
  aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W) memc a)
  by (intros a Ha Na1 Na2 Na3; rewrite KEEPr; exact (KEEP a Ha Na1 Na2 Na3)).
assert (KSH2 : forall sx, SHADOW_OFF <= sx < kHighShadowEnd -> aview SEGS (w_H W1) mem2 sx = aview SEGS (w_H W) memc sx)
  by (intros sx Hsx; rewrite KEEPr; exact (KSH sx Hsx)).
assert (HK2 : tsb_ch_kept B lyc Sc W memc W1 mem2 (spZ regs)
  (fun a => spZ regs + 152 + 16 <= a < spZ regs + 152 + 28 \/
            D + n0 <= a < D + n0 + Z.of_nat (length (rbn2_wr1 n0 c))))
  by (apply (rbn2_kept_post lyc Sc W memc W1 mem1 mem2); [exact KEEPr | exact HGr | exact HKc]).
assert (HFA : forall cid pos, frame_addr lyc1 cid pos = frame_addr lyc cid pos)
  by exact (rbn2_lyF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc lyc1 Sc1 W1 mem1 md1 k k HJ HJ1).
exists lyc1, Sc1, regs2, mem2, md2.
split.
{ unfold rbn2_pc. destruct s as [|x s'].
  - rewrite Hc1e. cbn [hd app]. reflexivity.
  - assert (Hx : 0 < x < 256) by (inversion Hall as [|? ? ? Hy]; inversion Hy; assumption).
    rewrite Hc1e. cbn [hd app]. rewrite (proj2 (Z.eqb_neq x 0) ltac:(lia)). reflexivity. }
assert (HROD2 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) mem2))
  by exact (rbn2_rod_kept lyc Sc W memc W1 mem2 (spZ regs) _ HK2 HROD).
split.
{ split; [exact HJ2|]. split; [exact HROD2|].
  split; [rewrite (KR 3 3%bv ltac:(lia) ltac:(rbn2_nin) ltac:(apply bv_eq; vm_compute; reflexivity)); exact H3|].
  split; [rewrite (KR 4 4%bv ltac:(lia) ltac:(rbn2_nin) ltac:(apply bv_eq; vm_compute; reflexivity)); exact H4|].
  split; [rewrite (KR 9 9%bv ltac:(lia) ltac:(rbn2_nin) ltac:(apply bv_eq; vm_compute; reflexivity)),
                  (KR 2 2%bv ltac:(lia) ltac:(rbn2_nin) ltac:(apply bv_eq; vm_compute; reflexivity)); exact H9|].
  split; [rewrite (KR 22 22%bv ltac:(lia) ltac:(rbn2_nin) ltac:(apply bv_eq; vm_compute; reflexivity)); exact H22|].
  rewrite Esp. split; [exact Hal | split; [exact Hlo | exact Hhi]]. }
split; [exact Esp|].
split; [exact Hfr1|]. split; [exact Hbl1|]. split; [exact HFA|].
assert (VN1 : val_mem SEGS (mrestrict (w_H W1) mem2) (spZ regs + 152 + 16) 8 (rbn2_n1 n0) /\
              val_mem SEGS (mrestrict (w_H W1) mem2) (spZ regs + 152 + 24) 4 (rbn2_ov1 n0 ov0)).
{ unfold rbn2_n1, rbn2_ov1.
  destruct Hcase as [(Hge & V24 & HK) | (Hlt & V16 & Vb & HK)].
  - replace (Z.min 23 (n0 + 1)) with 23 by lia. rewrite (proj2 (Z.leb_le 23 n0) ltac:(lia)).
    split.
    + apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W1) memc mem2 _ 8 23).
      * intros x Hx. cbn [Z.of_nat] in Hx. rewrite KEEPr.
        exact (proj1 HK x ltac:(lia) ltac:(lia) ltac:(intros HH; cbv beta in HH; lia)).
      * replace 23 with n0 by lia. exact VR16.
    + apply (val_mem_aview_kept_x SEGS (w_H W1) (w_H W1) mem1 mem2 _ 4 1); [intros x _; apply KEEPr | exact V24].
  - replace (Z.min 23 (n0 + 1)) with (n0 + 1) by lia. rewrite (proj2 (Z.leb_gt 23 n0) ltac:(lia)).
    split.
    + apply (val_mem_aview_kept_x SEGS (w_H W1) (w_H W1) mem1 mem2 _ 8 (n0 + 1)); [intros x _; apply KEEPr|].
      replace (spZ regs + 152 + 16) with (spZ regs + 152 + 16) by lia. exact V16.
    + apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W1) memc mem2 _ 4 ov0).
      * intros x Hx. cbn [Z.of_nat] in Hx. rewrite KEEPr.
        exact (proj1 HK x ltac:(lia) ltac:(lia) ltac:(intros HH; cbv beta in HH; lia)).
      * exact VR24. }
destruct VN1 as (VN16 & VN24).
assert (HAPR : forall a, spZ regs + 152 + 16 <= a < spZ regs + 152 + 28 -> apresent (w_H W1) mem2 a).
{ intros a Ha. apply rbn2_apresent_of_some; [lia | exact (rbn2_off_img _ 28 a HRimg ltac:(lia))|].
  destruct (Z_lt_le_dec a (spZ regs + 152 + 24)) as [Hlt | Hge].
  - replace a with (spZ regs + 152 + 16 + (a - (spZ regs + 152 + 16))) by lia.
    apply (rbn2_vm_some _ _ _ 8 _ _ VN16). cbn [Z.of_nat]. lia.
  - replace a with (spZ regs + 152 + 24 + (a - (spZ regs + 152 + 24))) by lia.
    apply (rbn2_vm_some _ _ _ 4 _ _ VN24). cbn [Z.of_nat]. lia. }
split.
{ split; [exact HR0|]. split; [exact HR8|]. split; [exact HR63|]. split; [exact HRam|].
  split; [exact HRimg|]. split; [exact HRside|].
  split; [exact HD64|]. split; [exact Hcap64|].
  split; [unfold rbn2_n1; lia|]. split; [unfold rbn2_n1; lia|].
  split; [unfold rbn2_ov1; destruct (23 <=? n0); lia|].
  split.
  { apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W1) memc mem2 _ 8 D); [|exact VR0].
    intros x Hx. cbn [Z.of_nat] in Hx. apply KEEP2; [lia | lia | rbn2_wrl | lia]. }
  split.
  { apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W1) memc mem2 _ 8 24); [|exact VR8].
    intros x Hx. cbn [Z.of_nat] in Hx. apply KEEP2; [lia | lia | rbn2_wrl | lia]. }
  split; [exact VN16|]. split; [exact VN24|].
  split; [exact (rbn2_ra_keep _ _ (spZ regs + 152) 28 KSH2 ltac:(lia) ltac:(lia) HRra)|].
  split; [exact (rbn2_shv_keep _ _ (spZ regs + 152) 28 KSH2 ltac:(lia) ltac:(lia) ltac:(lia) HRsv)|].
  intros a Ha. split; [|exact (HAPR a Ha)].
  exact (rbn2_awr_tr STK sp0 FP (ablocks B ly S) own lyc Sc lyc1 Sc1 a HFA Hbl1 (proj1 (HRwr a Ha))). }
split.
{ split; [exact HDpos|]. split; [exact HD63|]. split; [exact HDapp|]. split; [exact HDam|].
  split; [exact HDimg|]. split; [exact HDside|]. split; [exact HDR|].
  split; [exact (rbn2_ra_keep _ _ D 24 KSH2 ltac:(lia) ltac:(lia) HDra)|].
  split; [exact (rbn2_shv_keep _ _ D 24 KSH2 ltac:(lia) ltac:(lia) ltac:(lia) HDsv)|].
  intros a Ha. split;
    [exact (rbn2_awr_tr STK sp0 FP (ablocks B ly S) own lyc Sc lyc1 Sc1 a HFA Hbl1 (proj1 (HDwr a Ha)))|].
  apply rbn2_apresent_of_some; [lia | exact (rbn2_off_img D 24 a HDimg Ha)|].
  destruct (Z.eq_dec a (D + n0)) as [-> | Hne].
  - destruct Hcase as [(Hge & V24 & HK) | (Hlt & V16 & Vb & HK)].
    + rewrite KEEP2; [| lia | lia | rbn2_wrl | lia].
      apply (aview_some_of_apresent SEGS). exact (proj2 (HDwr (D + n0) ltac:(lia))).
    + rewrite KEEPr.
      replace (D + n0) with (D + n0 + 0) by lia.
      apply (rbn2_vm_some _ _ _ 1 _ _ Vb). cbn [Z.of_nat]. lia.
  - rewrite KEEP2; [| lia | lia | rbn2_wrl | lia].
    apply (aview_some_of_apresent SEGS). exact (proj2 (HDwr a Ha)). }
split.
{ split.
  { apply (garr8_aview_kept SEGS (w_H W) (w_H W1) memc mem2 (P + 1) (s ++ [0])).
    - intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
      apply KEEP2; [lia | lia | rbn2_wrl | lia].
    - change ((c :: s) ++ [0]) with (c :: (s ++ [0])) in HGs.
      pose proof (proj1 (garr8_app SEGS (mrestrict (w_H W) memc) P [c] (s ++ [0]))
        ltac:(cbn [app]; exact HGs)) as (_ & HG2).
      cbn [length Z.of_nat] in HG2. exact HG2. }
  split; [lia|]. split; [rewrite length_app; cbn [length]; lia|].
  split; [rewrite length_app; cbn [length]; lia|].
  apply (rbn2_ra_keep _ _ (P + 1) (Z.of_nat (length (s ++ [0]))) KSH2 ltac:(lia)
    ltac:(rewrite length_app; cbn [length]; lia)).
  apply (range_addressable_sub _ _ P (Z.of_nat (length ((c :: s) ++ [0]))) _ _ HRAs);
    [lia | rewrite !length_app; cbn [length]; lia]. }
split; [exact HKEEP|].
split; [rewrite <- Hc1e; exact N10|]. split; [exact N20|]. split; [exact N21|].
split.
{ unfold rbn2_wr1. destruct Hcase as [(Hge & V24 & HK) | (Hlt & V16 & Vb & HK)].
  - rewrite (proj2 (Z.ltb_ge n0 23) ltac:(lia)). apply garr8_nil.
  - rewrite (proj2 (Z.ltb_lt n0 23) ltac:(lia)).
    apply garr8_cons_x; [|lia|apply garr8_nil].
    apply (val_mem_aview_kept_x SEGS (w_H W1) (w_H W1) mem1 mem2 (D + n0) 1 c);
      [intros x _; apply KEEPr | exact Vb]. }
exact HK2.
Qed.
Lemma rbn2_gen : forall (s : list Z) (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) memc mdc k (regs : bvmap 5 word) P D n0 ov0,
  rbn_L2_run B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    (Z.min 23 (n0 + Z.of_nat (length s)))
    (if 23 <? n0 + Z.of_nat (length s) then 1 else ov0)
    (firstn (Z.to_nat (23 - n0)) s).
Proof.
induction s as [|c r IH]; intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0;
  unfold rbn_L2_run; intros HX HR HD Hne Hall HSRC HSEP Hn0 Hov0 H10 H20 H21 H24;
  [exfalso; exact (Hne eq_refl)|].
cbn [hd] in H10.
pose proof (Zle_0_nat (length r)) as Hlr.
assert (Hlc : Z.of_nat (length (c :: r)) = Z.of_nat (length r) + 1) by (cbn [length]; lia).
pose proof HSEP as (Hsep1 & Hsep2 & Hsep3).
eapply SRr_bind.
{ exact (rbn2_iter fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 c r
           HX HR HD Hall HSRC HSEP Hn0 Hov0 H10 H20 H21 H24). }
cbv beta. intros W2 c2 Hle2
  (lycA & ScA & regsA & memA & mdA & -> & HXA & EspA & HfrA & HblA & HFA & HRA & HDA & HSA & HKA &
   NA10 & NA20 & NA21 & HGA & HKEA).
assert (HNA24 : getr regsA 24 = w64 (-1)).
{ rewrite <- H24. replace (24%bv : bv 5) with (Z_to_bv 5 24) by (apply bv_eq; vm_compute; reflexivity).
  exact (HKA 24 ltac:(lia) ltac:(rbn2_nin)). }
destruct r as [|c2 r2].
- cbn [length] in *. change (Z.of_nat 1) with 1 in *. change (Z.of_nat 0) with 0 in *.
  replace (Z.min 23 (n0 + 1)) with (rbn2_n1 n0) by (unfold rbn2_n1; lia).
  replace (if 23 <? n0 + 1 then 1 else ov0) with (rbn2_ov1 n0 ov0)
    by (unfold rbn2_ov1; destruct (Z.ltb_spec 23 (n0 + 1)), (Z.leb_spec 23 n0); lia).
  assert (Ewr : firstn (Z.to_nat (23 - n0)) [c] = rbn2_wr1 n0 c).
  { unfold rbn2_wr1. destruct (Z.ltb_spec n0 23).
    - replace (23 - n0) with (Z.succ (22 - n0)) by lia.
      rewrite Z2Nat.inj_succ by lia. cbn [firstn]. rewrite firstn_nil. reflexivity.
    - replace (23 - n0) with 0 by lia. cbn [Z.to_nat firstn]. reflexivity. }
  rewrite Ewr.
  apply SRr_ret. exists lycA, ScA, regsA, memA, mdA.
  pose proof HXA as (HJA & HRODA & _).
  pose proof HRA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VA16 & VA24 & _).
  split; [reflexivity|]. split; [exact HJA|]. split; [exact HfrA|]. split; [exact HblA|].
  split; [exact HRODA|]. split; [exact HKA|].
  split; [exact VA16|]. split; [exact VA24|]. split; [exact HGA | exact HKEA].
- assert (Hne2 : c2 :: r2 <> []) by discriminate.
  assert (Hall2 : Forall (fun x => 0 < x < 256) (c2 :: r2)) by (inversion Hall; assumption).
  eapply SRr_mono.
  { change (rbn2_pc (c2 :: r2)) with RBN_L2.
    apply (IH fq STK sp0 FP ly S W0 mem0 md0 own lycA ScA W2 memA mdA k regsA (P + 1) D
             (rbn2_n1 n0) (rbn2_ov1 n0 ov0)).
    - exact HXA.
    - rewrite EspA. exact HRA.
    - rewrite EspA. exact HDA.
    - exact Hne2.
    - exact Hall2.
    - exact HSA.
    - rewrite EspA. cbn [length] in Hsep1, Hsep2, Hsep3 |- *.
      split; [lia|]. split; [lia | lia].
    - unfold rbn2_n1; lia.
    - unfold rbn2_ov1; destruct (23 <=? n0); lia.
    - exact NA10.
    - exact NA20.
    - rewrite NA21. unfold w64. f_equal. lia.
    - exact HNA24. }
  cbv beta. intros W3 c3 Hle3 (lycB & ScB & regsB & memB & mdB & -> & HJB & HfrB & HblB & HRODB & HKB &
    VB16 & VB24 & HGB & HKEB).
  rewrite EspA in VB16, VB24. rewrite ?EspA in HKEB.
  exists lycB, ScB, regsB, memB, mdB.
  split; [reflexivity|]. split; [exact HJB|].
  split; [rewrite HfrB; exact HfrA|]. split; [rewrite HblB; exact HblA|].
  split; [exact HRODB|].
  split.
  { intros rr Hrr Hnin. rewrite (HKB rr Hrr Hnin). exact (HKA rr Hrr Hnin). }
  assert (Hmin : Z.min 23 (rbn2_n1 n0 + Z.of_nat (length (c2 :: r2))) =
                 Z.min 23 (n0 + Z.of_nat (length (c :: c2 :: r2))))
    by (unfold rbn2_n1; cbn [length] in *; lia).
  assert (Hovf : (if 23 <? rbn2_n1 n0 + Z.of_nat (length (c2 :: r2)) then 1 else rbn2_ov1 n0 ov0) =
                 (if 23 <? n0 + Z.of_nat (length (c :: c2 :: r2)) then 1 else ov0)).
  { unfold rbn2_n1, rbn2_ov1.
    repeat match goal with
    | |- context [if (?x <? ?y)%Z then _ else _] => destruct (Z.ltb_spec x y)
    | |- context [if (?x <=? ?y)%Z then _ else _] => destruct (Z.leb_spec x y)
    end; try reflexivity; lia. }
  rewrite Hmin in VB16. rewrite Hovf in VB24.
  split; [exact VB16|]. split; [exact VB24|].
  assert (Hwr : firstn (Z.to_nat (23 - n0)) (c :: c2 :: r2) =
                rbn2_wr1 n0 c ++ firstn (Z.to_nat (23 - rbn2_n1 n0)) (c2 :: r2)).
  { unfold rbn2_wr1, rbn2_n1. destruct (Z.ltb_spec n0 23).
    - replace (Z.min 23 (n0 + 1)) with (n0 + 1) by lia.
      replace (23 - n0) with (Z.succ (23 - (n0 + 1))) by lia.
      rewrite Z2Nat.inj_succ by lia. cbn [firstn app]. reflexivity.
    - replace (Z.min 23 (n0 + 1)) with 23 by lia.
      replace (23 - n0) with 0 by lia. replace (23 - 23) with 0 by lia.
      cbn [Z.to_nat firstn app]. reflexivity. }
  assert (HD1 : D + rbn2_n1 n0 = D + n0 + Z.of_nat (length (rbn2_wr1 n0 c)))
    by (unfold rbn2_wr1, rbn2_n1; destruct (Z.ltb_spec n0 23); cbn [length Z.of_nat]; lia).
  rewrite Hwr. rewrite HD1 in HGB, HKEB.
  split.
  { apply garr8_app. split.
    - apply (garr8_aview_kept SEGS (w_H W2) (w_H W3) memA memB (D + n0) (rbn2_wr1 n0 c)); [|exact HGA].
      intros x Hx. apply (proj1 HKEB x).
      + pose proof HDA as (HDposA & HD63A & _). unfold rbn2_wr1 in Hx; destruct (Z.ltb_spec n0 23);
          cbn [length Z.of_nat] in Hx; lia.
      + pose proof HDA as (_ & _ & _ & _ & _ & HDsideA & _).
        unfold rbn2_wr1 in Hx; destruct (Z.ltb_spec n0 23); cbn [length Z.of_nat] in Hx; lia.
      + intros [HH | HH].
        * pose proof HDA as (_ & _ & _ & _ & _ & _ & HDRA & _).
          unfold rbn2_wr1 in Hx; destruct (Z.ltb_spec n0 23); cbn [length Z.of_nat] in Hx; lia.
        * unfold rbn2_wr1 in Hx, HH; destruct (Z.ltb_spec n0 23);
            cbn [length Z.of_nat] in Hx, HH; lia.
    - exact HGB. }
  eapply rbn2_kept_mono; [|exact (rbn2_kept_trans lyc Sc W memc lycA ScA W2 memA W3 memB (spZ regs) _ _
    HFA HfrA HblA HKEA HKEB)].
  intros a Ha. cbv beta in Ha |- *. rewrite length_app.
  destruct Ha as [[HH | HH] | [HH | HH]]; [left; lia | right; lia | left; lia | right; lia].
Qed.
Theorem rbn_l2_fits : rbn_L2_fits B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s Hle.
pose proof (rbn2_gen s fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0) as Hg.
replace (Z.min 23 (n0 + Z.of_nat (length s))) with (n0 + Z.of_nat (length s)) in Hg by lia.
rewrite (proj2 (Z.ltb_ge 23 (n0 + Z.of_nat (length s))) ltac:(lia)) in Hg.
replace (firstn (Z.to_nat (23 - n0)) s) with s in Hg
  by (symmetry; apply firstn_all2; apply (proj2 (Nat2Z.inj_le (length s) (Z.to_nat (23 - n0))));
      rewrite Z2Nat.id by lia; lia).
exact Hg.
Qed.
Theorem rbn_l2_ovf : rbn_L2_ovf B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s Hlt.
pose proof (rbn2_gen s fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0) as Hg.
replace (Z.min 23 (n0 + Z.of_nat (length s))) with 23 in Hg by lia.
rewrite (proj2 (Z.ltb_lt 23 (n0 + Z.of_nat (length s))) ltac:(lia)) in Hg.
exact Hg.
Qed.
End h.
End f.
End d.

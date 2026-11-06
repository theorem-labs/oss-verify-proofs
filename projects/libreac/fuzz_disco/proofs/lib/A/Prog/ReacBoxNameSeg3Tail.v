(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACgc.v:176-178;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACjv.v:45-51, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:154-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg3.v, with its module paths, module names, addresses and numbers changed; 1284 of its 1537 lines of code are new or changed and 2287 lines of the source are left out. *)
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
SbDec DiscoRo ReacBoxName ReacBoxNameCut ReacBoxNameSeg3Mid ReacBoxNameSeg3Head.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition RBN_Q2 : Z := 0x284.
Definition RBN_Q3 : Z := 0x294.
Definition RBN_Q4 : Z := 0x2a4.
Definition RBN_Q5 : Z := 0x2c0.
Definition RBN_Q6 : Z := 0x2d0.
Lemma r3t_sh_w4 : forall j, j <> 4%nat ->
  nth j (rbn_sh true false false false) 0 = nth j (rbn_sh false false false false) 0.
Proof. intros j Hj. do 5 (destruct j as [|j]; [try reflexivity; lia|]). reflexivity. Qed.
Lemma r3t_sh_nb : forall j, (j < 8 \/ 11 <= j)%nat ->
  nth j (rbn_sh true true false false) 0 = nth j (rbn_sh true false false false) 0.
Proof. intros j Hj. do 11 (destruct j as [|j]; [try reflexivity; lia|]). reflexivity. Qed.
Lemma r3t_sh_nb0 : forall j, (8 <= j < 11)%nat -> nth j (rbn_sh true true false false) 0 = 0.
Proof. intros j Hj. do 11 (destruct j as [|j]; [try reflexivity; lia|]). lia. Qed.
Lemma r3t_dec2 : forall v, bn_ok v = true ->
  sb_dec_c.sb_dec_D v 2 = bn_dec v 2 /\ length (bn_dec v 2) = 2%nat /\ 0 <= v <= 40.
Proof.
intros v Hv. apply bn_ok_in in Hv. vm_compute in Hv.
repeat (destruct Hv as [<- | Hv]; [split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | lia]]|]).
destruct Hv.
Qed.
Lemma r3t_args : forall i o name name_len token token_len display display_len,
  reac_box_name_c.bn_args_ok name name_len token token_len display display_len i o = true ->
  bn_ok i = true /\ bn_ok o = true.
Proof.
intros i o name name_len token token_len display display_len HA. unfold reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [_ Hi].
split; assumption.
Qed.
Lemma r3t_pres_get : forall (regs regs2 : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r.
Proof. intros regs regs2 r HP Hr. specialize (HP _ Hr). rewrite !Z_to_bv_bv_unsigned in HP. exact HP. Qed.
Ltac r3t_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
    change (bv_unsigned x) with v end; lia.
Lemma r3t_stem_ne : forall s f, bn_stem f s <> [].
Proof.
intros s f. unfold bn_stem. destruct s as [|c l]; [|discriminate].
unfold bn_STEM. destruct (f =? 1); [discriminate|]. destruct (f =? 2); [discriminate|].
destruct (f =? 3); discriminate.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Definition r3t_cells2 (X : rbn_in) (pos n : Z) : list (Z * nat * Z) :=
  [(rbn_A X + 8, 8%nat, ri_display X); (rbn_A X + 56, 8%nat, ri_display_len X);
   (rbn_A X + 64, 8%nat, ri_name_len X); (rbn_A X + 80, 8%nat, ri_i X); (rbn_A X + 88, 8%nat, ri_o X);
   (rbn_A X + 152, 8%nat, rbn_F X pos + 32); (rbn_A X + 160, 8%nat, 5); (rbn_A X + 168, 8%nat, n);
   (rbn_A X + 176, 4%nat, 0)].
Definition r3t_cells5 (X : rbn_in) (pos : Z) : list (Z * nat * Z) :=
  (rbn_A X + 32, 8%nat, ri_token_len X) :: r3t_cells2 X pos 4.
Lemma r3t_cells_kept : forall H H' (m m' : word -> option byte) l,
  (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros H H' m m' l. induction l as [|[[a n] v] t IH]; cbn [rbn_cells]; intros HE HC; [exact I|].
destruct HC as [H1 H2]. split.
- apply (val_mem_kept SEGS H H' m m'); [|exact H1]. intros k Hk. exact (HE a n v k (or_introl eq_refl) Hk).
- apply IH; [|exact H2]. intros a' n' v' k Hin Hk. exact (HE a' n' v' k (or_intror Hin) Hk).
Qed.
Lemma r3t_garr8_kept : forall H H' (m m' : word -> option byte) base l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS H' m' (base + j) = aview SEGS H m (base + j)) ->
  garr8 SEGS (mrestrict H m) base l -> garr8 SEGS (mrestrict H' m') base l.
Proof.
intros H H' m m' base l HE HG j Hj. destruct (HG j Hj) as [V Hb]. split; [|exact Hb].
apply (val_mem_kept SEGS H H' m m'); [|exact V].
intros k Hk. rewrite <- Z.add_assoc. apply HE. lia.
Qed.
Lemma r3t_hd : forall (W : world SEGS) (m : word -> option byte) P s,
  s <> [] -> Forall (fun c => 0 < c < 256) s -> garr8 SEGS (mrestrict (w_H W) m) P (s ++ [0]) ->
  1 <= hd 0 s <= 255 /\ (1 <= length s)%nat /\ val_mem SEGS (mrestrict (w_H W) m) P 1 (hd 0 s).
Proof.
intros W m P s Hne Hch Hg. destruct s as [|c s]; [exfalso; exact (Hne eq_refl)|].
apply Forall_inv in Hch. cbn [hd length]. split; [lia|]. split; [lia|].
destruct (Hg 0%nat ltac:(cbn [length app]; lia)) as [V _]. cbn [Z.of_nat app nth] in V.
rewrite Z.add_0_r in V. exact V.
Qed.
Lemma r3t_val_mem_zero4 : forall H (m : word -> option byte) a,
  (forall i, 0 <= i < 4 -> aview SEGS H m (a + i) = Some 0) -> val_mem SEGS (mrestrict H m) a 4 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte SEGS H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
Definition r3t_E (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Definition r3t_stk1 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 184 8 184
    [YP09.mkChunk 80 (CVal 8 (SOff 12 0)); YP09.mkChunk 88 (CVal 8 (SOff 13 0))].
Definition r3t_ss1 : sstate := mkSS (AF_reac_box_name + RBN_T3) sr_atoms
  [r3t_stk1; YP09.mkRegion (Some 18%nat) 0 64 4 5 []] None
  (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Lemma r3t_entry1 : forall (fq : YK11.FPState) (regs : bvmap 5 word) (W : world SEGS) (memc : word -> option byte)
  A SH i o,
  getr regs 9 = w64 A -> getr regs 18 = w64 SH -> getr regs 12 = w64 i -> getr regs 13 = w64 o ->
  2 ^ 46 <= A -> A + 184 <= 2 ^ 47 -> A mod 32 = 0 -> 0 <= SH -> SH + 64 <= A ->
  0 <= i < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
  (forall k, 8 <= k < 184 -> apresent (w_H W) memc (A + k)) -> apresent (w_H W) memc (SH + 4) ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 80) 8 i -> val_mem SEGS (mrestrict (w_H W) memc) (A + 88) 8 o ->
  st_ok_pi SEGS VAL (r3t_E regs) r3t_ss1
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_T3))) memc (seg_rom SEGS))).
Proof.
intros fq regs W memc A SH i o R9 R18 R12 R13 HA0 HA1 HA32 HS0 HSA Hi Ho PA PS Mi Mo.
rewrite restrict_mkst_fx.
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (r3t_E regs) n = getr regs r)
  by (intros n r Hn; unfold r3t_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew (r3t_E regs) 9 = Z_to_bv 64 A) by (rewrite (EL 9%nat 9%bv eq_refl); exact R9).
assert (E18 : ew (r3t_E regs) 18 = Z_to_bv 64 SH) by (rewrite (EL 18%nat 18%bv eq_refl); exact R18).
assert (E12 : ew (r3t_E regs) 12 = Z_to_bv 64 i) by (rewrite (EL 12%nat 12%bv eq_refl); exact R12).
assert (E13 : ew (r3t_E regs) 13 = Z_to_bv 64 o) by (rewrite (EL 13%nat 13%bv eq_refl); exact R13).
assert (VB : forall n v, ew (r3t_E regs) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  base_val (r3t_E regs) (Some n) = v)
  by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
unfold r3t_ss1. apply pa_entry_st_ok_full.
- unfold r3t_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold r3t_stk1. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 9%nat A E9) by lia. split; [lia|]. split; [lia|]. split.
    * intros k Hk. apply (apresent_writable SEGS). apply PA. lia.
    * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- apply (chunk_ok_val SEGS _ _ A 80 8 (SOff 12 0) i);
           [cbn [sv_denot]; rewrite E12, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
         change (N.to_nat 8) with 8%nat. exact Mi.
      -- apply (chunk_ok_val SEGS _ _ A 88 8 (SOff 13 0) o);
           [cbn [sv_denot]; rewrite E13, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
         change (N.to_nat 8) with 8%nat. exact Mo.
  + rewrite (VB 18%nat SH E18) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros k Hk. apply (apresent_writable SEGS). replace (SH + k) with (SH + 4) by lia. exact PS.
- apply pairwise_disjoint_of_extents. unfold r3t_stk1, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 9%nat A E9), (VB 18%nat SH E18) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, unsigned_lit_small by lia. change (2 ^ 5) with 32. lia.
Qed.
Definition r3t_rD : YP09.region :=
  YP09.mkRegion (Some 9%nat) 80 96 0 0 [YP09.mkChunk 80 (CVal 8 (SOff 32 0)); YP09.mkChunk 88 (CVal 8 (SOff 33 0))].
Definition r3t_ssD (q : Z) : sstate := mkSS (AF_reac_box_name + q) sr_atoms [r3t_rD] None
  (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Definition r3t_ED (regs : bvmap 5 word) (i o : Z) : env := Eimg (Ereg regs [Z_to_bv 64 i; Z_to_bv 64 o]).
Lemma r3t_entryD : forall (fq : YK11.FPState) (regs : bvmap 5 word) (W : world SEGS) (memc : word -> option byte)
  A i o q,
  getr regs 9 = w64 A -> 2 ^ 46 <= A -> A + 184 <= 2 ^ 47 -> A mod 32 = 0 ->
  0 <= i < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 80) 8 i -> val_mem SEGS (mrestrict (w_H W) memc) (A + 88) 8 o ->
  st_ok_pi SEGS VAL (r3t_ED regs i o) (r3t_ssD q)
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + q))) memc (seg_rom SEGS))).
Proof.
intros fq regs W memc A i o q R9 HA0 HA1 HA32 Hi Ho Mi Mo.
rewrite restrict_mkst_fx.
assert (E9 : ew (r3t_ED regs i o) 9 = Z_to_bv 64 A)
  by (unfold r3t_ED; rewrite (ew_Eimg_Ereg_nat regs _ 9%nat 9%bv eq_refl); exact R9).
assert (E32 : ew (r3t_ED regs i o) 32 = Z_to_bv 64 i)
  by (unfold r3t_ED; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (r3t_ED regs i o) 33 = Z_to_bv 64 o)
  by (unfold r3t_ED; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
unfold r3t_ssD. apply pa_entry_st_ok_full.
- unfold r3t_ED. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, r3t_rD.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros k Hk; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (chunk_ok_val SEGS _ _ A 80 8 (SOff 32 0) i);
      [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 8) with 8%nat. exact Mi.
  + apply (chunk_ok_val SEGS _ _ A 88 8 (SOff 33 0) o);
      [cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 8) with 8%nat. exact Mo.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, unsigned_lit_small by lia. change (2 ^ 5) with 32. lia.
Qed.
Definition r3t_rT2A : YP09.region := YP09.mkRegion (Some 9%nat) 32 176 32 40 [YP09.mkChunk 168 (CVal 8 (SLit 4))].
Definition r3t_ssT2 : sstate := mkSS (AF_reac_box_name + RBN_Q4) sr_atoms [r3t_rT2A] None
  (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (25%nat, mkAF 4096 0x7fffff800000 5)] [] []).
Lemma r3t_entryT2 : forall (fq : YK11.FPState) (regs : bvmap 5 word) (W : world SEGS) (memc : word -> option byte)
  A Fp,
  getr regs 9 = w64 A -> getr regs 25 = w64 Fp -> getr regs 22 = w64 SHADOW_OFF ->
  2 ^ 46 <= A -> A + 184 <= 2 ^ 47 -> A mod 32 = 0 -> 4096 <= Fp -> Fp <= 0x7fffff800000 -> Fp + 5 <= A ->
  Fp mod 32 = 0 ->
  (forall k, 32 <= k < 40 -> apresent (w_H W) memc (A + k)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 168) 8 4 ->
  st_ok_pi SEGS VAL (r3t_E regs) r3t_ssT2
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_Q4))) memc (seg_rom SEGS))).
Proof.
intros fq regs W memc A Fp R9 R25 R22 HA0 HA1 HA32 HF0 HF1 HFA HF32 PA M168.
rewrite restrict_mkst_fx.
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (r3t_E regs) n = getr regs r)
  by (intros n r Hn; unfold r3t_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew (r3t_E regs) 9 = Z_to_bv 64 A) by (rewrite (EL 9%nat 9%bv eq_refl); exact R9).
assert (E25 : ew (r3t_E regs) 25 = Z_to_bv 64 Fp) by (rewrite (EL 25%nat 25%bv eq_refl); exact R25).
assert (E22 : ew (r3t_E regs) 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EL 22%nat 22%bv eq_refl); exact R22).
unfold r3t_ssT2. apply pa_entry_st_ok_full.
- unfold r3t_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, r3t_rT2A.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split.
  + intros k Hk. apply (apresent_writable SEGS). apply PA. lia.
  + apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ A 168 8 (SLit 4) 4); [reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 8) with 8%nat. exact M168.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E25, E22, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
Definition r3t_ssP4 : sstate := mkSS (AF_reac_box_name + RBN_Q5) sr_atoms
  [YP09.mkRegion (Some 10%nat) 0 1 0 1 []; YP09.mkRegion (Some 18%nat) 0 64 8 11 []] None (mkFacts [] [] []).
Lemma r3t_entryP4 : forall (fq : YK11.FPState) (regs : bvmap 5 word) (W : world SEGS) (memc : word -> option byte)
  a0 SH,
  getr regs 10 = w64 a0 -> getr regs 18 = w64 SH -> 0 <= a0 -> 0 <= SH -> SH + 64 <= 2 ^ 47 -> a0 + 1 <= 2 ^ 47 ->
  (a0 + 1 <= SH \/ SH + 64 <= a0) ->
  apresent (w_H W) memc a0 -> (forall k, 8 <= k < 11 -> apresent (w_H W) memc (SH + k)) ->
  st_ok_pi SEGS VAL (r3t_E regs) r3t_ssP4
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_Q5))) memc (seg_rom SEGS))).
Proof.
intros fq regs W memc a0 SH R10 R18 Ha0 HS0 HS1 Ha1 Hd Pa PS.
rewrite restrict_mkst_fx.
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (r3t_E regs) n = getr regs r)
  by (intros n r Hn; unfold r3t_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E10 : ew (r3t_E regs) 10 = Z_to_bv 64 a0) by (rewrite (EL 10%nat 10%bv eq_refl); exact R10).
assert (E18 : ew (r3t_E regs) 18 = Z_to_bv 64 SH) by (rewrite (EL 18%nat 18%bv eq_refl); exact R18).
assert (VB : forall n v, ew (r3t_E regs) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  base_val (r3t_E regs) (Some n) = v)
  by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
unfold r3t_ssP4. apply pa_entry_st_ok_full.
- unfold r3t_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 10%nat a0 E10) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros k Hk. apply (apresent_writable SEGS). replace (a0 + k) with a0 by lia. exact Pa.
  + rewrite (VB 18%nat SH E18) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros k Hk. apply (apresent_writable SEGS). apply PS. lia.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 10%nat a0 E10), (VB 18%nat SH E18) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.
Definition r3t_rT3A : YP09.region := YP09.mkRegion (Some 9%nat) 16 24 16 24 [].
Definition r3t_fT3 : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (20%nat, mkAF 4096 (2 ^ 47 - 2) 0); (32%nat, mkAF 1 255 0) ] [] [].
Definition r3t_ssT3 : sstate :=
  mkSS (AF_reac_box_name + RBN_Q6) sr_atoms [r3t_rT3A; r3h_rS (SOff 32 0)] None r3t_fT3.
Lemma r3t_entryT3 : forall (fq : YK11.FPState) (regs : bvmap 5 word) (W : world SEGS) memc A s c,
  getr regs 9 = w64 A -> getr regs 20 = w64 s -> getr regs 22 = w64 SHADOW_OFF ->
  2 ^ 46 <= A -> A + 184 <= 2 ^ 47 -> A mod 32 = 0 ->
  4096 <= s <= 2 ^ 47 - 2 -> (s + 1 <= A + 16 \/ A + 24 <= s) -> 1 <= c <= 255 ->
  (forall o, 16 <= o < 24 -> apresent (w_H W) memc (A + o)) ->
  val_mem SEGS (mrestrict (w_H W) memc) s 1 c ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s 1 ->
  ~ (SHADOW_OFF <= s < SHADOW_OFF + 17592186044416) ->
  st_ok_pi SEGS VAL (r3h_EA regs c) r3t_ssT3
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_Q6))) memc (seg_rom SEGS)))
  /\ sh_ok SEGS r3h_Bx r3h_SHA (r3h_EA regs c) (mrestrict (w_H W) memc).
Proof.
intros fq regs W memc A s c R9 R20 R22 HA0 HA1 HA32 Hs Hsd Hc PA Vc HRA Hap.
rewrite restrict_mkst_fx.
assert (E32 : ew (r3h_EA regs c) 32 = Z_to_bv 64 c)
  by (unfold r3h_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
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
- unfold r3t_ssT3. apply pa_entry_st_ok_full.
  + exact HRO.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, r3t_rT3A, r3h_rS;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 9%nat A E9) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply PA; lia | constructor].
    * rewrite (VB 20%nat s E20) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ s 0 1 (SOff 32 0) c);
        [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat. exact Vc.
  + apply pairwise_disjoint_of_extents. unfold r3t_rT3A, r3h_rS, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 9%nat A E9), (VB 20%nat s E20) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; try exact I; lia.
  + split; [|split; exact I].
    cbn [r3t_fT3 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E20, E22, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
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
Definition r3t_regl : list (bv 5) :=
  [(2%bv : bv 5); 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Definition r3t_same (regs1 regs2 : bvmap 5 word) : Prop :=
  forall r, In r r3t_regl -> getr regs2 r = getr regs1 r.
Ltac r3t_same_tac HS EE :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In r3t_regl] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr _ ?r0 = _ =>
        let R := fresh "R" in prreg HS r0 R; rewrite R; apply EE; reflexivity end
    | ]);
  destruct Hr.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Definition r3t_src (X : rbn_in) (pos P : Z) : Prop := 4096 <= P /\ P <= 2 ^ 47 - 2 /\ rbn3_pk B X pos P.
Definition r3t_core (X : rbn_in) (pos P : Z) (sh : list Z) (cells : list (Z * nat * Z))
  (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate) (W1 : world SEGS) (memc1 : word -> option byte)
  (mdc1 : Model) : Prop :=
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh /\ rbn_rbase B X pos regs1 /\
  getr regs1 18 = w64 (rbn_SH X pos) /\ getr regs1 26 = w64 (rbn_F X pos) /\ getr regs1 20 = w64 P /\
  getr regs1 23 = w64 (ri_token X) /\ getr regs1 24 = w64 (ri_name X) /\
  getr regs1 27 = w64 (ri_token_len X) /\
  rbn_cells (mrestrict (w_H W1) memc1) cells /\ rbm_args X /\ r3t_src X pos P.
Definition r3t_s2 (X : rbn_in) (pos P : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  r3t_core X pos P (rbn_sh true false false false) (r3t_cells2 X pos 0) regs1 lyc1 Sc1 W1 memc1 mdc1 /\
  getr regs1 25 = w64 (rbn_F X pos + 32).
Definition r3t_s3 (X : rbn_in) (pos P : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  r3t_core X pos P (rbn_sh true false false false) (r3t_cells2 X pos 2) regs1 lyc1 Sc1 W1 memc1 mdc1 /\
  getr regs1 25 = w64 (rbn_F X pos + 32) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 32) (bn_dec (ri_i X) 2).
Definition r3t_s4 (X : rbn_in) (pos P : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  r3t_core X pos P (rbn_sh true false false false) (r3t_cells2 X pos 4) regs1 lyc1 Sc1 W1 memc1 mdc1 /\
  getr regs1 25 = w64 (rbn_F X pos + 32) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 32) (rbm_w4 X).
Definition r3t_s5 (X : rbn_in) (pos P : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  r3t_core X pos P (rbn_sh true false false false) (r3t_cells5 X pos) regs1 lyc1 Sc1 W1 memc1 mdc1 /\
  getr regs1 25 = w64 (rbn_F X pos + 32) /\ getr regs1 12 = w64 4 /\ getr regs1 10 = w64 (rbn_F X pos + 36) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 32) (rbm_w4 X).
Definition r3t_s6 (X : rbn_in) (pos P : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  r3t_core X pos P (rbn_sh true true false false) (r3t_cells5 X pos) regs1 lyc1 Sc1 W1 memc1 mdc1 /\
  getr regs1 25 = w64 (rbn_F X pos + 32) /\ getr regs1 12 = w64 4 /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 32) (rbm_w4 X ++ [0]).
Definition r3t_at (X : rbn_in) (q : Z)
  (s : bvmap 5 word -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop)
  : world SEGS -> config -> Prop :=
  fun W2 c2 => exists regs2 lyc2 Sc2 memc2 mdc2, c2 = rbn_cfg X q regs2 memc2 mdc2 /\ s regs2 lyc2 Sc2 W2 memc2 mdc2.
Lemma r3t_geo : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  alloc_ceiling + REAC_BOX_NAME_STK <= rbn_SP X /\ rbn_SP X + 16 <= 2 ^ 47 /\ rbn_SP X mod 16 = 0 /\
  rbn_SP X - 320 <= rbn_A X /\ rbn_A X + 288 <= rbn_SP X /\ rbn_A X mod 32 = 0 /\
  ly_stk_lo lyc1 <= rbn_SP X - REAC_BOX_NAME_STK /\ rbn_SP X <= ly_stk_hi lyc1 /\
  (forall a, rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X -> apresent (w_H W1) memc1 a) /\
  frames Sc1 = (3, pos) :: frames (ri_Sc X) /\ Z.of_nat (length (frames Sc1)) <= 9 /\
  (forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p) /\
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 32 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 ->
     apresent (w_H W1) memc1 a /\ ~ in_img SEGS a /\ ~ aowned B lyc1 Sc1 a) /\
  rbn_SH X pos = SHADOW_OFF + rbn_F X pos / 8 /\
  (forall i, 0 <= i < 64 -> apresent (w_H W1) memc1 (rbn_SH X pos + i) /\ ~ aowned B lyc1 Sc1 (rbn_SH X pos + i)).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM.
pose proof (r3h_fa B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM) as FA.
destruct (r3h_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & Hal & _ & _ & Hlen & _).
pose proof HM as (HJ1 & Hfrs & _).
pose proof HJ1 as (HAR1 & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres &
  (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
destruct (r3h_F_facts B LAWS X pos lyc1 Sc1 W1 memc1 mdc1 Er sh memc1 mdc1 HX HM HAR1)
  as (HF4096 & HFceil & HF32 & HFapp & HFpr & HSpr).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (_ & _ & Hfb & Hsb).
rewrite FA in Hfb, Hsb. change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos) in Hfb, Hsb.
change (fs_frame_bytes 3) with 512 in Hfb, Hsb. change (512 / 8) with 64 in Hsb.
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [lia|]. split; [exact AR7|].
split; [rewrite Elo; unfold rbn_SP in *; lia|]. split; [rewrite Ehi; unfold rbn_SP in *; lia|].
split; [intros a Ha; apply Hpres; unfold rbn_SP in *; lia|].
split; [exact Hfrs|]. split; [rewrite Hfrs; cbn [length]; lia|]. split; [exact FA|].
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact HF32|]. split; [exact HFapp|].
split.
{ intros a Ha. split; [exact (proj1 (HFpr a Ha))|]. split; [exact (proj2 (HFpr a Ha))|].
  exact (proj2 (Hfb a Ha)). }
split; [reflexivity|].
intros i Hi. split; [exact (HSpr i Hi)|]. exact (proj2 (Hsb i Hi)).
Qed.
Lemma r3t_mid_upd : forall X pos lyc1 Sc1 W1 memc1 mdc1 sh lyc2 Sc2 W2 memc2 mdc2 sh2,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 memc2 mdc2 (ri_k X) ->
  Permutation (ablocks B lyc2 Sc2) (ablocks B lyc1 Sc1) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X) ->
     aview SEGS (w_H W2) memc2 a = aview SEGS (w_H W1) memc1 a) ->
  (forall b m j, In (b, m) (ablocks B lyc1 Sc1) -> 0 <= j < req_size m ->
     aview SEGS (w_H W2) memc2 (b + j) = aview SEGS (w_H W1) memc1 (b + j)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) memc2 a = aview SEGS (w_H W1) memc1 a) ->
  (forall cid p a, In (cid, p) (frames (ri_Sc X)) ->
     (in_zr a (frame_rng (ri_lyc X) (cid, p)) \/
      in_zr a (shadow_addr (frame_addr (ri_lyc X) cid p), fs_frame_bytes cid / 8)) ->
     aview SEGS (w_H W2) memc2 a = aview SEGS (w_H W1) memc1 a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X) ->
     apresent (w_H W1) memc1 a -> apresent (w_H W2) memc2 a) ->
  (forall a, rbn_SP X - 104 <= a < rbn_SP X -> aview SEGS (w_H W2) memc2 a = aview SEGS (w_H W1) memc1 a) ->
  (forall a, rbn_F X pos + 504 <= a < rbn_F X pos + 512 ->
     aview SEGS (w_H W2) memc2 a = aview SEGS (w_H W1) memc1 a) ->
  rbn_shadow_at W2 memc2 (rbn_SH X pos) sh2 ->
  rbn_mid B X pos lyc2 Sc2 W2 memc2 mdc2 (fun _ => False) sh2.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 sh lyc2 Sc2 W2 memc2 mdc2 sh2 HX HM HJ2 Hperm2 K1' K2' K3' K4' K5' FR' FL' Hsh2.
pose proof HM as (HJ1 & Hfrs & Hperm & Hro & (K1 & K2 & K3 & K4 & K5 & K6) & Hfr & Hfl & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & Hfrs1 & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & Hfrs2 & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
destruct (r3h_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & _).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
split; [exact HJ2|].
split; [rewrite Hfrs2, <- Hfrs1; exact Hfrs|].
split; [exact (Permutation_trans Hperm2 Hperm)|].
split.
{ intros a Hro0 Ho He.
  assert (Hia : in_img SEGS a)
    by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
  rewrite (K3' a Hia Ho He). exact (Hro a Hro0 Ho He). }
split.
{ split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn He. rewrite (K1' a Ha Hn). exact (K1 a Ha Hn He).
  - intros b m j Hb Hj He.
    assert (Hb1 : In (b, m) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hb).
    rewrite (K2' b m j Hb1 Hj). exact (K2 b m j Hb Hj He).
  - intros a Hia Ho He. rewrite (K3' a Hia Ho He). exact (K3 a Hia Ho He).
  - intros cid p a Hcp Ha He. rewrite (K4' cid p a Hcp Ha). exact (K4 cid p a Hcp Ha He).
  - intros a Ha Hn Hp. exact (K5' a Ha Hn (K5 a Ha Hn Hp)).
  - intros a Ha. apply Hpres2. unfold rbn_SP in *. lia. }
split.
{ unfold rbn_frame. intros j r Hj.
  assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length rbn_saved_regs) with 13%nat in Hj13.
  apply (val_mem_kept SEGS (w_H W1) (w_H W2) memc1 memc2); [|exact (Hfr j r Hj)].
  intros k Hk. apply FR'. lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) memc1 memc2); [|exact Hfl]. intros k Hk. apply FL'. lia. }
exact Hsh2.
Qed.
Lemma r3t_mid_eq : forall X pos lyc1 Sc1 W1 memc1 mdc1 sh mem2 md2 sh2,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 mem2 md2 (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 4208 <= a < rbn_A X + 184) ->
     ~ (rbn_F X pos <= a < rbn_F X pos + 504) -> ~ (rbn_SH X pos <= a < rbn_SH X pos + 64) ->
     aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  rbn_shadow_at W1 mem2 (rbn_SH X pos) sh2 ->
  rbn_mid B X pos lyc1 Sc1 W1 mem2 md2 (fun _ => False) sh2.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 sh mem2 md2 sh2 HX HM HJ2 HN Hsh2.
destruct (r3t_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HM as (HJ1 & _ & Hperm & _).
pose proof (proj1 HJ1) as HAR1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite G10; left; reflexivity).
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite G12; reflexivity).
assert (HFa : rbn_F X pos + 512 <= kLowShadowBeg \/ kHighMemBeg <= rbn_F X pos)
  by (unfold in_app in G16; unfold kLowShadowBeg, kHighMemBeg in *; lia).
pose proof (r3h_sh_band (rbn_F X pos) 512 0 G13 ltac:(lia) G14 ltac:(change (512 / 8) with 64; lia)) as SB0.
pose proof (r3h_sh_band (rbn_F X pos) 512 63 G13 ltac:(lia) G14 ltac:(change (512 / 8) with 64; lia)) as SB63.
change (shadow_addr (rbn_F X pos)) with (rbn_SH X pos) in SB0, SB63.
assert (HF8 : rbn_F X pos mod 8 = 0) by lia.
apply (r3t_mid_upd X pos lyc1 Sc1 W1 memc1 mdc1 sh lyc1 Sc1 W1 mem2 md2 sh2 HX HM HJ2 (Permutation_refl _));
  [| | | | | | | exact Hsh2].
- intros a Ha Hn. apply HN; unfold kLowShadowBeg, kHighMemBeg in *; unfold rbn_SP in *; lia.
- intros b m j Hb Hj.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR1 Hb) as (_ & Hb4 & Hbc & Hbapp & _).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 3 pos HAR1 Hb Hin3) as Hd.
  rewrite FA3 in Hd. change (fs_frame_bytes 3) with 512 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  unfold in_app in Hbapp. apply HN; unfold kLowShadowBeg, kHighMemBeg in *; lia.
- intros a Hia Ho He. pose proof (pa_img_range a Hia) as Hir.
  assert (Hnf : ~ (rbn_F X pos <= a < rbn_F X pos + 504)) by (intros Hf; exact (proj1 (proj2 (G17 a ltac:(lia))) Hia)).
  apply HN; [| | exact Hnf |]; unfold IMG_LO, IMG_TOP, kLowShadowBeg, kHighMemBeg in *; lia.
- intros cid p a Hcp Ha.
  assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite G10; right; exact Hcp).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp1) as (Hc4096 & Hcceil & Hcapp).
  rewrite G12 in Hc4096, Hcceil, Hcapp.
  pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
  destruct (in_split _ _ Hcp) as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (cid, p) [] l2 l3 HAR1
    ltac:(rewrite G10, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite FA3, G12 in Hd.
  change (fs_frame_bytes 3) with 512 in Hd.
  destruct Ha as [Ha | Ha].
  + unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. unfold in_app in Hcapp.
    apply HN; unfold kLowShadowBeg, kHighMemBeg in *; lia.
  + unfold in_zr in Ha. cbn [fst snd] in Ha.
    pose proof (r3h_sh_band (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid)
      (a - shadow_addr (frame_addr (ri_lyc X) cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
    pose proof (shadow_range_end (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid) Hcnn) as Se1.
    assert (S1 : frame_addr (ri_lyc X) cid p + fs_frame_bytes cid <= rbn_F X pos -> a < rbn_SH X pos).
    { intros Hd1. pose proof (shadow_mono _ _ Hd1) as Sm.
      change (shadow_addr (rbn_F X pos)) with (rbn_SH X pos) in Sm. lia. }
    assert (S2 : rbn_F X pos + 512 <= frame_addr (ri_lyc X) cid p -> rbn_SH X pos + 64 <= a).
    { intros Hd2. pose proof (shadow_mono _ _ Hd2) as Sm.
      assert (shadow_addr (rbn_F X pos + 512) = rbn_SH X pos + 64) by (rewrite G18; unfold shadow_addr; lia).
      lia. }
    assert (Hdis : a < rbn_SH X pos \/ rbn_SH X pos + 64 <= a).
    { destruct Hd as [Hd | Hd]; first [left; exact (S1 Hd) | right; exact (S2 Hd)]. }
    apply HN; unfold kLowShadowBeg, kHighMemBeg in *; lia.
- intros a Ha Hn Hp.
  apply (apresent_transfer SEGS (w_H W1) (w_H W1) memc1 mem2 a); [lia | | | exact Hp].
  + intros Hi. pose proof (pa_segs_low a Hi). unfold kLowMemEnd in *. lia.
  + apply HN; unfold kLowShadowBeg, kHighMemBeg in *; unfold rbn_SP in *; lia.
- intros a Ha. apply HN; unfold kLowShadowBeg, kHighMemBeg in *; unfold rbn_SP in *; lia.
- intros a Ha. apply HN; unfold kLowShadowBeg, kHighMemBeg in *; lia.
Qed.
Lemma r3t_stk_vis : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> ly_stk_lo ly <= a -> 0 < n -> a + n <= ly_stk_hi ly ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Proof.
intros ly S W mem md a n HAR H1 Hn H2.
pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
  (or_introl eq_refl)) as Hz. cbn [fst snd] in Hz.
pose proof (lo_top ly (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Lplo & Lphi & Lb).
unfold page_aligned in Lplo, Lphi. unfold kHighMemBeg in Lb.
exact (r3h_zs_vis _ (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly) a n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  Hz H1 Hn ltac:(lia)).
Qed.
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Lemma r3t_MS : forall X (W1 : world SEGS) c1, rbn_cx B X -> rbn3_mid B X W1 c1 ->
  SRr SEGS W1 c1 (fun W2 c2 => exists pos P, r3t_at X RBN_Q2 (r3t_s2 X pos P) W2 c2).
Proof.
intros X W1 c1 HX (pos & P & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & HM & HR & HP0 & HP1 & Ri & Ro & Mi & Mo & HPK & HA).
destruct HR as (B2 & B3 & B4 & B8 & B9 & B19 & B22 & R18 & R26 & R20 & R23 & R24 & R27 & R12 & R13 & R14 & R15 & R16).
destruct (r3t_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HM as (HJ & _ & Hperm & _ & _ & _ & _ & Hsh).
destruct (r3h_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8).
pose proof (proj1 HJ) as HAR1.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rnl &
  _ & _ & _ & _ & _ & Rdi & _ & Rdl & _).
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite G12; reflexivity).
assert (HSHl : 0 <= rbn_SH X pos) by (rewrite G18; unfold SHADOW_OFF; lia).
assert (HSHh : rbn_SH X pos + 64 <= alloc_ceiling) by (rewrite G18; unfold SHADOW_OFF; lia).
pose proof (r3t_entry1 (ri_fq X) regs1 W1 memc1 (rbn_A X) (rbn_SH X pos) (ri_i X) (ri_o X) B9 R18 R12 R13
  ltac:(lia) ltac:(lia) G6 HSHl ltac:(lia) Ri Ro
  (fun k Hk => G9 (rbn_A X + k) ltac:(lia)) (proj1 (G19 4 ltac:(lia))) Mi Mo) as HS.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (@SRr_run_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call (ri_fq X) _ _ _ _ _ B LAWS) as RUNC.
remember (r3t_E regs1) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold r3t_E; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = rbn_A X)
  by (rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = rbn_SH X pos)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (HW1 : forall a, in_wrange E (ss_mem r3t_ss1) a ->
  (rbn_A X + 8 <= a < rbn_A X + 184) \/ a = rbn_SH X pos + 4).
{ intros a (r & Hr & Hw). unfold r3t_ss1, r3t_stk1 in Hr. cbn [ss_mem In] in Hr.
  repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
  - rewrite U9 in Hw. left. lia.
  - rewrite U18 in Hw. right. lia. }
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + RBN_T3) with (BASE + (AF_reac_box_name + RBN_T3)) by ring.
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off E _ _ (ri_STK X) (ri_sp0 X) (ri_FP X) _ _ lyc1 _ 9%nat (rbn_A X - ri_sp0 X));
    [reflexivity | rewrite U9; lia | cbn; unfold rbn_SP in *; lia | cbn; unfold rbn_SP in *; lia |].
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 18%nat (rbn_SH X pos)); [reflexivity | exact U18 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 3, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite FA3.
    change (fs_frame_bytes 3 / 8) with 64. change (shadow_addr (rbn_F X pos)) with (rbn_SH X pos). lia. }
  apply awr_ok_nil. }
pose proof (r3h_kept E _ (w_H W1) memc1 (ms_mem ms) _ HFr HW1) as Kr.
clear HF HFr HW1.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) Rs0. prreg HS (9%bv : bv 5) Rs1. prreg HS (18%bv : bv 5) Rs2.
prreg HS (19%bv : bv 5) Rs3. prreg HS (20%bv : bv 5) Rs4. prreg HS (22%bv : bv 5) Rs6.
prreg HS (23%bv : bv 5) Rs7. prreg HS (24%bv : bv 5) Rs8. prreg HS (25%bv : bv 5) Rs9.
prreg HS (26%bv : bv 5) Rs10. prreg HS (27%bv : bv 5) Rs11.
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as RA.
pose proof (st_ok_region_nth E _ _ 1 _ HS eq_refl) as RSH.
cbn [ms_mem restrict] in RA, RSH.
assert (V8 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 8) 8 (ri_display X)).
{ apply (field_of_region E _ 9 (rbn_A X) _ 8 184 8 184 8 8 (SOff 14 0) (ri_display X) RA U9);
    [repeat (first [left; reflexivity | right]) | | cbn; lia | cbn; lia].
  cbn [sv_denot]. rewrite (EE 14%nat 14%bv eq_refl), R14. unfold w64.
  rewrite unsigned_lit_small, Z.add_0_r by lia. reflexivity. }
assert (V56 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 56) 8 (ri_display_len X)).
{ apply (field_of_region E _ 9 (rbn_A X) _ 8 184 8 184 56 8 (SOff 16 0) (ri_display_len X) RA U9);
    [repeat (first [left; reflexivity | right]) | | cbn; lia | cbn; lia].
  cbn [sv_denot]. rewrite (EE 16%nat 16%bv eq_refl), R16. unfold w64.
  rewrite unsigned_lit_small, Z.add_0_r by lia. reflexivity. }
assert (V64 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 64) 8 (ri_name_len X)).
{ apply (field_of_region E _ 9 (rbn_A X) _ 8 184 8 184 64 8 (SOff 15 0) (ri_name_len X) RA U9);
    [repeat (first [left; reflexivity | right]) | | cbn; lia | cbn; lia].
  cbn [sv_denot]. rewrite (EE 15%nat 15%bv eq_refl), R15. unfold w64.
  rewrite unsigned_lit_small, Z.add_0_r by lia. reflexivity. }
assert (V80 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 80) 8 (ri_i X)).
{ apply (field_of_region E _ 9 (rbn_A X) _ 8 184 8 184 80 8 (SOff 12 0) (ri_i X) RA U9);
    [repeat (first [left; reflexivity | right]) | | cbn; lia | cbn; lia].
  cbn [sv_denot]. rewrite (EE 12%nat 12%bv eq_refl), R12. unfold w64.
  rewrite unsigned_lit_small, Z.add_0_r by lia. reflexivity. }
assert (V88 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 88) 8 (ri_o X)).
{ apply (field_of_region E _ 9 (rbn_A X) _ 8 184 8 184 88 8 (SOff 13 0) (ri_o X) RA U9);
    [repeat (first [left; reflexivity | right]) | | cbn; lia | cbn; lia].
  cbn [sv_denot]. rewrite (EE 13%nat 13%bv eq_refl), R13. unfold w64.
  rewrite unsigned_lit_small, Z.add_0_r by lia. reflexivity. }
assert (V152 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 152) 8 (rbn_F X pos + 32)).
{ apply (field_of_region E _ 9 (rbn_A X) _ 8 184 8 184 152 8 (SOff 19 32) (rbn_F X pos + 32) RA U9);
    [repeat (first [left; reflexivity | right]) | | cbn; lia | cbn; lia].
  cbn [sv_denot]. rewrite (EE 19%nat 19%bv eq_refl), B19. unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (V160 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 160) 8 5).
{ apply (field_of_region E _ 9 (rbn_A X) _ 8 184 8 184 160 8 (SLit 5) 5 RA U9);
    [repeat (first [left; reflexivity | right]) | reflexivity | cbn; lia | cbn; lia]. }
assert (VSH4 : aview SEGS (w_H W1) (ms_mem ms) (rbn_SH X pos + 4) = Some 5).
{ apply aview_of_val_mem1; [|lia].
  exact (field_of_region E _ 18 (rbn_SH X pos) _ 0 64 4 5 4 1 (SLit 5) 5 RSH U18
    ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ _ _) _) _ =>
  assert (HspT : spZ rT = ri_sp0 X + (rbn_A X - ri_sp0 X))
    by (unfold spZ at 1; rewrite Rsp, (EE 2%nat 2%bv eq_refl), B2; unfold w64; rewrite unsigned_lit_small by lia; lia) end.
eapply SRr_bind.
{ eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA DS___asan_memset) (AMEMSET (ri_fq X)) W1 (ms_regs ms) (ms_mem ms)
    (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 _ (ri_k X) (rbn_A X + 168) 0 16 (rbn_A X - ri_sp0 X) _ HJ).
  - rewrite Ra0, U9. reflexivity.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact HspT.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _). lia.
  - unfold rbn_SP in *. lia.
  - rewrite Hes. unfold rbn_SP in *. lia.
  - rewrite Rgp, (EE 3%nat 3%bv eq_refl). exact B3.
  - rewrite Rtp, (EE 4%nat 4%bv eq_refl). exact B4.
  - exact Rra.
  - apply ret_ok_codeptr_v; [change (2 ^ 40) with 1099511627776; lia | reflexivity].
  - intros a Ha. split; [left; unfold rbn_SP in *; lia | rewrite Hes; lia].
  - unfold amem_range, kHighMemBeg, kHighMemEnd. right. lia.
  - exact (proj1 (r3t_stk_vis lyc1 Sc1 W1 _ _ (rbn_A X + 168) 16 (proj1 HJ) ltac:(unfold rbn_SP in *; lia) ltac:(lia)
      ltac:(unfold rbn_SP in *; lia))).
  - intros _. exact (proj2 (r3t_stk_vis lyc1 Sc1 W1 _ _ (rbn_A X + 168) 16 (proj1 HJ)
      ltac:(unfold rbn_SP in *; lia) ltac:(lia) ltac:(unfold rbn_SP in *; lia))).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfrm & Hpres2).
apply SRr_ret.
assert (Kc : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 168 <= a < rbn_A X + 184) -> ~ (rbn_A X - 4096 <= a < rbn_A X) ->
  aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) (ms_mem ms) a).
{ intros a Ha H1 H2. apply Hfrm; [exact Ha | lia | rewrite Hes; lia]. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 4096 <= a < rbn_A X + 184) -> a <> rbn_SH X pos + 4 ->
  aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha H1 H2. rewrite (Kc a Ha) by lia. apply Kr; [exact Ha|]. lia. }
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r)
  by (intros r Hr; exact (r3t_pres_get _ _ r HP2 Hr)).
exists pos, P, regs2, lyc1, Sc1, mem2, md2.
split.
{ unfold rbn_cfg, cfg_at, w64.
  do 2 f_equal. f_equal. unfold AF_reac_box_name, RBN_Q2; lia. }
unfold r3t_s2, r3t_core. split; [|rewrite PR, Rs9, (EE 19%nat 19%bv eq_refl), B19 by r3t_cs; unfold w64;
  rewrite unsigned_lit_small by lia; reflexivity].
split.
{ apply (r3t_mid_eq X pos lyc1 Sc1 W1 memc1 mdc1 _ mem2 md2 (rbn_sh true false false false) HX HM HJ2).
  - intros a Ha H1 H2 H3. apply KEEP; [exact Ha | lia | lia].
  - intros j Hj. rewrite r3h_sh_len in Hj.
    destruct (Z.eq_dec j 4) as [-> | Hj4].
    + rewrite (Kc (rbn_SH X pos + 4)) by lia. rewrite VSH4. reflexivity.
    + rewrite (KEEP (rbn_SH X pos + j)) by lia.
      rewrite (Hsh j) by (rewrite r3h_sh_len; lia).
      rewrite r3t_sh_w4 by lia. reflexivity. }
split.
{ split; [rewrite PR, Rsp, (EE 2%nat 2%bv eq_refl) by r3t_cs; exact B2|].
  split; [rewrite PR, Rgp, (EE 3%nat 3%bv eq_refl) by r3t_cs; exact B3|].
  split; [rewrite PR, Rtp, (EE 4%nat 4%bv eq_refl) by r3t_cs; exact B4|].
  split; [rewrite PR, Rs0, (EE 8%nat 8%bv eq_refl) by r3t_cs; exact B8|].
  split; [rewrite PR, Rs1, (EE 9%nat 9%bv eq_refl) by r3t_cs; exact B9|].
  split; [rewrite PR, Rs3, (EE 19%nat 19%bv eq_refl) by r3t_cs; exact B19|].
  rewrite PR, Rs6, (EE 22%nat 22%bv eq_refl) by r3t_cs; exact B22. }
split; [rewrite PR, Rs2, (EE 18%nat 18%bv eq_refl) by r3t_cs; exact R18|].
split; [rewrite PR, Rs10, (EE 26%nat 26%bv eq_refl) by r3t_cs; exact R26|].
split; [rewrite PR, Rs4, (EE 20%nat 20%bv eq_refl) by r3t_cs; exact R20|].
split; [rewrite PR, Rs7, (EE 23%nat 23%bv eq_refl) by r3t_cs; exact R23|].
split; [rewrite PR, Rs8, (EE 24%nat 24%bv eq_refl) by r3t_cs; exact R24|].
split; [rewrite PR, Rs11, (EE 27%nat 27%bv eq_refl) by r3t_cs; exact R27|].
split; [|split; [exact HA | split; [exact HP0 | split; [exact HP1 | exact HPK]]]].
unfold r3t_cells2. cbn [rbn_cells].
split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [intros k Hk; apply Kc; lia | exact V8]|].
split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [intros k Hk; apply Kc; lia | exact V56]|].
split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [intros k Hk; apply Kc; lia | exact V64]|].
split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [intros k Hk; apply Kc; lia | exact V80]|].
split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [intros k Hk; apply Kc; lia | exact V88]|].
split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [intros k Hk; apply Kc; lia | exact V152]|].
split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [intros k Hk; apply Kc; lia | exact V160]|].
split; [apply val_mem_zero8; intros i Hi; rewrite (Heff i) by lia; reflexivity|].
split; [|exact I].
apply r3t_val_mem_zero4. intros i Hi. replace (rbn_A X + 176 + i) with (rbn_A X + 168 + (8 + i)) by ring.
rewrite (Heff (8 + i)) by lia. reflexivity.
Qed.
Lemma r3t_chain_at : forall X (W1 : world SEGS) lyc1 memc1,
  rbn_cx B X ->
  ly_top lyc1 = ly_top (ri_ly X) -> ly_top (ri_lyc X) = ly_top (ri_ly X) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X) ->
     aview SEGS (w_H W1) memc1 a = aview SEGS (w_H (ri_W X)) (ri_memc X) a) ->
  rbn_frame X (mrestrict (w_H W1) memc1) ->
  exists ch, achain lyc1 (aview SEGS (w_H W1) memc1) (rbn_A X) (rbn_SP X) ch.
Proof.
intros X W1 lyc1 memc1 HX Htop1 Htop0 Kold Hfrm.
pose proof HX as (HJ0 & _ & _ & _ & Hra4 & _ & _ & Hch0 & Hal & Hstk & Hsp & _).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htopx) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
destruct (r3h_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8).
assert (Hal8 : rbn_SP X mod 8 = 0).
{ unfold rbn_SP. pose proof (Z.div_mod (spZ (ri_regs X)) 16 ltac:(lia)) as D.
  rewrite Hal, Z.add_0_r in D.
  replace (spZ (ri_regs X)) with ((2 * (spZ (ri_regs X) / 16)) * 8) by lia. apply Z_mod_mult. }
assert (Hagree : forall a, rbn_SP X <= a < 2 ^ 64 ->
   aview SEGS (w_H W1) memc1 a = aview SEGS (w_H (ri_W X)) (ri_memc X) a)
  by (intros a Ha; apply Kold; lia).
destruct (Z_lt_ge_dec (rbn_SP X) (ly_top lyc1 - 16)) as [Hlt | Hge].
- assert (Qra : 0 <= raZ (ri_regs X) < 2 ^ 64)
    by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr (ri_regs X) 1)) as Hq;
        change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
  assert (Qs0 : 0 <= s0Z (ri_regs X) < 2 ^ 64)
    by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr (ri_regs X) 8)) as Hq;
        change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
  pose proof (Hfrm 0%nat 1 eq_refl) as Vra. pose proof (Hfrm 1%nat 8 eq_refl) as Vs0.
  assert (Era : bv_unsigned (getr (ri_regs X) (Z_to_bv 5 1)) = raZ (ri_regs X)) by reflexivity.
  assert (Es0 : bv_unsigned (getr (ri_regs X) (Z_to_bv 5 8)) = s0Z (ri_regs X)) by reflexivity.
  rewrite Era in Vra. rewrite Es0 in Vs0.
  replace (rbn_SP X - 8 - 8 * Z.of_nat 0) with (rbn_SP X - 8) in Vra by lia.
  replace (rbn_SP X - 8 - 8 * Z.of_nat 1) with (rbn_SP X - 16) in Vs0 by lia.
  exists ((rbn_SP X, raZ (ri_regs X), s0Z (ri_regs X)) :: ri_ch X).
  apply (achain_ly_top (ri_lyc X) lyc1); [congruence|].
  apply (achain_push (ri_lyc X) (aview SEGS (w_H W1) memc1) (aview SEGS (w_H W1) memc1) (rbn_SP X)
    (s0Z (ri_regs X)) (raZ (ri_regs X)) (ri_ch X) (rbn_A X)).
  + eapply (achain_kept (ri_lyc X) (aview SEGS (w_H (ri_W X)) (ri_memc X)) _ _ _ _ (rbn_SP X));
      [exact Hch0 | unfold rbn_SP; lia | lia | intros a Ha; apply Hagree; lia].
  + lia.
  + intros a Ha. reflexivity.
  + exact (rdword_of_val_mem SEGS _ _ _ _ Vra Qra).
  + exact (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0).
  + exact Hra4.
  + lia.
  + exact Hal8.
  + lia.
  + lia.
- exists []. left. split; [right; left; lia | reflexivity].
Qed.
Lemma r3t_frame_img : forall ly S (W : world SEGS) mem md cid p a n,
  AR SEGS B ly S W mem md -> In (cid, p) (frames S) ->
  frame_addr ly cid p <= a -> a + n <= frame_addr ly cid p + fs_frame_bytes cid -> 0 < n ->
  a + n <= IMG_LO \/ IMG_TOP <= a.
Proof.
intros ly S W mem md cid p a n HAR Hin H1 H2 Hn.
assert (HIT : IMG_LO < IMG_TOP) by (unfold IMG_LO, IMG_TOP; lia).
destruct (Z_le_gt_dec (a + n) IMG_LO) as [Hle | Hgt]; [left; exact Hle|].
destruct (Z_le_gt_dec IMG_TOP a) as [Hge | Hlt]; [right; exact Hge|].
exfalso.
assert (Hex : exists x, IMG_LO <= x < IMG_TOP /\
   frame_addr ly cid p <= x < frame_addr ly cid p + fs_frame_bytes cid).
{ destruct (Z_le_gt_dec IMG_LO a) as [Ha | Ha].
  - exists a. split; lia.
  - exists IMG_LO. split; lia. }
destruct Hex as (x & Hx1 & Hx2).
destruct (al_client_img _ _ LAWS ly S W mem md x HAR
  (or_intror (or_introl (ex_intro _ cid (ex_intro _ p (conj Hin Hx2)))))) as (Himg & _).
apply Himg. destruct (pa_img_cover ly S md (proj1 (proj2 HAR))) as (Hc1 & Hc2).
unfold in_zr. lia.
Qed.
Lemma r3t_buf_ra : forall X pos (W : world SEGS) m j,
  rbn_F X pos mod 32 = 0 -> rbn_SH X pos = SHADOW_OFF + rbn_F X pos / 8 ->
  aview SEGS (w_H W) m (rbn_SH X pos + 4) = Some 5 -> 0 <= j -> j <= 5 ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (rbn_F X pos + 32) j.
Proof.
intros X pos W m j HF Hsh H5 Hj0 Hj1 x Hx. exists 5. split.
- unfold shadow_of_addr. replace (SHADOW_OFF + x / 8) with (rbn_SH X pos + 4); [exact H5|].
  rewrite Hsh. pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D. rewrite HF, Z.add_0_r in D. lia.
- right. split; [|lia]. pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D. rewrite HF, Z.add_0_r in D. lia.
Qed.
Hypothesis HSB : tsb_dec_spec B.
Lemma r3t_dcall : forall X pos P regsT lyc1 Sc1 W1 memT mdT n n2 v pre q,
  rbn_cx B X ->
  r3t_core X pos P (rbn_sh true false false false) (r3t_cells2 X pos n) regsT lyc1 Sc1 W1 memT mdT ->
  (n = 0 \/ n = 2) -> n2 = n + 2 -> length pre = Z.to_nat n -> bn_ok v = true ->
  garr8 SEGS (mrestrict (w_H W1) memT) (rbn_F X pos + 32) pre ->
  getr regsT 1 = Z_to_bv 64 (BASE + (AF_reac_box_name + q)) -> 0 <= q < 4096 -> q mod 2 = 0 ->
  getr regsT 10 = w64 (rbn_A X + 152) -> getr regsT 11 = w64 v -> getr regsT 12 = w64 2 ->
  getr regsT 25 = w64 (rbn_F X pos + 32) ->
  SRr SEGS W1 (cfg_at (fx := ri_fq X) SEGS (BASE + AF_sb_dec) regsT memT mdT)
    (r3t_at X q (fun regs2 lyc2 Sc2 W2 mem2 md2 =>
       r3t_core X pos P (rbn_sh true false false false) (r3t_cells2 X pos n2) regs2 lyc2 Sc2 W2 mem2 md2 /\
       getr regs2 25 = w64 (rbn_F X pos + 32) /\
       garr8 SEGS (mrestrict (w_H W2) mem2) (rbn_F X pos + 32) (pre ++ bn_dec v 2))).
Proof.
intros X pos P regsT lyc1 Sc1 W1 memT mdT n n2 v pre q HX HC Hn Hn2 Hpre Hv Gpre Rra Hq0 Hq2 Ra0 Ra1 Ra2 R25.
destruct HC as (HM & (B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R26 & R20 & R23 & R24 & R27 & HCL & HA & HSRC).
destruct (r3t_geo X pos lyc1 Sc1 W1 memT mdT _ _ HX HM)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
destruct (r3h_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8).
pose proof HM as (HJ & Hfrs & Hperm & Hro & (K1 & K2 & K3 & K4 & K5 & K6) & Hfrm & Hfl & Hsh).
pose proof (proj1 HJ) as HAR1.
pose proof HX as (HJ0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB4).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSBS : SB_DEC_STK = 4208) by reflexivity.
destruct (r3t_dec2 v Hv) as (HD & HDl & Hv40).
assert (Hroom : sb_dec_c.sb_dec_room 5 n = 4 - n) by (destruct Hn as [-> | ->]; reflexivity).
assert (Hacc : sb_dec_c.sb_dec_acc v 2 5 n = 2)
  by (unfold sb_dec_c.sb_dec_acc; rewrite HD, HDl, Hroom; destruct Hn as [-> | ->]; reflexivity).
assert (Hovr : (if sb_dec_c.sb_dec_room 5 n <? Z.of_nat (length (sb_dec_c.sb_dec_D v 2)) then 1 else 0) = 0)
  by (rewrite HD, HDl, Hroom; destruct Hn as [-> | ->]; reflexivity).
assert (Hn0 : 0 <= n <= 2) by (destruct Hn as [-> | ->]; lia).
unfold r3t_cells2 in HCL. cbn [rbn_cells] in HCL.
destruct HCL as (M8 & M56 & M64 & M80 & M88 & M152 & M160 & M168 & M176 & _).
destruct (proj1 (proj2 HJ)) as (_ & _ & _ & _ & _ & _ & _ & _ & Htop1 & _).
destruct (proj1 (proj2 HJ0)) as (_ & _ & _ & _ & _ & _ & _ & _ & Htop0 & _).
destruct (r3t_chain_at X W1 lyc1 memT HX Htop1 Htop0 (fun a Ha Hn' => K1 a Ha Hn' (fun H => H)) Hfrm) as (ch & HCH).
assert (Hsh5 : aview SEGS (w_H W1) memT (rbn_SH X pos + 4) = Some 5)
  by (rewrite (Hsh 4 ltac:(rewrite r3h_sh_len; lia)); reflexivity).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite G10; left; reflexivity).
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite G12; reflexivity).
assert (HspA : spZ regsT = rbn_A X) by (unfold spZ; rewrite B2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0A : s0Z regsT = rbn_SP X) by (unfold s0Z; rewrite B8; unfold w64; apply unsigned_lit_small; lia).
eapply SRr_bind.
{ apply (HSB (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X)
    (ri_md0 X) ((3, pos) :: ri_own X) lyc1 Sc1 W1 memT mdT (ri_k X) regsT ch
    (rbn_A X + 152) v 2 (rbn_F X pos + 32) 5 n 0 HJ Hro).
  - rewrite Rra. apply ret_ok_codeptr_v; unfold AF_reac_box_name; lia.
  - unfold raZ. rewrite Rra. rewrite unsigned_lit_small by (unfold AF_reac_box_name; lia).
    unfold AF_reac_box_name; lia.
  - exact B3.
  - exact B4.
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - rewrite HspA, Hs0A. exact HCH.
  - rewrite HspA. lia.
  - rewrite HspA. unfold rbn_SP in *. lia.
  - rewrite HspA. unfold rbn_SP in *. lia.
  - exact G11.
  - lia.
  - right. reflexivity.
  - lia.
  - right. unfold rbn_SP in *. lia.
  - lia.
  - right. unfold IMG_TOP. lia.
  - left. rewrite HspA. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact M152.
  - replace (rbn_A X + 152 + 8) with (rbn_A X + 160) by ring. exact M160.
  - replace (rbn_A X + 152 + 16) with (rbn_A X + 168) by ring. exact M168.
  - replace (rbn_A X + 152 + 24) with (rbn_A X + 176) by ring. exact M176.
  - exact (proj1 (r3t_stk_vis lyc1 Sc1 W1 _ _ (rbn_A X + 152) 28 HAR1 ltac:(unfold rbn_SP in *; lia) ltac:(lia)
      ltac:(unfold rbn_SP in *; lia))).
  - intros a Ha. apply G9. lia.
  - intros a Ha. left. unfold rbn_SP in *. lia.
  - intros _. rewrite Hacc.
    split; [lia|]. split.
    { apply (in_app_sub (rbn_F X pos) 512); [exact G16 | lia | lia | lia]. }
    split.
    { exact (r3t_frame_img lyc1 Sc1 W1 _ _ 3 pos (rbn_F X pos + 32 + n) 2 HAR1 Hin3
        ltac:(rewrite FA3; lia) ltac:(rewrite FA3; change (fs_frame_bytes 3) with 512; lia) ltac:(lia)). }
    split; [left; lia|].
    split; [right; rewrite HspA, HSBS; lia|].
    split.
    { intros x Hx. destruct (r3t_buf_ra X pos W1 memT (n + 2) G15 G18 Hsh5 ltac:(lia) ltac:(lia) x ltac:(lia)) as (s & Hs1 & Hs2).
      exists s. split; [exact Hs1 | exact Hs2]. }
    intros a Ha. split.
    + right. right. right. exists 3, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite FA3. change (fs_frame_bytes 3) with 512. lia.
    + exact (proj1 (G17 a ltac:(lia))). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & Hfrs2 & Hperm2 &
  Kc1 & Kc2 & Kc3 & Kc4 & Kc5 & Kc6 & Mp2 & Mcap2 & Mn2 & Mov2 & Hdig).
apply SRr_ret.
rewrite Hacc in Kc1, Kc2, Kc4, Mn2. rewrite Hovr in Mov2.
rewrite Hroom in Kc1, Kc2, Kc4, Hdig.
specialize (Hdig ltac:(lia)). rewrite HD in Hdig.
rewrite firstn_all2 in Hdig by (rewrite HDl; cbn; lia).
rewrite HspA, HSBS in Kc1, Kc5.
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regsT r)
  by (intros r Hr; exact (r3t_pres_get _ _ r HP2 Hr)).
assert (KF : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> ~ (rbn_F X pos + 32 + n <= a < rbn_F X pos + 34 + n) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memT a).
{ intros a Ha Hb. apply (Kc4 3 pos a Hin3); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FA3;
    change (fs_frame_bytes 3) with 512; lia | unfold rbn_SP in *; lia | intros (_ & Hc); lia]. }
assert (KS : forall a, rbn_SH X pos <= a < rbn_SH X pos + 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memT a).
{ intros a Ha. pose proof (r3h_sh_band (rbn_F X pos) 512 (a - rbn_SH X pos) G13 ltac:(lia) G14
    ltac:(change (512 / 8) with 64; lia)) as Hb.
  change (shadow_addr (rbn_F X pos)) with (rbn_SH X pos) in Hb.
  apply (Kc4 3 pos a Hin3).
  - right. unfold in_zr. rewrite FA3. change (fs_frame_bytes 3 / 8) with 64.
    change (shadow_addr (rbn_F X pos)) with (rbn_SH X pos). cbn [fst snd]. lia.
  - unfold kLowShadowBeg, kHighMemBeg in *. unfold rbn_SP in *. lia.
  - intros (_ & Hc). unfold in_app, kLowShadowBeg, kHighMemBeg in *. lia. }
assert (KA : forall a, rbn_A X <= a < rbn_A X + 168 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memT a).
{ intros a Ha. apply Kc1; [lia | lia | lia | intros (_ & Hc); lia]. }
exists regs2, ly2, S2, mem2, md2.
split.
{ rewrite Hc2, Rra. unfold rbn_cfg, cfg_at, w64. rewrite Z.add_assoc. reflexivity. }
split; [|split].
- split.
  { apply (r3t_mid_upd X pos lyc1 Sc1 W1 memT mdT _ ly2 S2 W2 mem2 md2 _ HX HM HJ2 Hperm2).
    - intros a Ha Hn'. apply Kc1; [exact Ha | unfold rbn_SP in *; lia | unfold rbn_SP in *; lia | intros (_ & Hc); lia].
    - intros b m j Hb Hj.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR1 Hb) as (_ & Hb4 & Hbc & _).
      pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 3 pos HAR1 Hb Hin3) as Hd.
      rewrite FA3 in Hd. change (fs_frame_bytes 3) with 512 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      apply (Kc2 b m j Hb Hj); [lia | intros (_ & Hc); lia].
    - exact Kc3.
    - intros cid p a Hcp Ha.
      assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite G10; right; exact Hcp).
      destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp1) as (Hc4096 & Hcceil & Hcapp).
      rewrite G12 in Hc4096, Hcceil, Hcapp.
      pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
      destruct (in_split _ _ Hcp) as (l2 & l3 & El).
      pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (cid, p) [] l2 l3 HAR1
        ltac:(rewrite G10, El; reflexivity)) as Hd.
      unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite FA3, G12 in Hd.
      change (fs_frame_bytes 3) with 512 in Hd.
      apply (Kc4 cid p a Hcp1).
      + unfold frame_rng. rewrite !G12. exact Ha.
      + destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha.
        * lia.
        * pose proof (r3h_sh_band (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid)
            (a - shadow_addr (frame_addr (ri_lyc X) cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
          unfold kLowShadowBeg, kHighMemBeg in *. unfold rbn_SP in *. lia.
      + intros (_ & Hc). destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha.
        * lia.
        * pose proof (r3h_sh_band (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid)
            (a - shadow_addr (frame_addr (ri_lyc X) cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
          unfold in_app, kLowShadowBeg, kHighMemBeg in *. lia.
    - intros a Ha Hn' Hp. apply Kc5; [exact Ha | unfold rbn_SP in *; lia | exact Hp].
    - intros a Ha. apply Kc1; [lia | unfold rbn_SP in *; lia | lia | intros (_ & Hc); lia].
    - intros a Ha. apply KF; lia.
    - intros j Hj. rewrite KS by (rewrite r3h_sh_len in Hj; lia). exact (Hsh j Hj). }
  split.
  { split; [rewrite PR by r3t_cs; exact B2|]. split; [rewrite PR by r3t_cs; exact B3|].
    split; [rewrite PR by r3t_cs; exact B4|]. split; [rewrite PR by r3t_cs; exact B8|].
    split; [rewrite PR by r3t_cs; exact B9|]. split; [rewrite PR by r3t_cs; exact B19|].
    rewrite PR by r3t_cs; exact B22. }
  split; [rewrite PR by r3t_cs; exact R18|]. split; [rewrite PR by r3t_cs; exact R26|].
  split; [rewrite PR by r3t_cs; exact R20|]. split; [rewrite PR by r3t_cs; exact R23|].
  split; [rewrite PR by r3t_cs; exact R24|]. split; [rewrite PR by r3t_cs; exact R27|].
  split; [|split; [exact HA | exact HSRC]].
  unfold r3t_cells2. cbn [rbn_cells]. subst n2.
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) memT mem2); [intros k Hk; apply KA; lia | exact M8]|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) memT mem2); [intros k Hk; apply KA; lia | exact M56]|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) memT mem2); [intros k Hk; apply KA; lia | exact M64]|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) memT mem2); [intros k Hk; apply KA; lia | exact M80]|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) memT mem2); [intros k Hk; apply KA; lia | exact M88]|].
  split; [exact Mp2|]. split; [replace (rbn_A X + 160) with (rbn_A X + 152 + 8) by ring; exact Mcap2|].
  split; [replace (rbn_A X + 168) with (rbn_A X + 152 + 16) by ring; exact Mn2|].
  split; [replace (rbn_A X + 176) with (rbn_A X + 152 + 24) by ring; exact Mov2 | exact I].
- rewrite PR by r3t_cs. exact R25.
- apply garr8_app. split.
  + apply (r3t_garr8_kept (w_H W1) (w_H W2) memT mem2); [|exact Gpre].
    intros j Hj. rewrite Hpre in Hj. apply KF; lia.
  + rewrite Hpre, Z2Nat.id by lia. replace (rbn_F X pos + 32 + n) with (rbn_F X pos + 32 + n) by ring. exact Hdig.
Qed.
Lemma r3t_core_tr : forall X pos P sh sh2 cells cells2 regs1 regs2 lyc1 Sc1 W1 memc1 mdc1 mem2 md2,
  rbn_cx B X -> r3t_core X pos P sh cells regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 mem2 md2 (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 4208 <= a < rbn_A X + 184) ->
     ~ (rbn_F X pos <= a < rbn_F X pos + 504) -> ~ (rbn_SH X pos <= a < rbn_SH X pos + 64) ->
     aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  rbn_shadow_at W1 mem2 (rbn_SH X pos) sh2 -> rbn_cells (mrestrict (w_H W1) mem2) cells2 ->
  r3t_same regs1 regs2 ->
  r3t_core X pos P sh2 cells2 regs2 lyc1 Sc1 W1 mem2 md2.
Proof.
intros X pos P sh sh2 cells cells2 regs1 regs2 lyc1 Sc1 W1 memc1 mdc1 mem2 md2 HX HC HJ2 HN Hsh2 HC2 HSm.
destruct HC as (HM & (B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R26 & R20 & R23 & R24 & R27 & _ & HA & HSRC).
split; [exact (r3t_mid_eq X pos lyc1 Sc1 W1 memc1 mdc1 sh mem2 md2 sh2 HX HM HJ2 HN Hsh2)|].
assert (S : forall r, In r r3t_regl -> getr regs2 r = getr regs1 r) by exact HSm.
split.
{ unfold rbn_rbase. rewrite !S by (cbn [In r3t_regl]; tauto). repeat split; assumption. }
rewrite !S by (cbn [In r3t_regl]; tauto).
split; [exact R18|]. split; [exact R26|]. split; [exact R20|]. split; [exact R23|].
split; [exact R24|]. split; [exact R27|]. split; [exact HC2|]. split; [exact HA | exact HSRC].
Qed.
Lemma r3t_cells_A : forall X H H' (m m' : word -> option byte) l,
  Forall (fun c => match c with (a, n, _) => rbn_A X <= a /\ a + Z.of_nat n <= rbn_A X + 184 end) l ->
  (forall a, rbn_A X <= a < rbn_A X + 184 -> aview SEGS H' m' a = aview SEGS H m a) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros X H H' m m' l HF HK. apply r3t_cells_kept. intros a n v k Hin Hk.
rewrite Forall_forall in HF. specialize (HF _ Hin). cbv beta iota in HF. apply HK. lia.
Qed.
Lemma r3t_Dfin : forall X pos P n n2 v pre q regs1 lyc1 Sc1 W1 memc1 mdc1 regsT memT mdT,
  rbn_cx B X ->
  r3t_core X pos P (rbn_sh true false false false) (r3t_cells2 X pos n) regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memT mdT (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview SEGS (w_H W1) memT a = aview SEGS (w_H W1) memc1 a) ->
  r3t_same regs1 regsT -> getr regs1 25 = w64 (rbn_F X pos + 32) ->
  (n = 0 \/ n = 2) -> n2 = n + 2 -> length pre = Z.to_nat n -> bn_ok v = true ->
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 32) pre ->
  getr regsT 1 = Z_to_bv 64 (BASE + (AF_reac_box_name + q)) -> 0 <= q < 4096 -> q mod 2 = 0 ->
  getr regsT 10 = w64 (rbn_A X + 152) -> getr regsT 11 = w64 v -> getr regsT 12 = w64 2 ->
  SRr SEGS W1 (mkCfg (mkst (fx := ri_fq X) regsT (Z_to_bv 64 (SIGMA DS_sb_dec)) memT (seg_rom SEGS)) mdT)
    (r3t_at X q (fun regs2 lyc2 Sc2 W2 mem2 md2 =>
       r3t_core X pos P (rbn_sh true false false false) (r3t_cells2 X pos n2) regs2 lyc2 Sc2 W2 mem2 md2 /\
       getr regs2 25 = w64 (rbn_F X pos + 32) /\
       garr8 SEGS (mrestrict (w_H W2) mem2) (rbn_F X pos + 32) (pre ++ bn_dec v 2))).
Proof.
intros X pos P n n2 v pre q regs1 lyc1 Sc1 W1 memc1 mdc1 regsT memT mdT HX HC HJ Kr HSm R25 Hn Hn2 Hpre Hv Gpre
  Rra Hq0 Hq2 Ra0 Ra1 Ra2.
pose proof HC as (HM & _ & _ & _ & _ & _ & _ & _ & HCL & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & Hsh).
destruct (r3t_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (K : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) memT a = aview SEGS (w_H W1) memc1 a)
  by (intros a Ha; exact (Kr a Ha (fun H => H))).
rewrite pa_sigma_sb_dec.
apply (r3t_dcall X pos P regsT lyc1 Sc1 W1 memT mdT n n2 v pre q HX); try assumption.
- apply (r3t_core_tr X pos P _ _ _ _ regs1 regsT lyc1 Sc1 W1 memc1 mdc1 memT mdT HX HC HJ).
  + intros a Ha _ _ _. exact (K a Ha).
  + intros j Hj. rewrite r3h_sh_len in Hj. rewrite K by (rewrite G18; unfold SHADOW_OFF; lia).
    apply Hsh. rewrite r3h_sh_len. exact Hj.
  + assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
    apply (r3t_cells_A X (w_H W1) (w_H W1) memc1 memT); [|intros a Ha; apply K; lia | exact HCL].
    unfold r3t_cells2. repeat constructor; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
  + exact HSm.
- apply (r3t_garr8_kept (w_H W1) (w_H W1) memc1 memT); [|exact Gpre].
  intros j Hj. apply K. lia.
- rewrite (HSm 25%bv ltac:(cbn [In r3t_regl]; tauto)). exact R25.
Qed.
Lemma r3t_D1 : forall X pos P (W1 : world SEGS) c1, rbn_cx B X -> r3t_at X RBN_Q2 (r3t_s2 X pos P) W1 c1 ->
  SRr SEGS W1 c1 (r3t_at X RBN_Q3 (r3t_s3 X pos P)).
Proof.
intros X pos P W1 c1 HX (regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & HC & R25).
pose proof HC as (HM & (B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R26 & R20 & R23 & R24 & R27 & HCL & HA & HSRC).
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & Hsh).
destruct (r3h_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8).
destruct (r3t_args _ _ _ _ _ _ _ _ HA) as (Hbi & Hbo).
destruct (r3t_dec2 _ Hbi) as (_ & _ & Hi40). destruct (r3t_dec2 _ Hbo) as (_ & _ & Ho40).
pose proof HCL as HCL0. unfold r3t_cells2 in HCL0. cbn [rbn_cells] in HCL0.
destruct HCL0 as (_ & _ & _ & M80 & M88 & _).
pose proof pa_B_ok as (HB0 & HB1 & HB4). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (r3t_entryD (ri_fq X) regs1 W1 memc1 (rbn_A X) (ri_i X) (ri_o X) RBN_Q2 B9 ltac:(lia) ltac:(lia) AR7
  ltac:(lia) ltac:(lia) M80 M88) as HS.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (@SRr_run_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call (ri_fq X) _ _ _ _ _ B LAWS) as RUNC.
remember (r3t_ED regs1 (ri_i X) (ri_o X)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold r3t_ED; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (ri_i X))
  by (subst E; unfold r3t_ED; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = rbn_A X)
  by (rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; lia).
assert (HW : forall a, in_wrange E (ss_mem (r3t_ssD RBN_Q2)) a -> False)
  by (intros a (r & Hr & Hw); cbn [ss_mem r3t_ssD In] in Hr; destruct Hr as [<- | []];
      cbn [r3t_rD YP09.r_wlo YP09.r_whi] in Hw; lia).
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + RBN_Q2) with (BASE + (AF_reac_box_name + RBN_Q2)) by ring.
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
pose proof (r3h_kept E _ (w_H W1) memc1 (ms_mem ms) (fun _ => False) HFr HW) as Kr.
clear HF HFr HW.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
eapply SRr_mono.
{ apply (r3t_Dfin X pos P 0 2 (ri_i X) [] RBN_Q3 regs1 lyc1 Sc1 W1 memc1 mdc1 _ _ _ HX HC HJ Kr);
    [r3t_same_tac HS EE | exact R25 | left; reflexivity | reflexivity | reflexivity | exact Hbi | apply garr8_nil
    | rewrite Rra; f_equal; unfold AF_reac_box_name, RBN_Q3; lia | unfold RBN_Q3; lia | reflexivity
    | rewrite Ra0, U9; reflexivity | rewrite Ra1, E32; reflexivity | rewrite Ra2; reflexivity]. }
intros W2 c2 _ (regs2 & lyc2 & Sc2 & mem2 & md2 & -> & HC2 & R25' & G2).
exists regs2, lyc2, Sc2, mem2, md2. split; [reflexivity|]. split; [exact HC2|]. split; [exact R25' | exact G2].
Qed.
Lemma r3t_D2 : forall X pos P (W1 : world SEGS) c1, rbn_cx B X -> r3t_at X RBN_Q3 (r3t_s3 X pos P) W1 c1 ->
  SRr SEGS W1 c1 (r3t_at X RBN_Q4 (r3t_s4 X pos P)).
Proof.
intros X pos P W1 c1 HX (regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & HC & R25 & G1).
pose proof HC as (HM & (B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R26 & R20 & R23 & R24 & R27 & HCL & HA & HSRC).
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & Hsh).
destruct (r3h_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8).
destruct (r3t_args _ _ _ _ _ _ _ _ HA) as (Hbi & Hbo).
destruct (r3t_dec2 _ Hbi) as (_ & Hil & Hi40). destruct (r3t_dec2 _ Hbo) as (_ & _ & Ho40).
pose proof HCL as HCL0. unfold r3t_cells2 in HCL0. cbn [rbn_cells] in HCL0.
destruct HCL0 as (_ & _ & _ & M80 & M88 & _).
pose proof pa_B_ok as (HB0 & HB1 & HB4). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (r3t_entryD (ri_fq X) regs1 W1 memc1 (rbn_A X) (ri_i X) (ri_o X) RBN_Q3 B9 ltac:(lia) ltac:(lia) AR7
  ltac:(lia) ltac:(lia) M80 M88) as HS.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (@SRr_run_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call (ri_fq X) _ _ _ _ _ B LAWS) as RUNC.
remember (r3t_ED regs1 (ri_i X) (ri_o X)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold r3t_ED; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew E 33 = Z_to_bv 64 (ri_o X))
  by (subst E; unfold r3t_ED; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = rbn_A X)
  by (rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; lia).
assert (HW : forall a, in_wrange E (ss_mem (r3t_ssD RBN_Q3)) a -> False)
  by (intros a (r & Hr & Hw); cbn [ss_mem r3t_ssD In] in Hr; destruct Hr as [<- | []];
      cbn [r3t_rD YP09.r_wlo YP09.r_whi] in Hw; lia).
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + RBN_Q3) with (BASE + (AF_reac_box_name + RBN_Q3)) by ring.
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
pose proof (r3h_kept E _ (w_H W1) memc1 (ms_mem ms) (fun _ => False) HFr HW) as Kr.
clear HF HFr HW.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
eapply SRr_mono.
{ apply (r3t_Dfin X pos P 2 4 (ri_o X) (bn_dec (ri_i X) 2) RBN_Q4 regs1 lyc1 Sc1 W1 memc1 mdc1 _ _ _ HX HC HJ Kr);
    [r3t_same_tac HS EE | exact R25 | right; reflexivity | reflexivity | rewrite Hil; reflexivity | exact Hbo
    | exact G1
    | rewrite Rra; f_equal; unfold AF_reac_box_name, RBN_Q4; lia | unfold RBN_Q4; lia | reflexivity
    | rewrite Ra0, U9; reflexivity | rewrite Ra1, E33; reflexivity | rewrite Ra2; reflexivity]. }
intros W2 c2 _ (regs2 & lyc2 & Sc2 & mem2 & md2 & -> & HC2 & R25' & G2).
exists regs2, lyc2, Sc2, mem2, md2. split; [reflexivity|]. split; [exact HC2|]. split; [exact R25' | exact G2].
Qed.
Lemma r3t_cells_Ax : forall X lo hi H H' (m m' : word -> option byte) l,
  Forall (fun c => match c with (a, n, _) =>
    rbn_A X <= a /\ a + Z.of_nat n <= rbn_A X + 184 /\ (a + Z.of_nat n <= lo \/ hi <= a) end) l ->
  (forall a, rbn_A X <= a < rbn_A X + 184 -> ~ (lo <= a < hi) -> aview SEGS H' m' a = aview SEGS H m a) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros X lo hi H H' m m' l HF HK. apply r3t_cells_kept. intros a n v k Hin Hk.
rewrite Forall_forall in HF. specialize (HF _ Hin). cbv beta iota in HF. apply HK; lia.
Qed.
Lemma r3t_T2 : forall X pos P (W1 : world SEGS) c1, rbn_cx B X -> r3t_at X RBN_Q4 (r3t_s4 X pos P) W1 c1 ->
  SRr SEGS W1 c1 (r3t_at X RBN_Q5 (r3t_s5 X pos P)).
Proof.
intros X pos P W1 c1 HX (regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & HC & R25 & GW).
pose proof HC as (HM & (B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R26 & R20 & R23 & R24 & R27 & HCL & HA & HSRC).
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & Hsh).
destruct (r3t_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
destruct (r3h_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8).
destruct (r3t_args _ _ _ _ _ _ _ _ HA) as (Hbi & Hbo).
destruct (r3t_dec2 _ Hbi) as (_ & Hil & _). destruct (r3t_dec2 _ Hbo) as (_ & Hol & _).
assert (Hw4 : length (rbm_w4 X) = 4%nat) by (unfold rbm_w4, bn_w4; rewrite length_app, Hil, Hol; reflexivity).
pose proof HCL as HCL0. unfold r3t_cells2 in HCL0. cbn [rbn_cells] in HCL0.
destruct HCL0 as (_ & _ & _ & _ & _ & _ & _ & M168 & _).
pose proof pa_B_ok as (HB0 & HB1 & HB4). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
assert (Hsh5 : aview SEGS (w_H W1) memc1 (rbn_SH X pos + 4) = Some 5)
  by (rewrite (Hsh 4 ltac:(rewrite r3h_sh_len; lia)); reflexivity).
pose proof (r3t_buf_ra X pos W1 memc1 5 G15 G18 Hsh5 ltac:(lia) ltac:(lia)) as HRA.
assert (HBD : forall j, 0 <= j < 64 -> kLowShadowBeg <= rbn_SH X pos + j < kHighMemBeg).
{ intros j Hj. pose proof (r3h_sh_band (rbn_F X pos) 512 j G13 ltac:(lia) G14 ltac:(change (512 / 8) with 64; lia)) as Hb.
  exact Hb. }
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & Rtl & _).
pose proof (r3t_entryT2 (ri_fq X) regs1 W1 memc1 (rbn_A X) (rbn_F X pos + 32) B9 R25 B22 ltac:(lia) ltac:(lia) AR7
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (fun k Hk => G9 (rbn_A X + k) ltac:(unfold rbn_SP in *; lia)) M168) as HS.
remember (r3t_E regs1) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold r3t_E; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = rbn_A X)
  by (rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = rbn_F X pos + 32)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = SHADOW_OFF)
  by (rewrite (EE 22%nat 22%bv eq_refl), B22; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS r3h_Bx [mkSHE 25 4 5] E (mrestrict (w_H W1) memc1)).
{ unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
  eapply shent_ok_of_range.
  - exact HRA.
  - unfold U, r3h_Bx. cbn [sv_denot]. rewrite U22, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
  - unfold U. cbn [sv_denot]. rewrite U25, Z.add_0_r. apply unsigned_lit_small. lia.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
assert (HW : forall a, in_wrange E (ss_mem r3t_ssT2) a -> rbn_A X + 32 <= a < rbn_A X + 40).
{ intros a (r & Hr & Hw). cbn [ss_mem r3t_ssT2 In] in Hr. destruct Hr as [<- | []].
  cbn [r3t_rT2A YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite U9 in Hw. lia. }
pose proof (paj_run_to (fx := ri_fq X) B LAWS) as RUNTO.
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + RBN_Q4) with (BASE + (AF_reac_box_name + RBN_Q4)) by ring.
paj_run_to_tok RUNTO HS HJ SHOK r3h_span (AF_reac_box_name + RBN_Q5).
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off E _ _ (ri_STK X) (ri_sp0 X) (ri_FP X) _ _ lyc1 _ 9%nat (rbn_A X - ri_sp0 X));
    [reflexivity | rewrite U9; lia | cbn; unfold rbn_SP in *; lia | cbn; unfold rbn_SP in *; lia |].
  apply awr_ok_nil. }
pose proof (r3h_kept E _ (w_H W1) memc1 (ms_mem ms) _ HFr HW) as Kr.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RA.
cbn [ms_mem restrict] in RA.
apply SRr_ret. pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (12%bv : bv 5) Ra2. prreg HS (25%bv : bv 5) Rs9.
lazymatch goal with |- r3t_at _ _ _ _ (mkCfg (mkst (ms_regs ?m) (Z_to_bv 64 ?q) (ms_mem ?m) _) ?md) =>
  exists (ms_regs m), lyc1, Sc1, (ms_mem m), md end.
split; [unfold rbn_cfg, cfg_at, w64; do 2 f_equal; f_equal; unfold AF_reac_box_name, RBN_Q5; lia|].
assert (KA : forall a, rbn_A X <= a < rbn_A X + 184 -> ~ (rbn_A X + 32 <= a < rbn_A X + 40) ->
  aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) memc1 a) by (intros a Ha Hn; apply Kr; [lia | exact Hn]).
split.
{ apply (r3t_core_tr X pos P _ _ _ _ regs1 _ lyc1 Sc1 W1 memc1 mdc1 _ _ HX HC HJ).
  - intros a Ha H1 _ _. apply Kr; [exact Ha | lia].
  - intros j Hj. rewrite r3h_sh_len in Hj. rewrite Kr.
    + apply Hsh. rewrite r3h_sh_len. exact Hj.
    + pose proof (HBD j Hj). unfold kLowShadowBeg, kHighMemBeg in *. lia.
    + pose proof (HBD j Hj). unfold kLowShadowBeg, kHighMemBeg in *. unfold rbn_SP in *. lia.
  - unfold r3t_cells5. cbn [rbn_cells]. split.
    + apply (field_of_region _ _ 9 (rbn_A X) _ 32 176 32 40 32 8 (SOff 27 0) (ri_token_len X) RA);
        [cbn [ewset ew Nat.eqb]; exact U9 | cbn [In]; tauto | | cbn; lia | cbn; lia].
      cbn [sv_denot]. cbn [ewset ew Nat.eqb]. rewrite (EE 27%nat 27%bv eq_refl), R27. unfold w64.
      rewrite unsigned_lit_small, Z.add_0_r by lia. reflexivity.
    + apply (r3t_cells_Ax X (rbn_A X + 32) (rbn_A X + 40) (w_H W1) (w_H W1) memc1 (ms_mem ms)); [| exact KA | exact HCL].
      unfold r3t_cells2. repeat apply Forall_cons; try apply Forall_nil; cbn -[rbn_A rbn_F]; lia.
  - r3t_same_tac HS EE. }
split; [rewrite Rs9, (EE 25%nat 25%bv eq_refl); exact R25|].
split; [rewrite Ra2; reflexivity|].
split; [rewrite Ra0; cbn [sv_denot]; rewrite ?U25; unfold w64; f_equal; lia|].
apply (r3t_garr8_kept (w_H W1) (w_H W1) memc1 (ms_mem ms)); [|exact GW].
intros j Hj. rewrite Hw4 in Hj. apply Kr; [lia | lia].
Qed.
Lemma r3t_P4 : forall X pos P (W1 : world SEGS) c1, rbn_cx B X -> r3t_at X RBN_Q5 (r3t_s5 X pos P) W1 c1 ->
  SRr SEGS W1 c1 (r3t_at X RBN_Q6 (r3t_s6 X pos P)).
Proof.
intros X pos P W1 c1 HX (regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & HC & R25 & R12 & R10 & GW).
pose proof HC as (HM & (B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R26 & R20 & R23 & R24 & R27 & HCL & HA & HSRC).
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & Hsh).
destruct (r3t_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
destruct (r3h_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8).
destruct (r3t_args _ _ _ _ _ _ _ _ HA) as (Hbi & Hbo).
destruct (r3t_dec2 _ Hbi) as (_ & Hil & _). destruct (r3t_dec2 _ Hbo) as (_ & Hol & _).
assert (Hw4 : length (rbm_w4 X) = 4%nat) by (unfold rbm_w4, bn_w4; rewrite length_app, Hil, Hol; reflexivity).
pose proof pa_B_ok as (HB0 & HB1 & HB4). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
assert (HBD : forall j, 0 <= j < 64 -> kLowShadowBeg <= rbn_SH X pos + j < kHighMemBeg).
{ intros j Hj. pose proof (r3h_sh_band (rbn_F X pos) 512 j G13 ltac:(lia) G14 ltac:(change (512 / 8) with 64; lia)) as Hb.
  exact Hb. }
assert (HSF : rbn_SH X pos + 64 <= rbn_F X pos \/ rbn_F X pos + 512 <= rbn_SH X pos).
{ pose proof (HBD 0 ltac:(lia)). pose proof (HBD 63 ltac:(lia)).
  unfold in_app, kLowShadowBeg, kHighMemBeg in *. lia. }
pose proof (r3t_entryP4 (ri_fq X) regs1 W1 memc1 (rbn_F X pos + 36) (rbn_SH X pos) R10 R18
  ltac:(lia) ltac:(rewrite G18; unfold SHADOW_OFF; lia) ltac:(rewrite G18; unfold SHADOW_OFF; lia) ltac:(lia)
  ltac:(lia) (proj1 (G17 (rbn_F X pos + 36) ltac:(lia))) (fun k Hk => proj1 (G19 k ltac:(lia)))) as HS.
remember (r3t_E regs1) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold r3t_E; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
assert (U10 : bv_unsigned (ew E 10) = rbn_F X pos + 36)
  by (rewrite (EE 10%nat 10%bv eq_refl), R10; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = rbn_SH X pos)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; rewrite G18; unfold SHADOW_OFF; lia).
assert (HW : forall a, in_wrange E (ss_mem r3t_ssP4) a ->
  a = rbn_F X pos + 36 \/ (rbn_SH X pos + 8 <= a < rbn_SH X pos + 11)).
{ intros a (r & Hr & Hw). cbn [ss_mem r3t_ssP4 In] in Hr.
  repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
  - rewrite U10 in Hw. left. lia.
  - rewrite U18 in Hw. right. lia. }
pose proof (@SRr_run_to_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNTOP.
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + RBN_Q5) with (BASE + (AF_reac_box_name + RBN_Q5)) by ring.
paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN_Q6).
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 10%nat (rbn_F X pos + 36)); [reflexivity | exact U10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 3, pos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite (G12 3 pos). change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos).
    change (fs_frame_bytes 3) with 512. lia. }
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 18%nat (rbn_SH X pos)); [reflexivity | exact U18 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 3, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite (G12 3 pos). change (fs_frame_bytes 3 / 8) with 64.
    change (shadow_addr (frame_addr (ri_lyc X) 3 pos)) with (rbn_SH X pos). lia. }
  apply awr_ok_nil. }
pose proof (r3h_kept E _ (w_H W1) memc1 (ms_mem ms) _ HFr HW) as Kr.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RF.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RS.
cbn [ms_mem restrict] in RF, RS.
apply SRr_ret. pmkst HS.
prreg HS (12%bv : bv 5) Ra2. prreg HS (25%bv : bv 5) Rs9.
lazymatch goal with |- r3t_at _ _ _ _ (mkCfg (mkst (ms_regs ?m) (Z_to_bv 64 ?q) (ms_mem ?m) _) ?md) =>
  exists (ms_regs m), lyc1, Sc1, (ms_mem m), md end.
split; [unfold rbn_cfg, cfg_at, w64; do 2 f_equal; f_equal; unfold AF_reac_box_name, RBN_Q6; lia|].
assert (VF : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_F X pos + 36) 1 0).
{ replace (rbn_F X pos + 36) with (rbn_F X pos + 36 + 0) by ring.
  apply (field_of_region _ _ 10 (rbn_F X pos + 36) _ 0 1 0 1 0 1 (SLit 0) 0 RF);
    [cbn [ewset ew Nat.eqb]; exact U10 | cbn [In]; tauto | reflexivity | cbn; lia | cbn; lia]. }
assert (VS : forall j, 8 <= j < 11 -> aview SEGS (w_H W1) (ms_mem ms) (rbn_SH X pos + j) = Some 0).
{ intros j Hj. pose proof (HBD j ltac:(lia)) as Hbj. unfold kLowShadowBeg, kHighMemBeg in Hbj.
  apply aview_of_val_mem1; [|lia].
  apply (field_of_region _ _ 18 (rbn_SH X pos) _ 0 64 8 11 j 1 (SLit 0) 0 RS);
    [cbn [ewset ew Nat.eqb]; exact U18 | | reflexivity | cbn; lia | cbn; lia].
  cbn [In]. assert (Hj3 : j = 8 \/ j = 9 \/ j = 10) by lia. destruct Hj3 as [-> | [-> | ->]]; tauto. }
split.
{ apply (r3t_core_tr X pos P _ _ _ _ regs1 _ lyc1 Sc1 W1 memc1 mdc1 _ _ HX HC HJ).
  - intros a Ha _ H2 H3. apply Kr; [exact Ha | intros [Hc | Hc]; lia].
  - intros j Hj. rewrite r3h_sh_len in Hj.
    destruct (Z_lt_le_dec j 8) as [Hj8 | Hj8]; [|destruct (Z_lt_le_dec j 11) as [Hj11 | Hj11]].
    + rewrite Kr; [| rewrite G18; unfold SHADOW_OFF; lia | intros [Hc | Hc]; lia].
      rewrite (Hsh j) by (rewrite r3h_sh_len; lia). rewrite r3t_sh_nb by lia. reflexivity.
    + rewrite (VS j) by lia. rewrite r3t_sh_nb0 by lia. reflexivity.
    + rewrite Kr; [| rewrite G18; unfold SHADOW_OFF; lia | intros [Hc | Hc]; lia].
      rewrite (Hsh j) by (rewrite r3h_sh_len; lia). rewrite r3t_sh_nb by lia. reflexivity.
  - apply (r3t_cells_A X (w_H W1) (w_H W1) memc1 (ms_mem ms)); [| | exact HCL].
    + unfold r3t_cells5, r3t_cells2. repeat apply Forall_cons; try apply Forall_nil; cbn -[rbn_A rbn_F]; lia.
    + intros a Ha. apply Kr; [lia|]. intros [Hc | Hc].
      * lia.
      * pose proof (HBD 8 ltac:(lia)). pose proof (HBD 10 ltac:(lia)). unfold kLowShadowBeg, kHighMemBeg in *. lia.
  - r3t_same_tac HS EE. }
split; [rewrite Rs9, (EE 25%nat 25%bv eq_refl); exact R25|].
split; [rewrite Ra2, (EE 12%nat 12%bv eq_refl); exact R12|].
apply garr8_app. split.
- apply (r3t_garr8_kept (w_H W1) (w_H W1) memc1 (ms_mem ms)); [|exact GW].
  intros j Hj. rewrite Hw4 in Hj. apply Kr; [lia|]. intros [Hc | Hc]; [lia|].
  pose proof (HBD 8 ltac:(lia)). unfold in_app, kLowShadowBeg, kHighMemBeg in *. lia.
- rewrite Hw4. intros j Hj. cbn [length] in Hj. assert (j = 0%nat) as -> by lia.
  cbn [nth]. split; [|lia]. replace (rbn_F X pos + 32 + Z.of_nat 4 + Z.of_nat 0) with (rbn_F X pos + 36) by lia.
  exact VF.
Qed.
Lemma r3t_T3 : forall X pos P (W1 : world SEGS) c1, rbn_cx B X -> r3t_at X RBN_Q6 (r3t_s6 X pos P) W1 c1 ->
  SRr SEGS W1 c1 (rbn_at4 B X).
Proof.
intros X pos P W1 c1 HX (regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & HC & R25 & R12 & GW).
pose proof HC as (HM & (B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R26 & R20 & R23 & R24 & R27 & HCL & HA & HSRC).
destruct HSRC as (HP0 & HP1 & HPK).
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & Hsh).
destruct (r3t_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
destruct (r3h_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8).
pose proof pa_B_ok as (HB0 & HB1 & HB4). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rnm & _).
destruct (HPK _ _ _ _ _ _ HM) as (Hstr & Hdis).
pose proof Hstr as (Hch & Hg & Hp0 & Hp1 & Hl32 & Ham & Hra & _).
destruct (r3t_hd W1 memc1 P (rbm_stem X) (r3t_stem_ne (ri_sd X) (ri_f X)) Hch Hg) as (Hc & Hlen & Vc).
assert (Hap : ~ (SHADOW_OFF <= P < SHADOW_OFF + 17592186044416))
  by (unfold amem_range in Ham; unfold SHADOW_OFF; lia).
assert (Hdj : P + 1 <= rbn_A X + 16 \/ rbn_A X + 24 <= P).
{ destruct (Hdis P ltac:(lia)) as [Hd1 _]. unfold rbn_SP in *. lia. }
assert (HRA1 : range_addressable (aview SEGS (w_H W1) memc1) SHADOW_OFF P 1)
  by (eapply range_addressable_sub; [exact Hra | lia | lia]).
destruct (r3t_entryT3 (ri_fq X) regs1 W1 memc1 (rbn_A X) P (hd 0 (rbm_stem X)) B9 R20 B22 ltac:(lia) ltac:(lia) AR7
  ltac:(lia) Hdj Hc (fun o Ho => G9 (rbn_A X + o) ltac:(unfold rbn_SP in *; lia)) Vc HRA1 Hap) as [HS SHOK].
remember (r3h_EA regs1 (hd 0 (rbm_stem X))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold r3h_EA; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold r3h_EA; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (hd 0 (rbm_stem X)))
  by (subst E; unfold r3h_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = rbn_A X)
  by (rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = rbn_F X pos)
  by (rewrite (EE 19%nat 19%bv eq_refl), B19; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = P)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
assert (HW : forall a, in_wrange E (ss_mem r3t_ssT3) a -> rbn_A X + 16 <= a < rbn_A X + 24).
{ intros a (r & Hr & Hw). cbn [ss_mem r3t_ssT3 In] in Hr.
  repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [r3t_rT3A r3h_rS YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
  - rewrite U9 in Hw. lia.
  - lia. }
pose proof (paj_run_to (fx := ri_fq X) B LAWS) as RUNTO.
unfold rbn_at4.
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + RBN_Q6) with (BASE + (AF_reac_box_name + RBN_Q6)) by ring.
paj_run_to_tok RUNTO HS HJ SHOK r3h_span (AF_reac_box_name + RBN_P4).
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off E _ _ (ri_STK X) (ri_sp0 X) (ri_FP X) _ _ lyc1 _ 9%nat (rbn_A X - ri_sp0 X));
    [reflexivity | rewrite U9; lia | cbn; unfold rbn_SP in *; lia | cbn; unfold rbn_SP in *; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (r3h_kept E _ (w_H W1) memc1 (ms_mem ms) _ HFr HW) as Kr.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RA.
cbn [ms_mem restrict] in RA.
apply SRr_ret. pmkst HS.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
prreg HS (9%bv : bv 5) Rs1. prreg HS (19%bv : bv 5) Rs3. prreg HS (22%bv : bv 5) Rs6. prreg HS (18%bv : bv 5) Rs2.
prreg HS (26%bv : bv 5) Rs10. prreg HS (20%bv : bv 5) Rs4. prreg HS (23%bv : bv 5) Rs7. prreg HS (25%bv : bv 5) Rs9.
prreg HS (27%bv : bv 5) Rs11. prreg HS (24%bv : bv 5) Rs8. prreg HS (30%bv : bv 5) Rt5. prreg HS (15%bv : bv 5) Ra5.
prreg HS (13%bv : bv 5) Ra3. prreg HS (10%bv : bv 5) Ra0. prreg HS (14%bv : bv 5) Ra4. prreg HS (12%bv : bv 5) Ra2.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md _ => set (md2 := md) in * end.
exists pos, (ms_regs ms), lyc1, Sc1, (ms_mem ms), md2, P.
split; [unfold rbn_cfg, cfg_at, w64; do 2 f_equal; f_equal; unfold AF_reac_box_name, RBN_P4; lia|].
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 16 <= a < rbn_A X + 24) ->
  aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) memc1 a) by (intros a Ha Hn; apply Kr; [exact Ha | exact Hn]).
assert (HM2 : rbn_mid B X pos lyc1 Sc1 W1 (ms_mem ms) md2 (fun _ => False) (rbn_sh true true false false)).
{ apply (r3t_mid_eq X pos lyc1 Sc1 W1 memc1 mdc1 _ (ms_mem ms) md2 _ HX HM HJ).
  - intros a Ha H1 _ _. apply KA; [exact Ha | lia].
  - intros j Hj. rewrite KA; [exact (Hsh j Hj) | | ].
    + rewrite r3h_sh_len in Hj. rewrite G18. unfold SHADOW_OFF. lia.
    + rewrite r3h_sh_len in Hj. rewrite G18. unfold SHADOW_OFF. lia. }
destruct (r3t_args _ _ _ _ _ _ _ _ HA) as (Hbi & Hbo).
destruct (r3t_dec2 _ Hbi) as (_ & Hil & _). destruct (r3t_dec2 _ Hbo) as (_ & Hol & _).
assert (Hw4 : length (rbm_w4 X) = 4%nat) by (unfold rbm_w4, bn_w4; rewrite length_app, Hil, Hol; reflexivity).
unfold r3t_cells5, r3t_cells2 in HCL. cbn [rbn_cells] in HCL.
destruct HCL as (M32 & M8 & M56 & M64 & M80 & M88 & M152 & M160 & M168 & M176 & _).
assert (KV : forall a n v, rbn_A X <= a -> a + Z.of_nat n <= rbn_A X + 184 ->
  (a + Z.of_nat n <= rbn_A X + 16 \/ rbn_A X + 24 <= a) ->
  val_mem SEGS (mrestrict (w_H W1) memc1) a n v -> val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) a n v).
{ intros a n v H1 H2 H3 V. apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 (ms_mem ms)); [|exact V].
  intros k Hk. apply KA; lia. }
split; [exact HM2|].
split.
{ split; [rewrite Rsp, (EE 2%nat 2%bv eq_refl); exact B2|].
  split; [rewrite Rgp, (EE 3%nat 3%bv eq_refl); exact B3|].
  split; [rewrite Rtp, (EE 4%nat 4%bv eq_refl); exact B4|].
  split; [rewrite Rs0, (EE 8%nat 8%bv eq_refl); exact B8|].
  split; [rewrite Rs1, (EE 9%nat 9%bv eq_refl); exact B9|].
  split; [rewrite Rs3, (EE 19%nat 19%bv eq_refl); exact B19|].
  rewrite Rs6, (EE 22%nat 22%bv eq_refl); exact B22. }
split; [rewrite Rs2, (EE 18%nat 18%bv eq_refl); exact R18|].
split; [rewrite Rs10, (EE 26%nat 26%bv eq_refl); exact R26|].
split; [rewrite Rs4, (EE 20%nat 20%bv eq_refl); exact R20|].
split; [rewrite Rs7, (EE 23%nat 23%bv eq_refl); exact R23|].
split; [rewrite Rs9, (EE 25%nat 25%bv eq_refl); exact R25|].
split; [rewrite Rs11, U19; reflexivity|].
split; [rewrite Rs8; reflexivity|].
split; [rewrite Rt5; reflexivity|].
split; [rewrite Ra5, E32; reflexivity|].
split; [rewrite Ra3, U20; reflexivity|].
split; [rewrite Ra0, U20; reflexivity|].
split; [rewrite Ra4; reflexivity|].
split; [rewrite Ra2, (EE 12%nat 12%bv eq_refl); exact R12|].
split.
{ unfold rbn_locs4. cbn [rbn_cells].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact M8]|].
  split.
  { apply (field_of_region _ _ 9 (rbn_A X) _ 16 24 16 24 16 8 (SOff 24 0) (ri_name X) RA);
      [cbn [ewset ew Nat.eqb]; exact U9 | cbn [In]; tauto | | cbn; lia | cbn; lia].
    cbn [sv_denot]. cbn [ewset ew Nat.eqb]. rewrite (EE 24%nat 24%bv eq_refl), R24. unfold w64.
    rewrite unsigned_lit_small, Z.add_0_r by lia. reflexivity. }
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact M32]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact M56]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact M64]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact M80]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact M88]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact M152]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact M160]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact M168]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact M176] | exact I]. }
split.
{ apply (r3t_garr8_kept (w_H W1) (w_H W1) memc1 (ms_mem ms)); [|exact GW].
  intros j Hj. rewrite length_app, Hw4 in Hj. cbn [length] in Hj. apply KA; lia. }
split; [exact (HPK _ _ _ _ _ _ HM2) | exact HA].
Qed.
Theorem rbn3_tail : rbn3_tail_stmt B.
Proof.
intros X W1 c1 HX HM.
eapply SRr_bind; [exact (r3t_MS X W1 c1 HX HM)|].
intros W2 c2 _ (pos & P & H2).
eapply SRr_bind; [exact (r3t_D1 X pos P W2 c2 HX H2)|].
intros W3 c3 _ H3.
eapply SRr_bind; [exact (r3t_D2 X pos P W3 c3 HX H3)|].
intros W4 c4 _ H4.
eapply SRr_bind; [exact (r3t_T2 X pos P W4 c4 HX H4)|].
intros W5 c5 _ H5.
eapply SRr_bind; [exact (r3t_P4 X pos P W5 c5 HX H5)|].
intros W6 c6 _ H6.
exact (r3t_T3 X pos P W6 c6 HX H6).
Qed.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Theorem rbn_seg3 : rbn_seg3_stmt B.
Proof. exact (rbn_seg3_of_parts B (rbn3_head B LAWS DRO GM HV) rbn3_tail). Qed.
End h.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths, module names and numbers changed; 379 of its 508 lines of code are new or changed and 531 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/SbDecSeg5.v; 907 of its 974 lines of code are new or changed and 441 lines of the source are left out. *)
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
YC1g YC1h YC81 YC4b YC45 YC85 YC88 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDecLoops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition SBD_L2B : Z := 0x228.
Definition l2_Bx : sv := SOff 21 0.
Definition l2_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition l2_shx (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff 21 0).
Definition l2_srs :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    11%bv (SOff 18 16)) 12%bv (SOff 18 8)) 13%bv (SOff 18 24)) 7%bv (l2_shx (SOff 18 0)))
    28%bv (l2_shx (SOff 18 16))) 29%bv (l2_shx (SOff 18 8))) 14%bv (SOff 6 0).
Definition l2_recR : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 28 16 28
    [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0));
     YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 4 (SOff 35 0))].
Definition l2_digR : YP09.region := YP09.mkRegion (Some 6%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))].
Definition l2_dstR : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 1 [].
Definition l2_cellR : YP09.region := YP09.mkRegion (Some 30%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 38 0))].
Definition l2_cmn : list (nat * afact) :=
  [(18%nat, mkAF 4096 (2 ^ 47 - 28) 3); (21%nat, mkAF SB SB 0); (31%nat, mkAF 3 3 0); (19%nat, mkAF 1 1 0);
   (32%nat, mkAF 0 (2 ^ 64 - 1) 0); (33%nat, mkAF 0 (2 ^ 64 - 1) 0); (34%nat, mkAF 0 (2 ^ 64 - 2) 0);
   (35%nat, mkAF 0 (2 ^ 32 - 1) 0); (5%nat, mkAF (2 ^ 64 - 3) (2 ^ 64 - 1) 0)].
Definition l2_ssC (st : Z) : sstate :=
  mkSS (AF_sb_dec + st) l2_srs [l2_recR; l2_digR; l2_dstR] None
    (mkFacts ((6%nat, mkAF 4096 (2 ^ 47 - 1) 0) :: (36%nat, mkAF 4096 (2 ^ 47 - 1) 0) ::
              (37%nat, mkAF 0 255 0) :: l2_cmn)
       [mkAC BC_LTU (SOff 34 1) (SOff 33 0)]
       [(SAlu ALU_ADD (SOff 32 0) (SOff 34 0), SOff 36 0)]).
Definition l2_ssO (st : Z) (z : bool) : sstate :=
  mkSS (AF_sb_dec + st) l2_srs [l2_recR; l2_cellR] None
    (mkFacts ((30%nat, mkAF SB (SB + 2 ^ 44 - 1) 0) :: (38%nat, if z then mkAF 0 0 0 else mkAF 4 7 0) :: l2_cmn)
       (mkAC BC_GEU (SOff 34 1) (SOff 33 0) :: (if z then [mkAC BC_EQ (SOff 38 0) (SLit 0)] else [])) []).
Definition l2_SHC : list shent := [mkSHE 18 28 16; mkSHE 36 1 0].
Definition l2_SHO : list shent := [mkSHE 18 28 16].
Definition l2_ssX : sstate :=
  mkSS (AF_sb_dec + SBD_L2B) (sr_set sr_atoms 5%bv (SLit 0)) [] None (mkFacts [] [] []).
Definition l2_keptC : list (bv 5) := [1; 2; 3; 4; 8; 9; 10; 16; 17; 18; 19; 21; 24; 25; 26; 27; 30; 31]%bv.
Lemma l2_soff : forall E n c z, ew E n = Z_to_bv 64 z -> sv_denot E (SOff n c) = Z_to_bv 64 (z + c).
Proof.
intros E n c z Hn. rewrite denot_lit_U, U_SOff, Hn. apply Z_to_bv64_eq_mod.
rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.
Lemma l2_af : forall E q v lo hi al, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  v mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E q (mkAF lo hi al).
Proof.
intros E q v lo hi al He Hv Hlh Hm Hal. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite He, unsigned_lit_small by exact Hv. lia.
Qed.
Lemma l2_vm1 : forall segs H (m : word -> option byte) a v,
  aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v.
Proof.
intros segs H m a v Hv. destruct (aview_byte segs H m a v Hv) as (b & Hb & -> & Hr).
intros k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small (bv_unsigned b) 256) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma l2_not_band : forall A x, (A + 28 <= 2147446784 \/ 17594333495296 <= A) -> A <= x < A + 28 ->
  ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof. intros A x HA Hx Hb. unfold SHADOW_OFF in Hb. lia. Qed.
Lemma l2_shadow_band : forall x, 0 <= x < 2 ^ 47 -> SHADOW_OFF <= SHADOW_OFF + x / 8 < SHADOW_OFF + 17592186044416.
Proof. intros x Hx. lia. Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma l2_app_not_band : forall a n x, in_app a n -> a <= x < a + n -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof.
intros a n x (H4 & Hc) Hx Hb. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. ceil. lia.
Qed.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Definition EL2 (regs : bvmap 5 word) (p cap n ov dn c s : Z) : env :=
  Eimg (Ereg regs (map (Z_to_bv 64) [p; cap; n; ov; dn; c; s])).
Lemma l2_ew : forall regs p cap n ov dn c s,
  ew (EL2 regs p cap n ov dn c s) 32 = Z_to_bv 64 p /\ ew (EL2 regs p cap n ov dn c s) 33 = Z_to_bv 64 cap /\
  ew (EL2 regs p cap n ov dn c s) 34 = Z_to_bv 64 n /\ ew (EL2 regs p cap n ov dn c s) 35 = Z_to_bv 64 ov /\
  ew (EL2 regs p cap n ov dn c s) 36 = Z_to_bv 64 dn /\ ew (EL2 regs p cap n ov dn c s) 37 = Z_to_bv 64 c /\
  ew (EL2 regs p cap n ov dn c s) 38 = Z_to_bv 64 s /\
  (forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (EL2 regs p cap n ov dn c s) k = getr regs r).
Proof.
intros regs p cap n ov dn c s. unfold EL2.
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)|].
intros k r Hk. apply ew_Eimg_Ereg_nat. exact Hk.
Qed.
Lemma l2_regs_ok : forall regs p cap n ov dn c s A q,
  0 <= A -> A + 28 <= 2 ^ 47 ->
  getr regs 11 = w64 (A + 16) -> getr regs 12 = w64 (A + 8) -> getr regs 13 = w64 (A + 24) ->
  getr regs 14 = w64 q -> getr regs 6 = w64 q ->
  getr regs 7 = w64 (SHADOW_OFF + A / 8) -> getr regs 28 = w64 (SHADOW_OFF + (A + 16) / 8) ->
  getr regs 29 = w64 (SHADOW_OFF + (A + 8) / 8) -> getr regs 18 = w64 A -> getr regs 21 = w64 SHADOW_OFF ->
  regs_ok (EL2 regs p cap n ov dn c s) l2_srs regs.
Proof.
intros regs p cap n ov dn c s A q HA0 HA47 H11 H12 H13 H14 H6 H7 H28 H29 H18 H21.
destruct (l2_ew regs p cap n ov dn c s) as (_ & _ & _ & _ & _ & _ & _ & EE).
set (E := EL2 regs p cap n ov dn c s) in *.
assert (E18 : ew E 18 = Z_to_bv 64 A) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
assert (E6 : ew E 6 = Z_to_bv 64 q) by (rewrite (EE 6%nat 6%bv eq_refl); exact H6).
assert (HR0 : regs_ok E sr_atoms regs) by (unfold E, EL2; apply regs_ok_Eimg_Ereg).
unfold l2_srs, l2_shx.
repeat (apply regs_ok_pin; [| discriminate |]); [exact HR0 | ..].
- rewrite H11, (l2_soff E 18 16 A E18). reflexivity.
- rewrite H12, (l2_soff E 18 8 A E18). reflexivity.
- rewrite H13, (l2_soff E 18 24 A E18). reflexivity.
- rewrite H7, (denot_shx E 18 21 0 A SHADOW_OFF E18 E21) by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r. reflexivity.
- rewrite H28, (denot_shx E 18 21 16 A SHADOW_OFF E18 E21) by (unfold SHADOW_OFF; lia). reflexivity.
- rewrite H29, (denot_shx E 18 21 8 A SHADOW_OFF E18 E21) by (unfold SHADOW_OFF; lia). reflexivity.
- rewrite H14, (l2_soff E 6 0 q E6), Z.add_0_r. reflexivity.
Qed.
Ltac l2_afs :=
  repeat first [ exact I
    | split; [ eapply l2_af; [ eassumption | unfold SB, SHADOW_OFF; lia | unfold SB, SHADOW_OFF; lia
        | first [ rewrite Z.pow_0_r; apply Z.mod_1_r | change (2 ^ 3) with 8; assumption ] | lia ] | ] ].
Lemma l2_w64_neg : forall t, -3 <= t <= -1 -> w64 t = Z_to_bv 64 (2 ^ 64 + t).
Proof.
intros t Ht. unfold w64. apply Z_to_bv64_eq_mod.
replace (2 ^ 64 + t) with (t + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma l2c_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) memc st A p cap n ov q c t,
  A mod 8 = 0 -> 4096 <= A -> A + 28 <= 2 ^ 47 ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n -> n + 1 < cap -> 0 <= ov < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) memc) A 8 p -> val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 n -> val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 4 ov ->
  (forall a, A + 16 <= a < A + 28 -> apresent (w_H W) memc a) ->
  0 <= c < 256 -> val_mem SEGS (mrestrict (w_H W) memc) q 1 c -> 4096 <= q -> q + 1 <= 2 ^ 47 ->
  4096 <= p + n -> p + n + 1 <= 2 ^ 47 -> apresent (w_H W) memc (p + n) ->
  (A + 28 <= q \/ q + 1 <= A) -> (p + n + 1 <= A \/ A + 28 <= p + n) -> (p + n + 1 <= q \/ q + 1 <= p + n) ->
  -3 <= t <= -1 -> getr regs 5 = w64 t ->
  getr regs 11 = w64 (A + 16) -> getr regs 12 = w64 (A + 8) -> getr regs 13 = w64 (A + 24) ->
  getr regs 14 = w64 q -> getr regs 6 = w64 q ->
  getr regs 7 = w64 (SHADOW_OFF + A / 8) -> getr regs 28 = w64 (SHADOW_OFF + (A + 16) / 8) ->
  getr regs 29 = w64 (SHADOW_OFF + (A + 8) / 8) ->
  getr regs 31 = w64 3 -> getr regs 19 = w64 1 -> getr regs 18 = w64 A -> getr regs 21 = w64 SHADOW_OFF ->
  st_ok_pi SEGS VAL (EL2 regs p cap n ov (p + n) c 0) (l2_ssC st)
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_sb_dec + st))) memc (seg_rom SEGS))).
Proof.
intros fq W regs memc st A p cap n ov q c t HA8 HA4 HA47 Rp Rcap Rn Hcp Rov Mp Mcap Mn Mov HWA Rc Mc Hq4 Hq47
  Hd4 Hd47 HPd Hqa Hda Hdq Ht H5 H11 H12 H13 H14 H6 H7 H28 H29 H31 H19 H18 H21.
rewrite restrict_mkst_fx.
pose proof (l2_regs_ok regs p cap n ov (p + n) c 0 A q ltac:(lia) HA47 H11 H12 H13 H14 H6 H7 H28 H29 H18 H21) as HR.
destruct (l2_ew regs p cap n ov (p + n) c 0) as (E32 & E33 & E34 & E35 & E36 & E37 & _ & EE).
set (E := EL2 regs p cap n ov (p + n) c 0) in *.
assert (E18 : ew E 18 = Z_to_bv 64 A) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
assert (E6 : ew E 6 = Z_to_bv 64 q) by (rewrite (EE 6%nat 6%bv eq_refl); exact H6).
assert (E31 : ew E 31 = Z_to_bv 64 3) by (rewrite (EE 31%nat 31%bv eq_refl); exact H31).
assert (E19 : ew E 19 = Z_to_bv 64 1) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
assert (E5 : ew E 5 = Z_to_bv 64 (2 ^ 64 + t)) by (rewrite (EE 5%nat 5%bv eq_refl), H5; apply l2_w64_neg; exact Ht).
unfold l2_ssC. apply pa_entry_st_ok_full.
- exact HR.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks l2_recR l2_digR l2_dstR base_val].
  + rewrite E18, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply HWA; lia|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    * apply (chunk_ok_val SEGS E _ A 0 8 (SOff 32 0) p); [rewrite (l2_soff E 32 0 p E32), Z.add_0_r; reflexivity | zside | zside |].
      change (N.to_nat 8) with 8%nat. rewrite Z.add_0_r. exact Mp.
    * apply (chunk_ok_val SEGS E _ A 8 8 (SOff 33 0) cap); [rewrite (l2_soff E 33 0 cap E33), Z.add_0_r; reflexivity | zside | zside |].
      change (N.to_nat 8) with 8%nat. exact Mcap.
    * apply (chunk_ok_val SEGS E _ A 16 8 (SOff 34 0) n); [rewrite (l2_soff E 34 0 n E34), Z.add_0_r; reflexivity | zside | zside |].
      change (N.to_nat 8) with 8%nat. exact Mn.
    * apply (chunk_ok_val SEGS E _ A 24 4 (SOff 35 0) ov); [rewrite (l2_soff E 35 0 ov E35), Z.add_0_r; reflexivity | zside | zside |].
      change (N.to_nat 4) with 4%nat. exact Mov.
  + rewrite E6, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ q 0 1 (SOff 37 0) c); [rewrite (l2_soff E 37 0 c E37), Z.add_0_r; reflexivity | zside | zside |].
    change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r. exact Mc.
  + rewrite E36, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). replace (p + n + o) with (p + n) by lia. exact HPd.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val l2_recR l2_digR l2_dstR].
  rewrite E18, E6, E36, !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split].
  + cbn [f_atoms atoms_ok l2_cmn]. l2_afs.
  + cbn [f_conds conds_ok]; unfold acond_ok; cbn [ac_c ac_a ac_b]. split; [|exact I].
    rewrite branch_ltu_U, (U_atom_off E 34 n 1 E34), (U_atom E 33 cap E33) by lia. apply Z.ltb_lt. lia.
  + cbn [f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 32 p E32), (U_atom E 34 n E34), (U_atom E 36 (p + n) E36) by lia.
    apply zcanon_id. unfold M64. lia.
Qed.
Lemma l2o_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) memc st (z : bool) A p cap n ov s t,
  A mod 8 = 0 -> 4096 <= A -> A + 28 <= 2 ^ 47 -> (A + 28 <= 2147446784 \/ 17594333495296 <= A) ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n -> n + 1 < 2 ^ 64 -> cap <= n + 1 -> 0 <= ov < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) memc) A 8 p -> val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 n -> val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 4 ov ->
  (forall a, A + 16 <= a < A + 28 -> apresent (w_H W) memc a) ->
  aview SEGS (w_H W) memc (SHADOW_OFF + (A + 24) / 8) = Some s ->
  ((z = true /\ s = 0) \/ (z = false /\ 4 <= s <= 7)) ->
  -3 <= t <= -1 -> getr regs 5 = w64 t ->
  getr regs 11 = w64 (A + 16) -> getr regs 12 = w64 (A + 8) -> getr regs 13 = w64 (A + 24) ->
  getr regs 14 = getr regs 6 ->
  getr regs 7 = w64 (SHADOW_OFF + A / 8) -> getr regs 28 = w64 (SHADOW_OFF + (A + 16) / 8) ->
  getr regs 29 = w64 (SHADOW_OFF + (A + 8) / 8) -> getr regs 30 = w64 (SHADOW_OFF + (A + 24) / 8) ->
  getr regs 31 = w64 3 -> getr regs 19 = w64 1 -> getr regs 18 = w64 A -> getr regs 21 = w64 SHADOW_OFF ->
  st_ok_pi SEGS VAL (EL2 regs p cap n ov 0 0 s) (l2_ssO st z)
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_sb_dec + st))) memc (seg_rom SEGS))).
Proof.
intros fq W regs memc st z A p cap n ov s t HA8 HA4 HA47 HAb Rp Rcap Rn Rn1 Hcp Rov Mp Mcap Mn Mov HWA Hcell Hz
  Ht H5 H11 H12 H13 H14 H7 H28 H29 H30 H31 H19 H18 H21.
rewrite restrict_mkst_fx.
pose proof (l2_regs_ok regs p cap n ov 0 0 s A (bv_unsigned (getr regs 6)) ltac:(lia) HA47 H11 H12 H13
  ltac:(rewrite H14; unfold w64; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(unfold w64; symmetry; apply Z_to_bv_bv_unsigned) H7 H28 H29 H18 H21) as HR.
destruct (l2_ew regs p cap n ov 0 0 s) as (E32 & E33 & E34 & E35 & _ & _ & E38 & EE).
set (E := EL2 regs p cap n ov 0 0 s) in *.
assert (Hs : 0 <= s < 256) by (destruct Hz as [[_ ->] | [_ Hs]]; lia).
assert (HSB : 0 <= SHADOW_OFF + (A + 24) / 8 < 2 ^ 64) by (unfold SHADOW_OFF; lia).
assert (E18 : ew E 18 = Z_to_bv 64 A) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
assert (E30 : ew E 30 = Z_to_bv 64 (SHADOW_OFF + (A + 24) / 8)) by (rewrite (EE 30%nat 30%bv eq_refl); exact H30).
assert (E31 : ew E 31 = Z_to_bv 64 3) by (rewrite (EE 31%nat 31%bv eq_refl); exact H31).
assert (E19 : ew E 19 = Z_to_bv 64 1) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
assert (E5 : ew E 5 = Z_to_bv 64 (2 ^ 64 + t)) by (rewrite (EE 5%nat 5%bv eq_refl), H5; apply l2_w64_neg; exact Ht).
unfold l2_ssO. apply pa_entry_st_ok_full.
- exact HR.
- destruct z; vm_compute; reflexivity.
- constructor; [|constructor; [|constructor]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks l2_recR l2_cellR base_val].
  + rewrite E18, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply HWA; lia|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    * apply (chunk_ok_val SEGS E _ A 0 8 (SOff 32 0) p); [rewrite (l2_soff E 32 0 p E32), Z.add_0_r; reflexivity | zside | zside |].
      change (N.to_nat 8) with 8%nat. rewrite Z.add_0_r. exact Mp.
    * apply (chunk_ok_val SEGS E _ A 8 8 (SOff 33 0) cap); [rewrite (l2_soff E 33 0 cap E33), Z.add_0_r; reflexivity | zside | zside |].
      change (N.to_nat 8) with 8%nat. exact Mcap.
    * apply (chunk_ok_val SEGS E _ A 16 8 (SOff 34 0) n); [rewrite (l2_soff E 34 0 n E34), Z.add_0_r; reflexivity | zside | zside |].
      change (N.to_nat 8) with 8%nat. exact Mn.
    * apply (chunk_ok_val SEGS E _ A 24 4 (SOff 35 0) ov); [rewrite (l2_soff E 35 0 ov E35), Z.add_0_r; reflexivity | zside | zside |].
      change (N.to_nat 4) with 4%nat. exact Mov.
  + rewrite E30, unsigned_lit_small by exact HSB.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ _ 0 1 (SOff 38 0) s); [rewrite (l2_soff E 38 0 s E38), Z.add_0_r; reflexivity | zside | zside |].
    change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r. exact (l2_vm1 SEGS _ _ _ _ Hcell).
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val l2_recR l2_cellR].
  rewrite E18, E30, !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SHADOW_OFF. repeat split; lia.
- split; [|split].
  + destruct Hz as [[-> Hs0] | [-> Hs0]]; cbn [f_atoms atoms_ok l2_cmn]; l2_afs.
  + destruct Hz as [[-> Hs0] | [-> Hs0]]; cbn [f_conds conds_ok]; unfold acond_ok; cbn [ac_c ac_a ac_b];
      (split; [rewrite branch_geu_U, (U_atom_off E 34 n 1 E34), (U_atom E 33 cap E33) by lia;
               apply negb_true_iff, Z.ltb_ge; lia|]).
    * split; [|exact I]. rewrite branch_eq_U, (U_atom E 38 s E38), U_SLit by lia. subst s. reflexivity.
    * exact I.
  + cbn [f_alias alias_ok]. exact I.
Qed.
Definition l2_cl : list Z := [5; 6; 14; 15; 20; 22; 23].
Definition l2_keepb (sr0 sr1 : list sv) : bool :=
  forallb (fun z => existsb (Z.eqb z) l2_cl ||
    (sv_eqb (sr_get sr1 (Z_to_bv 5 z)) (sr_get sr0 (Z_to_bv 5 z)) && sv_atoms_lt 512 (sr_get sr0 (Z_to_bv 5 z))))
    (map Z.of_nat (seq 0 32)).
Lemma l2_room_cp : forall cap n, 0 <= n -> n + 1 < cap ->
  sb_dec_c.sb_dec_room cap n = cap - 1 - n /\ sb_dec_c.sb_dec_room cap (n + 1) = cap - 2 - n.
Proof.
intros cap n Hn Hc. unfold sb_dec_c.sb_dec_room.
rewrite (proj2 (Z.leb_le (n + 1) cap)) by lia. rewrite (proj2 (Z.leb_le (n + 1 + 1) cap)) by lia. lia.
Qed.
Lemma l2_room_ovf : forall cap n, cap <= n + 1 -> sb_dec_c.sb_dec_room cap n = 0.
Proof. intros cap n Hc. unfold sb_dec_c.sb_dec_room. destruct (Z.leb_spec (n + 1) cap); lia. Qed.
Lemma l2_room_nonneg : forall cap n, 0 <= sb_dec_c.sb_dec_room cap n.
Proof. intros cap n. unfold sb_dec_c.sb_dec_room. destruct (Z.leb_spec (n + 1) cap); lia. Qed.
Lemma l2_kr : forall (regs regs2 : bvmap 5 word) (r : Z) (rb : bv 5),
  sbd_keep_regs regs regs2 l2_cl -> Z_to_bv 5 r = rb -> 0 <= r < 32 -> ~ In r l2_cl -> getr regs2 rb = getr regs rb.
Proof. intros regs regs2 r rb HK <- Hr Hn. exact (HK r Hr Hn). Qed.
Lemma l2_keep_trans : forall r1 r2 r3 : bvmap 5 word,
  sbd_keep_regs r1 r2 l2_cl -> sbd_keep_regs r2 r3 l2_cl -> sbd_keep_regs r1 r3 l2_cl.
Proof. intros r1 r2 r3 H1 H2 z Hz Hn. rewrite (H2 z Hz Hn). exact (H1 z Hz Hn). Qed.
Lemma l2_ra_kept : forall H (m m2 : word -> option byte) a len,
  (forall x, a <= x < a + len -> aview SEGS H m2 (SHADOW_OFF + x / 8) = aview SEGS H m (SHADOW_OFF + x / 8)) ->
  range_addressable (aview SEGS H m) SHADOW_OFF a len -> range_addressable (aview SEGS H m2) SHADOW_OFF a len.
Proof.
intros H m m2 a len He Hra x Hx. destruct (Hra x Hx) as (s & Hs & Hok).
exists s. split; [|exact Hok]. unfold shadow_of_addr in *. rewrite (He x Hx). exact Hs.
Qed.
Lemma l2_sh_notA : forall A x, (A + 28 <= 2147446784 \/ 17594333495296 <= A) -> 0 <= x < 2 ^ 47 ->
  ~ (A + 16 <= SHADOW_OFF + x / 8 < A + 28).
Proof. intros A x HA Hx Hb. unfold SHADOW_OFF in Hb. lia. Qed.
Lemma l2_sh_notapp : forall a n x, in_app a n -> 0 < n -> 0 <= x < 2 ^ 47 -> a <> SHADOW_OFF + x / 8.
Proof.
intros a n x Happ Hn Hx Heq. apply (l2_app_not_band a n a Happ ltac:(lia)). rewrite Heq. unfold SHADOW_OFF. lia.
Qed.
Lemma l2_kept_nil : forall E (H : word -> bool) (m m' : word -> option byte),
  frame_of E [] (mrestrict H m) (mrestrict H m') -> forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E H m m' HF a Ha. apply (kept_of_frame E [] H m m' (fun _ => False) HF); [| exact Ha | intros []].
intros b wlo whi x Hin. destruct Hin.
Qed.
Section g. Context {fx : YK11.FPState}.
Lemma l2_keep : forall sr0 E E' (regs : bvmap 5 word) (H1 : word -> bool) ms1 ss1,
  regs_ok E sr0 regs -> env_agree 512 E E' -> st_ok_pi SEGS VAL E' ss1 (restrict H1 ms1) ->
  l2_keepb sr0 (ss_regs ss1) = true -> sbd_keep_regs regs (ms_regs ms1) l2_cl.
Proof.
intros sr0 E E' regs H1 ms1 ss1 HR HAG HS Hb r Hr Hn.
unfold l2_keepb in Hb. rewrite forallb_forall in Hb.
assert (Hin : In r (map Z.of_nat (seq 0 32))).
{ apply in_map_iff. exists (Z.to_nat r). split; [lia | apply in_seq; lia]. }
specialize (Hb r Hin).
assert (He : existsb (Z.eqb r) l2_cl = false).
{ apply Bool.not_true_iff_false. intros Hx. apply existsb_exists in Hx as (x & Hx & Heq).
  apply Z.eqb_eq in Heq. subst x. exact (Hn Hx). }
rewrite He in Hb. cbn [orb] in Hb. apply andb_prop in Hb as [Hq Ha].
apply sv_eqb_eq in Hq.
rewrite (st_ok_pi_restrict_reg H1 E' ss1 ms1 _ HS), Hq, (HR (Z_to_bv 5 r)).
apply (sv_denot_agree 512 E E'); assumption.
Qed.
Lemma l2_rv : forall E E' (H1 : word -> bool) ms1 ss1 (r : bv 5) n c z,
  st_ok_pi SEGS VAL E' ss1 (restrict H1 ms1) -> env_agree 512 E E' -> sr_get (ss_regs ss1) r = SOff n c ->
  (n < 512)%nat -> ew E n = Z_to_bv 64 z -> getr (ms_regs ms1) r = Z_to_bv 64 (z + c).
Proof.
intros E E' H1 ms1 ss1 r n c z HS HAG Hr Hn En.
rewrite (st_ok_pi_restrict_reg H1 E' ss1 ms1 r HS), Hr.
rewrite (sv_denot_agree 512 E E') by (first [exact HAG | cbn [sv_atoms_lt]; apply Nat.ltb_lt; exact Hn]).
apply l2_soff. exact En.
Qed.
Lemma l2_field : forall E E' (H1 : word -> bool) ms1 ss1 i nb lo hi wlo whi cs b od (w : N) n c z,
  st_ok_pi SEGS VAL E' ss1 (restrict H1 ms1) -> env_agree 512 E E' ->
  nth_error (ss_mem ss1) i = Some (YP09.mkRegion (Some nb) lo hi wlo whi cs) -> (nb < 512)%nat ->
  ew E nb = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 ->
  In (YP09.mkChunk od (CVal w (SOff n c))) cs -> (n < 512)%nat -> ew E n = Z_to_bv 64 z ->
  0 <= z + c < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS (mrestrict H1 (ms_mem ms1)) (b + od) (N.to_nat w) (z + c).
Proof.
intros E E' H1 ms1 ss1 i nb lo hi wlo whi cs b od w n c z HS HAG Hnth Hnb Eb Hb Hin Hn En Hzc Hw.
pose proof (st_ok_pi_region_nth E' ss1 _ i _ HS Hnth) as HR. cbn [ms_mem restrict] in HR.
assert (Eb' : bv_unsigned (ew E' nb) = b).
{ destruct HAG as [HA _]. rewrite HA by exact Hnb. rewrite Eb. apply unsigned_lit_small. exact Hb. }
pose proof (@field_of_region_any SEGS E' _ nb b cs lo hi wlo whi od w (SOff n c) HR Eb' Hin Hw) as V.
rewrite (sv_denot_agree 512 E E') in V by (first [exact HAG | cbn [sv_atoms_lt]; apply Nat.ltb_lt; exact Hn]).
rewrite (l2_soff E n c z En) in V.
assert (Hp : 2 ^ (8 * Z.of_N w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
rewrite unsigned_lit_small in V by lia. rewrite Z.mod_small in V by lia. exact V.
Qed.
End g.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Definition l2_bpost (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (k : Z) (regs : bvmap 5 word)
  (A p cap n0 ov0 q c t : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = cfg_at (fx := fq) SEGS (BASE + AF_sb_dec + SBD_L2B) regs2 mem2 md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
    sbd_keep_regs regs regs2 l2_cl /\
    getr regs2 5 = w64 (t + 1) /\ getr regs2 6 = w64 (q - 1) /\ getr regs2 14 = w64 (q - 1) /\
    val_mem SEGS (mrestrict (w_H W) mem2) (A + 16) 8 (if n0 + 1 <? cap then n0 + 1 else n0) /\
    val_mem SEGS (mrestrict (w_H W) mem2) (A + 24) 4 (if n0 + 1 <? cap then ov0 else 1) /\
    (n0 + 1 < cap -> val_mem SEGS (mrestrict (w_H W) mem2) (p + n0) 1 c) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (A + 16 <= a < A + 28) -> ~ (n0 + 1 < cap /\ a = p + n0) ->
       aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a).
Lemma l2_post_cfg : forall (fq : YK11.FPState) pc E' ss1 (W : world SEGS) ms md,
  st_ok_pi SEGS VAL E' ss1 (restrict (w_H W) ms) -> ss_resv ss1 = None -> ss_pc ss1 = AF_sb_dec + pc ->
  {| cfg_ms := ms; cfg_model := md |} = cfg_at (fx := fq) SEGS (BASE + AF_sb_dec + pc) (ms_regs ms) (ms_mem ms) md.
Proof.
intros fq pc E' ss1 W ms md HS Hrv Hpc.
pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS Hrv) as Hms. rewrite Hpc in Hms.
rewrite Hms at 1. unfold cfg_at, w64. rewrite Z.add_assoc. reflexivity.
Qed.
Lemma l2c_post : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) A p cap n0 ov0 q c t E E' ss1 ms mat,
  regs_ok E l2_srs regs -> env_agree 512 E E' ->
  ew E 18 = Z_to_bv 64 A -> ew E 6 = Z_to_bv 64 q -> ew E 36 = Z_to_bv 64 (p + n0) ->
  ew E 5 = Z_to_bv 64 (2 ^ 64 + t) -> ew E 34 = Z_to_bv 64 n0 -> ew E 35 = Z_to_bv 64 ov0 -> ew E 37 = Z_to_bv 64 c ->
  0 <= A -> A + 28 <= 2 ^ 47 -> 4096 <= q -> q < 2 ^ 47 -> 0 <= p + n0 < 2 ^ 64 -> -3 <= t <= -1 ->
  0 <= n0 -> n0 + 1 < cap -> cap < 2 ^ 64 -> 0 <= ov0 < 2 ^ 32 -> 0 <= c < 256 ->
  st_ok_pi SEGS VAL E' ss1 (restrict (w_H W) ms) ->
  l2_keepb l2_srs (ss_regs ss1) = true ->
  sr_get (ss_regs ss1) 5 = SOff 5 1 -> sr_get (ss_regs ss1) 6 = SOff 6 (-1) -> sr_get (ss_regs ss1) 14 = SOff 6 (-1) ->
  ss_pc ss1 = AF_sb_dec + SBD_L2B -> ss_resv ss1 = None ->
  (exists cs0, nth_error (ss_mem ss1) 0 = Some (YP09.mkRegion (Some 18%nat) 0 28 16 28 cs0) /\
     In (YP09.mkChunk 16 (CVal 8 (SOff 34 1))) cs0 /\ In (YP09.mkChunk 24 (CVal 4 (SOff 35 0))) cs0) ->
  (exists cs2, nth_error (ss_mem ss1) 2 = Some (YP09.mkRegion (Some 36%nat) 0 1 0 1 cs2) /\
     In (YP09.mkChunk 0 (CVal 1 (SOff 37 0))) cs2) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc) k ->
  frame_of E [l2_recR; l2_digR; l2_dstR] (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)) ->
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)) ->
  SRr SEGS W (mkCfg ms (with_vm_backing (m_vm_lazy mdc) mat mdc))
    (l2_bpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs A p cap n0 ov0 q c t).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 q c t E E' ss1 ms mat
  HR HAG E18 E6 E36 E5 E34 E35 E37 HA0 HA47 Hq4 Hq47 Hd Ht Hn0 Hcp Hcap Hov Hc HS Hkb R5 R6 R14 Hpc Hrv
  (cs0 & Hr0 & C16 & C24) (cs2 & Hr2 & C0) HJ HFr HG.
apply SRr_ret. split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [exact (l2_post_cfg fq SBD_L2B E' ss1 W ms _ HS Hrv Hpc)|].
split; [exact HJ|].
split; [exact (l2_keep l2_srs E E' regs (w_H W) ms ss1 HR HAG HS Hkb)|].
split.
{ rewrite (l2_rv E E' (w_H W) ms ss1 5%bv 5 1 (2 ^ 64 + t) HS HAG R5 ltac:(lia) E5). unfold w64.
  apply Z_to_bv64_eq_mod. replace (2 ^ 64 + t + 1) with (t + 1 + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity. }
split; [rewrite (l2_rv E E' (w_H W) ms ss1 6%bv 6 (-1) q HS HAG R6 ltac:(lia) E6); unfold w64; f_equal; lia|].
split; [rewrite (l2_rv E E' (w_H W) ms ss1 14%bv 6 (-1) q HS HAG R14 ltac:(lia) E6); unfold w64; f_equal; lia|].
replace (n0 + 1 <? cap) with true by (symmetry; apply Z.ltb_lt; exact Hcp).
split.
{ pose proof (l2_field E E' (w_H W) ms ss1 0 18 0 28 16 28 cs0 A 16 8 34 1 n0 HS HAG Hr0 ltac:(lia) E18
    ltac:(lia) C16 ltac:(lia) E34 ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as V.
  change (N.to_nat 8) with 8%nat in V. exact V. }
split.
{ pose proof (l2_field E E' (w_H W) ms ss1 0 18 0 28 16 28 cs0 A 24 4 35 0 ov0 HS HAG Hr0 ltac:(lia) E18
    ltac:(lia) C24 ltac:(lia) E35 ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as V.
  change (N.to_nat 4) with 4%nat in V. rewrite Z.add_0_r in V. exact V. }
split.
{ intros _. pose proof (l2_field E E' (w_H W) ms ss1 2 36 0 1 0 1 cs2 (p + n0) 0 1 37 0 c HS HAG Hr2 ltac:(lia) E36
    ltac:(lia) C0 ltac:(lia) E37 ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as V.
  change (N.to_nat 1) with 1%nat in V. rewrite !Z.add_0_r in V. exact V. }
split.
{ intros a Ha Hn1 Hn2.
  apply (kept_of_frame E [l2_recR; l2_digR; l2_dstR] (w_H W) memc (ms_mem ms)
    (fun x => A + 16 <= x < A + 28 \/ x = p + n0) HFr); [| exact Ha |].
  - intros bq wlo whi aq Hin Haq.
    cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi l2_recR l2_digR l2_dstR In] in Hin.
    destruct Hin as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <- <-; cbn [base_val] in Haq;
      rewrite ?E18, ?E6, ?E36, ?unsigned_lit_small in Haq by lia; lia.
  - intros [Hx | Hx]; [exact (Hn1 Hx) | exact (Hn2 (conj Hcp Hx))]. }
intros a Ha. exact (apresent_grows (w_H W) memc (ms_mem ms) a HG Ha).
Qed.
Lemma l2o_post : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) A p cap n0 ov0 q c t E E' ss1 ms mat,
  regs_ok E l2_srs regs -> env_agree 512 E E' ->
  ew E 18 = Z_to_bv 64 A -> ew E 6 = Z_to_bv 64 q -> ew E 5 = Z_to_bv 64 (2 ^ 64 + t) ->
  ew E 34 = Z_to_bv 64 n0 -> ew E 19 = Z_to_bv 64 1 ->
  0 <= A -> A + 28 <= 2 ^ 47 -> 4096 <= q -> q < 2 ^ 47 -> -3 <= t <= -1 ->
  0 <= n0 -> n0 + 1 < 2 ^ 64 -> cap <= n0 + 1 ->
  st_ok_pi SEGS VAL E' ss1 (restrict (w_H W) ms) ->
  l2_keepb l2_srs (ss_regs ss1) = true ->
  sr_get (ss_regs ss1) 5 = SOff 5 1 -> sr_get (ss_regs ss1) 6 = SOff 6 (-1) -> sr_get (ss_regs ss1) 14 = SOff 6 (-1) ->
  ss_pc ss1 = AF_sb_dec + SBD_L2B -> ss_resv ss1 = None ->
  (exists cs0, nth_error (ss_mem ss1) 0 = Some (YP09.mkRegion (Some 18%nat) 0 28 16 28 cs0) /\
     In (YP09.mkChunk 16 (CVal 8 (SOff 34 0))) cs0 /\ In (YP09.mkChunk 24 (CVal 4 (SOff 19 0))) cs0) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc) k ->
  frame_of E [l2_recR; l2_cellR] (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)) ->
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)) ->
  SRr SEGS W (mkCfg ms (with_vm_backing (m_vm_lazy mdc) mat mdc))
    (l2_bpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs A p cap n0 ov0 q c t).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 q c t E E' ss1 ms mat
  HR HAG E18 E6 E5 E34 E19 HA0 HA47 Hq4 Hq47 Ht Hn0 Hn1 Hcp HS Hkb R5 R6 R14 Hpc Hrv
  (cs0 & Hr0 & C16 & C24) HJ HFr HG.
apply SRr_ret. split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [exact (l2_post_cfg fq SBD_L2B E' ss1 W ms _ HS Hrv Hpc)|].
split; [exact HJ|].
split; [exact (l2_keep l2_srs E E' regs (w_H W) ms ss1 HR HAG HS Hkb)|].
split.
{ rewrite (l2_rv E E' (w_H W) ms ss1 5%bv 5 1 (2 ^ 64 + t) HS HAG R5 ltac:(lia) E5). unfold w64.
  apply Z_to_bv64_eq_mod. replace (2 ^ 64 + t + 1) with (t + 1 + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity. }
split; [rewrite (l2_rv E E' (w_H W) ms ss1 6%bv 6 (-1) q HS HAG R6 ltac:(lia) E6); unfold w64; f_equal; lia|].
split; [rewrite (l2_rv E E' (w_H W) ms ss1 14%bv 6 (-1) q HS HAG R14 ltac:(lia) E6); unfold w64; f_equal; lia|].
replace (n0 + 1 <? cap) with false by (symmetry; apply Z.ltb_ge; exact Hcp).
split.
{ pose proof (l2_field E E' (w_H W) ms ss1 0 18 0 28 16 28 cs0 A 16 8 34 0 n0 HS HAG Hr0 ltac:(lia) E18
    ltac:(lia) C16 ltac:(lia) E34 ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as V.
  change (N.to_nat 8) with 8%nat in V. rewrite Z.add_0_r in V. exact V. }
split.
{ pose proof (l2_field E E' (w_H W) ms ss1 0 18 0 28 16 28 cs0 A 24 4 19 0 1 HS HAG Hr0 ltac:(lia) E18
    ltac:(lia) C24 ltac:(lia) E19 ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as V.
  change (N.to_nat 4) with 4%nat in V. exact V. }
split; [intros Hx; lia|].
split.
{ intros a Ha Hn2 _.
  apply (kept_of_frame E [l2_recR; l2_cellR] (w_H W) memc (ms_mem ms) (fun x => A + 16 <= x < A + 28) HFr);
    [| exact Ha | exact Hn2].
  intros bq wlo whi aq Hin Haq.
  cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi l2_recR l2_cellR In] in Hin.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Haq;
    rewrite ?E18, ?unsigned_lit_small in Haq by lia; lia. }
intros a Ha. exact (apresent_grows (w_H W) memc (ms_mem ms) a HG Ha).
Qed.

Lemma l2_body_c : forall st (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) A p cap n0 ov0 q c t,
  (st = SBD_L2 \/ st = SBD_L2B) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  A mod 8 = 0 -> 4096 <= A -> A + 28 <= 2 ^ 47 -> (A + 28 <= 2147446784 \/ 17594333495296 <= A) ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n0 -> n0 + 1 < cap -> 0 <= ov0 < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) memc) A 8 p -> val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 n0 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 4 ov0 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF A 28 ->
  sbd_wbytes B STK sp0 FP ly S own lyc Sc W memc (A + 16) 12 ->
  0 <= c < 256 -> val_mem SEGS (mrestrict (w_H W) memc) q 1 c -> 4096 <= q -> q + 1 <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q 1 -> (A + 28 <= q \/ q + 1 <= A) ->
  in_app (p + n0) 1 -> range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + n0) 1 ->
  sbd_wbytes B STK sp0 FP ly S own lyc Sc W memc (p + n0) 1 ->
  (p + n0 + 1 <= A \/ A + 28 <= p + n0) -> (p + n0 + 1 <= q \/ q + 1 <= p + n0) ->
  -3 <= t <= -1 -> getr regs 5 = w64 t ->
  getr regs 11 = w64 (A + 16) -> getr regs 12 = w64 (A + 8) -> getr regs 13 = w64 (A + 24) ->
  getr regs 14 = w64 q -> getr regs 6 = w64 q ->
  getr regs 7 = w64 (SHADOW_OFF + A / 8) -> getr regs 28 = w64 (SHADOW_OFF + (A + 16) / 8) ->
  getr regs 29 = w64 (SHADOW_OFF + (A + 8) / 8) ->
  getr regs 31 = w64 3 -> getr regs 19 = w64 1 -> getr regs 18 = w64 A -> getr regs 21 = w64 SHADOW_OFF ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_sb_dec + st) regs memc mdc)
    (l2_bpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs A p cap n0 ov0 q c t).
Proof.
intros st fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 q c t Hst HJ HA8 HA4 HA47 HAb
  Rp Rcap Rn0 Hcp Rov Mp Mcap Mn Mov HRA HWA Rc Mc Hq4 Hq47 HRAq Hqa Happ HRAd HWd Hda Hdq Ht H5
  H11 H12 H13 H14 H6 H7 H28 H29 H31 H19 H18 H21.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (@paj_run fq _ _ _ _ _ B LAWS) as RUN.
pose proof Happ as (Hd4 & Hdc). ceil.
assert (Hd47 : p + n0 + 1 <= 2 ^ 47) by (unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
destruct (HWd (p + n0) ltac:(lia)) as [HWd1 HPd].
assert (HPA : forall a, A + 16 <= a < A + 28 -> apresent (w_H W) memc a) by (intros a Ha; exact (proj2 (HWA a ltac:(lia)))).
pose proof (l2c_entry fq W regs memc st A p cap n0 ov0 q c t HA8 HA4 HA47 Rp Rcap Rn0 Hcp Rov Mp Mcap Mn Mov HPA
  Rc Mc Hq4 Hq47 Hd4 Hd47 HPd Hqa Hda Hdq Ht H5 H11 H12 H13 H14 H6 H7 H28 H29 H31 H19 H18 H21) as HS.
pose proof (l2_regs_ok regs p cap n0 ov0 (p + n0) c 0 A q ltac:(lia) HA47 H11 H12 H13 H14 H6 H7 H28 H29 H18 H21) as HR.
destruct (l2_ew regs p cap n0 ov0 (p + n0) c 0) as (E32 & E33 & E34 & E35 & E36 & E37 & _ & EE).
set (E := EL2 regs p cap n0 ov0 (p + n0) c 0) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, EL2; apply Eimg_env).
assert (E18 : ew E 18 = Z_to_bv 64 A) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
assert (E6 : ew E 6 = Z_to_bv 64 q) by (rewrite (EE 6%nat 6%bv eq_refl); exact H6).
assert (E5 : ew E 5 = Z_to_bv 64 (2 ^ 64 + t)) by (rewrite (EE 5%nat 5%bv eq_refl), H5; apply l2_w64_neg; exact Ht).
assert (HUB : U E l2_Bx = SHADOW_OFF) by (unfold l2_Bx; apply (U_atom E 21 SHADOW_OFF E21); unfold SHADOW_OFF; lia).
assert (HU18 : U E (SOff 18 0) = A) by (apply (U_atom E 18 A E18); lia).
assert (HU18a : U E (SOff 18 8) = A + 8) by (apply (U_atom_off E 18 A 8 E18); lia).
assert (HU18b : U E (SOff 18 16) = A + 16) by (apply (U_atom_off E 18 A 16 E18); lia).
assert (HU6 : U E (SOff 6 0) = q) by (apply (U_atom E 6 q E6); lia).
assert (HU36 : U E (SOff 36 0) = p + n0) by (apply (U_atom E 36 (p + n0) E36); lia).
assert (SHOK : sh_ok SEGS l2_Bx l2_SHC E (mrestrict (w_H W) memc)).
{ constructor; [|constructor; [|constructor]].
  - eapply shent_app_of_app; [exact HUB | exact HU18 | unfold kLowShadowBeg, kHighMemBeg; lia | lia].
  - eapply shent_app_of_app; [exact HUB | exact HU36 | unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia | lia]. }
unfold cfg_at. rewrite <- Z.add_assoc.
destruct Hst as [-> | ->]; (paj_run_tok RUN HS HJ SHOK l2_span;
  [ (cbn [ms_mem mkst]; rewrite ?HU18, ?HU18a, ?HU18b, ?HU6, ?HU36;
      first [ apply (obl_of_range SEGS (w_H W) memc E l2_Bx _ _ A 28 HRA HUB); lia
            | apply (obl_of_range SEGS (w_H W) memc E l2_Bx _ _ q 1 HRAq HUB); lia
            | apply (obl_of_range SEGS (w_H W) memc E l2_Bx _ _ (p + n0) 1 HRAd HUB); lia ]) ..
  | lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
    eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 18 A);
      [ reflexivity | rewrite E18; apply unsigned_lit_small; lia
      | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; exact (proj1 (HWA a ltac:(lia))) | ];
    apply awr_ok_cons_ro; [cbn; lia|];
    eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 36 (p + n0));
      [ reflexivity | rewrite E36; apply unsigned_lit_small; lia
      | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with (p + n0) by lia; exact HWd1 | apply awr_ok_nil ]
  | lazymatch type of HS with st_ok_pi _ _ ?E' ?ss1 _ =>
      apply (l2c_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 q c t E E' ss1) end;
    first [ exact HR | exact HS | exact HJ | exact HFr | exact HG | assumption
      | env_agree_chain (env_agree_refl 512 E) | lia | (vm_compute; reflexivity)
      | (eexists; split; [reflexivity | repeat split; cbn [In]; repeat (first [left; reflexivity | right])]) ] ]).
Qed.

Lemma l2_body_o : forall st (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) A p cap n0 ov0 q c t s,
  (st = SBD_L2 \/ st = SBD_L2B) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  A mod 8 = 0 -> 4096 <= A -> A + 28 <= 2 ^ 47 -> (A + 28 <= 2147446784 \/ 17594333495296 <= A) ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n0 -> n0 + 1 < 2 ^ 64 -> cap <= n0 + 1 -> 0 <= ov0 < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) memc) A 8 p -> val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 n0 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 4 ov0 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF A 28 ->
  sbd_wbytes B STK sp0 FP ly S own lyc Sc W memc (A + 16) 12 ->
  aview SEGS (w_H W) memc (SHADOW_OFF + (A + 24) / 8) = Some s -> (s = 0 \/ 4 <= s <= 7) ->
  4096 <= q -> q + 1 <= 2 ^ 47 ->
  -3 <= t <= -1 -> getr regs 5 = w64 t ->
  getr regs 11 = w64 (A + 16) -> getr regs 12 = w64 (A + 8) -> getr regs 13 = w64 (A + 24) ->
  getr regs 14 = w64 q -> getr regs 6 = w64 q ->
  getr regs 7 = w64 (SHADOW_OFF + A / 8) -> getr regs 28 = w64 (SHADOW_OFF + (A + 16) / 8) ->
  getr regs 29 = w64 (SHADOW_OFF + (A + 8) / 8) -> getr regs 30 = w64 (SHADOW_OFF + (A + 24) / 8) ->
  getr regs 31 = w64 3 -> getr regs 19 = w64 1 -> getr regs 18 = w64 A -> getr regs 21 = w64 SHADOW_OFF ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_sb_dec + st) regs memc mdc)
    (l2_bpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs A p cap n0 ov0 q c t).
Proof.
intros st fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 q c t s Hst HJ HA8 HA4 HA47 HAb
  Rp Rcap Rn0 Rn1 Hcp Rov Mp Mcap Mn Mov HRA HWA Hcell Hs Hq4 Hq47 Ht H5
  H11 H12 H13 H14 H6 H7 H28 H29 H30 H31 H19 H18 H21.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (@paj_run fq _ _ _ _ _ B LAWS) as RUN.
assert (HPA : forall a, A + 16 <= a < A + 28 -> apresent (w_H W) memc a) by (intros a Ha; exact (proj2 (HWA a ltac:(lia)))).
assert (Hz : exists z, (z = true /\ s = 0) \/ (z = false /\ 4 <= s <= 7))
  by (destruct Hs as [Hs | Hs]; [exists true | exists false]; auto).
destruct Hz as [z Hz].
pose proof (l2o_entry fq W regs memc st z A p cap n0 ov0 s t HA8 HA4 HA47 HAb Rp Rcap Rn0 Rn1 Hcp Rov Mp Mcap Mn Mov HPA
  Hcell Hz Ht H5 H11 H12 H13 ltac:(rewrite H14, H6; reflexivity) H7 H28 H29 H30 H31 H19 H18 H21) as HS.
pose proof (l2_regs_ok regs p cap n0 ov0 0 0 s A q ltac:(lia) HA47 H11 H12 H13 H14 H6 H7 H28 H29 H18 H21) as HR.
destruct (l2_ew regs p cap n0 ov0 0 0 s) as (E32 & E33 & E34 & E35 & _ & _ & E38 & EE).
set (E := EL2 regs p cap n0 ov0 0 0 s) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, EL2; apply Eimg_env).
assert (E18 : ew E 18 = Z_to_bv 64 A) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
assert (E6 : ew E 6 = Z_to_bv 64 q) by (rewrite (EE 6%nat 6%bv eq_refl); exact H6).
assert (E19 : ew E 19 = Z_to_bv 64 1) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
assert (E5 : ew E 5 = Z_to_bv 64 (2 ^ 64 + t)) by (rewrite (EE 5%nat 5%bv eq_refl), H5; apply l2_w64_neg; exact Ht).
assert (HUB : U E l2_Bx = SHADOW_OFF) by (unfold l2_Bx; apply (U_atom E 21 SHADOW_OFF E21); unfold SHADOW_OFF; lia).
assert (HU18 : U E (SOff 18 0) = A) by (apply (U_atom E 18 A E18); lia).
assert (HU18a : U E (SOff 18 8) = A + 8) by (apply (U_atom_off E 18 A 8 E18); lia).
assert (HU18b : U E (SOff 18 16) = A + 16) by (apply (U_atom_off E 18 A 16 E18); lia).
assert (SHOK : sh_ok SEGS l2_Bx l2_SHO E (mrestrict (w_H W) memc)).
{ constructor; [|constructor].
  eapply shent_app_of_app; [exact HUB | exact HU18 | unfold kLowShadowBeg, kHighMemBeg; lia | lia]. }
unfold cfg_at. rewrite <- Z.add_assoc.
destruct Hz as [[-> _] | [-> _]]; destruct Hst as [-> | ->]; (paj_run_tok RUN HS HJ SHOK l2_span;
  [ (cbn [ms_mem mkst]; rewrite ?HU18a, ?HU18b;
      apply (obl_of_range SEGS (w_H W) memc E l2_Bx _ _ A 28 HRA HUB); lia) ..
  | lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
    eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 18 A);
      [ reflexivity | rewrite E18; apply unsigned_lit_small; lia
      | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; exact (proj1 (HWA a ltac:(lia)))
      | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] ]
  | lazymatch type of HS with st_ok_pi _ _ ?E' ?ss1 _ =>
      apply (l2o_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 q c t E E' ss1) end;
    first [ exact HR | exact HS | exact HJ | exact HFr | exact HG | assumption
      | env_agree_chain (env_agree_refl 512 E) | lia | (vm_compute; reflexivity)
      | (eexists; split; [reflexivity | repeat split; cbn [In]; repeat (first [left; reflexivity | right])]) ] ]).
Qed.
Lemma l2_body : forall st (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) A p cap n0 ov0 q c t,
  (st = SBD_L2 \/ st = SBD_L2B) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  A mod 8 = 0 -> 4096 <= A -> A + 28 <= 2 ^ 47 -> (A + 28 <= 2147446784 \/ 17594333495296 <= A) ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n0 -> n0 + 1 < 2 ^ 64 -> 0 <= ov0 < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) memc) A 8 p -> val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 n0 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 4 ov0 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF A 28 ->
  sbd_wbytes B STK sp0 FP ly S own lyc Sc W memc (A + 16) 12 ->
  0 <= c < 256 -> val_mem SEGS (mrestrict (w_H W) memc) q 1 c -> 4096 <= q -> q + 1 <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q 1 -> (A + 28 <= q \/ q + 1 <= A) ->
  (n0 + 1 < cap ->
     in_app (p + n0) 1 /\ range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + n0) 1 /\
     sbd_wbytes B STK sp0 FP ly S own lyc Sc W memc (p + n0) 1 /\
     (p + n0 + 1 <= A \/ A + 28 <= p + n0) /\ (p + n0 + 1 <= q \/ q + 1 <= p + n0)) ->
  -3 <= t <= -1 -> getr regs 5 = w64 t ->
  getr regs 11 = w64 (A + 16) -> getr regs 12 = w64 (A + 8) -> getr regs 13 = w64 (A + 24) ->
  getr regs 14 = w64 q -> getr regs 6 = w64 q ->
  getr regs 7 = w64 (SHADOW_OFF + A / 8) -> getr regs 28 = w64 (SHADOW_OFF + (A + 16) / 8) ->
  getr regs 29 = w64 (SHADOW_OFF + (A + 8) / 8) -> getr regs 30 = w64 (SHADOW_OFF + (A + 24) / 8) ->
  getr regs 31 = w64 3 -> getr regs 19 = w64 1 -> getr regs 18 = w64 A -> getr regs 21 = w64 SHADOW_OFF ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_sb_dec + st) regs memc mdc)
    (l2_bpost fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs A p cap n0 ov0 q c t).
Proof.
intros st fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 q c t Hst HJ HA8 HA4 HA47 HAb
  Rp Rcap Rn0 Rn1 Rov Mp Mcap Mn Mov HRA HWA Rc Mc Hq4 Hq47 HRAq Hqa Hroom Ht H5
  H11 H12 H13 H14 H6 H7 H28 H29 H30 H31 H19 H18 H21.
destruct (Z_lt_le_dec (n0 + 1) cap) as [Hcp | Hcp].
- destruct (Hroom Hcp) as (Happ & HRAd & HWd & Hda & Hdq).
  exact (l2_body_c st fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 q c t Hst HJ HA8 HA4
    HA47 HAb Rp Rcap Rn0 Hcp Rov Mp Mcap Mn Mov HRA HWA Rc Mc Hq4 Hq47 HRAq Hqa Happ HRAd HWd Hda Hdq Ht H5
    H11 H12 H13 H14 H6 H7 H28 H29 H31 H19 H18 H21).
- destruct (HRA (A + 27) ltac:(lia)) as (s & Hs & Hok).
  unfold shadow_of_addr in Hs. replace ((A + 27) / 8) with ((A + 24) / 8) in Hs by lia.
  assert (Hs47 : s = 0 \/ 4 <= s <= 7) by (unfold saddr_ok in Hok; lia).
  exact (l2_body_o st fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 q c t s Hst HJ HA8 HA4
    HA47 HAb Rp Rcap Rn0 Rn1 Hcp Rov Mp Mcap Mn Mov HRA HWA Hs Hs47 Hq4 Hq47 Ht H5
    H11 H12 H13 H14 H6 H7 H28 H29 H30 H31 H19 H18 H21).
Qed.

Definition l2_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (k : Z) (regs : bvmap 5 word)
  (A p cap n0 ov0 : Z) (buf : list Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = cfg_at (fx := fq) SEGS (BASE + AF_sb_dec + SBD_L2X) regs2 mem2 md2 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       sbd_keep_regs regs regs2 [5; 6; 14; 15; 20; 22; 23] /\
       val_mem SEGS (mrestrict (w_H W) mem2) (A + 16) 8
         (n0 + Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0)) /\
       val_mem SEGS (mrestrict (w_H W) mem2) (A + 24) 4
         (if sb_dec_c.sb_dec_room cap n0 <? Z.of_nat (length buf) then 1 else ov0) /\
       (0 < sb_dec_c.sb_dec_room cap n0 ->
          garr8 SEGS (mrestrict (w_H W) mem2) (p + n0)
            (firstn (Z.to_nat (Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0))) (rev buf))) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (A + 16 <= a < A + 28) ->
          ~ (0 < sb_dec_c.sb_dec_room cap n0 /\ p + n0 <= a <
               p + n0 + Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0)) ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
       (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a).
Definition l2_gen (pc : Z) (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (A p cap n0 ov0 D : Z) (buf : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  A mod 8 = 0 -> 4096 <= A -> A + 28 <= 2 ^ 47 -> (A + 28 <= 2147446784 \/ 17594333495296 <= A) ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n0 -> n0 + 1 < 2 ^ 64 -> 0 <= ov0 < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) memc) A 8 p ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 n0 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 4 ov0 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF A 28 ->
  sbd_wbytes B STK sp0 FP ly S own lyc Sc W memc (A + 16) 12 ->
  (length buf <= 3)%nat -> Forall (fun c => 0 <= c < 256) buf ->
  garr8 SEGS (mrestrict (w_H W) memc) D buf -> 4096 <= D -> D + 3 <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF D (Z.of_nat (length buf)) ->
  (A + 28 <= D \/ D + Z.of_nat (length buf) <= A) ->
  (0 < sb_dec_c.sb_dec_room cap n0 ->
     p + cap <= 2 ^ 64 /\
     in_app (p + n0) (Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0)) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + n0)
       (Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0)) /\
     sbd_wbytes B STK sp0 FP ly S own lyc Sc W memc (p + n0)
       (Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0)) /\
     (p + n0 + Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0) <= A \/ A + 28 <= p + n0) /\
     (p + n0 + Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0) <= D \/
      D + Z.of_nat (length buf) <= p + n0)) ->
  getr regs 11 = w64 (A + 16) -> getr regs 12 = w64 (A + 8) -> getr regs 13 = w64 (A + 24) ->
  getr regs 5 = w64 (- Z.of_nat (length buf)) ->
  getr regs 14 = w64 (D + Z.of_nat (length buf) - 1) -> getr regs 6 = w64 (D + Z.of_nat (length buf) - 1) ->
  getr regs 7 = w64 (SHADOW_OFF + A / 8) -> getr regs 28 = w64 (SHADOW_OFF + (A + 16) / 8) ->
  getr regs 29 = w64 (SHADOW_OFF + (A + 8) / 8) -> getr regs 30 = w64 (SHADOW_OFF + (A + 24) / 8) ->
  getr regs 31 = w64 3 -> getr regs 19 = w64 1 -> getr regs 18 = w64 A -> getr regs 21 = w64 SHADOW_OFF ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_sb_dec + pc) regs memc mdc)
    (l2_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs A p cap n0 ov0 buf).
Lemma l2_exit : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) A p cap n0 ov0 D,
  l2_gen SBD_L2B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 D [].
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 D.
unfold l2_gen. intros HJ HA8 HA4 HA47 HAb Rp Rcap Rn0 Rn1 Rov Mp Mcap Mn Mov HRA HWA Hlen Hall Hga HD4 HD47 HRAD HAD Hroom
  H11 H12 H13 H5 H14 H6 H7 H28 H29 H30 H31 H19 H18 H21.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (@SRr_run_to_pi_AJ fq _ _ _ _ _ B LAWS) as RUNTOP.
set (E := EL2 regs 0 0 0 0 0 0 0).
assert (HEI : img_env VAL A_LIM E) by (unfold E, EL2; apply Eimg_env).
assert (HR : regs_ok E (sr_set sr_atoms 5%bv (SLit 0)) regs).
{ apply regs_ok_pin; [unfold E, EL2; apply regs_ok_Eimg_Ereg | discriminate |].
  rewrite H5. cbn [length Z.of_nat]. reflexivity. }
assert (HS : st_ok_pi SEGS VAL E l2_ssX
  (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_sb_dec + SBD_L2B))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold l2_ssX. apply pa_entry_st_ok_full.
  - exact HR.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
unfold cfg_at. rewrite <- Z.add_assoc.
paj_run_to_sh RUNTOP HS HJ (AF_sb_dec + SBD_L2X).
{ cbn [l2_ssX ss_mem]. apply awr_ok_nil. }
pose proof (l2_room_nonneg cap n0) as Hr0.
apply SRr_ret. unfold l2_post. cbn [length rev]. change (Z.of_nat 0) with 0. split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [exact (l2_post_cfg fq SBD_L2X E _ W ms _ HS ltac:(reflexivity) ltac:(vm_compute; reflexivity))|].
split; [exact HJ|].
split; [exact (l2_keep _ E E regs (w_H W) ms _ HR (env_agree_refl 512 E) HS ltac:(vm_compute; reflexivity))|].
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a)
  by (apply (l2_kept_nil E); exact HFr).
rewrite (Z.min_l 0 (sb_dec_c.sb_dec_room cap n0)) by exact Hr0.
split.
{ rewrite Z.add_0_r. apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) memc (ms_mem ms) (A + 16) 8 n0); [|exact Mn].
  intros x Hx. apply KA. lia. }
split.
{ replace (sb_dec_c.sb_dec_room cap n0 <? 0) with false by (symmetry; apply Z.ltb_ge; exact Hr0).
  apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) memc (ms_mem ms) (A + 24) 4 ov0); [|exact Mov].
  intros x Hx. apply KA. lia. }
split; [intros _; rewrite firstn_nil; apply garr8_nil|].
split; [intros a Ha _ _; apply KA; exact Ha|].
intros a Ha. exact (apresent_grows (w_H W) memc (ms_mem ms) a HG Ha).
Qed.

Ltac l2_kg KG := lazymatch goal with |- getr _ ?rb = _ =>
  let z := eval vm_compute in (bv_unsigned rb) in
  eapply (KG z); [apply bv_eq; vm_compute; reflexivity | lia | unfold l2_cl; cbn [In]; lia | eassumption] end.
Lemma l2_step : forall st buf c, (st = SBD_L2 \/ st = SBD_L2B) ->
  (forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
     (regs : bvmap 5 word) A p cap n0 ov0 D,
     l2_gen SBD_L2B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 D buf) ->
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs : bvmap 5 word) A p cap n0 ov0 D,
  l2_gen st fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 D (buf ++ [c]).
Proof.
intros st buf c Hst IH fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 D.
unfold l2_gen. intros HJ HA8 HA4 HA47 HAb Rp Rcap Rn0 Rn1 Rov Mp Mcap Mn Mov HRA HWA Hlen Hall Hga HD4 HD47 HRAD HAD Hroom
  H11 H12 H13 H5 H14 H6 H7 H28 H29 H30 H31 H19 H18 H21.
assert (HL : Z.of_nat (length (buf ++ [c])) = Z.of_nat (length buf) + 1) by (rewrite length_app; cbn [length]; lia).
assert (HlenB : (length buf <= 3)%nat) by (rewrite length_app in Hlen; cbn [length] in Hlen; lia).
assert (HlenZ : Z.of_nat (length buf) <= 2) by (rewrite length_app in Hlen; cbn [length] in Hlen; lia).
rewrite HL in HRAD, HAD, Hroom, H5, H14, H6.
destruct (proj1 (garr8_app SEGS _ D buf [c]) Hga) as [HgaB HgaC].
destruct (garr8_nthZ SEGS _ _ [c] 0 HgaC ltac:(lia) ltac:(cbn; lia)) as [Vc Rc].
cbn [nth Z.to_nat] in Vc, Rc. rewrite Z.add_0_r in Vc.
apply Forall_app in Hall as [HallB _].
assert (HRAq : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (D + Z.of_nat (length buf)) 1)
  by (eapply range_addressable_sub; [exact HRAD | lia | lia]).
assert (HRAB : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF D (Z.of_nat (length buf)))
  by (eapply range_addressable_sub; [exact HRAD | lia | lia]).
assert (H14' : getr regs 14 = w64 (D + Z.of_nat (length buf))) by (rewrite H14; unfold w64; f_equal; lia).
assert (H6' : getr regs 6 = w64 (D + Z.of_nat (length buf))) by (rewrite H6; unfold w64; f_equal; lia).
destruct (Z_lt_le_dec (n0 + 1) cap) as [Hcp | Hcp].
- destruct (l2_room_cp cap n0 Rn0 Hcp) as [Er0 Er1].
  rewrite Er0 in Hroom.
  destruct (Hroom ltac:(lia)) as (Hpcap & Happ & HRAd & HWd & HdA & HdD).
  pose proof Happ as (Hd4 & Hdc). ceil.
  assert (Hd47 : p + n0 + Z.min (Z.of_nat (length buf) + 1) (cap - 1 - n0) <= 2 ^ 47)
    by (unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
  assert (Happ1 : in_app (p + n0) 1) by (eapply in_app_sub; [exact Happ | lia | lia | lia]).
  eapply SRr_bind.
  { apply (l2_body st fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0
      (D + Z.of_nat (length buf)) c (- (Z.of_nat (length buf) + 1))); try assumption; try lia.
    intros _. split; [exact Happ1|]. split; [eapply range_addressable_sub; [exact HRAd | lia | lia]|].
    split; [intros a Ha; apply HWd; lia|]. split; lia. }
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HK2 & R5 & R6 & R14 & V16 & V24 & Vd & Hkept & Hpres).
  rewrite (proj2 (Z.ltb_lt _ _) Hcp) in V16, V24. specialize (Vd Hcp).
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (A + 16 <= a < A + 28) -> a <> p + n0 ->
    aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a)
    by (intros a Ha H1 H2; apply Hkept; [exact Ha | exact H1 | intros [_ H3]; exact (H2 H3)]).
  assert (SHK : forall x, 0 <= x < 2 ^ 47 ->
    aview SEGS (w_H W) mem2 (SHADOW_OFF + x / 8) = aview SEGS (w_H W) memc (SHADOW_OFF + x / 8)).
  { intros x Hx. apply KEEP; [unfold SHADOW_OFF; lia | exact (l2_sh_notA A x HAb Hx) |].
    intros Heq. exact (l2_sh_notapp (p + n0) 1 x Happ1 ltac:(lia) Hx (eq_sym Heq)). }
  assert (KG : forall z (rb : bv 5) v, Z_to_bv 5 z = rb -> 0 <= z < 32 -> ~ In z l2_cl -> getr regs rb = v ->
    getr regs2 rb = v) by (intros z rb v Hz Hr Hn Hv; rewrite (l2_kr regs regs2 z rb HK2 Hz Hr Hn); exact Hv).
  assert (G5 : getr regs2 5 = w64 (- Z.of_nat (length buf))) by (rewrite R5; unfold w64; f_equal; lia).
  assert (G14 : getr regs2 14 = w64 (D + Z.of_nat (length buf) - 1)) by (rewrite R14; unfold w64; f_equal; lia).
  assert (G6 : getr regs2 6 = w64 (D + Z.of_nat (length buf) - 1)) by (rewrite R6; unfold w64; f_equal; lia).
  assert (M2p : val_mem SEGS (mrestrict (w_H W) mem2) A 8 p).
  { apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) memc mem2 A 8 p); [|exact Mp].
    intros x Hx. apply KEEP; lia. }
  assert (M2cap : val_mem SEGS (mrestrict (w_H W) mem2) (A + 8) 8 cap).
  { apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) memc mem2 (A + 8) 8 cap); [|exact Mcap].
    intros x Hx. apply KEEP; lia. }
  assert (RA2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF A 28)
    by (apply (l2_ra_kept (w_H W) memc mem2 A 28); [intros x Hx; apply SHK; lia | exact HRA]).
  assert (W2A : sbd_wbytes B STK sp0 FP ly S own lyc Sc W mem2 (A + 16) 12)
    by (intros a Ha; destruct (HWA a Ha) as [Hw Hp]; exact (conj Hw (Hpres a Hp))).
  assert (Hga2 : garr8 SEGS (mrestrict (w_H W) mem2) D buf).
  { apply (garr8_aview_kept SEGS (w_H W) (w_H W) memc mem2 D buf); [|exact HgaB].
    intros a Ha. apply KEEP; lia. }
  assert (RAD2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF D (Z.of_nat (length buf)))
    by (apply (l2_ra_kept (w_H W) memc mem2); [intros x Hx; apply SHK; lia | exact HRAB]).
  eapply SRr_mono.
  { apply (IH fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k regs2 A p cap (n0 + 1) ov0 D);
      first [ assumption | lia | l2_kg KG
            | (rewrite Er1; intros Hr; split; [exact Hpcap|];
               split; [eapply in_app_sub; [exact Happ | lia | lia | lia]|];
               split; [apply (l2_ra_kept (w_H W) memc mem2);
                         [intros x Hx; apply SHK; lia | eapply range_addressable_sub; [exact HRAd | lia | lia]]|];
               split; [intros a Ha; destruct (HWd a ltac:(lia)) as [Hw Hp]; exact (conj Hw (Hpres a Hp))|];
               split; lia) ]. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & V16' & V24' & Hga3 & Hkept3 & Hpres3).
  unfold l2_post. rewrite HL, Er0. rewrite Er1 in V16', V24', Hga3, Hkept3.
  split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
  split; [exact (l2_keep_trans regs regs2 regs3 HK2 HK3)|].
  split.
  { replace (n0 + Z.min (Z.of_nat (length buf) + 1) (cap - 1 - n0))
      with (n0 + 1 + Z.min (Z.of_nat (length buf)) (cap - 2 - n0)) by lia. exact V16'. }
  split.
  { replace (cap - 1 - n0 <? Z.of_nat (length buf) + 1) with (cap - 2 - n0 <? Z.of_nat (length buf))
      by (apply Bool.eq_iff_eq_true; rewrite !Z.ltb_lt; lia). exact V24'. }
  split.
  { intros Hr. rewrite rev_app_distr. cbn [rev app].
    replace (Z.to_nat (Z.min (Z.of_nat (length buf) + 1) (cap - 1 - n0)))
      with (Datatypes.S (Z.to_nat (Z.min (Z.of_nat (length buf)) (cap - 2 - n0)))) by lia.
    cbn [firstn]. apply garr8_cons_x.
    - apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem2 mem3 (p + n0) 1 c); [|exact Vd].
      intros x Hx. apply Hkept3; lia.
    - exact Rc.
    - destruct (Z_lt_le_dec 0 (cap - 2 - n0)) as [Hr' | Hr'].
      + replace (p + n0 + 1) with (p + (n0 + 1)) by lia. exact (Hga3 Hr').
      + replace (Z.to_nat (Z.min (Z.of_nat (length buf)) (cap - 2 - n0))) with 0%nat by lia.
        cbn [firstn]. apply garr8_nil. }
  split.
  { intros a Ha Hn1 Hn2.
    rewrite (Hkept3 a Ha Hn1 ltac:(intros [Hx1 Hx2]; apply Hn2; split; lia)).
    apply KEEP; [exact Ha | exact Hn1 | intros ->; apply Hn2; split; lia]. }
  intros a Ha. exact (Hpres3 a (Hpres a Ha)).
- assert (Er0 : sb_dec_c.sb_dec_room cap n0 = 0) by (apply l2_room_ovf; exact Hcp).
  eapply SRr_bind.
  { apply (l2_body st fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0
      (D + Z.of_nat (length buf)) c (- (Z.of_nat (length buf) + 1))); try assumption; try lia. }
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HK2 & R5 & R6 & R14 & V16 & V24 & _ & Hkept & Hpres).
  rewrite (proj2 (Z.ltb_ge _ _) Hcp) in V16, V24.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (A + 16 <= a < A + 28) ->
    aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a)
    by (intros a Ha H1; apply Hkept; [exact Ha | exact H1 | intros [Hx _]; lia]).
  assert (SHK : forall x, 0 <= x < 2 ^ 47 ->
    aview SEGS (w_H W) mem2 (SHADOW_OFF + x / 8) = aview SEGS (w_H W) memc (SHADOW_OFF + x / 8))
    by (intros x Hx; apply KEEP; [unfold SHADOW_OFF; lia | exact (l2_sh_notA A x HAb Hx)]).
  assert (KG : forall z (rb : bv 5) v, Z_to_bv 5 z = rb -> 0 <= z < 32 -> ~ In z l2_cl -> getr regs rb = v ->
    getr regs2 rb = v) by (intros z rb v Hz Hr Hn Hv; rewrite (l2_kr regs regs2 z rb HK2 Hz Hr Hn); exact Hv).
  assert (G5 : getr regs2 5 = w64 (- Z.of_nat (length buf))) by (rewrite R5; unfold w64; f_equal; lia).
  assert (G14 : getr regs2 14 = w64 (D + Z.of_nat (length buf) - 1)) by (rewrite R14; unfold w64; f_equal; lia).
  assert (G6 : getr regs2 6 = w64 (D + Z.of_nat (length buf) - 1)) by (rewrite R6; unfold w64; f_equal; lia).
  assert (M2p : val_mem SEGS (mrestrict (w_H W) mem2) A 8 p).
  { apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) memc mem2 A 8 p); [|exact Mp].
    intros x Hx. apply KEEP; lia. }
  assert (M2cap : val_mem SEGS (mrestrict (w_H W) mem2) (A + 8) 8 cap).
  { apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) memc mem2 (A + 8) 8 cap); [|exact Mcap].
    intros x Hx. apply KEEP; lia. }
  assert (RA2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF A 28)
    by (apply (l2_ra_kept (w_H W) memc mem2 A 28); [intros x Hx; apply SHK; lia | exact HRA]).
  assert (W2A : sbd_wbytes B STK sp0 FP ly S own lyc Sc W mem2 (A + 16) 12)
    by (intros a Ha; destruct (HWA a Ha) as [Hw Hp]; exact (conj Hw (Hpres a Hp))).
  assert (Hga2 : garr8 SEGS (mrestrict (w_H W) mem2) D buf).
  { apply (garr8_aview_kept SEGS (w_H W) (w_H W) memc mem2 D buf); [|exact HgaB].
    intros a Ha. apply KEEP; lia. }
  assert (RAD2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF D (Z.of_nat (length buf)))
    by (apply (l2_ra_kept (w_H W) memc mem2); [intros x Hx; apply SHK; lia | exact HRAB]).
  eapply SRr_mono.
  { apply (IH fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k regs2 A p cap n0 1 D);
      first [ assumption | lia | l2_kg KG | (intros Hr; rewrite Er0 in Hr; lia) ]. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & V16' & V24' & _ & Hkept3 & Hpres3).
  unfold l2_post. rewrite HL, Er0. rewrite Er0 in V16', V24', Hkept3.
  split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
  split; [exact (l2_keep_trans regs regs2 regs3 HK2 HK3)|].
  split.
  { replace (n0 + Z.min (Z.of_nat (length buf) + 1) 0) with (n0 + Z.min (Z.of_nat (length buf)) 0) by lia.
    exact V16'. }
  split.
  { replace (0 <? Z.of_nat (length buf) + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (0 <? Z.of_nat (length buf)); exact V24'. }
  split; [intros Hx; lia|].
  split.
  { intros a Ha Hn1 _. rewrite (Hkept3 a Ha Hn1 ltac:(intros [Hx _]; lia)). apply KEEP; assumption. }
  intros a Ha. exact (Hpres3 a (Hpres a Ha)).
Qed.
Lemma l2_bot : forall buf (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) A p cap n0 ov0 D,
  l2_gen SBD_L2B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 D buf.
Proof.
intros buf. induction buf as [|c buf IH] using rev_ind.
- exact l2_exit.
- exact (l2_step SBD_L2B buf c (or_intror eq_refl) IH).
Qed.
Lemma l2_head : forall buf (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) A p cap n0 ov0 D, (1 <= length buf)%nat ->
  l2_gen SBD_L2 fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 D buf.
Proof.
intros buf. induction buf as [|c buf _] using rev_ind.
- intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 D Hl. cbn [length] in Hl. lia.
- intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 D _.
  exact (l2_step SBD_L2 buf c (or_introl eq_refl) (l2_bot buf)
    fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 D).
Qed.
Theorem sbd_l2 : sbd_L2_spec B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 D buf.
unfold sbd_L2_run.
intros HJ HA8 HA4 HA47 HAb Rp Rcap Rn0 Rn1 Rov Mp Mcap Mn Mov HRA HWA Hlen Hall Hga HD4 HD47 HRAD HAD Hroom
  H11 H12 H13 H5 H14 H6 H7 H28 H29 H30 H31 H19 H18 H21.
exact (l2_head buf fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 D (proj1 Hlen)
  HJ HA8 HA4 HA47 HAb Rp Rcap Rn0 ltac:(lia) Rov Mp Mcap Mn Mov HRA HWA (proj2 Hlen) Hall Hga HD4 HD47 HRAD HAD Hroom
  H11 H12 H13 H5 H14 H6 H7 H28 H29 H30 H31 H19 H18 H21).
Qed.
End h.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbd.v:102-108, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_L4.v, with its module paths and module names changed; 967 of its 1073 lines of code are new or changed and 714 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC88 YK0w YC85 YC45 YC81 YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacBoxNameLoops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Definition l4_pcA : Z := AF_both3_reac_box_name + RBN_L4.
Definition l4_pcB : Z := AF_both3_reac_box_name + RBN_L4 + 12.
Definition l4_pcX : Z := AF_both3_reac_box_name + RBN_L4X.
Definition l4_srcR : YP09.region := YP09.mkRegion (Some 24%nat) 1 2 1 1 [YP09.mkChunk 1 (CVal 1 (SOff 32 0))].
Definition l4_facts : facts :=
  mkFacts [(22%nat, mkAF SB SB 0); (24%nat, mkAF 0 (2 ^ 47 - 2) 0); (20%nat, mkAF 1 (2 ^ 47 - 1) 0);
           (21%nat, mkAF (2 ^ 64 - 1) (2 ^ 64 - 1) 0); (32%nat, mkAF 0 255 0)] [] [].
Definition l4_ssA : sstate := mkSS l4_pcA sr_atoms [] None (mkFacts [] [] []).
Definition l4_ssB : sstate := mkSS l4_pcB sr_atoms [l4_srcR] None l4_facts.
Definition l4_Bx : sv := SOff 22 0.
Definition l4_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition l4_kpA : list (bv 5) :=
  [2;3;4;5;6;7;8;9;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31]%bv.
Definition l4_kpB : list (bv 5) :=
  [2;3;4;5;6;7;8;9;12;13;14;15;16;17;18;19;21;22;23;25;26;27;28;29;30;31]%bv.
Definition l4_clA : list Z := [1; 10; 11].
Definition l4_clB : list Z := [1; 10; 11; 20; 24].

Lemma l4_getr_x0 : forall (r1 r2 : bvmap 5 word), getr r1 (Z_to_bv 5 0) = getr r2 (Z_to_bv 5 0).
Proof.
intros r1 r2. unfold getr. replace (bv_eqb (Z_to_bv 5 0) 0) with true by (vm_compute; reflexivity). reflexivity.
Qed.
Lemma l4_keep_of : forall (regs regs2 : bvmap 5 word) (l : list (bv 5)) (cl : list Z),
  (forall r : bv 5, In r l -> getr regs2 r = getr regs r) ->
  (forall z, 0 < z < 32 -> ~ In z cl -> In (Z_to_bv 5 z) l) ->
  rbn_keep_regs regs regs2 cl.
Proof.
intros regs regs2 l cl Hk Hin z Hz Hnc.
destruct (Z.eq_dec z 0) as [-> | Hz0]; [apply l4_getr_x0 | apply Hk; apply Hin; [lia | exact Hnc]].
Qed.
Lemma l4_keep_trans : forall (regs r1 r2 : bvmap 5 word) cl,
  rbn_keep_regs regs r1 cl -> rbn_keep_regs r1 r2 cl -> rbn_keep_regs regs r2 cl.
Proof. intros regs r1 r2 cl H1 H2 z Hz Hn. rewrite (H2 z Hz Hn). exact (H1 z Hz Hn). Qed.
Lemma l4_keep_sub : forall (regs r1 : bvmap 5 word) cl cl',
  rbn_keep_regs regs r1 cl -> (forall z, In z cl -> In z cl') -> rbn_keep_regs regs r1 cl'.
Proof. intros regs r1 cl cl' H Hs z Hz Hn. apply H; [exact Hz | intros Hin; exact (Hn (Hs z Hin))]. Qed.
Lemma l4_keep_get : forall (regs regs2 : bvmap 5 word) cl (r : bv 5),
  rbn_keep_regs regs regs2 cl -> existsb (Z.eqb (bv_unsigned r)) cl = false -> getr regs2 r = getr regs r.
Proof.
intros regs regs2 cl r HK Hb. pose proof (u5_range r) as Hr.
assert (Hn : ~ In (bv_unsigned r) cl).
{ intros Hin. assert (E : existsb (Z.eqb (bv_unsigned r)) cl = true)
    by (apply existsb_exists; exists (bv_unsigned r); split; [exact Hin | apply Z.eqb_refl]).
  rewrite E in Hb. discriminate. }
pose proof (HK _ Hr Hn) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E.
Qed.
Lemma l4_u_neg1 : bv_unsigned (w64 (-1)) = 2 ^ 64 - 1.
Proof. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. vm_compute. reflexivity. Qed.
Lemma l4_land255 : forall c, 0 <= c < 256 -> Z.land c 255 = c.
Proof.
intros c Hc. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. cbn. lia.
Qed.
Lemma l4_and255 : forall c, 0 <= c < 256 -> alu64 ALU_AND (w64 c) (Z_to_bv 64 255) = w64 c.
Proof.
intros c Hc. rewrite alu_and. unfold v_and, w64. rewrite !unsigned_lit_small by lia.
rewrite l4_land255 by lia. reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Definition EL0 (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Definition EL1 (regs : bvmap 5 word) (c2 : Z) : env := Eimg (Ereg regs [w64 c2]).
Lemma EL0_img : forall regs, img_env VAL A_LIM (EL0 regs).
Proof. intros. unfold EL0. apply Eimg_env. Qed.
Lemma EL1_img : forall regs c2, img_env VAL A_LIM (EL1 regs c2).
Proof. intros. unfold EL1. apply Eimg_env. Qed.
Lemma EL0_reg : forall regs n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew (EL0 regs) n = getr regs r.
Proof.
intros regs n r Hn Hr. unfold EL0. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr.
Qed.
Lemma EL1_reg : forall regs c2 n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (EL1 regs c2) n = getr regs r.
Proof.
intros regs c2 n r Hn Hr. unfold EL1. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr.
Qed.
Lemma EL1_32 : forall regs c2, ew (EL1 regs c2) 32 = w64 c2.
Proof. intros. unfold EL1. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma EL0_agree : forall regs, env_agree 32 (Ereg regs []) (EL0 regs).
Proof. intros. split; [intros q Hq; unfold EL0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma EL1_agree : forall regs c2, env_agree 32 (Ereg regs [w64 c2]) (EL1 regs c2).
Proof. intros. split; [intros q Hq; unfold EL1; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma l4_afact : forall E q v lo hi, ew E q = w64 v -> 0 <= v < 2 ^ 64 -> lo <= v -> v <= hi ->
  afact_ok E q (mkAF lo hi 0).
Proof.
intros E q v lo hi He Hv Hlo Hhi. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite He. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r.
split; [lia|]. split; [reflexivity | lia].
Qed.
Lemma l4_shadow_apart : forall D n x, in_app D n -> 0 <= x -> x < 2 ^ 47 -> ~ (D <= SHADOW_OFF + x / 8 < D + n).
Proof.
intros D n x [H4096 Hc] Hx0 Hx Hbad.
assert (Hd : 0 <= x / 8 < 17592186044416)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | change (8 * 17592186044416) with (2 ^ 47); lia]]).
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
try (let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; unfold YG0f.ASAN_CEIL in H).
destruct Hc as [HL | [HH1 HH2]]; lia.
Qed.
Lemma l4_ra_kept : forall (H H' : word -> bool) (m m2 : word -> option byte) a len,
  (forall x, a <= x < a + len -> aview SEGS H' m2 (SHADOW_OFF + x / 8) = aview SEGS H m (SHADOW_OFF + x / 8)) ->
  range_addressable (aview SEGS H m) SHADOW_OFF a len ->
  range_addressable (aview SEGS H' m2) SHADOW_OFF a len.
Proof.
intros H H' m m2 a len He Hra x Hx. destruct (Hra x Hx) as (s & Hs & Hok).
exists s. split; [|exact Hok]. unfold shadow_of_addr in *. rewrite (He x Hx). exact Hs.
Qed.
Lemma l4_shadow_lo : forall x, 0 <= x -> x <= 2 ^ 47 -> 0 <= SHADOW_OFF + x / 8 < alloc_ceiling.
Proof.
intros x H0 H47. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D1.
assert (D2 : x / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
pose proof asan_consts as (C1 & _). change (2 ^ 47 / 8) with 17592186044416 in D2.
unfold SHADOW_OFF. lia.
Qed.
Lemma l4_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) p L,
  (forall a, p <= a < p + Z.of_nat (length L) -> aview SEGS H' m' a = aview SEGS H m a) ->
  garr8 SEGS (mrestrict H m) p L -> garr8 SEGS (mrestrict H' m') p L.
Proof.
intros H H' m m' p L He Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_kept SEGS H H' m m'); [|exact Hv]. intros q Hq. cbn [Z.of_nat] in Hq. apply He. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TSB : tsb_ch_spec B.

Lemma l4_entryA : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte),
  st_ok_pi SEGS VAL (EL0 regs) l4_ssA
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + l4_pcA)) mem (seg_rom SEGS))).
Proof.
intros fq W regs mem. rewrite restrict_mkst_fx. unfold l4_ssA. apply pa_entry_st_ok_full.
- unfold EL0. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint]. exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.

Lemma l4_entryB : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (Q c2 : Z),
  0 <= Q <= 2 ^ 47 - 2 -> 0 <= c2 < 256 ->
  getr regs 20 = w64 (Q + 1) -> getr regs 21 = w64 (-1) -> getr regs 22 = w64 SHADOW_OFF ->
  getr regs 24 = w64 Q ->
  val_mem SEGS (mrestrict (w_H W) mem) (Q + 1) 1 c2 ->
  st_ok_pi SEGS VAL (EL1 regs c2) l4_ssB
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + l4_pcB)) mem (seg_rom SEGS))).
Proof.
intros fq W regs mem Q c2 HQ Hc2 H20 H21 H22 H24 HV.
assert (E20 : ew (EL1 regs c2) 20 = w64 (Q + 1))
  by (rewrite (EL1_reg regs c2 20%nat 20%bv) by (first [lia | vm_compute; reflexivity]); exact H20).
assert (E21 : ew (EL1 regs c2) 21 = w64 (-1))
  by (rewrite (EL1_reg regs c2 21%nat 21%bv) by (first [lia | vm_compute; reflexivity]); exact H21).
assert (E22 : ew (EL1 regs c2) 22 = w64 SHADOW_OFF)
  by (rewrite (EL1_reg regs c2 22%nat 22%bv) by (first [lia | vm_compute; reflexivity]); exact H22).
assert (E24 : ew (EL1 regs c2) 24 = w64 Q)
  by (rewrite (EL1_reg regs c2 24%nat 24%bv) by (first [lia | vm_compute; reflexivity]); exact H24).
assert (E32 : ew (EL1 regs c2) 32 = w64 c2) by apply EL1_32.
assert (U24 : bv_unsigned (ew (EL1 regs c2) 24) = Q)
  by (rewrite E24; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold l4_ssB, l4_facts. apply pa_entry_st_ok_full.
- unfold EL1. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold l4_srcR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ Q 1 1 (SOff 32 0) c2);
    [cbn [sv_denot]; rewrite E32; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia | cbn; lia |].
  change (N.to_nat 1) with 1%nat. exact HV.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok].
  split; [apply (l4_afact _ _ SHADOW_OFF); [exact E22 | unfold SHADOW_OFF; lia | unfold SB, SHADOW_OFF; lia
    | unfold SB, SHADOW_OFF; lia]|].
  split; [apply (l4_afact _ _ Q); [exact E24 | lia | lia | lia]|].
  split; [apply (l4_afact _ _ (Q + 1)); [exact E20 | lia | lia | lia]|].
  split.
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E21, l4_u_neg1.
    rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia]. }
  split; [apply (l4_afact _ _ c2); [exact E32 | lia | lia | lia]|]. exact I.
Qed.

Lemma l4_pre : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) (mem : word -> option byte) (md : Model) (k : Z) (regs : bvmap 5 word) (A9 c : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  getr regs 9 = w64 A9 -> 0 <= A9 -> A9 + 88 < 2 ^ 64 ->
  getr regs 10 = w64 c -> 0 <= c < 256 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + l4_pcA) regs mem md)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model),
       c1 = cfg_at (fx := fq) SEGS (BASE + AF_both3_sb_ch) regs1 mem1 md1 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k /\
       (forall a, aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) /\
       getr regs1 1 = w64 (BASE + l4_pcB) /\ getr regs1 10 = w64 (A9 + 88) /\
       getr regs1 11 = w64 c /\ rbn_keep_regs regs regs1 l4_clA).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs A9 c HJ H9 HA0 HA63 H10 Hc.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (@SRr_run_pi_AJ fq _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call fq _ _ _ _ _ B LAWS) as RUNC.
set (E := EL0 regs) in *.
assert (HEI : img_env VAL A_LIM E) by apply EL0_img.
assert (E9 : ew E 9 = w64 A9)
  by (unfold E; rewrite (EL0_reg regs 9%nat 9%bv) by (first [lia | vm_compute; reflexivity]); exact H9).
assert (E10 : ew E 10 = w64 c)
  by (unfold E; rewrite (EL0_reg regs 10%nat 10%bv) by (first [lia | vm_compute; reflexivity]); exact H10).
pose proof (l4_entryA fq W regs mem) as HS. fold E in HS.
unfold cfg_at. change (w64 (BASE + l4_pcA)) with (Z_to_bv 64 (BASE + l4_pcA)).
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_nil. }
prreg HS (1%bv : bv 5) R1.
prreg HS (10%bv : bv 5) R10.
prreg HS (11%bv : bv 5) R11.

assert (HKP : rbn_keep_regs regs (ms_regs ms) l4_clA).
{ apply (l4_keep_of _ _ l4_kpA).
  - exact (regs_kept_of_st_ok SEGS E _ _ regs [] l4_kpA HS ltac:(apply EL0_agree) ltac:(vm_compute; reflexivity)).
  - intros z Hz Hnc. unfold l4_kpA.
    assert (Hd : z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9
      \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19
      \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29
      \/ z = 30 \/ z = 31) by lia.
    repeat (destruct Hd as [Hd | Hd]); subst z;
    solve [ exfalso; apply Hnc; cbn [In l4_clA]; repeat (first [left; reflexivity | right])
          | cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]) ]. }
apply SRr_ret. pmkst HS. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst ?rg _ ?mm _) ?mdx] => exists rg, mm, mdx end.
split.
{ unfold cfg_at, w64. rewrite pa_sigma_sb_ch. reflexivity. }
split; [exact HJ|].
split; [intros a; apply (aview_kept_nil E (w_H W) _ _ HFr)|].
split; [intros a Hp; exact (apresent_grows (w_H W) _ _ a HG Hp)|].
split.
{ rewrite R1. unfold w64. first [ reflexivity | f_equal; unfold l4_pcB, RBN_L4, AF_both3_reac_box_name; lia ]. }
split.
{ rewrite R10, E9. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
split; [|exact HKP].
rewrite R11, E10. apply l4_and255. lia.
Qed.

Lemma l4_post : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) (mem : word -> option byte) (md : Model) (k : Z) (regs : bvmap 5 word) (Q c2 : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  0 <= Q <= 2 ^ 47 - 2 -> 0 <= c2 < 256 ->
  getr regs 20 = w64 (Q + 1) -> getr regs 21 = w64 (-1) -> getr regs 22 = w64 SHADOW_OFF ->
  getr regs 24 = w64 Q ->
  val_mem SEGS (mrestrict (w_H W) mem) (Q + 1) 1 c2 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (Q + 1) 1 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + l4_pcB) regs mem md)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model),
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k /\
       (forall a, aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) /\
       rbn_keep_regs regs regs1 l4_clB /\
       ((c2 = 0 /\ c1 = cfg_at (fx := fq) SEGS (BASE + l4_pcX) regs1 mem1 md1) \/
        (c2 <> 0 /\ c1 = cfg_at (fx := fq) SEGS (BASE + l4_pcA) regs1 mem1 md1 /\
         getr regs1 24 = w64 (Q + 1) /\ getr regs1 20 = w64 (Q + 2) /\ getr regs1 10 = w64 c2))).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs Q c2 HJ HQ Hc2 H20 H21 H22 H24 HV HRA.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (@paj_run fq _ _ _ _ _ B LAWS) as RUN.
pose proof (@paj_run_to fq _ _ _ _ _ B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := EL1 regs c2) in *.
assert (HEI : img_env VAL A_LIM E) by apply EL1_img.
assert (E20 : ew E 20 = w64 (Q + 1))
  by (unfold E; rewrite (EL1_reg regs c2 20%nat 20%bv) by (first [lia | vm_compute; reflexivity]); exact H20).
assert (E22 : ew E 22 = w64 SHADOW_OFF)
  by (unfold E; rewrite (EL1_reg regs c2 22%nat 22%bv) by (first [lia | vm_compute; reflexivity]); exact H22).
assert (E24 : ew E 24 = w64 Q)
  by (unfold E; rewrite (EL1_reg regs c2 24%nat 24%bv) by (first [lia | vm_compute; reflexivity]); exact H24).
assert (E32 : ew E 32 = w64 c2) by apply EL1_32.
pose proof (l4_entryB fq W regs mem Q c2 HQ Hc2 H20 H21 H22 H24 HV) as HS. fold E in HS.
assert (SHOK : sh_ok SEGS l4_Bx (@nil shent) E (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold cfg_at. change (w64 (BASE + l4_pcB)) with (Z_to_bv 64 (BASE + l4_pcB)).
paj_run_tok RUN HS HJ SHOK l4_span.
{ unfold l4_Bx. rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom E 20 (Q + 1) E20) by lia. rewrite <- (aview_rd_of SEGS). exact HRA. }
{ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi l4_srcR]; lia | apply awr_ok_nil]. }
rename HF into HFa. rename HFr into HFra. rename HG into HGa.
assert (KEEP1 : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a. rewrite (aview_wrap (w_H W) (ms_mem ms) a), (aview_wrap (w_H W) mem a).
  apply (aview_kept_out _ _ (w_H W) _ _ HFra); [apply Z.mod_pos_bound; lia|].
  intros (r & Hin & Hr). cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [subst r|]); try destruct Hin;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val l4_srcR] in Hr; lia. }
psrr_branch_tok RUN BR HS SHOK l4_span.
{ match goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB end.
  lazymatch type of HB with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    assert (F32 : ew Ex 32 = w64 c2) by (cbn [ew ewset Nat.eqb]; exact E32);
    rewrite branch_eq_U, (U_atom Ex 32 c2 F32 ltac:(lia)), (U_lit Ex 0 ltac:(lia)) in HB end.
  apply Z.eqb_eq in HB.
  paj_run_to_tok RUNTO HS HJ SHOK l4_span l4_pcX.
  { apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
  assert (KEEP2 : forall a, aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
  { intros a. rewrite (aview_wrap (w_H W) (ms_mem ms0) a), (aview_wrap (w_H W) (ms_mem ms) a).
    apply (aview_kept_out _ _ (w_H W) _ _ HFr); [apply Z.mod_pos_bound; lia|].
    intros (r & Hin & Hr). cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst r|]); try destruct Hin;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs [w64 c2] l4_kpB HS
    ltac:(env_agree_chain (EL1_agree regs c2)) ltac:(vm_compute; reflexivity)) as HK2.
  cbn [ms_regs restrict] in HK2.
  assert (HKP : rbn_keep_regs regs (ms_regs ms0) l4_clB).
  { apply (l4_keep_of _ _ l4_kpB); [exact HK2|].
    intros z Hz Hnc. unfold l4_kpB.
    assert (Hd : z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9
      \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19
      \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29
      \/ z = 30 \/ z = 31) by lia.
    repeat (destruct Hd as [Hd | Hd]); subst z;
    solve [ exfalso; apply Hnc; cbn [In l4_clB]; repeat (first [left; reflexivity | right])
          | cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]) ]. }
  apply SRr_ret. pmkst HS. split; [reflexivity|].
  lazymatch goal with |- context [mkCfg (mkst ?rg _ ?mm _) ?mdx] => exists rg, mm, mdx end.
  split; [exact HJ|].
  split; [intros a; rewrite (KEEP2 a); exact (KEEP1 a)|].
  split.
  { intros a Hp. eapply apresent_grows; [exact HG|]. eapply apresent_grows; [exact HGa | exact Hp]. }
  split; [exact HKP|].
  left. split; [exact HB|]. unfold cfg_at, w64. first [ reflexivity | f_equal; f_equal; f_equal; lia ]. }
{ match goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB end.
  lazymatch type of HB with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    assert (F32 : ew Ex 32 = w64 c2) by (cbn [ew ewset Nat.eqb]; exact E32);
    rewrite branch_eq_U, (U_atom Ex 32 c2 F32 ltac:(lia)), (U_lit Ex 0 ltac:(lia)) in HB end.
  apply Z.eqb_neq in HB.
  paj_run_to_tok RUNTO HS HJ SHOK l4_span l4_pcA.
  { apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
  assert (KEEP2 : forall a, aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
  { intros a. rewrite (aview_wrap (w_H W) (ms_mem ms0) a), (aview_wrap (w_H W) (ms_mem ms) a).
    apply (aview_kept_out _ _ (w_H W) _ _ HFr); [apply Z.mod_pos_bound; lia|].
    intros (r & Hin & Hr). cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst r|]); try destruct Hin;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs [w64 c2] l4_kpB HS
    ltac:(env_agree_chain (EL1_agree regs c2)) ltac:(vm_compute; reflexivity)) as HK2.
  cbn [ms_regs restrict] in HK2.
  assert (HKP : rbn_keep_regs regs (ms_regs ms0) l4_clB).
  { apply (l4_keep_of _ _ l4_kpB); [exact HK2|].
    intros z Hz Hnc. unfold l4_kpB.
    assert (Hd : z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9
      \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19
      \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29
      \/ z = 30 \/ z = 31) by lia.
    repeat (destruct Hd as [Hd | Hd]); subst z;
    solve [ exfalso; apply Hnc; cbn [In l4_clB]; repeat (first [left; reflexivity | right])
          | cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]) ]. }
  pmkst HS.
  prreg HS (24%bv : bv 5) Rv24. prreg HS (20%bv : bv 5) Rv20. prreg HS (10%bv : bv 5) Rv10.
  apply SRr_ret. split; [reflexivity|].
  lazymatch goal with |- context [mkCfg (mkst ?rg _ ?mm _) ?mdx] => exists rg, mm, mdx end.
  split; [exact HJ|].
  split; [intros a; rewrite (KEEP2 a); exact (KEEP1 a)|].
  split.
  { intros a Hp. eapply apresent_grows; [exact HG|]. eapply apresent_grows; [exact HGa | exact Hp]. }
  split; [exact HKP|].
  right. split; [exact HB|].
  split; [unfold cfg_at, w64; first [ reflexivity | f_equal; f_equal; f_equal; lia ]|].
  split.
  { rewrite Rv24, E24. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  split.
  { rewrite Rv20, E20. unfold w64. rewrite unsigned_lit_small by lia. first [ reflexivity | f_equal; lia ]. }
  { rewrite Rv10, E32. reflexivity. } }
Qed.

Lemma l4_pres_get : forall (r1 r2 : bvmap 5 word) (r : bv 5),
  aregs_preserved r1 r2 -> acallee_saved (bv_unsigned r) -> getr r2 r = getr r1 r.
Proof. intros r1 r2 r H Hr. pose proof (H _ Hr) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E. Qed.
Lemma l4_keep_of_pres : forall (r1 r2 : bvmap 5 word), aregs_preserved r1 r2 -> rbn_keep_regs r1 r2 rbn_clc.
Proof.
intros r1 r2 H z Hz Hn. destruct (Z.eq_dec z 0) as [->|Hz0]; [apply l4_getr_x0|].
apply H. unfold rbn_clc in Hn. cbn [In] in Hn. unfold acallee_saved. lia.
Qed.
Lemma l4_kept_of_eq : forall lyc Sc (Wa : world SEGS) (ma : word -> option byte) (Wb : world SEGS)
  (mb : word -> option byte) sp (E : Z -> Prop),
  (forall a, aview SEGS (w_H Wb) mb a = aview SEGS (w_H Wa) ma a) ->
  (forall a, apresent (w_H Wa) ma a -> apresent (w_H Wb) mb a) ->
  (forall a, sp - TSB_CH_STK <= a < sp -> apresent (w_H Wa) ma a) ->
  tsb_ch_kept B lyc Sc Wa ma Wb mb sp E.
Proof.
intros lyc Sc Wa ma Wb mb sp E Heq Hpr Hwin.
split; [intros; apply Heq|]. split; [intros; apply Heq|]. split; [intros; apply Heq|].
split; [intros; apply Heq|]. split; [intros a Ha Hs Hp; exact (Hpr a Hp)|].
intros a Ha. exact (Hpr a (Hwin a Ha)).
Qed.
Lemma l4_kept_trans : forall lyc Sc lyc1 Sc1 (W : world SEGS) memc mdc (W1 : world SEGS) mem1
  (W2 : world SEGS) mem2 sp (E1 E2 E : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= sp - TSB_CH_STK ->
  (forall a, E1 a -> E a) -> (forall a, E2 a -> E a) ->
  tsb_ch_kept B lyc Sc W memc W1 mem1 sp E1 ->
  tsb_ch_kept B lyc1 Sc1 W1 mem1 W2 mem2 sp E2 ->
  tsb_ch_kept B lyc Sc W memc W2 mem2 sp E.
Proof.
intros lyc Sc lyc1 Sc1 W memc mdc W1 mem1 W2 mem2 sp E1 E2 E HAR Hceil HE1 HE2 K1 K2.
destruct K1 as (K1a & K1b & K1c & K1d & K1e & K1f).
destruct K2 as (K2a & K2b & K2c & K2d & K2e & K2f).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KO : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - TSB_CH_STK <= a < sp) -> ~ E a ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a)
  by (intros a Ha Hs He; apply (K2a a Ha Hs); intros X; exact (He (HE2 a X))).
split.
{ intros a Ha Hs He. rewrite (KO a Ha Hs He). apply (K1a a Ha Hs). intros X. exact (He (HE1 a X)). }
split.
{ intros b mm i Hb Hi Hn. destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR Hb) as (_ & Hb4096 & Hbceil & _).
  rewrite (KO (b + i) ltac:(lia) ltac:(lia) Hn).
  exact (K1b b mm i Hb Hi ltac:(intros X; exact (Hn (HE1 (b + i) X)))). }
split.
{ intros a Him Hns Herr. rewrite (K2c a Him Hns Herr). exact (K1c a Him Hns Herr). }
split.
{ intros cid pos a Hf Hz Hn.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hf) as (Hf4096 & Hfceil & Hfapp).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  pose proof (Z.mul_div_le (frame_addr lyc cid pos) 8 ltac:(lia)) as DV1.
  pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)) as DV2.
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)) as DV3.
  pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as DV4.
  assert (Ha : 0 <= a < alloc_ceiling).
  { destruct Hz as [Hz | Hz]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hz; cbn [fst snd] in Hz; lia. }
  rewrite (KO a ltac:(lia) ltac:(lia) Hn).
  exact (K1d cid pos a Hf Hz ltac:(intros X; exact (Hn (HE1 a X)))). }
split.
{ intros a Ha Hs Hp. apply (K2e a Ha Hs). exact (K1e a Ha Hs Hp). }
intros a Ha. exact (K2f a Ha).
Qed.
Lemma l4_lyF : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> ly_F lyc = ly_F ly.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ.
pose proof (proj1 (proj2 HJ)) as HL. destruct HL as (_ & _ & _ & _ & _ & HF & _). exact HF.
Qed.
Lemma l4_awr_move : forall STK sp0 FP ly S lyc Sc lyc1 Sc1 own a,
  ablocks B lyc1 Sc1 = ablocks B lyc Sc -> ly_F lyc1 = ly_F lyc ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc1 Sc1) lyc1 own a.
Proof.
intros STK sp0 FP ly S lyc Sc lyc1 Sc1 own a Hab Hf H.
unfold awr_byte, in_tmp_block, in_frames, frame_addr in *. rewrite Hab, Hf. exact H.
Qed.
Lemma l4_ro_move : forall (Wa : world SEGS) ma (Wb : world SEGS) mb,
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H Wb) mb a = aview SEGS (w_H Wa) ma a) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wa) ma) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wb) mb).
Proof.
intros Wa ma Wb mb Heq HR a Hro Ho He. rewrite (Heq a); [exact (HR a Hro Ho He) | | exact Ho | exact He].
destruct Hro as [(sg & Hsg & _ & Hr) | Hgot]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hgot)].
Qed.
Lemma l4_hull_move : forall (Wa : world SEGS) ma (Wb : world SEGS) mb x nn (E : Z -> Prop),
  (forall s, 0 <= s < 2 ^ 64 -> ~ E s -> aview SEGS (w_H Wb) mb s = aview SEGS (w_H Wa) ma s) ->
  (forall s, E s -> aview SEGS (w_H Wb) mb s <> None) ->
  (forall s, E s \/ ~ E s) ->
  0 <= x -> x + nn <= 2 ^ 47 -> 0 < nn ->
  shadow_hull_vis (aview SEGS (w_H Wa) ma) x nn -> shadow_hull_vis (aview SEGS (w_H Wb) mb) x nn.
Proof.
intros Wa ma Wb mb x nn E Heq Hpres Hdec Hx0 Hx47 Hnn Hhv s Hs.
assert (Hd1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (Hd2 : (x + nn - 1) / 8 <= 2 ^ 47) by (apply Z.div_le_upper_bound; lia).
assert (Hd3 : 0 <= (SHADOW_OFF + x / 8) / 8) by (apply Z.div_pos; unfold SHADOW_OFF; lia).
assert (Hd4 : 8 * ((SHADOW_OFF + (x + nn - 1) / 8) / 8) <= SHADOW_OFF + (x + nn - 1) / 8)
  by (apply Z.mul_div_le; lia).
assert (Hsb : 0 <= s < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF in *; lia).
destruct (Hdec s) as [He | He]; [exact (Hpres s He)|].
rewrite (Heq s Hsb He). exact (Hhv s Hs).
Qed.
Lemma l4_val_pres : forall (Wa : world SEGS) ma a n v x,
  val_mem SEGS (mrestrict (w_H Wa) ma) a n v -> a <= x < a + Z.of_nat n ->
  aview SEGS (w_H Wa) ma x <> None.
Proof.
intros Wa ma a n v x HV Hx. pose proof (HV (Z.to_nat (x - a)) ltac:(lia)) as Hb.
replace (a + Z.of_nat (Z.to_nat (x - a))) with x in Hb by lia.
unfold aview. rewrite Hb. discriminate.
Qed.
Lemma l4_garr8_pres : forall (Wa : world SEGS) ma p L x,
  garr8 SEGS (mrestrict (w_H Wa) ma) p L -> p <= x < p + Z.of_nat (length L) ->
  aview SEGS (w_H Wa) ma x <> None.
Proof.
intros Wa ma p L x HG Hx. destruct (HG (Z.to_nat (x - p)) ltac:(lia)) as [Hv _].
apply (l4_val_pres Wa ma (p + Z.of_nat (Z.to_nat (x - p))) 1 (nth (Z.to_nat (x - p)) L 0) x);
  [exact Hv | cbn [Z.of_nat]; lia].
Qed.
Lemma l4_awr_pres : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (Wc : world SEGS) memc mdc k a,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc Wc memc mdc k ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  apresent (w_H Wc) memc a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc Wc memc mdc k a HJ Hw.
first [ exact (proj1 (awr_byte_present SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc Wc memc mdc k a HJ Hw))
      | exact (proj1 (awr_byte_present SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc Wc memc mdc k a HJ Hw)) ].
Qed.
Lemma l4_kept_weak : forall lyc Sc (Wa : world SEGS) ma (Wb : world SEGS) mb sp (E E' : Z -> Prop),
  (forall a, E a -> E' a) -> tsb_ch_kept B lyc Sc Wa ma Wb mb sp E ->
  tsb_ch_kept B lyc Sc Wa ma Wb mb sp E'.
Proof.
intros lyc Sc Wa ma Wb mb sp E E' HE (K1 & K2 & K3 & K4 & K5 & K6).
split; [intros a Ha Hs He; apply (K1 a Ha Hs); intros X; exact (He (HE a X))|].
split; [intros b mm i Hb Hi Hn; apply (K2 b mm i Hb Hi); intros X; exact (Hn (HE (b + i) X))|].
split; [exact K3|].
split; [intros cid pos a Hf Hz Hn; apply (K4 cid pos a Hf Hz); intros X; exact (Hn (HE a X))|].
split; [exact K5 | exact K6].
Qed.

Lemma l4_core : forall (m : nat) (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (D n0 ov0 : Z)
  (lyc1 : alayout) (Sc1 : astate) (W1 : world SEGS) (mem1 : word -> option byte) (md1 : Model)
  (regs1 : bvmap 5 word) (Q : Z) (t : list Z) (n ov : Z) (wr : list Z) (nF ovF : Z) (wrF : list Z),
  (length t <= m)%nat ->
  nF = Z.min (n + Z.of_nat (length t)) 47 ->
  ovF = (if n + Z.of_nat (length t) <=? 47 then ov else 1) ->
  wrF = wr ++ firstn (Z.to_nat (47 - n)) t ->
  t <> [] -> Forall (fun x => 0 < x < 256) t ->
  rbn_lcx B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 n0 ov0 ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 ->
  garr8 SEGS (mrestrict (w_H W) memc) Q (t ++ [0]) ->
  0 <= Q -> Q + Z.of_nat (length t) + 1 <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF Q (Z.of_nat (length t) + 1) ->
  rbn_lsep (spZ regs) (spZ regs + 88) D 48 Q (Z.of_nat (length t) + 1) ->
  0 <= n0 -> n0 <= n <= 47 -> (ov = 0 \/ ov = 1) -> Z.of_nat (length wr) = n - n0 ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 mem1 md1 k ->
  ablocks B lyc1 Sc1 = ablocks B lyc Sc -> frames Sc1 = frames Sc -> ly_F lyc1 = ly_F lyc ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) mem1) ->
  tsb_ch_kept B lyc Sc W memc W1 mem1 (spZ regs)
    (fun a => spZ regs + 104 <= a < spZ regs + 116 \/ D + n0 <= a < D + n) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs + 104) 8 n ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs + 112) 4 ov ->
  garr8 SEGS (mrestrict (w_H W1) mem1) (D + n0) wr ->
  getr regs1 10 = w64 (hd 0 t) -> getr regs1 24 = w64 Q -> getr regs1 20 = w64 (Q + 1) ->
  getr regs1 21 = w64 (-1) -> rbn_keep_regs regs regs1 rbn_cl4 ->
  SRr SEGS W1 (cfg_at (fx := fq) SEGS (BASE + l4_pcA) regs1 mem1 md1)
    (rbn_lpost B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L4X rbn_cl4
       (spZ regs + 88) D n0 nF ovF wrF).
Proof.
intros m. induction m as [|m IH];
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0
  lyc1 Sc1 W1 mem1 md1 regs1 Q t n ov wr nF ovF wrF
  Hm HnF HovF HwrF Ht0 Htb HCX HREC HBUF Hga HQ0 HQ47 HRAq HSEP Hn00 Hnn Hov Hwrl
  HJ1 Hab1 Hfr1 HlyF1 HRO1 HK1 Vn Vov Hgw G10 G24 G20 G21 HKP.
{ exfalso. destruct t as [|c t']; [exact (Ht0 eq_refl) | cbn [length] in Hm; lia]. }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. unfold YImgTop.IMG_LO in HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
pose proof HCX as HCX0. pose proof HREC as HREC0. pose proof HBUF as HBUF0. pose proof HSEP as HSEP0.
destruct t as [|c t']; [exact (False_ind _ (Ht0 eq_refl))|].
assert (HLn : Z.of_nat (length (c :: t')) = Z.of_nat (length t') + 1) by (cbn [length]; lia).
assert (Hcr : 0 < c < 256) by (inversion Htb; assumption).
assert (Htb' : Forall (fun x => 0 < x < 256) t') by (inversion Htb; assumption).
cbn [hd] in G10.
destruct HCX as (HJ & HROc & Ggp & Gtp & G9 & G22 & Hal16 & Hwlo & Hwhi).
destruct HREC as (HR0 & HR8 & HR63 & HRam & HRimg & HRside & HDrng & HCrng & Hn0a & Hn0b & Hovr &
  VD & Vcap & Vn0 & Vov0 & HRra & HRhv & HRwr).
destruct HBUF as (HD0 & HD63 & HDapp & HDam & HDimg & HDside & HDR & HDra & HDhv & HDwr).
destruct HSEP as (Hse1 & Hse2 & Hse3).
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & Hstk & _).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp.
change (bv_modulus 64) with (2 ^ 64) in Rsp. fold (spZ regs) in Rsp.
assert (Hceil2 : alloc_ceiling <= spZ regs - TSB_CH_STK) by lia.
assert (HR47 : spZ regs + 116 <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HRam; lia).
assert (HD47 : D + 48 <= 2 ^ 47)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HDam; lia).
assert (HD4096 : 4096 <= D) by (destruct HDapp as [HH _]; exact HH).
assert (Hidx : (1 < length ((c :: t') ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
destruct (Hga 1%nat Hidx) as [Hc2m0 Hc2r]. change (Z.of_nat 1) with 1 in Hc2m0.
set (c2 := nth 1 ((c :: t') ++ [0]) 0) in *.
assert (Hc2z : c2 = 0 -> t' = []).
{ unfold c2. destruct t' as [|x t'']; [reflexivity|]. cbn [app nth]. intros Hx. exfalso. inversion Htb'. lia. }
assert (Hc2nil : t' = [] -> c2 = 0) by (intros Hx; unfold c2; rewrite Hx; reflexivity).
assert (Hc2nz : t' <> [] -> c2 = hd 0 t').
{ unfold c2. destruct t' as [|x t'']; [intros HX; exfalso; exact (HX eq_refl)|]. cbn [app nth hd]. reflexivity. }
assert (Gr2 : getr regs1 2 = getr regs 2)
  by (apply (l4_keep_get regs regs1 rbn_cl4 (2%bv : bv 5) HKP); vm_compute; reflexivity).
assert (Gr3 : getr regs1 3 = getr regs 3)
  by (apply (l4_keep_get regs regs1 rbn_cl4 (3%bv : bv 5) HKP); vm_compute; reflexivity).
assert (Gr4 : getr regs1 4 = getr regs 4)
  by (apply (l4_keep_get regs regs1 rbn_cl4 (4%bv : bv 5) HKP); vm_compute; reflexivity).
assert (Gr9 : getr regs1 9 = getr regs 9)
  by (apply (l4_keep_get regs regs1 rbn_cl4 (9%bv : bv 5) HKP); vm_compute; reflexivity).
assert (Gr22 : getr regs1 22 = getr regs 22)
  by (apply (l4_keep_get regs regs1 rbn_cl4 (22%bv : bv 5) HKP); vm_compute; reflexivity).
assert (Hsp1 : spZ regs1 = spZ regs) by (unfold spZ; rewrite Gr2; reflexivity).
assert (KEQ1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TSB_CH_STK <= a < spZ regs) ->
  ~ (spZ regs + 104 <= a < spZ regs + 116) -> ~ (D + n0 <= a < D + n) ->
  aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hs H1 H2. apply (proj1 HK1 a Ha Hs). intros [X | X]; [exact (H1 X) | exact (H2 X)]. }
eapply SRr_bind.
{ eapply (l4_pre fq STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 mem1 md1 k regs1 (spZ regs) c).
  - exact HJ1.
  - rewrite Gr9, G9. unfold w64, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - lia.
  - lia.
  - exact G10.
  - lia. }
cbv beta. intros Wp cp _ (-> & regs2 & mem2 & md2 & Ecfg2 & HJ2 & Keq2 & Kpr2 & Gra & Ga0 & Ga1 & HKP2).
subst cp.
assert (Gq2 : getr regs2 2 = getr regs1 2)
  by (apply (l4_keep_get regs1 regs2 l4_clA (2%bv : bv 5) HKP2); vm_compute; reflexivity).
assert (Gq3 : getr regs2 3 = getr regs1 3)
  by (apply (l4_keep_get regs1 regs2 l4_clA (3%bv : bv 5) HKP2); vm_compute; reflexivity).
assert (Gq4 : getr regs2 4 = getr regs1 4)
  by (apply (l4_keep_get regs1 regs2 l4_clA (4%bv : bv 5) HKP2); vm_compute; reflexivity).
assert (Gq20 : getr regs2 20 = getr regs1 20)
  by (apply (l4_keep_get regs1 regs2 l4_clA (20%bv : bv 5) HKP2); vm_compute; reflexivity).
assert (Gq21 : getr regs2 21 = getr regs1 21)
  by (apply (l4_keep_get regs1 regs2 l4_clA (21%bv : bv 5) HKP2); vm_compute; reflexivity).
assert (Gq22 : getr regs2 22 = getr regs1 22)
  by (apply (l4_keep_get regs1 regs2 l4_clA (22%bv : bv 5) HKP2); vm_compute; reflexivity).
assert (Gq24 : getr regs2 24 = getr regs1 24)
  by (apply (l4_keep_get regs1 regs2 l4_clA (24%bv : bv 5) HKP2); vm_compute; reflexivity).
assert (Hsp2 : spZ regs2 = spZ regs) by (unfold spZ; rewrite Gq2, Gr2; reflexivity).
assert (HRO2 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) mem2))
  by (intros a Hro Ho He; rewrite (Keq2 a); exact (HRO1 a Hro Ho He)).
assert (KEQ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TSB_CH_STK <= a < spZ regs) ->
  ~ (spZ regs + 104 <= a < spZ regs + 116) -> ~ (D + n0 <= a < D + n) ->
  aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hs H1 H2; rewrite (Keq2 a); exact (KEQ1 a Ha Hs H1 H2)).
assert (VD2 : val_mem SEGS (mrestrict (w_H W1) mem2) (spZ regs + 88) 8 D).
{ apply (val_mem_kept SEGS (w_H W) (w_H W1) memc mem2); [|exact VD].
  intros j Hj. cbn [Z.of_nat] in Hj. apply KEQ2; lia. }
assert (Vcap2 : val_mem SEGS (mrestrict (w_H W1) mem2) (spZ regs + 88 + 8) 8 48).
{ apply (val_mem_kept SEGS (w_H W) (w_H W1) memc mem2); [|exact Vcap].
  intros j Hj. cbn [Z.of_nat] in Hj. apply KEQ2; lia. }
assert (Vn2 : val_mem SEGS (mrestrict (w_H W1) mem2) (spZ regs + 104) 8 n)
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 mem2); [intros j Hj; apply Keq2 | exact Vn]).
assert (Vov2 : val_mem SEGS (mrestrict (w_H W1) mem2) (spZ regs + 112) 4 ov)
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 mem2); [intros j Hj; apply Keq2 | exact Vov]).
assert (Hgw2 : garr8 SEGS (mrestrict (w_H W1) mem2) (D + n0) wr)
  by (apply (l4_garr8_kept (w_H W1) (w_H W1) mem1 mem2); [intros a Ha; apply Keq2 | exact Hgw]).
assert (HEpres2 : forall a, (spZ regs - TSB_CH_STK <= a < spZ regs) \/
    (spZ regs + 104 <= a < spZ regs + 116) \/ (D + n0 <= a < D + n) ->
  aview SEGS (w_H W1) mem2 a <> None).
{ intros a [Hw | [Hrec | Hbuf]].
  - apply (aview_some_of_apresent SEGS (w_H W1) mem2 a). apply Kpr2.
    exact (proj2 (proj2 (proj2 (proj2 (proj2 HK1)))) a Hw).
  - destruct (Z_lt_le_dec a (spZ regs + 112)) as [Hlt | Hge].
    + apply (l4_val_pres W1 mem2 (spZ regs + 104) 8 n a Vn2). cbn [Z.of_nat]. lia.
    + apply (l4_val_pres W1 mem2 (spZ regs + 112) 4 ov a Vov2). cbn [Z.of_nat]. lia.
  - apply (l4_garr8_pres W1 mem2 (D + n0) wr a Hgw2). lia. }
assert (HRra2 : range_addressable (aview SEGS (w_H W1) mem2) SHADOW_OFF (spZ regs + 88) 28).
{ apply (l4_ra_kept (w_H W) (w_H W1) memc mem2); [|exact HRra].
  intros x Hx. pose proof (l4_shadow_lo x ltac:(lia) ltac:(lia)) as Hsh.
  pose proof (l4_shadow_apart D 48 x HDapp ltac:(lia) ltac:(lia)) as Hap. apply KEQ2; lia. }
assert (HRhv2 : shadow_hull_vis (aview SEGS (w_H W1) mem2) (spZ regs + 88) 28).
{ apply (l4_hull_move W memc W1 mem2 (spZ regs + 88) 28
    (fun a => (spZ regs - TSB_CH_STK <= a < spZ regs) \/ (spZ regs + 104 <= a < spZ regs + 116)
              \/ (D + n0 <= a < D + n))).
  - cbv beta. intros s Hs He. apply KEQ2; [exact Hs | intros X; apply He; auto | intros X; apply He; auto
      | intros X; apply He; auto].
  - cbv beta. intros s He. exact (HEpres2 s He).
  - cbv beta. intros s. lia.
  - lia.
  - lia.
  - lia.
  - exact HRhv. }
eapply SRr_bind.
{ eapply (TSB fq STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 mem2 md2 k regs2
    (spZ regs + 88) c D 48 n []).
  - exact HJ2.
  - exact HRO2.
  - rewrite Gra. unfold w64. apply ret_ok_codeptr_v;
      [unfold l4_pcB, RBN_L4, AF_both3_reac_box_name; lia | vm_compute; reflexivity].
  - unfold raZ. rewrite Gra. unfold w64.
    rewrite unsigned_lit_small by (unfold l4_pcB, RBN_L4, AF_both3_reac_box_name; lia).
    unfold l4_pcB, RBN_L4, AF_both3_reac_box_name. lia.
  - rewrite Gq3, Gr3. exact Ggp.
  - rewrite Gq4, Gr4. exact Gtp.
  - exact Ga0.
  - exact Ga1.
  - apply achain_low. unfold s0Z. rewrite getr_same by reg_neq_tac.
    rewrite unsigned_lit_small by lia. lia.
  - rewrite Hsp2. exact Hal16.
  - rewrite Hsp2. exact Hwlo.
  - rewrite Hsp2. exact Hwhi.
  - lia.
  - exact HR0.
  - exact HR8.
  - exact HR63.
  - exact HRam.
  - rewrite Hsp2. exact HRside.
  - exact HRimg.
  - lia.
  - lia.
  - lia.
  - exact VD2.
  - exact Vcap2.
  - replace (spZ regs + 88 + 16) with (spZ regs + 104) by lia. exact Vn2.
  - exact HRra2.
  - exact HRhv2.
  - intros a Ha. split.
    + apply (l4_awr_move STK sp0 FP ly S lyc Sc lyc1 Sc1 own a Hab1 HlyF1).
      exact (proj1 (HRwr a ltac:(lia))).
    + apply (l4_awr_pres STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 mem2 md2 k a HJ2).
      apply (l4_awr_move STK sp0 FP ly S lyc Sc lyc1 Sc1 own a Hab1 HlyF1).
      exact (proj1 (HRwr a ltac:(lia))).
  - intros Hlt.
    assert (Hn46 : n <= 46) by lia.
    assert (Hawr : awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc1 Sc1) lyc1 own (D + n)).
    { apply (l4_awr_move STK sp0 FP ly S lyc Sc lyc1 Sc1 own (D + n) Hab1 HlyF1).
      exact (proj1 (HDwr (D + n) ltac:(lia))). }
    split; [lia|]. split; [lia|].
    split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia|].
    split.
    { apply (l4_ra_kept (w_H W) (w_H W1) memc mem2);
        [|apply (range_addressable_sub (aview SEGS (w_H W) memc) SHADOW_OFF D 48); [exact HDra | lia | lia]].
      intros x Hx. pose proof (l4_shadow_lo x ltac:(lia) ltac:(lia)) as Hsh.
      pose proof (l4_shadow_apart D 48 x HDapp ltac:(lia) ltac:(lia)) as Hap. apply KEQ2; lia. }
    split.
    { apply (l4_hull_move W memc W1 mem2 (D + n) 1
        (fun a => (spZ regs - TSB_CH_STK <= a < spZ regs) \/ (spZ regs + 104 <= a < spZ regs + 116)
                  \/ (D + n0 <= a < D + n))).
      - cbv beta. intros s Hs He. apply KEQ2; [exact Hs | intros X; apply He; auto | intros X; apply He; auto
          | intros X; apply He; auto].
      - cbv beta. intros s He. exact (HEpres2 s He).
      - cbv beta. intros s. lia.
      - lia.
      - lia.
      - lia.
      - intros s Hs. apply (HDhv s). unfold shadow_addr in *.
        pose proof (Z.div_le_mono D (D + n) 8 ltac:(lia) ltac:(lia)).
        pose proof (Z.div_le_mono (D + n) (D + 47) 8 ltac:(lia) ltac:(lia)).
        pose proof (Z.mul_div_le (SHADOW_OFF + D / 8) 8 ltac:(lia)).
        pose proof (Z.mul_div_le (SHADOW_OFF + (D + n) / 8) 8 ltac:(lia)).
        pose proof (Z.mul_div_le (SHADOW_OFF + (D + 47) / 8) 8 ltac:(lia)).
        assert (8 * ((SHADOW_OFF + D / 8) / 8) <= SHADOW_OFF + D / 8) by (apply Z.mul_div_le; lia).
        assert ((SHADOW_OFF + D / 8) / 8 <= (SHADOW_OFF + (D + n) / 8) / 8)
          by (apply Z.div_le_mono; lia).
        assert ((SHADOW_OFF + (D + n + 1 - 1) / 8) / 8 <= (SHADOW_OFF + (D + 48 - 1) / 8) / 8)
          by (apply Z.div_le_mono; lia).
        lia. }
    split; [rewrite Hsp2; lia|].
    split; [unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia|].
    split; [lia|].
    split; [exact Hawr|].
    apply (l4_awr_pres STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 mem2 md2 k (D + n) HJ2 Hawr). }
cbv beta. intros Wq cq _ (ly2 & S2 & regs3 & mem3 & md3 & Ecfg3 & HJ3 & Hpres3 & Hfrs3 & Habs3 & Hcase).
subst cq. rewrite Gra.
assert (P20 : getr regs3 20 = getr regs2 20)
  by (apply (l4_pres_get regs2 regs3 (20%bv : bv 5) Hpres3);
      change (bv_unsigned (20%bv : bv 5)) with 20; unfold acallee_saved; lia).
assert (P21 : getr regs3 21 = getr regs2 21)
  by (apply (l4_pres_get regs2 regs3 (21%bv : bv 5) Hpres3);
      change (bv_unsigned (21%bv : bv 5)) with 21; unfold acallee_saved; lia).
assert (P22 : getr regs3 22 = getr regs2 22)
  by (apply (l4_pres_get regs2 regs3 (22%bv : bv 5) Hpres3);
      change (bv_unsigned (22%bv : bv 5)) with 22; unfold acallee_saved; lia).
assert (P24 : getr regs3 24 = getr regs2 24)
  by (apply (l4_pres_get regs2 regs3 (24%bv : bv 5) Hpres3);
      change (bv_unsigned (24%bv : bv 5)) with 24; unfold acallee_saved; lia).
assert (G20' : getr regs3 20 = w64 (Q + 1)) by (rewrite P20, Gq20; exact G20).
assert (G21' : getr regs3 21 = w64 (-1)) by (rewrite P21, Gq21; exact G21).
assert (G22' : getr regs3 22 = w64 SHADOW_OFF) by (rewrite P22, Gq22, Gr22; exact G22).
assert (G24' : getr regs3 24 = w64 Q) by (rewrite P24, Gq24; exact G24).
assert (HKPc : rbn_keep_regs regs regs3 rbn_cl4).
{ apply (l4_keep_trans regs regs1 regs3); [exact HKP|].
  apply (l4_keep_trans regs1 regs2 regs3).
  - apply (l4_keep_sub regs1 regs2 l4_clA); [exact HKP2|].
    intros z Hz. unfold l4_clA in Hz. unfold rbn_cl4, rbn_clc. cbn [In app] in *. tauto.
  - apply (l4_keep_sub regs2 regs3 rbn_clc); [exact (l4_keep_of_pres regs2 regs3 Hpres3)|].
    intros z Hz. unfold rbn_cl4. apply in_or_app. left. exact Hz. }
assert (FINISH : forall (n' ov' : Z) (wr' : list Z),
  n0 <= n' <= 47 -> (ov' = 0 \/ ov' = 1) -> Z.of_nat (length wr') = n' - n0 ->
  (n' = n + 1 /\ ov' = ov /\ wr' = wr ++ [c] /\ n <= 46) \/ (n' = n /\ n = 47 /\ ov' = 1 /\ wr' = wr) ->
  val_mem SEGS (mrestrict (w_H Wq) mem3) (spZ regs + 104) 8 n' ->
  val_mem SEGS (mrestrict (w_H Wq) mem3) (spZ regs + 112) 4 ov' ->
  garr8 SEGS (mrestrict (w_H Wq) mem3) (D + n0) wr' ->
  tsb_ch_kept B lyc Sc W memc Wq mem3 (spZ regs)
    (fun a => spZ regs + 104 <= a < spZ regs + 116 \/ D + n0 <= a < D + n') ->
  SRr SEGS Wq (cfg_at (fx := fq) SEGS (BASE + l4_pcB) regs3 mem3 md3)
    (rbn_lpost B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L4X rbn_cl4
       (spZ regs + 88) D n0 nF ovF wrF)).
{ intros n' ov' wr' Hn'r Hov' Hwr'l Hrel Vn3 Vov3 Hgw3 HK3.
  assert (KEQ3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TSB_CH_STK <= a < spZ regs) ->
    ~ (spZ regs + 104 <= a < spZ regs + 116) -> ~ (D + n0 <= a < D + n') ->
    aview SEGS (w_H Wq) mem3 a = aview SEGS (w_H W) memc a).
  { intros a Ha Hs H1 H2. apply (proj1 HK3 a Ha Hs). intros [X | X]; [exact (H1 X) | exact (H2 X)]. }
  assert (HRO3 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wq) mem3)).
  { apply (l4_ro_move W memc Wq mem3); [|exact HROc].
    intros a Him Ho He. exact (proj1 (proj2 (proj2 HK3)) a Him Ho He). }
  assert (Vc2 : val_mem SEGS (mrestrict (w_H Wq) mem3) (Q + 1) 1 c2).
  { apply (val_mem_kept SEGS (w_H W) (w_H Wq) memc mem3); [|exact Hc2m0].
    intros j Hj. cbn [Z.of_nat] in Hj. apply KEQ3; lia. }
  assert (HRA3 : range_addressable (aview SEGS (w_H Wq) mem3) SHADOW_OFF (Q + 1) 1).
  { apply (l4_ra_kept (w_H W) (w_H Wq) memc mem3);
      [|apply (range_addressable_sub (aview SEGS (w_H W) memc) SHADOW_OFF Q
          (Z.of_nat (length (c :: t')) + 1)); [exact HRAq | lia | lia]].
    intros x Hx. pose proof (l4_shadow_lo x ltac:(lia) ltac:(lia)) as Hsh.
    pose proof (l4_shadow_apart D 48 x HDapp ltac:(lia) ltac:(lia)) as Hap. apply KEQ3; lia. }
  eapply SRr_bind.
  { eapply (l4_post fq STK sp0 FP ly S W0 mem0 md0 own ly2 S2 Wq mem3 md3 k regs3 Q c2).
    - exact HJ3.
    - lia.
    - lia.
    - exact G20'.
    - exact G21'.
    - exact G22'.
    - exact G24'.
    - exact Vc2.
    - exact HRA3. }
  cbv beta. intros Wr cr _ (-> & regs4 & mem4 & md4 & HJ4 & Keq4 & Kpr4 & HKP4 & Hcase2).
  assert (HK4 : tsb_ch_kept B lyc Sc W memc Wq mem4 (spZ regs)
    (fun a => spZ regs + 104 <= a < spZ regs + 116 \/ D + n0 <= a < D + n')).
  { eapply (l4_kept_trans lyc Sc ly2 S2 W memc mdc Wq mem3 Wq mem4 (spZ regs)
      (fun a => spZ regs + 104 <= a < spZ regs + 116 \/ D + n0 <= a < D + n') (fun _ => False)).
    - exact HARc.
    - lia.
    - cbv beta. intros a X. exact X.
    - cbv beta. intros a X. destruct X.
    - exact HK3.
    - apply l4_kept_of_eq; [exact Keq4 | exact Kpr4|].
      intros a Ha. exact (proj2 (proj2 (proj2 (proj2 (proj2 HK3)))) a Ha). }
  assert (Vn4 : val_mem SEGS (mrestrict (w_H Wq) mem4) (spZ regs + 104) 8 n')
    by (apply (val_mem_kept SEGS (w_H Wq) (w_H Wq) mem3 mem4); [intros j Hj; apply Keq4 | exact Vn3]).
  assert (Vov4 : val_mem SEGS (mrestrict (w_H Wq) mem4) (spZ regs + 112) 4 ov')
    by (apply (val_mem_kept SEGS (w_H Wq) (w_H Wq) mem3 mem4); [intros j Hj; apply Keq4 | exact Vov3]).
  assert (Hgw4 : garr8 SEGS (mrestrict (w_H Wq) mem4) (D + n0) wr')
    by (apply (l4_garr8_kept (w_H Wq) (w_H Wq) mem3 mem4); [intros a Ha; apply Keq4 | exact Hgw3]).
  assert (HRO4 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wq) mem4))
    by (apply (l4_ro_move Wq mem3 Wq mem4); [intros a Hi Ho He; apply Keq4 | exact HRO3]).
  assert (HKPd : rbn_keep_regs regs regs4 rbn_cl4).
  { apply (l4_keep_trans regs regs3 regs4); [exact HKPc|].
    apply (l4_keep_sub regs3 regs4 l4_clB); [exact HKP4|].
    intros z Hz. unfold l4_clB in Hz. unfold rbn_cl4, rbn_clc. cbn [In app] in *. tauto. }
  assert (Habs4 : ablocks B ly2 S2 = ablocks B lyc Sc) by (rewrite Habs3; exact Hab1).
  assert (Hfrs4 : frames S2 = frames Sc) by (rewrite Hfrs3; exact Hfr1).
  assert (HlyF4 : ly_F ly2 = ly_F lyc)
    by (rewrite (l4_lyF STK sp0 FP ly S W0 mem0 md0 own ly2 S2 Wq mem4 md4 k HJ4);
        symmetry; exact (l4_lyF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ)).
  destruct Hcase2 as [(Hc2eq & Ecfg4) | (Hc2ne & Ecfg4 & G24b & G20b & G10b)].
  - assert (Ht'nil : t' = []) by (apply Hc2z; exact Hc2eq).
    subst cr. apply SRr_ret.
    assert (HnFe : nF = n')
      by (rewrite HnF, Ht'nil; cbn [length];
          destruct Hrel as [(X1 & _ & _ & X4) | (X1 & X2 & _ & _)]; lia).
    assert (HovFe : ovF = ov').
    { rewrite HovF, Ht'nil. cbn [length].
      destruct Hrel as [(X1 & X2 & _ & X4) | (X1 & X2 & X3 & _)].
      - replace (n + Z.of_nat 1 <=? 47) with true by (symmetry; apply Z.leb_le; cbn [Z.of_nat]; lia).
        rewrite X2. reflexivity.
      - replace (n + Z.of_nat 1 <=? 47) with false by (symmetry; apply Z.leb_gt; cbn [Z.of_nat]; lia).
        rewrite X3. reflexivity. }
    assert (HwrFe : wrF = wr').
    { rewrite HwrF, Ht'nil.
      destruct Hrel as [(X1 & X2 & X3 & X4) | (X1 & X2 & X3 & X4)].
      - replace (Z.to_nat (47 - n)) with (Datatypes.S (Z.to_nat (47 - n - 1))) by lia.
        cbn [firstn]. rewrite firstn_nil. rewrite X3. reflexivity.
      - replace (Z.to_nat (47 - n)) with 0%nat by lia. cbn [firstn].
        rewrite X4, app_nil_r. reflexivity. }
    exists ly2, S2, regs4, mem4, md4.
    split.
    { replace (BASE + AF_both3_reac_box_name + RBN_L4X) with (BASE + l4_pcX)
        by (unfold l4_pcX; lia). reflexivity. }
    split; [exact HJ4|].
    split; [exact Hfrs4|].
    split; [exact Habs4|].
    split; [exact HRO4|].
    split; [exact HKPd|].
    split; [replace (spZ regs + 88 + 16) with (spZ regs + 104) by lia; rewrite HnFe; exact Vn4|].
    split; [replace (spZ regs + 88 + 24) with (spZ regs + 112) by lia; rewrite HovFe; exact Vov4|].
    split; [rewrite HwrFe; exact Hgw4|].
    apply (l4_kept_weak lyc Sc W memc Wq mem4 (spZ regs)
      (fun a => spZ regs + 104 <= a < spZ regs + 116 \/ D + n0 <= a < D + n'));
      [cbv beta; intros a X; rewrite HwrFe; lia | exact HK4].
  - assert (Ht'ne : t' <> []) by (intros X; apply Hc2ne; apply Hc2nil; exact X).
    subst cr.
    assert (HgaQ : garr8 SEGS (mrestrict (w_H W) memc) (Q + 1) (t' ++ [0])).
    { intros j Hj.
      assert (Hj2 : (Datatypes.S j < length ((c :: t') ++ [0%Z]))%nat)
        by (change ((c :: t') ++ [0%Z]) with (c :: (t' ++ [0%Z])); cbn [length]; lia).
      destruct (Hga (Datatypes.S j) Hj2) as [Hv Hr]. split; [|exact Hr].
      replace (Q + 1 + Z.of_nat j) with (Q + Z.of_nat (Datatypes.S j)) by lia. exact Hv. }
    eapply (IH fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0
      ly2 S2 Wq mem4 md4 regs4 (Q + 1) t' n' ov' wr' nF ovF wrF).
    + cbn [length] in Hm. lia.
    + rewrite HnF. destruct Hrel as [(X1 & _ & _ & _)|(X1 & X2 & _ & _)].
      * replace (n + Z.of_nat (length (c :: t'))) with (n' + Z.of_nat (length t')) by (rewrite HLn; lia).
        reflexivity.
      * rewrite HLn. lia.
    + rewrite HovF. destruct Hrel as [(X1 & X2 & _ & _)|(X1 & X2 & X3 & _)].
      * replace (n + Z.of_nat (length (c :: t'))) with (n' + Z.of_nat (length t')) by (rewrite HLn; lia).
        rewrite X2. reflexivity.
      * replace (n + Z.of_nat (length (c :: t')) <=? 47) with false
          by (symmetry; apply Z.leb_gt; rewrite HLn; lia).
        rewrite X3. destruct (n' + Z.of_nat (length t') <=? 47); reflexivity.
    + rewrite HwrF. destruct Hrel as [(X1 & X2 & X3 & X4)|(X1 & X2 & X3 & X4)].
      * replace (Z.to_nat (47 - n)) with (Datatypes.S (Z.to_nat (47 - n'))) by lia.
        cbn [firstn]. rewrite X3, <- app_assoc. reflexivity.
      * replace (Z.to_nat (47 - n)) with 0%nat by lia.
        replace (Z.to_nat (47 - n')) with 0%nat by lia. cbn [firstn].
        rewrite X4, !app_nil_r. reflexivity.
    + exact Ht'ne.
    + exact Htb'.
    + exact HCX0.
    + exact HREC0.
    + exact HBUF0.
    + exact HgaQ.
    + lia.
    + rewrite HLn in HQ47. lia.
    + apply (range_addressable_sub (aview SEGS (w_H W) memc) SHADOW_OFF Q
        (Z.of_nat (length (c :: t')) + 1)); [exact HRAq | lia | rewrite HLn; lia].
    + unfold rbn_lsep in HSEP0 |- *. rewrite HLn in HSEP0. lia.
    + lia.
    + lia.
    + exact Hov'.
    + exact Hwr'l.
    + exact HJ4.
    + exact Habs4.
    + exact Hfrs4.
    + exact HlyF4.
    + exact HRO4.
    + exact HK4.
    + exact Vn4.
    + exact Vov4.
    + exact Hgw4.
    + rewrite G10b, (Hc2nz Ht'ne). reflexivity.
    + exact G24b.
    + replace (Q + 1 + 1) with (Q + 2) by lia. exact G20b.
    + rewrite (l4_keep_get regs3 regs4 l4_clB (21%bv : bv 5) HKP4 ltac:(vm_compute; reflexivity)).
      exact G21'.
    + exact HKPd. }
destruct Hcase as [(Hge & Vov3 & Kc) | (Hlt & Vn3 & Vbyte & Kc)].
- assert (Hn47 : n = 47) by lia.
  apply (FINISH n 1 wr).
  + lia.
  + right; reflexivity.
  + exact Hwrl.
  + right. split; [reflexivity | split; [lia | split; [reflexivity | reflexivity]]].
  + apply (val_mem_kept SEGS (w_H W1) (w_H Wq) mem2 mem3); [|exact Vn2].
    intros j Hj. cbn [Z.of_nat] in Hj. apply (proj1 Kc); lia.
  + replace (spZ regs + 112) with (spZ regs + 88 + 24) by lia. exact Vov3.
  + apply (l4_garr8_kept (w_H W1) (w_H Wq) mem2 mem3); [|exact Hgw2].
    intros a Ha. apply (proj1 Kc); lia.
  + eapply (l4_kept_trans lyc Sc lyc1 Sc1 W memc mdc W1 mem2 Wq mem3 (spZ regs)
      (fun a => spZ regs + 104 <= a < spZ regs + 116 \/ D + n0 <= a < D + n)
      (fun a => spZ regs + 88 + 24 <= a < spZ regs + 88 + 28)).
    * exact HARc.
    * lia.
    * cbv beta. intros a X. exact X.
    * cbv beta. intros a X. left. lia.
    * apply (l4_kept_trans lyc Sc lyc1 Sc1 W memc mdc W1 mem1 W1 mem2 (spZ regs)
        (fun a => spZ regs + 104 <= a < spZ regs + 116 \/ D + n0 <= a < D + n) (fun _ => False));
        [exact HARc | lia | cbv beta; intros a X; exact X | cbv beta; intros a X; destruct X | exact HK1 |].
      apply l4_kept_of_eq; [exact Keq2 | exact Kpr2|].
      intros a Ha. exact (proj2 (proj2 (proj2 (proj2 (proj2 HK1)))) a Ha).
    * rewrite Hsp2 in Kc. exact Kc.
- apply (FINISH (n + 1) ov (wr ++ [c])).
  + lia.
  + exact Hov.
  + rewrite length_app. cbn [length]. lia.
  + left. split; [reflexivity | split; [reflexivity | split; [reflexivity | lia]]].
  + replace (spZ regs + 104) with (spZ regs + 88 + 16) by lia. exact Vn3.
  + apply (val_mem_kept SEGS (w_H W1) (w_H Wq) mem2 mem3); [|exact Vov2].
    intros j Hj. cbn [Z.of_nat] in Hj. apply (proj1 Kc); lia.
  + apply (garr8_app1 SEGS (mrestrict (w_H W1) mem2) (mrestrict (w_H Wq) mem3) (D + n0) wr c).
    * exact Hgw2.
    * rewrite Hwrl. replace (D + n0 + (n - n0)) with (D + n) by lia.
      replace (c mod 256) with c in Vbyte by (symmetry; apply Z.mod_small; lia). exact Vbyte.
    * lia.
    * intros a Ha. rewrite Hwrl in Ha. apply (mbyte_of_aview SEGS (w_H W1) (w_H Wq)).
      apply (proj1 Kc); lia.
  + eapply (l4_kept_trans lyc Sc lyc1 Sc1 W memc mdc W1 mem2 Wq mem3 (spZ regs)
      (fun a => spZ regs + 104 <= a < spZ regs + 116 \/ D + n0 <= a < D + n)
      (fun a => spZ regs + 88 + 16 <= a < spZ regs + 88 + 24 \/ a = D + n)).
    * exact HARc.
    * lia.
    * cbv beta. intros a X. destruct X as [X|X]; [left; lia | right; lia].
    * cbv beta. intros a X. destruct X as [X|X]; [left; lia | right; lia].
    * apply (l4_kept_trans lyc Sc lyc1 Sc1 W memc mdc W1 mem1 W1 mem2 (spZ regs)
        (fun a => spZ regs + 104 <= a < spZ regs + 116 \/ D + n0 <= a < D + n) (fun _ => False));
        [exact HARc | lia | cbv beta; intros a X; exact X | cbv beta; intros a X; destruct X | exact HK1 |].
      apply l4_kept_of_eq; [exact Keq2 | exact Kpr2|].
      intros a Ha. exact (proj2 (proj2 (proj2 (proj2 (proj2 HK1)))) a Ha).
    * rewrite Hsp2 in Kc. exact Kc.
Qed.

Lemma l4_top : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) (P D n0 ov0 : Z) (s : list Z) (nF ovF : Z) (wrF : list Z),
  nF = Z.min (n0 + Z.of_nat (length s)) 47 ->
  ovF = (if n0 + Z.of_nat (length s) <=? 47 then ov0 else 1) ->
  wrF = firstn (Z.to_nat (47 - n0)) s ->
  rbn_L4_run B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s nF ovF wrF.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s nF ovF wrF HnF HovF HwrF.
unfold rbn_L4_run. intros HCX HREC HBUF Hs0 Hsb Hsrc Hsep Hn0 Hov G10 G24 G20 G21.
unfold rbn_lsrc in Hsrc. destruct Hsrc as (Hga & HP0 & HP63 & HP47 & Hra).
rewrite length_app in HP63, HP47, Hra. cbn [length] in HP63, HP47, Hra.
replace (Z.of_nat (length s + 1)) with (Z.of_nat (length s) + 1) in HP63, HP47, Hra by lia.
pose proof HCX as (HJ & HROc & _ & _ & _ & _ & _ & _ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & _).
pose proof HREC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vn0 & Vov0 & _).
replace (BASE + AF_both3_reac_box_name + RBN_L4) with (BASE + l4_pcA) by (unfold l4_pcA; lia).
apply (l4_core (length s) fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0
  lyc Sc W memc mdc regs P s n0 ov0 [] nF ovF wrF).
- lia.
- exact HnF.
- exact HovF.
- exact HwrF.
- exact Hs0.
- exact Hsb.
- exact HCX.
- exact HREC.
- exact HBUF.
- exact Hga.
- exact HP0.
- lia.
- exact Hra.
- exact Hsep.
- lia.
- lia.
- exact Hov.
- cbn [length]. lia.
- exact HJ.
- reflexivity.
- reflexivity.
- reflexivity.
- exact HROc.
- apply l4_kept_of_eq; [intros a; reflexivity | intros a Hp; exact Hp |].
  intros a Ha. apply Hpresc. pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi). lia.
- replace (spZ regs + 104) with (spZ regs + 88 + 16) by lia. exact Vn0.
- replace (spZ regs + 112) with (spZ regs + 88 + 24) by lia. exact Vov0.
- apply garr8_nil.
- exact G10.
- exact G24.
- exact G20.
- exact G21.
- intros z Hz Hnc. reflexivity.
Qed.

Theorem rbn_l4_fits : rbn_L4_fits B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s Hlen.
apply l4_top.
- lia.
- replace (n0 + Z.of_nat (length s) <=? 47) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
- symmetry. apply firstn_all2. lia.
Qed.

Theorem rbn_l4_ovf : rbn_L4_ovf B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s Hlen.
apply l4_top.
- lia.
- replace (n0 + Z.of_nat (length s) <=? 47) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
- reflexivity.
Qed.

End h.
End f.
End d.

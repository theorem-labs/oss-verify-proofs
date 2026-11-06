(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_ctrl_checksum_verify on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlChecksumVerify.v, with its module paths and numbers changed; 66 of its 271 lines of code are new or changed and 57 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow DiscoSyms DiscoList DiscoAddr DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Fixpoint ckv_zsum (BS : list Z) (k : nat) : Z :=
match k with O => 0 | S k' => ckv_zsum BS k' + nth k' BS 0 end.
Lemma ckv_zsum_range : forall BS k, (forall j, (j < k)%nat -> 0 <= nth j BS 0 < 256) ->
0 <= ckv_zsum BS k <= 255 * Z.of_nat k.
Proof.
intros BS k. induction k as [|k IH]; intros H; cbn [ckv_zsum]; [lia|].
pose proof (H k ltac:(lia)). pose proof (IH ltac:(intros j Hj; apply H; lia)). lia.
Qed.
Lemma ckv_psum_map : forall BS k, (forall j, (j < k)%nat -> 0 <= nth j BS 0 < 256) ->
psum (map (Z_to_bv 8) BS) k = ckv_zsum BS k.
Proof.
intros BS k. induction k as [|k IH]; intros H; cbn [psum ckv_zsum]; [reflexivity|].
rewrite IH by (intros j Hj; apply H; lia). f_equal.
rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. apply H. lia.
Qed.
Lemma ckv_fin : forall s, 0 <= s < 2 ^ 64 ->
alu64 ALU_ADD (alu64 ALU_SLTU (alu64 ALU_AND (Z_to_bv 64 s) (Z_to_bv 64 255)) (Z_to_bv 64 1)) (Z_to_bv 64 (-1)) =
w64 (if s mod 256 =? 0 then 0 else -1).
Proof.
intros s Hs. unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small s) by lia. change (255 mod 2 ^ 64) with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
pose proof (Z.mod_pos_bound s 256 ltac:(lia)) as M.
rewrite (Z.mod_small (s mod 256)) by lia. change (1 mod 2 ^ 64) with 1. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
destruct (Z.eqb_spec (s mod 256) 0) as [E|E].
- rewrite E. reflexivity.
- replace (s mod 256 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Definition REAC_CTRL_CHECKSUM_VERIFY_STK : Z := 16.
Definition CKV_SB : Z := 0x7fff8000.
Section h.
Variable B : asyms.
Definition treac_ctrl_checksum_verify_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (BS : list Z) : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B REAC_CTRL_CHECKSUM_VERIFY_STK [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' => ly' = ly /\ S' = S /\ W' = W /\
       getr regs' 10 = w64 (if blocksum (map (Z_to_bv 8) BS) =? 0 then 0 else -1)).
Definition treac_ctrl_checksum_verify_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (f : Z) (BS : list Z),
  afn_pre SEGS B REAC_CTRL_CHECKSUM_VERIFY_STK ly S W regs mem md ch ->
  getr regs 10 = w64 f ->
  (0 < f /\ f + 50 <= 2 ^ 47 /\ amem_range f 50 /\ off_img f 50 /\
   (f + 50 <= kLowShadowBeg \/ kHighMemBeg <= f) /\
   (spZ regs <= f \/ f + 50 <= spZ regs - REAC_CTRL_CHECKSUM_VERIFY_STK) /\
   (forall a, f <= a < f + 50 -> apresent (w_H W) mem a) /\
   range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF f 50 /\
   shadow_hull_vis (aview SEGS (w_H W) mem) f 50) ->
  garr8 SEGS (mrestrict (w_H W) mem) (f + 18) BS -> length BS = 32%nat ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_ctrl_checksum_verify) regs mem md)
    (treac_ctrl_checksum_verify_post fq regs ly S W mem md BS).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Definition CBx : sv := SOff 64 0.
Definition CBspan : Z * Z := (CKV_SB, CKV_SB + 2 ^ 44 - 1).
Definition ckv_chunk (j : nat) : YP09.chunk := YP09.mkChunk (18 + Z.of_nat j) (CVal 1 (SOff (32 + j) 0)).
Definition ckv_regions : smem :=
[ stack_region 16; got_regionP; bcell_regionP 64;
YP09.mkRegion (Some 10%nat) 0 50 0 0 (map ckv_chunk (seq 0 32)) ].
Definition ckv_facts : facts :=
mkFacts ((2%nat, mkAF (2^46) (2^47) 4) :: (10%nat, mkAF 1 (2 ^ 47 - 50) 0) ::
map (fun j => ((32 + j)%nat, mkAF 0 255 0)) (seq 0 32) ++ [(64%nat, mkAF CKV_SB CKV_SB 0)]) [] [].
Definition ss_ckv : sstate := mkSS AF_reac_ctrl_checksum_verify sr_atoms ckv_regions None ckv_facts.
Definition ckv_SH : list shent := [ mkSHE 10 0 50 ].
Definition ckv_extra (BS : list Z) : list word := map (Z_to_bv 64) (BS ++ [CKV_SB]).
Definition EC (regs : bvmap 5 word) (BS : list Z) : env := Eimg (Ereg regs (ckv_extra BS)).
Lemma afact_byte : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> afact_ok E n (mkAF 0 255 0).
Proof.
intros E n v H Hv. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H, unsigned_lit_small by lia.
rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
Lemma ckv_ew : forall regs BS, length BS = 32%nat ->
(forall n, (32 <= n < 64)%nat -> ew (EC regs BS) n = Z_to_bv 64 (nth (n - 32) BS 0)) /\
ew (EC regs BS) 64 = Z_to_bv 64 CKV_SB.
Proof.
intros regs BS HL. unfold EC. split.
- intros n Hn. rewrite Eimg_low by (unfold A_TEXT; lia).
replace n with (32 + (n - 32))%nat at 1 by lia. rewrite ew_Ereg_extra. unfold ckv_extra.
rewrite map_nth. rewrite app_nth1 by lia. reflexivity.
- rewrite Eimg_low by (unfold A_TEXT; lia).
replace 64%nat with (32 + 32)%nat by lia. rewrite ew_Ereg_extra. unfold ckv_extra.
rewrite map_nth. rewrite app_nth2 by lia. rewrite HL. reflexivity.
Qed.
Lemma ckv_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (f : Z) (BS : list Z),
afn_pre SEGS B REAC_CTRL_CHECKSUM_VERIFY_STK ly S W regs mem md ch -> getr regs 10 = w64 f ->
(0 < f /\ f + 50 <= 2 ^ 47 /\ amem_range f 50 /\ off_img f 50 /\
 (f + 50 <= kLowShadowBeg \/ kHighMemBeg <= f) /\
 (spZ regs <= f \/ f + 50 <= spZ regs - REAC_CTRL_CHECKSUM_VERIFY_STK) /\
 (forall a, f <= a < f + 50 -> apresent (w_H W) mem a) /\
 range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF f 50 /\
 shadow_hull_vis (aview SEGS (w_H W) mem) f 50) ->
garr8 SEGS (mrestrict (w_H W) mem) (f + 18) BS -> length BS = 32%nat ->
st_ok_pi (fx := fq) SEGS VAL (EC regs BS) ss_ckv
(restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_reac_ctrl_checksum_verify)) mem (seg_rom SEGS)))
/\ sh_ok SEGS CBx ckv_SH (EC regs BS) (mrestrict (w_H W) mem).
Proof.
intros fq ly S W regs mem md ch f BS HPRE H10 HFO HBS HLEN.
pose proof HFO as (Hf0 & Hf47 & Hamr & Hfimg & Hfsh & Hfsp & Hfpres & HRA & Hhull).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_CTRL_CHECKSUM_VERIFY_STK = 16) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR;
unfold IMG_LO, IMG_TOP in HcellR, HgotR.
assert (GB : forall j, (j < 32)%nat -> val_mem SEGS (mrestrict (w_H W) mem) (f + 18 + Z.of_nat j) 1 (nth j BS 0) /\ 0 <= nth j BS 0 < 256)
by (intros j Hj; apply HBS; lia).
rewrite restrict_mkst_fx.
destruct (ckv_ew regs BS HLEN) as [EX E64].
set (E := EC regs BS) in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ckv_extra BS)) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 f) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Eo66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_ckv. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold ckv_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
[cbn [sv_denot]; rewrite Eo66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Eo66) by (pose proof (pa_val_range (A_OBJ 66)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 CBx CKV_SB);
[cbn [sv_denot CBx]; rewrite E64, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold CKV_SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat f E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
unfold ckv_chunk. destruct (GB j ltac:(lia)) as [Gv Gr].
apply (chunk_ok_val SEGS E _ f (18 + Z.of_nat j) 1 (SOff (32 + j) 0) (nth j BS 0)).
-- cbn [sv_denot]. rewrite (EX (32 + j)%nat) by lia. replace (32 + j - 32)%nat with j by lia.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-- zside.
-- zside.
-- rewrite Z.add_assoc. exact Gv.
+ apply pairwise_disjoint_of_extents. unfold ckv_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat f E10) by lia.
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Eo66) by (pose proof (pa_val_range (A_OBJ 66)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hf0 Hf47 Hfsp Hfimg C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. unfold off_img, IMG_LO, IMG_TOP in *. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [ckv_facts f_atoms atoms_ok map seq app Nat.add].
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16; clear; intros; repeat split; lia|].
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r;
revert Hf0 Hf47; clear; intros; repeat split; lia|].
repeat match goal with
| |- afact_ok _ ?n (mkAF 0 255 0) /\ _ =>
split; [apply (afact_byte E n (nth (n - 32) BS 0)); [apply EX; lia | apply GB; lia] |]
end.
split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E64, unsigned_lit_small by (unfold CKV_SB; lia).
rewrite Z.pow_0_r, Z.mod_1_r. lia.
- unfold sh_ok, ckv_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E CBx 10 f 50 f 0 50 HRA).
+ unfold U, CBx. cbn [sv_denot]. rewrite E64, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold CKV_SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. revert Hfsh Hx. clear. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.
Theorem pb_reac_ctrl_checksum_verify : treac_ctrl_checksum_verify_spec.
Proof.
unfold treac_ctrl_checksum_verify_spec, treac_ctrl_checksum_verify_post.
intros fq ly S W regs mem md ch f BS HPRE H10 HFO HBS HLEN.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (ckv_entry fq ly S W regs mem md ch f BS HPRE H10 HFO HBS HLEN) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_CTRL_CHECKSUM_VERIFY_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (GB : forall j, (j < 32)%nat -> 0 <= nth j BS 0 < 256) by (intros j Hj; apply HBS; lia).
destruct (ckv_ew regs BS HLEN) as [EX E64].
remember (EC regs BS) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ckv_extra BS)) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (ckv_extra BS)) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at; pose proof (paj_run (fx := fq) B LAWS) as RUN; pose proof (paj_branch (fx := fq) (PI := PI)) as BR;
pose proof (paj_ret_at (fx := fq) (PL := PL_disco) (PI := PI)) as RET.
change (w64 (BASE + AF_reac_ctrl_checksum_verify)) with (Z_to_bv 64 (BASE + AF_reac_ctrl_checksum_verify)).
let leaf_ret := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
apply apost_base_same_fx; eexists ly, S, _, _, _;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (ckv_extra BS) HS);
[eapply env_agree_trans; [exact HAE | split; [intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]
| vm_compute; reflexivity]|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
cbn [ms_regs]; rewrite R10;
repeat (rewrite EX by lia); cbn [Nat.sub]; rewrite !alu64_add_lit;
lazymatch goal with |- context [alu64 ALU_AND (Z_to_bv 64 ?s) _] =>
replace s with (ckv_zsum BS 32) by (cbn [ckv_zsum]; lia) end;
rewrite ckv_fin by (pose proof (ckv_zsum_range BS 32 GB); lia);
unfold blocksum; rewrite (ckv_psum_map BS 32 GB); reflexivity
end in
let rec go := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK CBspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |];
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
lazymatch goal with
| HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM CBx ckv_SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K CBx CBspan ckv_SH (start K CBx CBspan ckv_SH ss) end in
lazymatch why with
| SR_jalr _ => leaf_ret
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' CBspan; [go | go]
| _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
end
end end in
go.
Qed.
End h.
End f.
End d.

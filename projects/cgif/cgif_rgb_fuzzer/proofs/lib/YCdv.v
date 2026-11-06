(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition A_cbb : Z := 0x8ba3c.
Definition A_cbb_loop : Z := 0x8bb5c.
Definition A_cbb_tail : Z := 0x8bab4.
Definition A_asan_memcpy : Z := 0x52074.
Definition CBB_LSTK : Z := ESTACK.
Definition CBB_STK : Z := 96 + ESTACK.
Lemma alias_srlw_sll : forall E v, ew E 23 = Z_to_bv 64 (256 * v) -> 0 <= v < 2 ^ 22 ->
sv_denot E (SAlu ALU_SLL (SAluw ALU_SRL (SOff 23 0) (SLit 8)) (SLit 8)) = sv_denot E (SOff 23 0).
Proof.
intros E v H23 Hv. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite (U_atom E 23 (256 * v) H23) by lia. rewrite !U_SLit.
change (zcanon 8 mod 2 ^ 32) with 8. change (Z.land 8 31) with 8. change (Z.land (zcanon 8) 63) with 8.
rewrite (Z.mod_small (256 * v)) by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
replace (256 * v / 2 ^ 8) with v by (change (2 ^ 8) with 256; rewrite Z.mul_comm, Z.div_mul; lia).
unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
replace (bv_modulus 32) with (2 ^ 32) by reflexivity. replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
rewrite (Z.mod_small (v + 2 ^ 31)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia.
rewrite (Z.mod_small v) by lia. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma req_size_pos' : forall m, 0 <= m -> 0 < req_size m /\ m <= req_size m.
Proof. intros m Hm. unfold req_size. destruct (Z.eqb_spec m 0); cbn; lia. Qed.
Section f.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis AIMC : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Definition PTR (al : Z) : afact := mkAF 4096 140737479966720 al.
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition TCBB_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition TCBB_KEPT' : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 27]%bv.
Lemma tcbb_kept_cases : forall r, In r TCBB_KEPT -> r = 26%bv \/ In r TCBB_KEPT'.
Proof. intros r Hr. cbv [TCBB_KEPT In] in Hr. cbv [TCBB_KEPT' In]. intuition (subst; auto 20). Qed.
Definition BxL : sv := SOff 20 0.
Definition NOTP : afact := mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1) 0.
Definition NOTP1 : afact := mkAF (2 ^ 64 - 1 - 140737479966720 - 1) (2 ^ 64 - 2) 0.
Definition ss_tcbb_loop : sstate :=
mkSS A_cbb_loop (sr_set sr_atoms 26%bv (SLit 18446744073709551615)) [ reg_at 32 ] None
(mkFacts [ (8%nat, PTR 4); (9%nat, PTR 4); (18%nat, mkAF 0 (2^21) 0); (23%nat, mkAF 0 (2^21) 0);
(21%nat, NOTP); (24%nat, NOTP); (25%nat, NOTP1); (22%nat, mkAF 4097 (140737479966720 + 1) 0);
(32%nat, PTR 0); (33%nat, PTR 0); (20%nat, mkAF SB SB 0) ]
[]
[ (SAlu ALU_ADD (SOff 8%nat 0) (SMd M_MUL (SOff 18%nat 0) (SLit 256)), SOff 32%nat 0);
(SAlu ALU_ADD (SOff 22%nat 0) (SMd M_MUL (SOff 18%nat 0) (SLit 256)), SOff 32%nat 1);
(SAlu ALU_ADD (SOff 9%nat 0) (SMd M_MUL (SOff 18%nat 0) (SLit 255)), SOff 33%nat 0) ]).
Lemma tcbb_loop : forall (k : nat) (i : Z) W regs memc mdc sp1 mem0 md0 lyc Sc bb Lbb bl Lbl q,
Z.of_nat k = q - i -> 0 <= i < q ->
ajournal trbsegs B CBB_LSTK sp1 [(bb, bb + 256 * q)] lyc Sc W mem0 md0 [] lyc Sc W memc mdc 0 ->
In (bb, Lbb) (ablocks B lyc Sc) -> In (bl, Lbl) (ablocks B lyc Sc) ->
(bb + req_size Lbb <= bl \/ bl + req_size Lbl <= bb) ->
256 * q + 1 <= Lbb -> 255 * q <= Lbl -> q < 2 ^ 21 ->
spZ regs = sp1 -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 18 = w64 i -> getr regs 23 = w64 q -> getr regs 8 = w64 bb -> getr regs 9 = w64 bl ->
getr regs 21 = w64 (2 ^ 64 - 1 - bb) -> getr regs 22 = w64 (bb + 1) -> getr regs 24 = w64 (2 ^ 64 - 1 - bl) ->
getr regs 25 = w64 (2 ^ 64 - 2 - bb) -> getr regs 26 = w64 18446744073709551615 -> getr regs 20 = w64 SB ->
SRr trbsegs W (mkCfg (mkst regs (Z_to_bv 64 A_cbb_loop) memc (seg_rom trbsegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 A_cbb_tail) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B CBB_LSTK sp1 [(bb, bb + 256 * q)] lyc Sc W mem0 md0 [] lyc Sc W mem' md' 0 /\
(forall r, In r TCBB_KEPT -> getr regs' r = getr regs r)).
Proof.
induction k as [|k IH]; intros i W regs memc mdc sp1 mem0 md0 lyc Sc bb Lbb bl Lbl q Hk Hi HJ Hbb Hbl Hdisj HLbb HLbl Hq
Hsp Hgp Htp H18 H23 H8 H9 H21 H22 H24 H25 H26 H20; [lia|].
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HLS : CBB_LSTK = 4096) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb Lbb HAR Hbb) as (Hbb16 & Hbb4096 & Hbbceil & Hbbh_ia & Hbbpres & _). pose proof (proj1 Hbbh_ia) as Hbbh.
pose proof (blk_off_img _ _ _ _ _ _ bb Lbb HAR Hbb) as Hbbh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bl Lbl HAR Hbl) as (Hbl16 & Hbl4096 & Hblceil & Hblh_ia & Hblpres & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_img _ _ _ _ _ _ bl Lbl HAR Hbl) as Hblh_img.
assert (Hrb : req_size Lbb = Lbb) by (unfold req_size; destruct (Z.eqb_spec Lbb 0); lia).
assert (Hrl : req_size Lbl = Lbl) by (unfold req_size; destruct (Z.eqb_spec Lbl 0); lia).
rewrite Hrb, Hrl in *.
remember (Ereg regs [Z_to_bv 64 (bb + 256 * i); Z_to_bv 64 (bl + 255 * i)]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (bb + 256 * i); Z_to_bv 64 (bl + 255 * i)]) E) by (rewrite HE; split; [intros n Hn; reflexivity | reflexivity]).
assert (E8 : ew E 8 = Z_to_bv 64 bb) by (subst E; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact H8).
assert (E9 : ew E 9 = Z_to_bv 64 bl) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E18 : ew E 18 = Z_to_bv 64 i) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E23 : ew E 23 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
assert (E21 : ew E 21 = Z_to_bv 64 (2 ^ 64 - 1 - bb)) by (subst E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 (bb + 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E24 : ew E 24 = Z_to_bv 64 (2 ^ 64 - 1 - bl)) by (subst E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E25 : ew E 25 = Z_to_bv 64 (2 ^ 64 - 2 - bb)) by (subst E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E20 : ew E 20 = Z_to_bv 64 SB) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (bb + 256 * i)) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (bl + 255 * i)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = sp1) by (rewrite E2; exact Hsp).
assert (HS : st_ok trbsegs E ss_tcbb_loop
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_cbb_loop) memc (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx, HE. unfold ss_tcbb_loop. apply (entry_st_ok_full trbsegs); rewrite <- ?HE.
- rewrite HE. apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H26].
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, reg_at. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trbsegs). apply Hbbpres. lia.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok, PTR, NOTP, NOTP1. cbn [af_lo af_hi af_al2].
rewrite E8, E9, E18, E23, E21, E24, E25, E22, E32, E33, E20, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
ceil; unfold ASAN_CEIL, SB, kLowShadowBeg, kHighMemBeg. rewrite ?C3 in *. idtac.
repeat match goal with |- _ /\ _ => split end; try lia.
all: match goal with |- ?g => idtac "LOOPFACT" g end; fail.
+ cbn [f_alias alias_ok]. split; [|split; [|split; [|exact I]]].
* apply U_inj. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom _ 8 bb E8), (U_atom _ 18 i E18), (U_atom _ 32 _ E32), U_SLit by lia.
change (zcanon 256) with 256. rewrite (zcanon_id (i * 256)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
* apply U_inj. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom _ 22 (bb + 1) E22), (U_atom _ 18 i E18), (U_atom_off _ 32 _ 1 E32), U_SLit by lia.
change (zcanon 256) with 256. rewrite (zcanon_id (i * 256)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
* apply U_inj. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom _ 9 bl E9), (U_atom _ 18 i E18), (U_atom _ 33 _ E33), U_SLit by lia.
change (zcanon 255) with 255. rewrite (zcanon_id (i * 255)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia. }
clear HE.
assert (HBx : U E BxL = SHADOW_OFF) by (unfold BxL; rewrite (U_atom E 20 SB E20) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok trbsegs BxL [mkSHE 32 1 0] E (mrestrict (w_H W) memc)).
{ constructor; [|constructor].
apply (shent_app_of_block trbsegs B LAWS lyc Sc W memc mdc E BxL 32 (bb + 256 * i) bb Lbb 0 1 _ HAR Hbb HBx);
[rewrite (U_atom E 32 (bb + 256 * i) E32) by lia; reflexivity | lia | lia | rewrite Hrb; lia]. }
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan.
{
rewrite (U_atom E 32 (bb + 256 * i) E32) by lia.
eapply (obl_of_block trbsegs B LAWS lyc Sc W memc mdc E BxL _ 1 bb Lbb HAR Hbb HBx); [lia | rewrite Hrb; lia]. }
{ eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 32 (bb + 256 * i));
[reflexivity | rewrite E32; apply unsigned_lit_small; lia | | apply awr_ok_nil].
unfold reg_at. cbn [r_wlo r_whi]. intros a Ha. right. left. split.
- exists (bb, bb + 256 * q). split; [left; reflexivity | cbn; lia].
- exists bb, Lbb. split; [exact Hbb | rewrite Hrb; lia]. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
cbn [ew ewset Nat.eqb] in Ra0, Ra1, Ra2, Rra, Rsp, Rgp, Rtp.
clear HF HFr HG SHOK.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS lyc Sc W _ _ bl Lbl HAR1 Hbl) as (_ & _ & _ & _ & Hblpres1 & _). rewrite Hrl in Hblpres1.
eapply SRr_bind.
{ eapply (aj_intrin_at trbsegs B LAWS Hsegs OCpy A_asan_memcpy AIMC W (ms_regs ms) (ms_mem ms) CBB_LSTK sp1 _ lyc Sc W mem0 md0 [] lyc Sc _ 0
(bb + 1 + 256 * i) (bl + 255 * i) 255 0 (Z_to_bv 64 572324) HJ).
- rewrite Ra0, E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
- rewrite Ra1, E33. reflexivity.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ. rewrite Rsp, Usp. lia.
- reflexivity. - lia. - unfold CBB_LSTK. lia.
- rewrite Rgp, E3. exact Hgp.
- rewrite Rtp, E4. exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split.
+ right. left. split.
* exists (bb, bb + 256 * q). split; [left; reflexivity | cbn; lia].
* exists bb, Lbb. split; [exact Hbb | rewrite Hrb; lia].
+ unfold ESTACK. intros Hx. lia.
- apply (amem_range_of_block trbsegs B LAWS lyc Sc W (ms_mem ms) _ bb Lbb _ _ HAR1 Hbb); [lia | rewrite Hrb; lia].
- apply (range_addressable_of_block trbsegs B LAWS lyc Sc W (ms_mem ms) _ bb Lbb _ _ HAR1 Hbb); [lia | rewrite Hrb; lia].
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS lyc Sc W (ms_mem ms) _ bb Lbb _ _ HAR1 Hbb); [lia | rewrite Hrb; lia | lia].
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ, ESTACK; rewrite Rsp, Usp; intro; lia].
apply (aview_some_of_apresent trbsegs). apply (proj1 (Hblpres1 a ltac:(lia))). }
split; [lia|]. split; [apply (amem_range_of_block trbsegs B LAWS lyc Sc W (ms_mem ms) _ bl Lbl _ _ HAR1 Hbl); [lia | rewrite Hrl; lia]|]. split.
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W (ms_mem ms) _ bl Lbl _ _ HAR1 Hbl); [lia | rewrite Hrl; lia].
+ intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS lyc Sc W (ms_mem ms) _ bl Lbl _ _ HAR1 Hbl); [lia | rewrite Hrl; lia | lia]. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout2 & Hpres2).
jafter_call_keep HS 36%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ 36 _) as Eb eqn:HEb in HS.
assert (OLD : forall n, (n < 34)%nat -> ew Eb n = ew E n).
{ intros n Hn. rewrite HEb, ew_havoc_old by lia. rewrite !ew_ewset_other by lia. reflexivity. }
assert (HAEb : env_agree 32 (Ereg regs [Z_to_bv 64 (bb + 256 * i); Z_to_bv 64 (bl + 255 * i)]) Eb).
{ rewrite HEb. apply env_agree_havoc_ge; [lia|].
eapply env_agree_trans; [exact HAE|]. apply (env_agree_le 34); [lia|].
eapply env_agree_trans; [apply env_agree_ewset|]. apply (env_agree_le 35); [lia|]. apply env_agree_ewset. }
clear HEb.
shok_auto SHOK BxL Eb (mrestrict (w_H W) mem2).
aj_run_tok trbtbl_lib_ok HS HJ2 SHOK Bspan. { awr_ok_tac. }
clear HF HFr HG.
assert (F23 : ew Eb 23 = Z_to_bv 64 q) by (rewrite OLD by lia; exact E23).
assert (F18 : ew Eb 18 = Z_to_bv 64 i) by (rewrite OLD by lia; exact E18).
srr_branch_tok trbtbl_lib_ok HS SHOK Bspan.
-
rewrite branch_ne_U, (U_atom_off _ 18 i 1 F18), (U_atom _ 23 q F23) in Hc by lia.
assert (Hlt : i + 1 < q) by (destruct (Z.eqb_spec (i + 1) q); [discriminate | lia]).
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK Bspan A_cbb_loop. { awr_ok_tac. }
clear HF HFr HG. rename HJ2 into HJ3.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ TCBB_KEPT' HS HAEb ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
rreg HS (18%bv : bv 5) N18. rreg HS (26%bv : bv 5) N26.
rewrite F18, unsigned_lit_small in N18 by lia.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_mono.
{ eapply (IH (i + 1) W _ _ _ sp1 mem0 md0 lyc Sc bb Lbb bl Lbl q);
[ lia | lia | exact HJ3 | exact Hbb | exact Hbl | rewrite Hrb, Hrl; exact Hdisj | exact HLbb | exact HLbl | exact Hq
| unfold spZ; cbn [ms_regs]; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp
| cbn [ms_regs]; rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp
| cbn [ms_regs]; rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| cbn [ms_regs]; rewrite N18; unfold w64; f_equal; lia
| cbn [ms_regs]; rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23
| cbn [ms_regs]; rewrite (HK 8%bv ltac:(cbv; tauto)); exact H8
| cbn [ms_regs]; rewrite (HK 9%bv ltac:(cbv; tauto)); exact H9
| cbn [ms_regs]; rewrite (HK 21%bv ltac:(cbv; tauto)); exact H21
| cbn [ms_regs]; rewrite (HK 22%bv ltac:(cbv; tauto)); exact H22
| cbn [ms_regs]; rewrite (HK 24%bv ltac:(cbv; tauto)); exact H24
| cbn [ms_regs]; rewrite (HK 25%bv ltac:(cbv; tauto)); exact H25
| cbn [ms_regs]; exact N26
| cbn [ms_regs]; rewrite (HK 20%bv ltac:(cbv; tauto)); exact H20 ]. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ4 & HK3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ4|].
intros r Hr. rewrite (HK3 r Hr). cbn [ms_regs]. destruct (tcbb_kept_cases r Hr) as [-> | Hr']; [rewrite N26, H26; reflexivity | exact (HK r Hr')].
-
rewrite branch_ne_U, (U_atom_off _ 18 i 1 F18), (U_atom _ 23 q F23) in Hc by lia.
assert (Heq : i + 1 = q) by (destruct (Z.eqb_spec (i + 1) q); [lia | discriminate]).
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK Bspan A_cbb_tail. { awr_ok_tac. }
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ TCBB_KEPT' HS HAEb ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
rreg HS (26%bv : bv 5) N26.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ2|].
intros r Hr. destruct (tcbb_kept_cases r Hr) as [-> | Hr']; [cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')].
Qed.
Definition A_cbb_test : Z := 0x8bab0.
Definition TCBB_TKEPT : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 27]%bv.
Lemma tcbb_tkept_kept : forall r, In r TCBB_TKEPT -> In r TCBB_KEPT.
Proof. intros r Hr. cbv [TCBB_TKEPT In] in Hr. cbv [TCBB_KEPT In]. intuition (subst; auto 20). Qed.
Lemma alu64_not : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small x) by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite lxor_allones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Definition ss_tcbb_test : sstate :=
mkSS A_cbb_test (sr_set sr_atoms 10%bv (SLit 255)) [] None
(mkFacts [ (8%nat, PTR 4); (9%nat, PTR 4); (19%nat, mkAF 0 (2^28) 0); (23%nat, mkAF 0 (2^21) 0); (20%nat, mkAF SB SB 0);
(21%nat, NOTP); (22%nat, mkAF 4097 (140737479966720 + 1) 0); (24%nat, NOTP) ] [] []).
Lemma tcbb_blocks : forall W regs memc mdc sp1 lyc Sc bb Lbb bl Lbl q n,
ajournal trbsegs B CBB_LSTK sp1 [(bb, bb + 256 * q)] lyc Sc W memc mdc [] lyc Sc W memc mdc 0 ->
In (bb, Lbb) (ablocks B lyc Sc) -> In (bl, Lbl) (ablocks B lyc Sc) ->
(bb + req_size Lbb <= bl \/ bl + req_size Lbl <= bb) ->
256 * q + 1 <= Lbb -> 255 * q <= Lbl -> 255 * q <= n < 255 * q + 255 -> 0 <= n < 2 ^ 28 ->
spZ regs = sp1 -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 19 = w64 n -> getr regs 23 = w64 q -> getr regs 10 = w64 255 ->
getr regs 8 = w64 bb -> getr regs 9 = w64 bl -> getr regs 20 = w64 SB ->
getr regs 21 = w64 (2 ^ 64 - 1 - bb) -> getr regs 22 = w64 (bb + 1) -> getr regs 24 = w64 (2 ^ 64 - 1 - bl) ->
SRr trbsegs W (mkCfg (mkst regs (Z_to_bv 64 A_cbb_test) memc (seg_rom trbsegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 A_cbb_tail) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B CBB_LSTK sp1 [(bb, bb + 256 * q)] lyc Sc W memc mdc [] lyc Sc W mem' md' 0 /\
(forall r, In r TCBB_TKEPT -> getr regs' r = getr regs r)).
Proof.
intros W regs memc mdc sp1 lyc Sc bb Lbb bl Lbl q n HJ Hbb Hbl Hdisj HLbb HLbl Hnq Hn Hsp Hgp Htp H19 H23 H10 H8 H9 H20 H21 H22 H24.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
assert (Hq : 0 <= q < 2 ^ 21) by lia.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb Lbb HAR Hbb) as (Hbb16 & Hbb4096 & Hbbceil & Hbbh_ia & _ & _). pose proof (proj1 Hbbh_ia) as Hbbh.
pose proof (blk_off_img _ _ _ _ _ _ bb Lbb HAR Hbb) as Hbbh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bl Lbl HAR Hbl) as (Hbl16 & Hbl4096 & Hblceil & Hblh_ia & _ & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_img _ _ _ _ _ _ bl Lbl HAR Hbl) as Hblh_img.
pose proof (req_size_pos' Lbb ltac:(lia)) as HrB. pose proof (req_size_pos' Lbl ltac:(lia)) as HrL.
remember (Ereg regs []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros k Hk; reflexivity | reflexivity]).
assert (E8 : ew E 8 = Z_to_bv 64 bb) by (subst E; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact H8).
assert (E9 : ew E 9 = Z_to_bv 64 bl) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E23 : ew E 23 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
assert (E20 : ew E 20 = Z_to_bv 64 SB) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E21 : ew E 21 = Z_to_bv 64 (2 ^ 64 - 1 - bb)) by (subst E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 (bb + 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E24 : ew E 24 = Z_to_bv 64 (2 ^ 64 - 1 - bl)) by (subst E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (HS : st_ok trbsegs E ss_tcbb_test (restrict (w_H W) (mkst regs (Z_to_bv 64 A_cbb_test) memc (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx, HE. unfold ss_tcbb_test. apply (entry_st_ok_full trbsegs); rewrite <- ?HE.
- rewrite HE. apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H10].
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint]. exact I.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok, PTR, NOTP. cbn [af_lo af_hi af_al2].
rewrite E8, E9, E19, E23, E20, E21, E22, E24, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
ceil; unfold ASAN_CEIL, SB, kLowShadowBeg, kHighMemBeg. rewrite ?C3 in *. idtac.
repeat match goal with |- _ /\ _ => split end; try lia.
all: match goal with |- ?g => idtac "TESTFACT" g end; fail. }
clear HE.
shok_auto SHOK BxL E (mrestrict (w_H W) memc).
srr_branch_tok trbtbl_lib_ok HS SHOK Bspan.
-
rewrite branch_geu_U, (U_atom E 19 n E19), U_lit in Hc by lia.
assert (Hq1 : 1 <= q) by (destruct (Z.ltb_spec n 255); [discriminate|lia]).
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK Bspan A_cbb_loop. { awr_ok_tac. }
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ TCBB_TKEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
rreg HS (18%bv : bv 5) L18. rreg HS (25%bv : bv 5) L25. rreg HS (26%bv : bv 5) L26.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_mono.
{ eapply (tcbb_loop (Z.to_nat q) 0 W _ _ _ sp1 memc mdc lyc Sc bb Lbb bl Lbl q);
[ lia | lia | exact HJ | exact Hbb | exact Hbl | exact Hdisj | exact HLbb | exact HLbl | lia
| unfold spZ; cbn [ms_regs]; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp
| cbn [ms_regs]; rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp
| cbn [ms_regs]; rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| cbn [ms_regs]; rewrite L18; reflexivity
| cbn [ms_regs]; rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23
| cbn [ms_regs]; rewrite (HK 8%bv ltac:(cbv; tauto)); exact H8
| cbn [ms_regs]; rewrite (HK 9%bv ltac:(cbv; tauto)); exact H9
| cbn [ms_regs]; rewrite (HK 21%bv ltac:(cbv; tauto)); exact H21
| cbn [ms_regs]; rewrite (HK 22%bv ltac:(cbv; tauto)); exact H22
| cbn [ms_regs]; rewrite (HK 24%bv ltac:(cbv; tauto)); exact H24
| cbn [ms_regs]; rewrite L25, E22, alu64_not by lia; unfold w64; f_equal; lia
| cbn [ms_regs]; rewrite L26; reflexivity
| cbn [ms_regs]; rewrite (HK 20%bv ltac:(cbv; tauto)); exact H20 ]. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
intros r Hr. rewrite (HK3 r (tcbb_tkept_kept r Hr)). cbn [ms_regs]. exact (HK r Hr).
-
rewrite branch_geu_U, (U_atom E 19 n E19), U_lit in Hc by lia.
assert (Hq0 : q = 0) by (destruct (Z.ltb_spec n 255); [lia|discriminate]).
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK Bspan A_cbb_tail. { awr_ok_tac. }
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ TCBB_TKEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ|].
intros r Hr. exact (HK r Hr).
Qed.
Definition Bx : sv := SOff 37 0.
Definition tcbb_facts : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, PTR 4); (11%nat, PTR 4); (12%nat, mkAF 0 (2^28) 0);
(32%nat, mkAF 0 (2^21) 0); (33%nat, mkAF 0 254 0); (34%nat, PTR 0); (35%nat, PTR 0); (36%nat, PTR 0);
(37%nat, mkAF SB SB 0); (38%nat, NOTP); (39%nat, NOTP); (40%nat, NOTP1) ].
Definition tcbb_aliases : list (sv * sv) :=
cbb_aliases ++
[ (SAlu ALU_XOR (SOff 11%nat 0) (SLit (-1)), SOff 38%nat 0);
(SAlu ALU_XOR (SOff 10%nat 0) (SLit (-1)), SOff 39%nat 0);
(SAlu ALU_XOR (SOff 11%nat 1) (SLit (-1)), SOff 40%nat 0) ].
Lemma alias_ok_app : forall E l1 l2, alias_ok E l1 -> alias_ok E l2 -> alias_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[a b] l1 IH]; [exact H2|]. destruct H1 as [Hf H1]. split; [exact Hf | apply IH; exact H1]. Qed.
Definition tcbb_regions : smem := [ stack_region 96; got_region; bcell_region 37; reg_at 34 ].
Definition ss_tcbb : sstate := mkSS A_cbb sr_atoms tcbb_regions None (mkFacts tcbb_facts [] tcbb_aliases).
Definition tcbb_extra (q r bb bl : Z) : list word :=
map (Z_to_bv 64) [q; r; bb + 256 * q; bl + 255 * q; bb + 256 * q + r + 1; SB; 2 ^ 64 - 1 - bb; 2 ^ 64 - 1 - bl; 2 ^ 64 - 2 - bb].
Lemma tcbb_entry : forall W ly S regs mem md ch bl Lbl bb Lbb n q r,
afn_pre trbsegs B CBB_STK ly S W regs mem md ch ->
getr regs 10 = w64 bl -> getr regs 11 = w64 bb -> getr regs 12 = w64 n ->
0 <= n < 2 ^ 28 -> n = 255 * q + r -> 0 <= r < 255 -> 256 * q + r + 1 <= Lbb -> n <= Lbl ->
In (bl, Lbl) (ablocks B ly S) -> In (bb, Lbb) (ablocks B ly S) ->
st_ok trbsegs (Ereg regs (tcbb_extra q r bb bl)) ss_tcbb
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_cbb) mem (seg_rom trbsegs))).
Proof.
intros W ly S regs mem md ch bl Lbl bb Lbb n q r HPRE H10 H11 H12 Hn Hdm Hr HLbb HLbl Hbl Hbb.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HS96 : CBB_STK = 4192) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bb Lbb HAR Hbb) as (Hbb16 & Hbb4096 & Hbbceil & Hbbh_ia & Hbbpres & _). pose proof (proj1 Hbbh_ia) as Hbbh.
pose proof (blk_off_img _ _ _ _ _ _ bb Lbb HAR Hbb) as Hbbh_img.
destruct (al_blocks _ _ LAWS ly S W mem md bl Lbl HAR Hbl) as (Hbl16 & Hbl4096 & Hblceil & Hblh_ia & _ & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_img _ _ _ _ _ _ bl Lbl HAR Hbl) as Hblh_img.
pose proof (req_size_pos' Lbb ltac:(lia)) as HrB. pose proof (req_size_pos' Lbl ltac:(lia)) as HrL.
assert (Hq : 0 <= q < 2 ^ 21) by lia.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Ereg regs (tcbb_extra q r bb bl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 bl) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 bb) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 q) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 r) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (bb + 256 * q)) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (bl + 255 * q)) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (bb + 256 * q + r + 1)) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (2 ^ 64 - 1 - bb)) by (subst E; exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 (2 ^ 64 - 1 - bl)) by (subst E; exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 (2 ^ 64 - 2 - bb)) by (subst E; exact (ew_Ereg_extra regs _ 8)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
unfold ss_tcbb. apply (entry_st_ok_full trbsegs); change (Ereg regs (tcbb_extra q r bb bl)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold tcbb_regions, stack_region, got_region, bcell_region, reg_at.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trbsegs). apply Hpres. lia.
+ cbn [base_val]. unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 668240) at 1.
apply (chunk_ok_val trbsegs E _ 0 668240 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kgot).
+ cbn [base_val]. unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 701048) at 1.
apply (chunk_ok_val trbsegs E _ 0 701048 8 Bx SB);
[cbn [sv_denot Bx]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kcell).
+ rewrite (VB 34%nat (bb + 256 * q) E34) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trbsegs). apply Hbbpres. lia.
- apply pairwise_disjoint_of_extents. unfold tcbb_regions, stack_region, got_region, bcell_region, reg_at, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite (VB 34%nat (bb + 256 * q) E34) by lia. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hbbceil Hbbh Hbbh_img C1 C3 HS96 Hstk0 HLbb Hq Hr HrB. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok tcbb_facts]. unfold afact_ok, PTR, NOTP, NOTP1. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E12, E32, E33, E34, E35, E36, E37, E38, E39, E40, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hbbceil Hbbh Hbbh_img Hbb16 Hblceil Hblh Hblh_img Hbl16 Hal16 C1 C3 HS96 Hstk0 HLbb HLbl Hdm Hq Hr Hn HrB HrL. clear. unfold off_img.
ceil; unfold SB, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat match goal with |- _ /\ _ => split end; try lia.
all: match goal with |- ?g => idtac "ENTRYFACT" g end; fail.
+ cbn [f_alias]. unfold tcbb_aliases. apply alias_ok_app; [eapply (cbb_aliases_ok E n q r bl bb); try eassumption; rewrite ?C1; try lia|].
all: try match goal with |- ?g => idtac "ALIASGOAL" g end.
cbn [alias_ok]. repeat split; apply U_inj.
* rewrite (U_not _ 11 bb E11), (U_atom _ 38 _ E38) by lia. reflexivity.
* rewrite (U_not _ 10 bl E10), (U_atom _ 39 _ E39) by lia. reflexivity.
* rewrite (U_not_off _ 11 bb 1 E11), (U_atom _ 40 _ E40) by lia. lia.
Qed.
Lemma region_kept_at1 : forall E STK1 sp1 FP1 lyc Sc W memc mdc mem2 md2 k1 nn c b m cs,
ajournal trbsegs B STK1 sp1 FP1 lyc Sc W memc mdc [] lyc Sc W mem2 md2 k1 ->
bv_unsigned (ew E nn) = c -> In (b, m) (ablocks B lyc Sc) -> b <= c -> c + 1 <= b + req_size m -> ~ inFP FP1 c ->
region_kept trbsegs E (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) (YQ0b.mkRegion (Some nn) 0 1 0 1 cs).
Proof.
intros E STK1 sp1 FP1 lyc Sc W memc mdc mem2 md2 k1 nn c b m cs HJ Hn Hin Hlo Hhi HnF.
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin) as (_ & _ & _ & _ & Hpres2 & _).
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview trbsegs). replace a with (b + (a - b)) by lia. apply (G2 b m (a - b) Hin Hin); [lia|].
replace (b + (a - b)) with c by lia. exact HnF.
- intros _. apply (apresent_writable trbsegs). apply (proj1 (Hpres2 a ltac:(lia))).
Qed.
Definition cbb_post (regs : bvmap 5 word) ly S (W : world trbsegs) mem md (bb Lbb n : Z) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B CBB_STK (spZ regs) (ablocks_fp [(bb, Lbb)]) ly S W mem md [] ly S W mem' md' 0 /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 (cbb_len n - 1).
Definition TCBB_TCLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 25; 26; 28; 29; 30; 31]%bv.
Lemma tcbb_tclob_kept : forall r : bv 5, reg_in r TCBB_TCLOB = false -> r = 0%bv \/ In r TCBB_TKEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Local Ltac awr_at k v Eq bbv Lbbv Hin :=
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ k v);
[ reflexivity | rewrite Eq; apply unsigned_lit_small; lia
| cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; right; left; split;
[ replace a with (bbv + (a - bbv)) by lia; apply (inFP_ablocks_fp _ bbv Lbbv); [left; reflexivity | lia]
| exists bbv, Lbbv; split; [exact Hin | lia] ]
| ].
Theorem trb_cbb : forall W ly S regs mem md ch bl Lbl bb Lbb n rest,
afn_pre trbsegs B CBB_STK ly S W regs mem md ch ->
getr regs 10 = w64 bl -> getr regs 11 = w64 bb -> getr regs 12 = w64 n ->
0 <= n < 2 ^ 28 -> n <= Lbl -> cbb_len n <= Lbb ->
Permutation (ablocks B ly S) ((bl, Lbl) :: (bb, Lbb) :: rest) ->
SRr trbsegs W (cfg_at trbsegs A_cbb regs mem md) (cbb_post regs ly S W mem md bb Lbb n).
Proof.
intros W ly S regs mem md ch bl Lbl bb Lbb n rest HPRE H10 H11 H12 Hn HLbl HLbb HPerm.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HS96 : CBB_STK = 4192) by reflexivity.
assert (Hbl : In (bl, Lbl) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | left; reflexivity]).
assert (Hbb : In (bb, Lbb) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | right; left; reflexivity]).
pose proof (sep_blocks_perm trbsegs B LAWS ly S W mem md _ _ _ HAR HPerm) as Hdisj. unfold zdisjoint, block_rng in Hdisj. cbn [fst snd] in Hdisj.
pose proof (Z.div_mod n 255 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound n 255 ltac:(lia)) as Hmb.
assert (Hcl : cbb_len n = 256 * (n / 255) + (if n mod 255 =? 0 then 1 else n mod 255 + 2)) by reflexivity.
unfold cbb_post. rewrite Hcl in HLbb |- *. clear Hcl.
set (q := n / 255) in *. set (r := n mod 255) in *. clearbody q r.
assert (Hlen1 : 256 * q + r + 1 <= Lbb) by (destruct (Z.eqb_spec r 0); lia).
destruct (al_blocks _ _ LAWS ly S W mem md bb Lbb HAR Hbb) as (Hbb16 & Hbb4096 & Hbbceil & Hbbh_ia & Hbbpres & _). pose proof (proj1 Hbbh_ia) as Hbbh.
pose proof (blk_off_img _ _ _ _ _ _ bb Lbb HAR Hbb) as Hbbh_img.
destruct (al_blocks _ _ LAWS ly S W mem md bl Lbl HAR Hbl) as (Hbl16 & Hbl4096 & Hblceil & Hblh_ia & _ & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_img _ _ _ _ _ _ bl Lbl HAR Hbl) as Hblh_img.
pose proof (req_size_pos' Lbb ltac:(lia)) as HrB. pose proof (req_size_pos' Lbl ltac:(lia)) as HrL.
pose proof (tcbb_entry W ly S regs mem md ch bl Lbl bb Lbb n q r HPRE H10 H11 H12 Hn ltac:(lia) ltac:(lia) Hlen1 HLbl Hbl Hbb) as HS.
pose proof (ajournal_init trbsegs B CBB_STK (ablocks_fp [(bb, Lbb)]) ly S W regs mem md ch HPRE) as HJ.
remember (Ereg regs (tcbb_extra q r bb bl)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (tcbb_extra q r bb bl)) E) by (rewrite HE; split; [intros k Hk; reflexivity | reflexivity]).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 bl) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 bb) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 q) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 r) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (bb + 256 * q)) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (bl + 255 * q)) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (bb + 256 * q + r + 1)) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (2 ^ 64 - 1 - bb)) by (subst E; exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 (2 ^ 64 - 1 - bl)) by (subst E; exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 (2 ^ 64 - 2 - bb)) by (subst E; exact (ew_Ereg_extra regs _ 8)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
assert (HBx0 : U E Bx = SHADOW_OFF) by (unfold Bx; rewrite (U_atom E 37 SB E37) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok trbsegs Bx [mkSHE 34 1 0] E (mrestrict (w_H W) mem)).
{ constructor; [|constructor].
apply (shent_app_of_block trbsegs B LAWS ly S W mem md E Bx 34 (bb + 256 * q) bb Lbb 0 1 _ HAR Hbb HBx0);
[rewrite (U_atom E 34 (bb + 256 * q) E34) by lia; reflexivity | lia | lia | pose proof HrB; lia]. }
unfold cfg_at. change (w64 A_cbb) with (Z_to_bv 64 A_cbb).
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK Bspan A_cbb_test.
{ awr_ok_tac; [exact Usp | awr_at 34%nat (bb + 256 * q) E34 bb Lbb Hbb; apply awr_ok_nil]. }
clear HF HFr HG.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rreg HS (19%bv : bv 5) T19. rreg HS (23%bv : bv 5) T23. rreg HS (10%bv : bv 5) T10.
rreg HS (8%bv : bv 5) T8. rreg HS (9%bv : bv 5) T9. rreg HS (20%bv : bv 5) T20.
rreg HS (21%bv : bv 5) T21. rreg HS (22%bv : bv 5) T22. rreg HS (24%bv : bv 5) T24.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
pose proof (ajournal_sub_init trbsegs B _ _ _ _ _ _ _ _ _ _ _ W (ms_mem msX) mdX _ CBB_LSTK (spZ regs - 96) [(bb, bb + 256 * q)] (-96)
HJ ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(unfold CBB_LSTK, ESTACK; lia) ltac:(rewrite HS96; unfold CBB_LSTK, ESTACK; lia)) as HJL
end.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ eapply (tcbb_blocks W _ _ _ (spZ regs - 96) ly S bb Lbb bl Lbl q n HJL Hbb Hbl ltac:(lia));
[ lia | lia | lia | lia
| unfold spZ at 1; rewrite Rsp, E2; change (bv_unsigned (getr regs 2)) with (spZ regs); rewrite unsigned_lit_small by lia; reflexivity
| rewrite Rgp, E3; exact Hgp | rewrite Rtp, E4; exact Htp
| rewrite T19, E12; reflexivity | rewrite T23, E32; reflexivity | exact T10
| rewrite T8, E11; reflexivity | rewrite T9, E10; reflexivity | rewrite T20, E37; reflexivity
| rewrite T21, E38; reflexivity | rewrite T22, E11; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | rewrite T24, E39; reflexivity ]. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJL3 & HK3).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
pose proof (ajournal_sub trbsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msX) _ 0 CBB_LSTK (spZ regs - 96) [(bb, bb + 256 * q)] [] ly S W mem3 md3 0
HJ HJL3 ltac:(rewrite HS96; unfold CBB_LSTK, ESTACK; lia) ltac:(lia)) as HJ3
end.
match type of HJ3 with ?P -> _ => assert (HFP : P); [|specialize (HJ3 HFP); clear HFP] end.
{ intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. left. split.
- replace a with (bb + (a - bb)) by lia. apply (inFP_ablocks_fp _ bb Lbb); [left; reflexivity | lia].
- exists bb, Lbb. split; [exact Hbb | lia]. }
cbn [app] in HJ3.
pose proof (proj1 HJ) as HAR1. pose proof (proj1 HJ3) as HAR3.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR1) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
jafter_stretch HS 41%nat regs3 (mrestrict (w_H W) mem3) TCBB_TCLOB A_cbb_tail HS2.
match type of HS2 with ?P -> ?Q -> _ =>
assert (HP : P); [|assert (HQ : Q); [|specialize (HS2 HP HQ); clear HP HQ]] end.
{ intros r0 Hr0. cbn [ms_regs restrict]. destruct (tcbb_tclob_kept r0 Hr0) as [-> | Hin]; [rewrite !getr_zero; reflexivity | exact (HK3 r0 Hin)]. }
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_sub trbsegs B E); [exact HJL3 | exact HJ3 | exact Usp | lia | rewrite HS96; lia | lia | lia | lia].
- apply (region_kept_val trbsegs E _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot1) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot3) | lia].
- apply (region_kept_val trbsegs E _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell1) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell3) | lia].
- eapply (region_kept_at1 E); [exact HJL3 | rewrite E34; apply unsigned_lit_small; lia | exact Hbb | lia | lia |].
intros (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 41 _) as Et eqn:HE2 in HS.
assert (OLD : forall k, (k < 41)%nat -> ew Et k = ew E k) by (intros k Hk; rewrite HE2; apply ew_havoc_old; exact Hk).
assert (HAE2 : env_agree 32 (Ereg regs (tcbb_extra q r bb bl)) Et) by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE2 HJ HJL HJL3 HK3 Rsp Rgp Rtp T19 T23 T10 T8 T9 T20 T21 T22 T24 SHOK. rename HJ3 into HJ.
assert (F34 : ew Et 34 = Z_to_bv 64 (bb + 256 * q)) by (rewrite OLD by lia; exact E34).
assert (F33 : ew Et 33 = Z_to_bv 64 r) by (rewrite OLD by lia; exact E33).
assert (F36 : ew Et 36 = Z_to_bv 64 (bb + 256 * q + r + 1)) by (rewrite OLD by lia; exact E36).
assert (F35 : ew Et 35 = Z_to_bv 64 (bl + 255 * q)) by (rewrite OLD by lia; exact E35).
assert (F32 : ew Et 32 = Z_to_bv 64 q) by (rewrite OLD by lia; exact E32).
assert (F37 : ew Et 37 = Z_to_bv 64 SB) by (rewrite OLD by lia; exact E37).
assert (F1 : ew Et 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
assert (Usp2 : bv_unsigned (ew Et 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
assert (HBx2 : U Et Bx = SHADOW_OFF) by (unfold Bx; rewrite (U_atom Et 37 SB F37) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok trbsegs Bx [mkSHE 34 1 0] Et (mrestrict (w_H W) mem3)).
{ constructor; [|constructor].
apply (shent_app_of_block trbsegs B LAWS ly S W _ _ Et Bx 34 (bb + 256 * q) bb Lbb 0 1 _ (proj1 HJ) Hbb HBx2);
[rewrite (U_atom Et 34 (bb + 256 * q) F34) by lia; reflexivity | lia | lia | pose proof HrB; lia]. }
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan.
{ awr_ok_tac; [exact Usp2 | awr_at 34%nat (bb + 256 * q) F34 bb Lbb Hbb; apply awr_ok_nil]. }
clear HF HFr HG.
srr_branch_tok trbtbl_lib_ok HS SHOK Bspan.
-
rewrite branch_eq_U, (U_atom Et 33 r F33), U_lit in Hc by lia.
assert (Hr0 : r = 0) by (destruct (Z.eqb_spec r 0); [lia|discriminate]).
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan.
{ rewrite (U_atom Et 34 (bb + 256 * q) F34) by lia.
eapply (obl_of_block trbsegs B LAWS ly S W _ _ Et Bx _ 1 bb Lbb (proj1 HJ) Hbb HBx2); lia. }
{ awr_ok_tac; [exact Usp2 | awr_at 34%nat (bb + 256 * q) F34 bb Lbb Hbb; apply awr_ok_nil]. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra.
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists rg, m, d end.
split; [cbn [ms_regs]; rewrite Rra; cbn [ew ewset Nat.eqb]; rewrite F1, Hra; reflexivity|].
split; [|split].
+ cbn [ms_mem]. apply (ajournal_materialize trbsegs B LAWS Hsegs). exact HJ.
+ eapply (aregs_preserved_of_st_ok trbsegs _ _ _ _ regs (tcbb_extra q r bb bl) HS); [|vm_compute; reflexivity].
env_agree_chain HAE2.
+ cbn [ms_regs]. rewrite Ra0. cbn [ew ewset Nat.eqb]. rewrite F32, alu64_sll_lit by lia.
unfold w64. f_equal. rewrite (proj2 (Z.eqb_eq r 0) Hr0). lia.
-
rewrite branch_eq_U, (U_atom Et 33 r F33), U_lit in Hc by lia.
assert (Hr1 : r <> 0) by (destruct (Z.eqb_spec r 0); [discriminate|lia]).
assert (Hlen2 : 256 * q + r + 2 <= Lbb) by (destruct (Z.eqb_spec r 0); lia).
lazymatch type of HS with st_ok _ _ ?ss (restrict _ ?msX) =>
pose proof (ast_ok_add_region trbsegs Et ss (restrict (w_H W) msX) (reg_at 36) HS eq_refl) as HS2
end.
match type of HS2 with ?P -> ?Q -> _ =>
assert (HP : P); [|assert (HQ : Q); [|specialize (HS2 HP HQ); clear HP HQ]] end.
{ unfold region_ok, reg_at. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict].
rewrite F36, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trbsegs).
destruct (al_blocks _ _ LAWS ly S W _ _ bb Lbb (proj1 HJ) Hbb) as (_ & _ & _ & _ & HbbpresT & _). apply HbbpresT. lia. }
{ unfold add_cond. cbn [ss_mem all_disjoint]. unfold extent_disjoint, reg_at.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite F36, F34, Usp2, !unsigned_lit_small by lia.
unfold A_GOT_shadow, A_shadow_glob. repeat split; zone_lia. }
clear HS. unfold add_cond in HS2. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS2. rename HS2 into HS.
lazymatch type of SHOK with sh_ok _ _ _ _ ?MM =>
clear SHOK; assert (SHOK : sh_ok trbsegs Bx [mkSHE 36 1 0; mkSHE 34 1 0] Et MM) end.
{ constructor; [|constructor; [|constructor]].
- apply (shent_app_of_block trbsegs B LAWS ly S W _ _ Et Bx 36 (bb + 256 * q + r + 1) bb Lbb 0 1 _ (proj1 HJ) Hbb HBx2);
[rewrite (U_atom Et 36 (bb + 256 * q + r + 1) F36) by lia; reflexivity | lia | lia | pose proof HrB; lia].
- apply (shent_app_of_block trbsegs B LAWS ly S W _ _ Et Bx 34 (bb + 256 * q) bb Lbb 0 1 _ (proj1 HJ) Hbb HBx2);
[rewrite (U_atom Et 34 (bb + 256 * q) F34) by lia; reflexivity | lia | lia | pose proof HrB; lia]. }
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan.
{ rewrite (U_atom Et 34 (bb + 256 * q) F34) by lia.
eapply (obl_of_block trbsegs B LAWS ly S W _ _ Et Bx _ 1 bb Lbb (proj1 HJ) Hbb HBx2); lia. }
{ awr_ok_tac. awr_at 36%nat (bb + 256 * q + r + 1) F36 bb Lbb Hbb.
awr_ok_tac; [ exact Usp2 | awr_at 34%nat (bb + 256 * q) F34 bb Lbb Hbb; apply awr_ok_nil ]. }
clear HF HFr HG.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
cbn [ew ewset Nat.eqb] in Ra0, Ra1, Ra2, Rra, Rsp, Rgp, Rtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
pose proof (proj1 HJ) as HAR4.
destruct (al_blocks _ _ LAWS ly S W _ _ bl Lbl HAR4 Hbl) as (_ & _ & _ & _ & Hblpres4 & _).
destruct (al_blocks _ _ LAWS ly S W _ _ bb Lbb HAR4 Hbb) as (_ & _ & _ & _ & Hbbpres4 & _).
eapply SRr_bind.
{ eapply (aj_intrin_at trbsegs B LAWS Hsegs OCpy A_asan_memcpy AIMC W _ _ CBB_STK (spZ regs) _ ly S W mem md [] ly S _ 0
(bb + 256 * q + 1) (bl + 255 * q) r (-96) (Z_to_bv 64 572188) HJ).
- rewrite Ra0, F34. unfold w64. rewrite unsigned_lit_small by lia. first [reflexivity | f_equal; lia].
- rewrite Ra1, F35. reflexivity.
- rewrite Ra2, F33. reflexivity.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp, Usp2, unsigned_lit_small by lia. lia.
- reflexivity. - lia. - rewrite HS96. unfold ESTACK. lia.
- rewrite Rgp, OLD, E3 by lia. exact Hgp.
- rewrite Rtp, OLD, E4 by lia. exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split.
+ right. left. split.
* replace a with (bb + (a - bb)) by lia. apply (inFP_ablocks_fp _ bb Lbb); [left; reflexivity | lia].
* exists bb, Lbb. split; [exact Hbb | lia].
+ unfold ESTACK. intros Hx. lia.
- apply (amem_range_of_block trbsegs B LAWS ly S W _ _ bb Lbb _ _ HAR4 Hbb); lia.
- apply (range_addressable_of_block trbsegs B LAWS ly S W _ _ bb Lbb _ _ HAR4 Hbb); lia.
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly S W _ _ bb Lbb _ _ HAR4 Hbb); lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ, ESTACK; rewrite Rsp, Usp2, unsigned_lit_small by lia; intro; lia].
apply (aview_some_of_apresent trbsegs). apply (proj1 (Hblpres4 a ltac:(lia))). }
split; [lia|]. split; [apply (amem_range_of_block trbsegs B LAWS ly S W _ _ bl Lbl _ _ HAR4 Hbl); lia|]. split.
+ apply (range_addressable_of_block trbsegs B LAWS ly S W _ _ bl Lbl _ _ HAR4 Hbl); lia.
+ intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly S W _ _ bl Lbl _ _ HAR4 Hbl); lia. }
cbv beta. intros W5 c5 Hwle5 (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha0' & Heff & Hout5 & Hpres5).
jafter_call_keep HS 62%nat regs5 (mrestrict (w_H W) mem5) HP5 [0; 1]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [|specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5' & _).
repeat apply Forall_cons; [| | apply Forall_nil].
-
split; unfold reg_at; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val];
cbn [ew ewset Nat.eqb]; rewrite F36, unsigned_lit_small by lia; intros a Ha.
+ apply (mbyte_of_aview trbsegs). apply Hout5; [lia | lia | unfold ESTACK; lia].
+ intros _. apply (apresent_writable trbsegs). apply Hpres5. apply (proj1 (Hbbpres4 a ltac:(lia))).
-
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val];
cbn [ew ewset Nat.eqb]; rewrite Usp2; intros a Ha.
+ apply (mbyte_of_aview trbsegs). apply Hout5; [lia | lia | unfold ESTACK; lia].
+ intros _. apply (apresent_writable trbsegs). apply Hpres5'. rewrite HS96. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ 62 _) as E5 eqn:HE5 in HS.
assert (OLD5 : forall k, (k < 41)%nat -> ew E5 k = ew Et k).
{ intros k Hk. rewrite HE5, ew_havoc_old by lia. rewrite !ew_ewset_other by lia. reflexivity. }
assert (HAE5 : env_agree 32 (Ereg regs (tcbb_extra q r bb bl)) E5) by (rewrite HE5; env_agree_chain HAE2).
clear HE5.
assert (G36 : ew E5 36 = Z_to_bv 64 (bb + 256 * q + r + 1)) by (rewrite OLD5 by lia; exact F36).
assert (G32 : ew E5 32 = Z_to_bv 64 q) by (rewrite OLD5 by lia; exact F32).
assert (G33 : ew E5 33 = Z_to_bv 64 r) by (rewrite OLD5 by lia; exact F33).
assert (G1 : ew E5 1 = getr regs 1) by (rewrite OLD5 by lia; exact F1).
assert (Usp5 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by lia; exact Usp2).
assert (G37 : ew E5 37 = Z_to_bv 64 SB) by (rewrite OLD5 by lia; exact F37).
assert (HBx5 : U E5 Bx = SHADOW_OFF) by (unfold Bx; rewrite (U_atom E5 37 SB G37) by (unfold SB; lia); reflexivity).
assert (SHOK5 : sh_ok trbsegs Bx [mkSHE 36 1 0] E5 (mrestrict (w_H W) mem5)).
{ constructor; [|constructor].
apply (shent_app_of_block trbsegs B LAWS ly S W _ _ E5 Bx 36 (bb + 256 * q + r + 1) bb Lbb 0 1 _ (proj1 HJ5) Hbb HBx5);
[rewrite (U_atom E5 36 (bb + 256 * q + r + 1) G36) by lia; reflexivity | lia | lia | pose proof HrB; lia]. }
aj_run_tok trbtbl_lib_ok HS HJ5 SHOK5 Bspan.
{ rewrite (U_atom E5 36 (bb + 256 * q + r + 1) G36) by lia.
eapply (obl_of_block trbsegs B LAWS ly S W _ _ E5 Bx _ 1 bb Lbb (proj1 HJ5) Hbb HBx5); lia. }
{ awr_ok_tac. awr_at 36%nat (bb + 256 * q + r + 1) G36 bb Lbb Hbb. awr_ok_tac. exact Usp5. }
rreg HS (10%bv : bv 5) Rb0. rreg HS (1%bv : bv 5) Rra5.
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists rg, m, d end.
split; [cbn [ms_regs]; rewrite Rra5; cbn [ew ewset Nat.eqb]; rewrite G1, Hra; reflexivity|].
split; [|split].
+ cbn [ms_mem]. apply (ajournal_materialize trbsegs B LAWS Hsegs). exact HJ5.
+ eapply (aregs_preserved_of_st_ok trbsegs _ _ _ _ regs (tcbb_extra q r bb bl) HS); [env_agree_chain HAE5 | vm_compute; reflexivity].
+ cbn [ms_regs]. rewrite Rb0. cbn [ew ewset Nat.eqb]. rewrite G32, G33, alu64_sll_lit, !alu64_add_lit by lia.
unfold w64. f_equal. destruct (Z.eqb_spec r 0); lia.
Qed.
End f.
End e.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03 YI07
YI1e YI1i YI0x YI56 YI1h YP14 YI08 YI0c YI0g YI0f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition PC_SL : Z := 0x13cac.
Definition PC_A2 : Z := 0x13cdc.
Definition PC_C  : Z := 0x13cfc.
Definition PC_SB : Z := 0x13d1c.
Definition PC_EX : Z := 0x13d38.
Definition PC_X2 : Z := 0x13d48.
Definition PC_X3 : Z := 0x13d54.
Definition sm_cond (ha bef : Z) : Z := if (ha =? 0) && negb (bef =? 0) then 1 else 0.
Definition sm_notha (ha : Z) : Z := if ha =? 0 then 1 else 0.
Ltac wr_ok_eval :=
lazymatch goal with |- wr_ok ?Ee ?rs ?stk ?spp ?fp ?b0 ?bc => let rs' := eval vm_compute in rs in change (wr_ok Ee rs' stk spp fp b0 bc) end.
Lemma in_bv5_sm : forall (r : reg) (L : list reg), existsb (bv_eqb r) L = true -> In r L.
Proof. intros r L H. apply existsb_exists in H as (r' & Hin & Heq). apply bv_eqb_eq in Heq. subst r'. exact Hin. Qed.
Lemma U_add_smallS : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
U E (SAlu ALU_ADD a b) = x + y.
Proof. intros E a b x y Ha Hb Hx Hy Hxy. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb. apply zcanon_id. unfold M64. lia. Qed.

Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Notation segs := src2segs (only parsing).
Local Notation rom := (seg_rom src2segs) (only parsing).
Lemma getr_of_U_mk : forall E ss (regs : bvmap 5 word) pc mem (rr : reg) v,
st_ok segs E ss (mkst regs pc mem rom) -> U E (sr_get (ss_regs ss) rr) = v -> getr regs rr = Z_to_bv 64 v.
Proof. intros E ss regs pc mem rr v HS HU. exact (getr_of_U segs E ss (mkst regs pc mem rom) rr v HS HU). Qed.
Tactic Notation "jregm" constr(HS) constr(r) "as" ident(Hr) := jreg HS r as Hr; cbn [ms_regs mkst] in Hr.
Definition SL_KEEP : list reg := [2; 3; 4; 8; 18; 19; 20; 21; 22; 24; 25; 27]%bv.
Definition cht_rd : YQ0b.region :=
YQ0b.mkRegion (Some 20%nat) 0 48 0 0 [mkChunk 8 (CVal 8 (SOff 32 0)); mkChunk 16 (CVal 8 (SOff 33 0)); mkChunk 44 (CVal 4 (SOff 34 0))].
Definition slot104_rd : YQ0b.region := YQ0b.mkRegion (Some 2%nat) 104 112 0 0 [mkChunk 104 (CVal 8 (SOff 35 0))].
Lemma ch_regions_ok : forall (regs : bvmap 5 word) mem (sp c hv uv T fmt : Z),
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5136 <= 2 ^ 63 ->
getr regs 20 = Z_to_bv 64 c -> 4096 <= c -> c + 48 <= alloc_ceiling ->
word_mem segs mem (c + 8) hv -> 0 <= hv < 2 ^ 64 -> word_mem segs mem (c + 16) uv -> 0 <= uv < 2 ^ 64 ->
val_mem segs mem (c + 44) 4 T -> 0 <= T < 2 ^ 31 ->
word_mem segs mem (sp + 104) fmt -> 0 <= fmt < 2 ^ 64 ->
let E := Ereg regs (map (Z_to_bv 64) [hv; uv; T; fmt] ++ []) in
Forall (region_ok segs E mem) [cht_rd; slot104_rd] /\ pairwise_disjoint E [cht_rd; slot104_rd] /\
bv_unsigned (ew E 2) = sp /\ bv_unsigned (ew E 20) = c /\
ew E 32 = Z_to_bv 64 hv /\ ew E 33 = Z_to_bv 64 uv /\ ew E 34 = Z_to_bv 64 T /\ ew E 35 = Z_to_bv 64 fmt.
Proof.
intros regs mem sp c hv uv T fmt Hr2 Hsplo Hsphi Hr20 Hc0 Hc1 Vh Hhv Vu Huv VT HT Vf Hfmt E.
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 hv) by (subst E; apply (Ereg_vals regs [hv; uv; T; fmt] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 uv) by (subst E; apply (Ereg_vals regs [hv; uv; T; fmt] [] 1%nat); reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 T) by (subst E; apply (Ereg_vals regs [hv; uv; T; fmt] [] 2%nat); reflexivity).
assert (A35 : ew E 35 = Z_to_bv 64 fmt) by (subst E; apply (Ereg_vals regs [hv; uv; T; fmt] [] 3%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU20 : bv_unsigned (ew E 20) = c) by (rewrite (HE 20%nat 20%bv eq_refl), Hr20; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = hv) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = uv) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = T) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HU35 : bv_unsigned (ew E 35) = fmt) by (rewrite A35; apply unsigned_lit_small; lia).
split; [|split; [|repeat split; assumption]].
- constructor; [|constructor; [|constructor]].
+ unfold region_ok, cht_rd. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Vh].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Vu].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU34; reflexivity | cbn; lia | cbn; lia | exact VT].
+ unfold region_ok, slot104_rd. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU35; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Vf].
- unfold cht_rd, slot104_rd. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU20. repeat split; lia.
Qed.
Definition ss_SLA0 : sstate :=
mkSS PC_SL (sr_set sr_atoms 26%bv (SLit 0)) [ cht_rd; slot104_rd ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (20%nat, mkAF 4096 (2^48) 0); (23%nat, mkAF 0 (2^48) 0); (19%nat, mkAF 0 (2^31) 0); (34%nat, mkAF 0 (2^31 - 1) 0) ] [] []).
Lemma SLA0_stretch : forall (regs : bvmap 5 word) mem (sp fi img c hv uv T fmt : Z),
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5136 <= 2 ^ 63 -> sp mod 16 = 0 ->
getr regs 26 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 fi -> 0 <= fi < 2 ^ 31 ->
getr regs 23 = Z_to_bv 64 img -> 0 <= img < 2 ^ 48 ->
getr regs 20 = Z_to_bv 64 c -> 4096 <= c -> c + 48 <= alloc_ceiling ->
word_mem segs mem (c + 8) hv -> 0 <= hv < 2 ^ 64 -> word_mem segs mem (c + 16) uv -> 0 <= uv < 2 ^ 64 ->
val_mem segs mem (c + 44) 4 T -> 0 <= T < 2 ^ 31 ->
word_mem segs mem (sp + 104) fmt -> 0 <= fmt < 2 ^ 64 ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_SL) mem rom) (mkst regs' (Z_to_bv 64 src2_A_col_hash) mem rom) /\
getr regs' 1 = Z_to_bv 64 PC_C /\ getr regs' 10 = Z_to_bv 64 (img + fi) /\ getr regs' 11 = Z_to_bv 64 hv /\
getr regs' 12 = Z_to_bv 64 uv /\ getr regs' 13 = Z_to_bv 64 T /\ getr regs' 14 = Z_to_bv 64 fmt /\
getr regs' 9 = getr regs 23 /\ getr regs' 23 = Z_to_bv 64 (img + fi) /\ getr regs' 26 = getr regs 26 /\
(forall r : reg, In r SL_KEEP -> getr regs' r = getr regs r).
Proof.
intros regs mem sp fi img c hv uv T fmt Hr2 Hsplo Hsphi Hal16 Hr26 Hr19 Hfi Hr23 Himg Hr20 Hc0 Hc1 Vh Hhv Vu Huv VT HT Vfmt Hfmt.
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (ch_regions_ok regs mem sp c hv uv T fmt Hr2 Hsplo Hsphi Hr20 Hc0 Hc1 Vh Hhv Vu Huv VT HT Vfmt Hfmt) as (HRG & HPD & HU2 & HU20 & A32 & A33 & A34 & A35).
set (E := Ereg regs (map (Z_to_bv 64) [hv; uv; T; fmt] ++ [])) in *.
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU23 : bv_unsigned (ew E 23) = img) by (rewrite (HE 23%nat 23%bv eq_refl), Hr23; apply unsigned_lit_small; lia).
assert (HU19 : bv_unsigned (ew E 19) = fi) by (rewrite (HE 19%nat 19%bv eq_refl), Hr19; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E ss_SLA0 (mkst regs (Z_to_bv 64 PC_SL) mem rom)).
{ unfold ss_SLA0. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 | cbn [sv_denot]; exact Hr26].
- vm_compute. reflexivity.
- exact HRG.
- exact HPD.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU20, HU23, HU19, A34, !unsigned_lit_small by lia. change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia. }
pure_to src2tbl_ok HS src2_A_col_hash.
exists regs0. split; [exact Hms|].
split; [jregm HS (1%bv:reg) as Hq; exact Hq|].
split; [eapply getr_of_U_mk; [exact HS|]; eval_sr_get; rewrite (Z.add_comm img fi); apply (U_add_smallS E _ _ fi img); [apply (U_atom E 19 fi); [rewrite (HE 19%nat 19%bv eq_refl); exact Hr19 | lia] | apply (U_atom E 23 img); [rewrite (HE 23%nat 23%bv eq_refl); exact Hr23 | lia] | lia | lia | lia]|].
split; [jregm HS (11%bv:reg) as Hq; rewrite Hq; exact A32|].
split; [jregm HS (12%bv:reg) as Hq; rewrite Hq; exact A33|].
split; [jregm HS (13%bv:reg) as Hq; rewrite Hq; exact A34|].
split; [jregm HS (14%bv:reg) as Hq; rewrite Hq; exact A35|].
split; [jregm HS (9%bv:reg) as Hq; rewrite Hq; exact (HE 23%nat 23%bv eq_refl)|].
split; [eapply getr_of_U_mk; [exact HS|]; eval_sr_get; rewrite (Z.add_comm img fi); apply (U_add_smallS E _ _ fi img); [apply (U_atom E 19 fi); [rewrite (HE 19%nat 19%bv eq_refl); exact Hr19 | lia] | apply (U_atom E 23 img); [rewrite (HE 23%nat 23%bv eq_refl); exact Hr23 | lia] | lia | lia | lia]|].
split; [jregm HS (26%bv:reg) as Hq; rewrite Hq, Hr26; reflexivity|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ SL_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_SLA1 : sstate :=
mkSS PC_SL (sr_set sr_atoms 26%bv (SLit 1))
[ YQ0b.mkRegion (Some 2%nat) 96 104 0 0 [mkChunk 96 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (23%nat, mkAF 0 (2^48) 0); (19%nat, mkAF 0 (2^31) 0);
(24%nat, mkAF 0 (2^31) 0); (32%nat, mkAF 0 (2^48) 0) ] [] []).
Lemma SLA1_stretch : forall (regs : bvmap 5 word) mem (sp fi bfi img bef : Z),
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5136 <= 2 ^ 63 -> sp mod 16 = 0 ->
getr regs 26 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 fi -> 0 <= fi < 2 ^ 31 ->
getr regs 24 = Z_to_bv 64 bfi -> 0 <= bfi < 2 ^ 31 ->
getr regs 23 = Z_to_bv 64 img -> 0 <= img < 2 ^ 48 ->
word_mem segs mem (sp + 96) bef -> 0 <= bef < 2 ^ 48 ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_SL) mem rom) (mkst regs' (Z_to_bv 64 src2_A_bcmp) mem rom) /\
getr regs' 1 = Z_to_bv 64 PC_A2 /\ getr regs' 10 = Z_to_bv 64 (img + fi) /\ getr regs' 11 = Z_to_bv 64 (bef + bfi) /\
getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 9 = getr regs 23 /\ getr regs' 23 = Z_to_bv 64 (img + fi) /\ getr regs' 26 = getr regs 26 /\
(forall r : reg, In r SL_KEEP -> getr regs' r = getr regs r).
Proof.
intros regs mem sp fi bfi img bef Hr2 Hsplo Hsphi Hal16 Hr26 Hr19 Hfi Hr24 Hbfi Hr23 Himg Vbef Hbef.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs (map (Z_to_bv 64) [bef] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 bef) by (subst E; apply (Ereg_vals regs [bef] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU23 : bv_unsigned (ew E 23) = img) by (rewrite (HE 23%nat 23%bv eq_refl), Hr23; apply unsigned_lit_small; lia).
assert (HU19 : bv_unsigned (ew E 19) = fi) by (rewrite (HE 19%nat 19%bv eq_refl), Hr19; apply unsigned_lit_small; lia).
assert (HU24 : bv_unsigned (ew E 24) = bfi) by (rewrite (HE 24%nat 24%bv eq_refl), Hr24; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = bef) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E ss_SLA1 (mkst regs (Z_to_bv 64 PC_SL) mem rom)).
{ unfold ss_SLA1. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 | cbn [sv_denot]; exact Hr26].
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Vbef].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU23, HU19, HU24, HU32. change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia. }
pure_to src2tbl_ok HS src2_A_bcmp.
exists regs0. split; [exact Hms|].
split; [jregm HS (1%bv:reg) as Hq; exact Hq|].
split; [eapply getr_of_U_mk; [exact HS|]; eval_sr_get; rewrite (Z.add_comm img fi); apply (U_add_smallS E _ _ fi img); [apply (U_atom E 19 fi); [rewrite (HE 19%nat 19%bv eq_refl); exact Hr19 | lia] | apply (U_atom E 23 img); [rewrite (HE 23%nat 23%bv eq_refl); exact Hr23 | lia] | lia | lia | lia]|].
split; [eapply getr_of_U_mk; [exact HS|]; eval_sr_get; rewrite (Z.add_comm bef bfi); apply (U_add_smallS E _ _ bfi bef); [apply (U_atom E 24 bfi); [rewrite (HE 24%nat 24%bv eq_refl); exact Hr24 | lia] | apply (U_atom E 32 bef); [exact A32 | lia] | lia | lia | lia]|].
split; [jregm HS (12%bv:reg) as Hq; exact Hq|].
split; [jregm HS (9%bv:reg) as Hq; rewrite Hq; exact (HE 23%nat 23%bv eq_refl)|].
split; [eapply getr_of_U_mk; [exact HS|]; eval_sr_get; rewrite (Z.add_comm img fi); apply (U_add_smallS E _ _ fi img); [apply (U_atom E 19 fi); [rewrite (HE 19%nat 19%bv eq_refl); exact Hr19 | lia] | apply (U_atom E 23 img); [rewrite (HE 23%nat 23%bv eq_refl); exact Hr23 | lia] | lia | lia | lia]|].
split; [jregm HS (26%bv:reg) as Hq; rewrite Hq, Hr26; reflexivity|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ SL_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition KEEP2 : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition ss_A2z : sstate := mkSS PC_A2 (sr_set sr_atoms 10%bv (SLit 0)) [] None (mkFacts [] [] []).
Lemma A2z_stretch : forall (regs : bvmap 5 word) mem,
getr regs 10 = Z_to_bv 64 0 ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_A2) mem rom) (mkst regs' (Z_to_bv 64 PC_SB) mem rom) /\
getr regs' 11 = getr regs 18 /\ (forall r : reg, In r KEEP2 -> getr regs' r = getr regs r).
Proof.
intros regs mem Hr10.
set (E := Ereg regs []).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HS : st_ok segs E ss_A2z (mkst regs (Z_to_bv 64 PC_A2) mem rom)).
{ unfold ss_A2z. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 | cbn [sv_denot]; exact Hr10].
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. exact I. }
pure_to src2tbl_ok HS PC_SB.
exists regs0. split; [exact Hms|].
split; [jregm HS (11%bv:reg) as Hq; rewrite Hq; exact (HE 18%nat 18%bv eq_refl)|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ KEEP2 HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_A2nz : sstate :=
mkSS PC_A2 sr_atoms [ cht_rd; slot104_rd ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (20%nat, mkAF 4096 (2^48) 0); (34%nat, mkAF 0 (2^31 - 1) 0) ] [mkAC BC_NE (SOff 10%nat 0) (SLit 0)] []).
Lemma A2nz_stretch : forall (regs : bvmap 5 word) mem (sp c hv uv T fmt : Z),
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5136 <= 2 ^ 63 -> sp mod 16 = 0 ->
bv_unsigned (getr regs 10) <> 0 ->
getr regs 20 = Z_to_bv 64 c -> 4096 <= c -> c + 48 <= alloc_ceiling ->
word_mem segs mem (c + 8) hv -> 0 <= hv < 2 ^ 64 -> word_mem segs mem (c + 16) uv -> 0 <= uv < 2 ^ 64 ->
val_mem segs mem (c + 44) 4 T -> 0 <= T < 2 ^ 31 ->
word_mem segs mem (sp + 104) fmt -> 0 <= fmt < 2 ^ 64 ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_A2) mem rom) (mkst regs' (Z_to_bv 64 src2_A_col_hash) mem rom) /\
getr regs' 1 = Z_to_bv 64 PC_C /\ getr regs' 10 = getr regs 23 /\ getr regs' 11 = Z_to_bv 64 hv /\
getr regs' 12 = Z_to_bv 64 uv /\ getr regs' 13 = Z_to_bv 64 T /\ getr regs' 14 = Z_to_bv 64 fmt /\
(forall r : reg, In r KEEP2 -> getr regs' r = getr regs r).
Proof.
intros regs mem sp c hv uv T fmt Hr2 Hsplo Hsphi Hal16 Hnz Hr20 Hc0 Hc1 Vh Hhv Vu Huv VT HT Vfmt Hfmt.
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (ch_regions_ok regs mem sp c hv uv T fmt Hr2 Hsplo Hsphi Hr20 Hc0 Hc1 Vh Hhv Vu Huv VT HT Vfmt Hfmt) as (HRG & HPD & HU2 & HU20 & A32 & A33 & A34 & A35).
set (E := Ereg regs (map (Z_to_bv 64) [hv; uv; T; fmt] ++ [])) in *.
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (bv_unsigned_in_range _ (getr regs 10)) as R10. change (bv_modulus 64) with (2 ^ 64) in R10.
assert (HS : st_ok segs E ss_A2nz (mkst regs (Z_to_bv 64 PC_A2) mem rom)).
{ unfold ss_A2nz. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- exact HRG.
- exact HPD.
- split; [|split; [split; [|exact I] | exact I]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2, HU20, A34, !unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, U_SOff, U_SLit, (HE 10%nat 10%bv eq_refl), Z.add_0_r. rewrite zcanon_id by (unfold M64; lia). change (zcanon 0) with 0.
destruct (Z.eqb_spec (bv_unsigned (getr regs 10)) 0); [lia | reflexivity]. }
pure_to src2tbl_ok HS src2_A_col_hash.
exists regs0. split; [exact Hms|].
split; [jregm HS (1%bv:reg) as Hq; exact Hq|].
split; [jregm HS (10%bv:reg) as Hq; rewrite Hq; exact (HE 23%nat 23%bv eq_refl)|].
split; [jregm HS (11%bv:reg) as Hq; rewrite Hq; exact A32|].
split; [jregm HS (12%bv:reg) as Hq; rewrite Hq; exact A33|].
split; [jregm HS (13%bv:reg) as Hq; rewrite Hq; exact A34|].
split; [jregm HS (14%bv:reg) as Hq; rewrite Hq; exact A35|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ KEEP2 HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_CT : sstate := mkSS PC_C (sr_set sr_atoms 10%bv (SLit (2 ^ 64 - 1))) [] None (mkFacts [] [] []).
Lemma CT_stretch : forall (regs : bvmap 5 word) mem,
getr regs 10 = Z_to_bv 64 (2 ^ 64 - 1) ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_C) mem rom) (mkst regs' (Z_to_bv 64 PC_SB) mem rom) /\
getr regs' 11 = getr regs 18 /\ (forall r : reg, In r KEEP2 -> getr regs' r = getr regs r).
Proof.
intros regs mem Hr10.
set (E := Ereg regs []).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HS : st_ok segs E ss_CT (mkst regs (Z_to_bv 64 PC_C) mem rom)).
{ unfold ss_CT. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 | cbn [sv_denot]; exact Hr10].
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. exact I. }
pure_to src2tbl_ok HS PC_SB.
exists regs0. split; [exact Hms|].
split; [jregm HS (11%bv:reg) as Hq; rewrite Hq; exact (HE 18%nat 18%bv eq_refl)|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ KEEP2 HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ci_alias : list (sv * sv) := [(SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SLL (SOff 10 0) (SLit 2)), SOff 33%nat 0)].
Definition ss_CI : sstate :=
mkSS PC_C sr_atoms
[ YQ0b.mkRegion (Some 20%nat) 32 40 0 0 [mkChunk 32 (CVal 8 (SOff 32 0))];
YQ0b.mkRegion (Some 33%nat) 0 4 0 0 [mkChunk 0 (CVal 4 (SOff 34 0))] ] None
(mkFacts [ (10%nat, mkAF 0 (2^30) 0); (20%nat, mkAF 4096 (2^48) 0);
(32%nat, mkAF 4096 (2^48) 2); (33%nat, mkAF 4096 (2^48) 2); (34%nat, mkAF 0 (2^32 - 1) 0) ] [] ci_alias).
Lemma CI_stretch : forall (regs : bvmap 5 word) mem (h c x v : Z),
getr regs 10 = Z_to_bv 64 h -> 0 <= h < 2 ^ 30 ->
getr regs 20 = Z_to_bv 64 c -> 4096 <= c -> c + 48 <= alloc_ceiling ->
word_mem segs mem (c + 32) x -> 4096 <= x -> x + 4 * h + 4 <= alloc_ceiling -> x mod 4 = 0 ->
val_mem segs mem (x + 4 * h) 4 v -> 0 <= v < 2 ^ 32 -> (c + 48 <= x \/ x + 4 * h + 4 <= c) ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_C) mem rom) (mkst regs' (Z_to_bv 64 PC_SB) mem rom) /\
(forall r : reg, In r KEEP2 -> getr regs' r = getr regs r).
Proof.
intros regs mem h c x v Hr10 Hh Hr20 Hc0 Hc1 Vx Hx0 Hx1 Hx4 Vv Hv Hcx.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs (map (Z_to_bv 64) [x; x + 4 * h; v] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 x) by (subst E; apply (Ereg_vals regs [x; x + 4 * h; v] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 (x + 4 * h)) by (subst E; apply (Ereg_vals regs [x; x + 4 * h; v] [] 1%nat); reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 v) by (subst E; apply (Ereg_vals regs [x; x + 4 * h; v] [] 2%nat); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = h) by (rewrite (HE 10%nat 10%bv eq_refl), Hr10; apply unsigned_lit_small; lia).
assert (HU20 : bv_unsigned (ew E 20) = c) by (rewrite (HE 20%nat 20%bv eq_refl), Hr20; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = x) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = x + 4 * h) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = v) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E ss_CI (mkst regs (Z_to_bv 64 PC_C) mem rom)).
{ unfold ss_CI. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Vx].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU34; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vv].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU20, HU33. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU10, HU20, HU32, HU33, HU34.
change (2 ^ 0) with 1. change (2 ^ 2) with 4. rewrite !Z.mod_1_r.
assert ((x + 4 * h) mod 4 = 0) by (replace (x + 4 * h) with (x + h * 4) by lia; rewrite Z.mod_add; [exact Hx4 | lia]).
repeat split; lia.
+ cbn [f_alias alias_ok ci_alias]. split; [|exact I].
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, HU10, HU32, HU33, !Z.add_0_r.
rewrite (zcanon_id x), (zcanon_id h) by (unfold M64; lia). change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 2) with 4. rewrite (zcanon_id (h * 4)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia. }
pure_to src2tbl_ok HS PC_SB.
exists regs0. split; [exact Hms|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ KEEP2 HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition X1_KEEP : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition ss_X1 : sstate :=
mkSS PC_EX sr_atoms [ YQ0b.mkRegion (Some 20%nat) 24 32 0 0 [mkChunk 24 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (20%nat, mkAF 4096 (2^48) 0) ] [] []).
Lemma X1_stretch : forall (regs : bvmap 5 word) mem (sp c p : Z),
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5136 <= 2 ^ 63 -> sp mod 16 = 0 ->
getr regs 20 = Z_to_bv 64 c -> 4096 <= c -> c + 48 <= alloc_ceiling ->
word_mem segs mem (c + 24) p -> 0 <= p < 2 ^ 64 ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_EX) mem rom) (mkst regs' (Z_to_bv 64 src2_A_memcpy) mem rom) /\
getr regs' 1 = Z_to_bv 64 PC_X2 /\ getr regs' 10 = Z_to_bv 64 (sp + 158) /\ getr regs' 11 = Z_to_bv 64 p /\
getr regs' 12 = Z_to_bv 64 768 /\
(forall r : reg, In r X1_KEEP -> getr regs' r = getr regs r).
Proof.
intros regs mem sp c p Hr2 Hsplo Hsphi Hal16 Hr20 Hc0 Hc1 Vp Hp.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs (map (Z_to_bv 64) [p] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 p) by (subst E; apply (Ereg_vals regs [p] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU20 : bv_unsigned (ew E 20) = c) by (rewrite (HE 20%nat 20%bv eq_refl), Hr20; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = p) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E ss_X1 (mkst regs (Z_to_bv 64 PC_EX) mem rom)).
{ unfold ss_X1. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Vp].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2, HU20.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
pure_to src2tbl_ok HS src2_A_memcpy.
exists regs0. split; [exact Hms|].
split; [jregm HS (1%bv:reg) as Hq; exact Hq|].
split; [jregm HS (10%bv:reg) as Hq; rewrite Hq, HU2; reflexivity|].
split; [jregm HS (11%bv:reg) as Hq; rewrite Hq; exact A32|].
split; [jregm HS (12%bv:reg) as Hq; exact Hq|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ X1_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition X2_KEEP : list reg := [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition ss_X2 : sstate :=
mkSS PC_X2 sr_atoms [ YQ0b.mkRegion (Some 20%nat) 40 44 0 0 [mkChunk 40 (CVal 4 (SOff 32 0))] ] None
(mkFacts [ (20%nat, mkAF 4096 (2^48) 0); (32%nat, mkAF 0 255 0) ] [] []).
Lemma X2_stretch : forall (regs : bvmap 5 word) mem (c cnt : Z),
getr regs 20 = Z_to_bv 64 c -> 4096 <= c -> c + 48 <= alloc_ceiling ->
val_mem segs mem (c + 40) 4 cnt -> 0 <= cnt <= 255 ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_X2) mem rom) (mkst regs' (Z_to_bv 64 src2_A_free_col_hash_table) mem rom) /\
getr regs' 1 = Z_to_bv 64 PC_X3 /\ getr regs' 10 = getr regs 20 /\ getr regs' 9 = Z_to_bv 64 cnt /\
(forall r : reg, In r X2_KEEP -> getr regs' r = getr regs r).
Proof.
intros regs mem c cnt Hr20 Hc0 Hc1 Vc Hcnt.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs (map (Z_to_bv 64) [cnt] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 cnt) by (subst E; apply (Ereg_vals regs [cnt] [] 0%nat); reflexivity).
assert (HU20 : bv_unsigned (ew E 20) = c) by (rewrite (HE 20%nat 20%bv eq_refl), Hr20; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = cnt) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E ss_X2 (mkst regs (Z_to_bv 64 PC_X2) mem rom)).
{ unfold ss_X2. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | exact Vc].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU20, HU32.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
pure_to src2tbl_ok HS src2_A_free_col_hash_table.
exists regs0. split; [exact Hms|].
split; [jregm HS (1%bv:reg) as Hq; exact Hq|].
split; [jregm HS (10%bv:reg) as Hq; rewrite Hq; exact (HE 20%nat 20%bv eq_refl)|].
split; [jregm HS (9%bv:reg) as Hq; rewrite Hq; exact A32|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ X2_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_X3 : sstate :=
mkSS PC_X3 sr_atoms [ YQ0b.mkRegion (Some 2%nat) 48 64 0 0 [mkChunk 48 (CVal 8 (SOff 32 0)); mkChunk 56 (CVal 8 (SOff 33 0))] ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (9%nat, mkAF 0 255 0) ] [] []).
Definition X3_KEEP : list reg := [2; 3; 4; 8; 9]%bv.
Lemma X3_stretch : forall (regs : bvmap 5 word) mem (sp cnt pnew fimg : Z),
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5136 <= 2 ^ 63 -> sp mod 16 = 0 ->
getr regs 9 = Z_to_bv 64 cnt -> 0 <= cnt <= 255 ->
word_mem segs mem (sp + 48) pnew -> 0 <= pnew < 2 ^ 64 -> word_mem segs mem (sp + 56) fimg -> 0 <= fimg < 2 ^ 64 ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 PC_X3) mem rom) (mkst regs' (Z_to_bv 64 0x14480) mem rom) /\
getr regs' 24 = Z_to_bv 64 pnew /\ getr regs' 25 = Z_to_bv 64 fimg /\
(forall r : reg, In r X3_KEEP -> getr regs' r = getr regs r).
Proof.
intros regs mem sp cnt pnew fimg Hr2 Hsplo Hsphi Hal16 Hr9 Hcnt V48 Hpnew V56 Hfimg.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs (map (Z_to_bv 64) [pnew; fimg] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 pnew) by (subst E; apply (Ereg_vals regs [pnew; fimg] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 fimg) by (subst E; apply (Ereg_vals regs [pnew; fimg] [] 1%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = cnt) by (rewrite (HE 9%nat 9%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = pnew) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = fimg) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E ss_X3 (mkst regs (Z_to_bv 64 PC_X3) mem rom)).
{ unfold ss_X3. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V48].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V56].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2, HU9.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia. }
pure_to src2tbl_ok HS 0x14480.
exists regs0. split; [exact Hms|].
split; [jregm HS (24%bv:reg) as Hq; rewrite Hq; exact A32|].
split; [jregm HS (25%bv:reg) as Hq; rewrite Hq; exact A33|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ X3_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Lemma U_cond : forall E n m nv bef, bv_unsigned (ew E n) = nv -> 0 <= nv <= 1 -> bv_unsigned (ew E m) = bef -> 0 <= bef < 2 ^ 64 ->
U E (SAlu ALU_AND (SOff n 0) (SAlu ALU_SLTU (SLit 0) (SOff m 0))) = if (nv =? 1) && negb (bef =? 0) then 1 else 0.
Proof.
intros E n m nv bef Hn Hnv Hm Hbef. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, Hn, Hm, !Z.add_0_r. rewrite (zcanon_id bef), (zcanon_id nv) by (unfold M64; lia). change (zcanon 0) with 0.
assert (Hnv' : nv = 0 \/ nv = 1) by lia. destruct Hnv' as [-> | ->]; destruct (Z.ltb_spec 0 bef), (Z.eqb_spec bef 0); try lia; reflexivity.
Qed.
Definition ss_P : sstate :=
mkSS 0x13c78 sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 56 112 104 112 [mkChunk 56 (CVal 8 (SOff 32 0)); mkChunk 88 (CVal 8 (SOff 33 0)); mkChunk 96 (CVal 8 (SOff 34 0))] ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (22%nat, mkAF 1 (2^31) 0); (9%nat, mkAF 3 4 0); (33%nat, mkAF 0 1 0); (32%nat, mkAF 0 (2^48) 0) ] [] []).
Definition P_KEEP : list reg := [2; 3; 4; 8; 9; 18; 20; 21; 23]%bv.
Section J.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Lemma P_stretch : forall (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (sp ha bef fmt fimg N : Z) Q,
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
sp0 - STK <= sp -> sp + 5136 <= sp0 -> sp mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 9 = Z_to_bv 64 fmt -> getr regs 22 = Z_to_bv 64 N ->
word_mem segs mem (sp + 56) fimg -> word_mem segs mem (sp + 88) (sm_notha ha) -> word_mem segs mem (sp + 96) bef ->
0 <= ha <= 1 -> 0 <= bef < 2 ^ 64 -> 3 <= fmt <= 4 -> 0 <= fimg < 2 ^ 48 -> 1 <= N < 2 ^ 31 ->
(forall regs' mem',
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
word_mem segs mem' (sp + 104) fmt ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp + 104 <= x < sp + 112) -> mbyte segs mem' x = mbyte segs mem x) ->
getr regs' 19 = Z_to_bv 64 0 -> getr regs' 24 = Z_to_bv 64 0 -> getr regs' 26 = Z_to_bv 64 (sm_cond ha bef) ->
getr regs' 25 = Z_to_bv 64 fmt -> getr regs' 22 = Z_to_bv 64 fimg -> getr regs' 27 = Z_to_bv 64 (fimg + N) ->
(forall r : reg, In r P_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (mkst regs' (Z_to_bv 64 PC_SL) mem' rom) md) Q) ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 0x13c78) mem rom) md) Q.
Proof.
intros regs mem STK sp0 FP L A mem0 md0 Lc Ac md sp ha bef fmt fimg N Q HJ Hwlo Hwhi Hal16 Hr2 Hr9 Hr22 V56 V88 V96 Hha Hbef Hfmt Hfimg HN HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (Hnv : 0 <= sm_notha ha <= 1) by (unfold sm_notha; destruct (ha =? 0); lia).
set (E := Ereg regs (map (Z_to_bv 64) [fimg; sm_notha ha; bef] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; apply (Ereg_vals regs [fimg; sm_notha ha; bef] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 (sm_notha ha)) by (subst E; apply (Ereg_vals regs [fimg; sm_notha ha; bef] [] 1%nat); reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 bef) by (subst E; apply (Ereg_vals regs [fimg; sm_notha ha; bef] [] 2%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU22 : bv_unsigned (ew E 22) = N) by (rewrite (HE 22%nat 22%bv eq_refl), Hr22; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = fmt) by (rewrite (HE 9%nat 9%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = fimg) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = sm_notha ha) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = bef) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E ss_P (mkst regs (Z_to_bv 64 0x13c78) mem rom)).
{ unfold ss_P. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V56].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V88].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU34; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V96].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU22, HU9, HU33, HU32. change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia. }
change mem with (ms_mem (mkst regs (Z_to_bv 64 0x13c78) mem rom)) in HJ.
jrun_to LAWS src2tbl_ok HS HJ PC_SL.
{ wr_ok_eval.
eapply (wr_ok_cons_win _ _ _ _ _ _ _ _ 2); [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
lazymatch type of HS with st_ok _ _ ?ssf _ =>
pose proof (st_chunk_val segs E ssf ms 0%nat _ 2%nat 104 8%N (SOff 9 0) sp fmt HS eq_refl eq_refl ltac:(cbn; tauto) HU2
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans (HE 9%nat 9%bv eq_refl) Hr9)) ltac:(cbn; lia) ltac:(cbn; lia)) as M104
end.
change (N.to_nat 8) with 8%nat in M104.
apply HK.
- exact HJ.
- apply val_mem_word_mem. exact M104.
- intros x Hx Hn1. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2; lia). reflexivity.
- jreg HS (19%bv:reg) as Hq; exact Hq.
- jreg HS (24%bv:reg) as Hq; exact Hq.
- eapply (getr_of_U segs); [exact HS|]. eval_sr_get. rewrite (U_cond E 33 34 (sm_notha ha) bef HU33 Hnv HU34 Hbef).
unfold sm_notha, sm_cond. destruct (Z.eqb_spec ha 0); cbn [Z.eqb Pos.eqb andb]; reflexivity.
- jreg HS (25%bv:reg) as Hq. rewrite Hq, (HE 9%nat 9%bv eq_refl). exact Hr9.
- jreg HS (22%bv:reg) as Hq. rewrite Hq. exact A32.
- eapply (getr_of_U segs); [exact HS|]. eval_sr_get. rewrite (Z.add_comm fimg N). apply (U_add_smallS E _ _ N fimg); [apply (U_atom E 22 N); [rewrite (HE 22%nat 22%bv eq_refl); exact Hr22 | lia] | apply (U_atom E 32 fimg); [exact A32 | lia] | lia | lia | lia].
- exact (regs_kept_of_st_ok _ _ _ _ regs _ P_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_SB (c : acond) : sstate :=
mkSS PC_SB sr_atoms
[ YQ0b.mkRegion (Some 22%nat) 0 1 0 1 []; YQ0b.mkRegion (Some 2%nat) 112 120 0 0 [mkChunk 112 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (2%nat, mkAF 4096 (2^63) 4); (22%nat, mkAF 4096 (2^48) 0); (27%nat, mkAF 0 (2^48) 0) ] [c] []).
Definition sb_cond (last : bool) : acond := mkAC (if last then BC_EQ else BC_NE) (SOff 22%nat 1) (SOff 27%nat 0).
Definition SB_KEEP : list reg := [2; 3; 4; 8; 9; 18; 20; 21; 25; 26; 27]%bv.
Lemma SB_stretch : forall (last : bool) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (sp cur lim v112 a24 a19 a25 : Z) Q,
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) cur -> writable_at segs mem cur ->
getr regs 2 = Z_to_bv 64 sp -> alloc_ceiling <= sp -> sp + 5136 <= 2 ^ 63 -> sp mod 16 = 0 ->
getr regs 22 = Z_to_bv 64 cur -> 4096 <= cur -> cur + 1 <= alloc_ceiling -> getr regs 27 = Z_to_bv 64 lim -> 0 <= lim <= alloc_ceiling ->
(if last then cur + 1 = lim else cur + 1 <> lim) ->
word_mem segs mem (sp + 112) v112 -> 0 <= v112 < 2 ^ 64 ->
getr regs 24 = Z_to_bv 64 a24 -> getr regs 19 = Z_to_bv 64 a19 -> getr regs 25 = Z_to_bv 64 a25 ->
(forall regs' mem',
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
(forall x, 0 <= x < 2 ^ 64 -> x <> cur -> mbyte segs mem' x = mbyte segs mem x) ->
getr regs' 22 = Z_to_bv 64 (cur + 1) -> getr regs' 24 = Z_to_bv 64 (a24 + v112) -> getr regs' 19 = Z_to_bv 64 (a19 + a25) ->
getr regs' 23 = getr regs 9 ->
(forall r : reg, In r SB_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (mkst regs' (Z_to_bv 64 (if last then PC_EX else PC_SL)) mem' rom) md) Q) ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 PC_SB) mem rom) md) Q.
Proof.
intros last regs mem STK sp0 FP L A mem0 md0 Lc Ac md sp cur lim v112 a24 a19 a25 Q HJ Hwb Hwa Hr2 Hsplo Hsphi Hal16 Hr22 Hcur0 Hcur1 Hr27 Hlim Hlast V112 Hv112 Hr24 Hr19 Hr25 HK.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs (map (Z_to_bv 64) [v112] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 v112) by (subst E; apply (Ereg_vals regs [v112] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU22 : bv_unsigned (ew E 22) = cur) by (rewrite (HE 22%nat 22%bv eq_refl), Hr22; apply unsigned_lit_small; lia).
assert (HU27 : bv_unsigned (ew E 27) = lim) by (rewrite (HE 27%nat 27%bv eq_refl), Hr27; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = v112) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : st_ok segs E (ss_SB (sb_cond last)) (mkst regs (Z_to_bv 64 PC_SB) mem rom)).
{ unfold ss_SB. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- destruct last; vm_compute; reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU22.
split; [lia|]. split; [lia|]. split; [| apply Forall_nil]. intros o Ho. replace (cur + o) with cur by lia. exact Hwa.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V112].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU22. repeat split; lia.
- split; [|split; [split; [|exact I] | exact I]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2, HU22, HU27.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia.
+ unfold acond_ok, sb_cond. cbn [ac_c ac_a ac_b]. destruct last.
* rewrite branch_eq_U, !U_SOff, HU22, HU27, Z.add_0_r. rewrite !zcanon_id by (unfold M64; lia). apply Z.eqb_eq. exact Hlast.
* rewrite branch_ne_U, !U_SOff, HU22, HU27, Z.add_0_r. rewrite !zcanon_id by (unfold M64; lia). destruct (Z.eqb_spec (cur + 1) lim); [lia | reflexivity]. }
change mem with (ms_mem (mkst regs (Z_to_bv 64 PC_SB) mem rom)) in HJ.
destruct last.
- jrun_to LAWS src2tbl_ok HS HJ PC_EX.
{ wr_ok_eval. eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 22); [reflexivity | exact HU22 | cbn [r_wlo r_whi]; intros x Hx; replace x with cur by lia; exact Hwb |].
apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
apply HK.
+ exact HJ.
+ intros x Hx Hne. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2, ?HU22; lia). reflexivity.
+ jreg HS (22%bv:reg) as Hq. rewrite Hq, HU22. reflexivity.
+ jreg HS (24%bv:reg) as Hq. rewrite Hq. cbn [alu64]. rewrite (HE 24%nat 24%bv eq_refl), Hr24, A32. apply lit_add.
+ jreg HS (19%bv:reg) as Hq. rewrite Hq. cbn [alu64]. rewrite (HE 19%nat 19%bv eq_refl), (HE 25%nat 25%bv eq_refl), Hr19, Hr25. apply lit_add.
+ jreg HS (23%bv:reg) as Hq. rewrite Hq. exact (HE 9%nat 9%bv eq_refl).
+ exact (regs_kept_of_st_ok _ _ _ _ regs _ SB_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
- jrun_to LAWS src2tbl_ok HS HJ PC_SL.
{ wr_ok_eval. eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 22); [reflexivity | exact HU22 | cbn [r_wlo r_whi]; intros x Hx; replace x with cur by lia; exact Hwb |].
apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
apply HK.
+ exact HJ.
+ intros x Hx Hne. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2, ?HU22; lia). reflexivity.
+ jreg HS (22%bv:reg) as Hq. rewrite Hq, HU22. reflexivity.
+ jreg HS (24%bv:reg) as Hq. rewrite Hq. cbn [alu64]. rewrite (HE 24%nat 24%bv eq_refl), Hr24, A32. apply lit_add.
+ jreg HS (19%bv:reg) as Hq. rewrite Hq. cbn [alu64]. rewrite (HE 19%nat 19%bv eq_refl), (HE 25%nat 25%bv eq_refl), Hr19, Hr25. apply lit_add.
+ jreg HS (23%bv:reg) as Hq. rewrite Hq. exact (HE 9%nat 9%bv eq_refl).
+ exact (regs_kept_of_st_ok _ _ _ _ regs _ SB_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
End J.
End d.

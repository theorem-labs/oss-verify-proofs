(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02 YQ07 YQ08 YC03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04 YC06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP14 YI08 YI0c YI0g YI0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC68 YC6e.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition QDS_HEAD : Z := 0x83bc4.
Definition QDS_EXIT : Z := 0x83c14.
Definition QNS_HEAD : Z := 0x840e4.
Definition QNS_EXIT : Z := 0x84108.
Section c.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trasegs).
Variable s1v : Z.
Hypothesis Hs1lo : sp0 - STK <= s1v. Hypothesis Hs1hi : s1v + 384 <= sp0.
Definition qs_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\ frm_zero (@fp_csr fy) /\ getr regs 25 = w64 SB /\ getr regs 9 = w64 s1v.
Lemma qs_stack : forall fy regs mem md, qs_base fy regs mem md -> 2 ^ 46 <= s1v /\ s1v + 384 <= 2 ^ 47.
Proof.
intros fy regs mem md (HJ & _). pose proof asan_consts as (C1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _). lia.
Qed.
Definition qs_Bx : sv := SOff 25 0.
Definition qs_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition qds_mem : smem := [ YQ0b.mkRegion (Some 9%nat) 160 248 0 0 [YQ0b.mkChunk 160 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 240 (CVal 8 (SOff 37 0))] ].
Definition ss_QDS : sstate := mkSS QDS_HEAD sr_atoms qds_mem None
(mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (25%nat, mkAF SB SB 0) ] [] []).
Definition QS_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc : Z) (KS : list (bv 5)) (Q : bvmap 5 word -> Prop) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trasegs)) md' /\
qs_base fy' regs' mem' md' /\ Q regs' /\
(forall r : bv 5, In r KS -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma qs_U_subw : forall E a b x y, U E a = x -> U E b = y -> 0 <= y -> y <= x -> x < 2 ^ 31 -> U E (SAluw ALU_SUB a b) = x - y.
Proof.
intros E a b x y Ha Hb Hy Hyx Hx. rewrite U_SAluw, Ha, Hb. cbn [zalu_raw].
rewrite (Z.mod_small x) by lia. rewrite (Z.mod_small y) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (x - y + 2 ^ 31)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Definition QDS_KEEP : list (bv 5) := [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31]%bv.
Lemma q_di_setup : forall (fy : FPState) (regs : bvmap 5 word) mem md (fmt N Wd root : Z),
qs_base fy regs mem md -> getr regs 10 = w64 fmt -> getr regs 13 = w64 N -> 0 <= root -> root + 50 < 2 ^ 47 -> 0 < Wd -> Wd <= N -> N < 2 ^ 29 -> 0 < fmt < 2 ^ 29 ->
fmt * (Wd + 1) < 2 ^ 60 ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 160) 8 Wd -> val_mem trasegs (mrestrict (w_H W) mem) (s1v + 240) 8 root ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 QDS_HEAD) mem (seg_rom trasegs)) md)
(QS_post fy regs mem QDS_EXIT QDS_KEEP
(fun regs' => getr regs' 16 = w64 0 /\ getr regs' 14 = w64 (fmt * 0) /\ getr regs' 7 = w64 N /\ getr regs' 15 = w64 (Wd - 1) /\ getr regs' 30 = w64 (N - Wd) /\
getr regs' 17 = w64 (fmt * Wd) /\ getr regs' 29 = w64 (fmt * (Wd - 1)) /\ getr regs' 28 = w64 (fmt * (Wd + 1)) /\
getr regs' 11 = w64 (root + 50) /\ getr regs' 5 = Z_to_bv 64 (SB + (root + 50) / 8))).
Proof.
intros fy regs mem md fmt N Wd root HB G10 G13 Hroot0 Hroot47 HWd0 HWdN HN29 Hfmt HfW VWd Vroot.
assert (Hroot : 0 <= root < 2 ^ 64) by lia. assert (HWd : 0 <= Wd < 2 ^ 64) by lia.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (qs_stack fy regs mem md HB) as Rs. pose proof HB as (HJ & Hfrm & G25 & G9).
set (E0 := Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; Wd; root] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; 0; Wd; root] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (U9 : bv_unsigned (ew E0 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (A36 : bv_unsigned (ew E0 36) = Wd) by (pose proof (HV 4%nat Wd eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact HWd).
assert (A37 : bv_unsigned (ew E0 37) = root) by (pose proof (HV 5%nat root eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact Hroot).
assert (HS0 : @st_ok trasegs fy E0 ss_QDS (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 QDS_HEAD) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_QDS. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold qds_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite U9.
split; [clear - Rs; lia|]. split; [clear - Rs; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ apply (chunk_ok_val trasegs E0 _ s1v 160 8 _ Wd); [cbn [sv_denot]; rewrite A36, Z.add_0_r; reflexivity | zside | zside | exact VWd].
+ apply (chunk_ok_val trasegs E0 _ s1v 240 8 _ root); [cbn [sv_denot]; rewrite A37, Z.add_0_r; reflexivity | zside | zside | exact Vroot].
- apply pairwise_disjoint_of_extents. unfold qds_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0. rewrite U9, E25. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Rs. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
pose proof (st_ok_enterF trasegs fy 64 E0 ss_QDS _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
set (E := ew_fregs E0 64 (@fp_regs fy)) in HS.
assert (SHOK : sh_ok trasegs qs_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 QDS_HEAD) mem (seg_rom trasegs))) in HJ, SHOK.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_QDS] in HS.
aj_run_to_tokF tratbl_lib_ok HS HJ SHOK qs_Bspan QDS_EXIT.
{ cbn [ss_mem]. unfold qds_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'. pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
pose proof HAEx as [EA ED].
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
assert (HAE0 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; Wd; root] ++ [])) _)
by (split; [intros j Hj; transitivity (ew E j); [apply EA; lia | apply HEE; lia] | transitivity (ed E); [exact ED | reflexivity]]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ QDS_KEEP HSL HAE0 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
assert (GR : forall (r : bv 5), getr (ms_regs ms) r = sv_denot _ (sr_get (ss_regs _) r)) by (intros r; exact (st_ok_restrict_reg trasegs (w_H W) _ _ ms r HSL)).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HSL eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|].
lazymatch type of HSL with @st_ok _ ?fz _ _ _ => exists fz, (ms_regs ms), (ms_mem ms) end. eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|].
lazymatch type of HSL with st_ok _ ?Ex _ _ => set (EX := Ex) in * end.
assert (EXlow : forall n, (n < 64)%nat -> ew EX n = ew E0 n) by (intros n Hn; unfold EX; transitivity (ew E n); [apply EA; lia | apply HEE; lia]).
assert (EX10 : ew EX 10 = Z_to_bv 64 fmt) by (rewrite EXlow by lia; rewrite (HE0 10%nat 10%bv eq_refl); exact G10).
assert (EX13 : ew EX 13 = Z_to_bv 64 N) by (rewrite EXlow by lia; rewrite (HE0 13%nat 13%bv eq_refl); exact G13).
assert (EX25 : ew EX 25 = Z_to_bv 64 SB) by (rewrite EXlow by lia; exact E25).
assert (EX36 : ew EX 36 = Z_to_bv 64 Wd) by (rewrite EXlow by lia; exact (HV 4%nat Wd eq_refl)).
assert (EX37 : ew EX 37 = Z_to_bv 64 root) by (rewrite EXlow by lia; exact (HV 5%nat root eq_refl)).
assert (HfWn : 0 <= fmt * (Wd - 1) /\ 0 <= fmt * Wd /\ fmt * (Wd - 1) <= fmt * (Wd + 1) /\ fmt * Wd <= fmt * (Wd + 1)) by (clear - Hfmt HWd0; nia).
assert (QMUL : forall a b x y, U EX a = x -> U EX b = y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= x * y < 2 ^ 64 -> U EX (SMd M_MUL a b) = x * y).
{ intros a b x y Ha Hb Hx Hy Hxy. rewrite U_SMd, Ha, Hb. cbn [zmd_raw]. apply zcanon_id. unfold M64. lia. }
split.
{ split; [rewrite (GR (16%bv : bv 5)); reflexivity|].
split; [rewrite (GR (14%bv : bv 5)), Z.mul_0_r; reflexivity|].
split; [rewrite (GR (7%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; apply U_zext32_shifts; [apply (U_atom EX 13 N EX13); clear - HWd0 HWdN HN29; lia | clear - HWd0 HWdN HN29; lia]|].
split; [rewrite (GR (15%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; rewrite (U_atom_off EX 36 Wd (-1) EX36) by (clear - HWd0 HWdN HN29; lia); clear; lia|].
split; [rewrite (GR (30%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; apply U_zext32_shifts; [apply (qs_U_subw EX _ _ N Wd); [apply (U_atom EX 13 N EX13); clear - HWd0 HWdN HN29; lia | apply (U_atom EX 36 Wd EX36); clear - HWd0 HWdN HN29; lia
| clear - HWd0; lia | exact HWdN | clear - HN29; lia] | clear - HWd0 HWdN HN29; lia]|].
split; [rewrite (GR (17%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; apply QMUL; [apply (U_atom EX 10 fmt EX10); clear - Hfmt; lia | apply (U_atom EX 36 Wd EX36); clear - HWd0 HWdN HN29; lia | clear - Hfmt; lia | clear - HWd0 HWdN HN29; lia | clear - HfWn HfW; lia]|].
split; [rewrite (GR (29%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; replace (Wd - 1) with (Wd + -1) by (clear; lia);
apply QMUL; [apply (U_atom EX 10 fmt EX10); clear - Hfmt; lia | apply (U_atom_off EX 36 Wd (-1) EX36); clear - HWd0 HWdN HN29; lia | clear - Hfmt; lia | clear - HWd0 HWdN HN29; lia
| replace (Wd + -1) with (Wd - 1) by (clear; lia); clear - HfWn HfW; lia]|].
split; [rewrite (GR (28%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; apply QMUL; [apply (U_atom EX 10 fmt EX10); clear - Hfmt; lia | apply (U_atom_off EX 36 Wd 1 EX36); clear - HWd0 HWdN HN29; lia | clear - Hfmt; lia | clear - HWd0 HWdN HN29; lia
| clear - HfWn HfW; lia]|].
split; [rewrite (GR (11%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; apply (U_atom_off EX 37 root 50 EX37); clear - Hroot0 Hroot47; lia|].
rewrite (GR (5%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end.
rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_atom_off EX 37 root 50 EX37) by (clear - Hroot0 Hroot47; lia). rewrite (U_atom EX 25 SB EX25) by (unfold SB; clear; lia).
rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (root + 50) / 8) by (apply Z.div_pos; lia). assert ((root + 50) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
rewrite (zcanon_id ((root + 50) / 8)) by (unfold M64; lia).
rewrite (Z.add_comm SB). apply zcanon_id. unfold M64, SB. lia. }
split; [exact HKR|].
split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
intros a Ha. apply (lg_kept_ro _ _ _ _ _ HFr); [|exact Ha].
intros rr Hin. cbn [ss_mem In] in Hin. unfold ss_QDS, qds_mem in Hin. cbn [ss_mem In] in Hin. destruct Hin as [<- | []]. cbn [YQ0b.r_wlo YQ0b.r_whi]. lia.
Qed.
Definition qns_mem : smem := [ YQ0b.mkRegion (Some 9%nat) 240 248 0 0 [YQ0b.mkChunk 240 (CVal 8 (SOff 36 0))] ].
Definition ss_QNS : sstate := mkSS QNS_HEAD sr_atoms qns_mem None
(mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (25%nat, mkAF SB SB 0) ] [] []).
Definition QNS_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma q_nd_setup : forall (fy : FPState) (regs : bvmap 5 word) mem md (N root : Z),
qs_base fy regs mem md -> getr regs 13 = w64 N -> 0 <= root -> root + 50 < 2 ^ 47 -> 0 <= N < 2 ^ 32 ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 240) 8 root ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 QNS_HEAD) mem (seg_rom trasegs)) md)
(QS_post fy regs mem QNS_EXIT QNS_KEEP
(fun regs' => getr regs' 14 = w64 0 /\ getr regs' 15 = w64 N /\ getr regs' 11 = w64 (root + 50) /\
getr regs' 17 = Z_to_bv 64 (SB + (root + 50) / 8) /\ getr regs' 16 = Z_to_bv 64 (Z.land (root + 50) 7))).
Proof.
intros fy regs mem md N root HB G13 Hroot0 Hroot47 HN Vroot.
assert (Hroot : 0 <= root < 2 ^ 64) by lia.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (qs_stack fy regs mem md HB) as Rs. pose proof HB as (HJ & Hfrm & G25 & G9).
set (E0 := Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; root] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; 0; root] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (U9 : bv_unsigned (ew E0 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (A36 : bv_unsigned (ew E0 36) = root) by (pose proof (HV 4%nat root eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact Hroot).
assert (HS0 : @st_ok trasegs fy E0 ss_QNS (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 QNS_HEAD) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_QNS. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold qns_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite U9.
split; [clear - Rs; lia|]. split; [clear - Rs; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ s1v 240 8 _ root); [cbn [sv_denot]; rewrite A36, Z.add_0_r; reflexivity | zside | zside | exact Vroot].
- apply pairwise_disjoint_of_extents. unfold qns_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0. rewrite U9, E25. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Rs. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
pose proof (st_ok_enterF trasegs fy 64 E0 ss_QNS _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
set (E := ew_fregs E0 64 (@fp_regs fy)) in HS.
assert (SHOK : sh_ok trasegs qs_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 QNS_HEAD) mem (seg_rom trasegs))) in HJ, SHOK.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_QNS] in HS.
aj_run_to_tokF tratbl_lib_ok HS HJ SHOK qs_Bspan QNS_EXIT.
{ cbn [ss_mem]. unfold qns_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'. pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
pose proof HAEx as [EA ED].
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
assert (HAE0 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; root] ++ [])) _)
by (split; [intros j Hj; transitivity (ew E j); [apply EA; lia | apply HEE; lia] | transitivity (ed E); [exact ED | reflexivity]]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ QNS_KEEP HSL HAE0 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
assert (GR : forall (r : bv 5), getr (ms_regs ms) r = sv_denot _ (sr_get (ss_regs _) r)) by (intros r; exact (st_ok_restrict_reg trasegs (w_H W) _ _ ms r HSL)).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HSL eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|].
lazymatch type of HSL with @st_ok _ ?fz _ _ _ => exists fz, (ms_regs ms), (ms_mem ms) end. eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|].
lazymatch type of HSL with st_ok _ ?Ex _ _ => set (EX := Ex) in * end.
assert (EXlow : forall n, (n < 64)%nat -> ew EX n = ew E0 n) by (intros n Hn; unfold EX; transitivity (ew E n); [apply EA; lia | apply HEE; lia]).
assert (EX13 : ew EX 13 = Z_to_bv 64 N) by (rewrite EXlow by lia; rewrite (HE0 13%nat 13%bv eq_refl); exact G13).
assert (EX25 : ew EX 25 = Z_to_bv 64 SB) by (rewrite EXlow by lia; exact E25).
assert (EX36 : ew EX 36 = Z_to_bv 64 root) by (rewrite EXlow by lia; exact (HV 4%nat root eq_refl)).
split.
{ split; [rewrite (GR (14%bv : bv 5)); reflexivity|].
split; [rewrite (GR (15%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; apply U_zext32_shifts; [apply (U_atom EX 13 N EX13); clear - HN; lia | exact HN]|].
split; [rewrite (GR (11%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; apply (U_atom_off EX 36 root 50 EX36); clear - Hroot0 Hroot47; lia|].
split.
- rewrite (GR (17%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end.
rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_atom_off EX 36 root 50 EX36) by (clear - Hroot0 Hroot47; lia). rewrite (U_atom EX 25 SB EX25) by (unfold SB; clear; lia).
rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (root + 50) / 8) by (apply Z.div_pos; lia). assert ((root + 50) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
rewrite (zcanon_id ((root + 50) / 8)) by (unfold M64; lia).
rewrite (Z.add_comm SB). apply zcanon_id. unfold M64, SB. lia.
- rewrite (GR (16%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end.
rewrite denot_lit_U. f_equal. rewrite U_and_lit by (clear; lia). rewrite (U_atom_off EX 36 root 50 EX36) by (clear - Hroot0 Hroot47; lia). reflexivity. }
split; [exact HKR|].
split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
intros a Ha. apply (lg_kept_ro _ _ _ _ _ HFr); [|exact Ha].
intros rr Hin. cbn [ss_mem In] in Hin. unfold ss_QNS, qns_mem in Hin. cbn [ss_mem In] in Hin. destruct Hin as [<- | []]. cbn [YQ0b.r_wlo YQ0b.r_whi]. lia.
Qed.
End c.

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
YG00 YG0a YG01 YG0h YG0u YG0d YCcz YCd2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfx YCe9 YCey.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g YI0d YI0f YCi1 YCia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03 YM06 YI0a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCib.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCji YCj9.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCjg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LNB_RET : Z := 0x8472c.
Definition LNB_BR : Z := 0x84780.
Definition LNB_EXIT : Z := 0x84808.
Definition LNBA_KEEP : list (bv 5) := [2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LNBB_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LNBS_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 21; 23; 27; 28; 29; 30; 31]%bv.
Definition LNBC_KEEP : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma lnb_wrap_add : forall E a b x y, U E a = x mod 2 ^ 64 -> U E b = y mod 2 ^ 64 -> sv_denot E (SAlu ALU_ADD a b) = Z_to_bv 64 (x + y).
Proof.
intros E a b x y Ha Hb. apply bv_eq. change (bv_unsigned (sv_denot E (SAlu ALU_ADD a b))) with (U E (SAlu ALU_ADD a b)).
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite <- Zplus_mod. reflexivity.
Qed.
Section c.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trbsegs).
Variables (flt nF s1v : Z).
Hypothesis HinF : In (flt, nF) (ablocks B lyc Sc).
Hypothesis Hs1lo : sp0 - STK <= s1v. Hypothesis Hs1hi : s1v + 416 <= sp0.
Definition lnb_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\ frm_zero (@fp_csr fy) /\ getr regs 27 = w64 SB /\ getr regs 9 = w64 s1v.
Definition lnb_Bx : sv := SOff 27 0.
Definition lnb_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma lnb_stack : forall fy regs mem md, lnb_base fy regs mem md -> 2 ^ 46 <= s1v /\ s1v + 416 <= 2 ^ 47 /\ alloc_ceiling <= s1v.
Proof.
intros fy regs mem md (HJ & _). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1. lia.
Qed.
Local Ltac lnb_sr_get E HAEy n :=
lazymatch goal with |- sv_denot ?Ey (sr_get ?rs ?r) = _ =>
let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v; try rewrite (sv_denot_agree n E Ey v HAEy ltac:(vm_compute; reflexivity)) end.
Local Ltac lnb_rs_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem add_cond In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction;
first [ left; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia
| right; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; repeat split; first [reflexivity | lia] ].
Definition lnba_mem : smem := [ YQ0b.mkRegion (Some 9%nat) 240 248 0 0 [YQ0b.mkChunk 240 (CVal 8 (SOff 36 0))] ].
Definition lnba_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (12%nat, mkAF 0 (2^29) 0); (18%nat, mkAF (2^64 - 1 - 140737479966720) (2^64 - 1 - 4096) 0);
(23%nat, mkAF 4096 140737479966720 4); (27%nat, mkAF SB SB 0) ] [] [].
Definition ss_LNBA : sstate := mkSS LNP_CALL sr_atoms lnba_mem None lnba_facts.
Lemma lnba_rs_ro : forall rr, In rr lnba_mem -> YQ0b.r_whi rr <= YQ0b.r_wlo rr.
Proof. intros rr [<- | []]. cbn. lia. Qed.
Definition LNBA_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (idx root : Z) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 A_get_leave_node_index) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 1 = Z_to_bv 64 LNB_RET /\ getr regs' 10 = w64 root /\ getr regs' 11 = w64 (flt + 4 * idx) /\
(forall r : bv 5, In r LNBA_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma LNBA_run : forall (fy : FPState) (regs : bvmap 5 word) mem md (idx root : Z),
lnb_base fy regs mem md -> 0 <= idx < 2 ^ 29 -> 4 * idx + 12 <= nF -> 0 <= root < 2 ^ 64 ->
getr regs 12 = w64 idx -> getr regs 23 = w64 flt -> getr regs 18 = w64 (2 ^ 64 - 1 - flt) ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 240) 8 root ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_CALL) mem (seg_rom trbsegs)) md) (LNBA_post fy regs mem idx root).
Proof.
intros fy regs mem md idx root HB Hidx Hlen Hroot G12 G23 G18 Vroot.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (lnb_stack fy regs mem md HB) as Rs1. pose proof asan_consts as (C1 & _).
pose proof HB as (HJ & Hfrm & G27 & G9). pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (Qf16 & Qf0 & Qf1 & _ & _ & _ & Hnf0).
pose proof (req_size_pos nF ltac:(lia)) as [_ QnF].
set (E := Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; root] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; 0; root] j = Some x -> ew E (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E; apply Ereg_vals; exact Hj).
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs1; lia).
assert (U12 : bv_unsigned (ew E 12) = idx) by (rewrite (HE0 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; clear - Hidx; lia).
assert (U18 : bv_unsigned (ew E 18) = 2 ^ 64 - 1 - flt) by (rewrite (HE0 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (U23 : bv_unsigned (ew E 23) = flt) by (rewrite (HE0 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (E27 : ew E 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (U36 : bv_unsigned (ew E 36) = root) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact Hroot).
assert (HS : @st_ok trbsegs fy E ss_LNBA (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_CALL) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNBA. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lnba_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U9.
split; [clear - Rs1; lia|]. split; [clear - Rs1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E _ s1v 240 8 _ root); [cbn [sv_denot]; rewrite U36, Z.add_0_r; reflexivity | zside | zside | exact Vroot].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok lnba_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U9, U12, U18, U23, E27. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Rs1 Hidx Hlen Qf0 Qf1 Qf16 QnF C1. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trbsegs lnb_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 37 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LNP_CALL) mem (seg_rom trbsegs))) in HJ, SHOK.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK lnb_Bspan A_get_leave_node_index. { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 37 E Ey) by (env_agree_chain HAE) end.
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; root] ++ [])) Ey) by (destruct HAEy as [EA ED]; split; [intros j Hj; first [reflexivity | rewrite EA by lia; reflexivity] | first [reflexivity | rewrite ED; reflexivity]]) end.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ LNBA_KEEP HS HAE' ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|]. split; [exact HJ|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (1%bv : bv 5) HS); reflexivity|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (10%bv : bv 5) HS);
lnb_sr_get E HAEy 37%nat;
cbn [sv_denot]; rewrite U36, Z.add_0_r; reflexivity|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (11%bv : bv 5) HS);
lnb_sr_get E HAEy 37%nat;
unfold w64; apply lg_denot_of_U; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SAlu; cbn [zalu_raw]; rewrite !U_SOff, U_SLit, U12, U23, !Z.add_0_r;
rewrite (zcanon_id idx), (zcanon_id flt) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia); change (Z.land (zcanon 2) 63) with 2;
rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 2) with 4; rewrite (zcanon_id (idx * 4)) by (unfold M64; clear - Hidx; lia);
rewrite zcanon_id by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia); lia|].
split; [exact HKR|].
split; [intros x Hx; exact (lg_kept_ro _ _ _ _ _ HFr lnba_rs_ro x Hx) | intros x Hx; exact (apresent_grows _ _ _ _ HG Hx)].
Qed.
Definition lnbb_mem : smem := [ YQ0b.mkRegion (Some 9%nat) 312 320 0 0 [YQ0b.mkChunk 312 (CVal 8 (SOff 36 0))] ].
Definition lnbb_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (24%nat, mkAF 4096 140737479966720 0); (27%nat, mkAF SB SB 0); (36%nat, mkAF 4096 140737479966720 0) ]
[ mkAC BC_GEU (SOff 24 0) (SOff 36 0) ] [].
Definition ss_LNBB : sstate := mkSS LNB_RET sr_atoms lnbb_mem None lnbb_facts.
Definition lnbb_SH : list shent := [ mkSHE 24 0 1 ].
Lemma lnbb_rs_ro : forall rr, In rr lnbb_mem -> YQ0b.r_whi rr <= YQ0b.r_wlo rr.
Proof. intros rr [<- | []]. cbn. lia. Qed.
Section d.
Variables (cur pimg pg pn : Z).
Hypothesis HinG : In (pg, pn) (ablocks B lyc Sc). Hypothesis HG0 : pg <= pimg. Hypothesis Hcur0 : pimg <= cur. Hypothesis Hcur1 : cur < pg + pn.
Hypothesis HGW : forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j).
Definition LNBB_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 LNP_STORE) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
(forall r : bv 5, In r LNBB_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma LNBB_run : forall (fy : FPState) (regs : bvmap 5 word) mem md,
lnb_base fy regs mem md -> getr regs 24 = w64 cur -> val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 312) 8 pimg ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNB_RET) mem (seg_rom trbsegs)) md) (LNBB_post fy regs mem).
Proof.
intros fy regs mem md HB G24 Vpi.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (lnb_stack fy regs mem md HB) as Rs1. pose proof asan_consts as (C1 & _).
pose proof HB as (HJ & Hfrm & G27 & G9). pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Qg0 & Qg1 & _ & Hgpres & _ & Hpn0).
pose proof (req_size_pos pn ltac:(lia)) as [_ Qpn].
set (E := Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; pimg] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; 0; pimg] j = Some x -> ew E (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E; apply Ereg_vals; exact Hj).
assert (Rpi : 4096 <= pimg /\ 4096 <= cur /\ cur < 140737479966720 /\ pimg < 140737479966720) by (clear - HG0 Hcur0 Hcur1 Qg0 Qg1 Qpn C1; lia).
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs1; lia).
assert (U24 : bv_unsigned (ew E 24) = cur) by (rewrite (HE0 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; clear - Rpi; lia).
assert (E27 : ew E 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (A36 : bv_unsigned (ew E 36) = pimg) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpi; lia).
assert (HS : @st_ok trbsegs fy E ss_LNBB (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNB_RET) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNBB. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lnbb_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U9.
split; [clear - Rs1; lia|]. split; [clear - Rs1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E _ s1v 312 8 _ pimg); [cbn [sv_denot]; rewrite A36, Z.add_0_r; reflexivity | zside | zside | exact Vpi].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; [split; [|exact I] | exact I]].
+ cbn [f_atoms atoms_ok lnbb_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U9, U24, E27, A36. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Rs1 Rpi. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
+ unfold acond_ok. cbn [ac_c ac_a ac_b]. fold E. rewrite YO3v.branch_geu_U, !U_SOff, U24, A36, !Z.add_0_r.
rewrite !zcanon_id by (unfold M64; clear - Rpi; lia). apply Bool.negb_true_iff, Z.ltb_ge. exact Hcur0. }
assert (SHOK : sh_ok trbsegs lnb_Bx lnbb_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, lnbb_SH. constructor; [|constructor].
apply (shent_ok_of_range trbsegs (w_H W) mem E lnb_Bx 24 cur 1 cur 0 1).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md pg pn _ _ HAR HinG); clear - HG0 Hcur0 Hcur1 Qpn; lia.
+ unfold U, lnb_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U24.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pg pn HAR HinG) as Hgimg.
revert Hy Hia Hgimg HG0 Hcur0 Hcur1 Qpn Qg0 Qg1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
assert (HAE : env_agree 37 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LNB_RET) mem (seg_rom trbsegs))) in HJ, SHOK.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK lnb_Bspan LNP_STORE. { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 37 E Ey) by (env_agree_chain HAE) end.
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; pimg] ++ [])) Ey) by (destruct HAEy as [EA ED]; split; [intros j Hj; first [reflexivity | rewrite EA by lia; reflexivity] | first [reflexivity | rewrite ED; reflexivity]]) end.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ LNBB_KEEP HS HAE' ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|]. split; [exact HJ|].
split; [exact HKR|].
split; [intros x Hx; exact (lg_kept_ro _ _ _ _ _ HFr lnbb_rs_ro x Hx) | intros x Hx; exact (apresent_grows _ _ _ _ HG Hx)].
Qed.
Definition lnbs_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 192 208 0 0 [YQ0b.mkChunk 192 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 200 (CVal 8 (SOff 37 0))];
YQ0b.mkRegion (Some 20%nat) 0 1 0 1 [] ].
Definition lnbs_facts : facts := mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (20%nat, mkAF 4096 140737479966720 0); (27%nat, mkAF SB SB 0) ] [] [].
Definition ss_LNBS : sstate := mkSS LNP_STORE sr_atoms lnbs_mem None lnbs_facts.
Definition lnbs_SH : list shent := [ mkSHE 20 0 1 ].
Lemma lnbs_rs : forall rr, In rr lnbs_mem -> YQ0b.r_whi rr <= YQ0b.r_wlo rr \/ (YQ0b.r_base rr = Some 20%nat /\ 0 <= YQ0b.r_wlo rr /\ YQ0b.r_whi rr <= 1).
Proof. intros rr [<- | [<- | []]]; cbn; first [left; lia | right; repeat split; lia]. Qed.
Definition LNBS_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc cnt s9v s10v fmt bfmt : Z) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 pc) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 20 = w64 (cur + 1) /\ getr regs' 24 = w64 (cur + 1) /\ getr regs' 22 = w64 (cnt - 1) /\
getr regs' 25 = Z_to_bv 64 (s9v + bfmt) /\ getr regs' 26 = Z_to_bv 64 (s10v + fmt) /\
(forall r : bv 5, In r LNBS_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (cur <= a < cur + 1) -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma LNBS_run : forall (fy : FPState) (regs : bvmap 5 word) mem md (cnt s9v s10v fmt bfmt : Z),
lnb_base fy regs mem md -> getr regs 20 = w64 cur -> getr regs 24 = w64 cur -> getr regs 22 = w64 cnt -> 1 <= cnt < 2 ^ 63 ->
getr regs 25 = Z_to_bv 64 s9v -> getr regs 26 = Z_to_bv 64 s10v -> 0 <= fmt < 2 ^ 64 -> 0 <= bfmt < 2 ^ 64 ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 192) 8 fmt -> val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 200) 8 bfmt ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_STORE) mem (seg_rom trbsegs)) md)
(LNBS_post fy regs mem (if cnt - 1 =? 0 then LNB_EXIT else LNP_HEAD) cnt s9v s10v fmt bfmt).
Proof.
intros fy regs mem md cnt s9v s10v fmt bfmt HB G20 G24 G22 Hcnt G25 G26 Hfmt Hbfmt Vf Vb.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (lnb_stack fy regs mem md HB) as Rs1. pose proof asan_consts as (C1 & _).
pose proof HB as (HJ & Hfrm & G27 & G9). pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Qg0 & Qg1 & _ & Hgpres & _ & Hpn0).
pose proof (req_size_pos pn ltac:(lia)) as [_ Qpn].
set (E := Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; fmt; bfmt] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; 0; fmt; bfmt] j = Some x -> ew E (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E; apply Ereg_vals; exact Hj).
assert (Rpi : 4096 <= cur /\ cur < 140737479966720) by (clear - HG0 Hcur0 Hcur1 Qg0 Qg1 Qpn C1; lia).
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs1; lia).
assert (U20 : bv_unsigned (ew E 20) = cur) by (rewrite (HE0 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; clear - Rpi; lia).
assert (U24 : bv_unsigned (ew E 24) = cur) by (rewrite (HE0 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; clear - Rpi; lia).
assert (U22 : bv_unsigned (ew E 22) = cnt) by (rewrite (HE0 22%nat 22%bv eq_refl), G22; apply unsigned_lit_small; clear - Hcnt; lia).
assert (U25 : bv_unsigned (ew E 25) = s9v mod 2 ^ 64) by (rewrite (HE0 25%nat 25%bv eq_refl), G25, Z_to_bv_unsigned; reflexivity).
assert (U26 : bv_unsigned (ew E 26) = s10v mod 2 ^ 64) by (rewrite (HE0 26%nat 26%bv eq_refl), G26, Z_to_bv_unsigned; reflexivity).
assert (E27 : ew E 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (A36 : bv_unsigned (ew E 36) = fmt) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact Hfmt).
assert (A37 : bv_unsigned (ew E 37) = bfmt) by (pose proof (HV 5%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact Hbfmt).
assert (DN : forall j x, bv_unsigned (ew E j) = x -> sv_denot E (SOff j 0) = Z_to_bv 64 x) by (intros j x Hj; cbn [sv_denot]; rewrite Hj, Z.add_0_r; reflexivity).
assert (HS : @st_ok trbsegs fy E ss_LNBS (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_STORE) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNBS. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lnbs_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U9.
split; [clear - Rs1; lia|]. split; [clear - Rs1; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trbsegs E _ s1v 192 8 _ fmt); [exact (DN _ _ A36) | zside | zside | exact Vf].
* apply (chunk_ok_val trbsegs E _ s1v 200 8 _ bfmt); [exact (DN _ _ A37) | zside | zside | exact Vb].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U20.
split; [clear - Rpi; lia|]. split; [clear - Rpi; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trbsegs). apply (proj1 (Hgpres (cur + o) ltac:(clear - Ho HG0 Hcur0 Hcur1 Qpn; lia))).
- apply pairwise_disjoint_of_extents. unfold lnbs_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E. rewrite U9, U20.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. clear - Rs1 Rpi C1 HG0 Hcur0 Hcur1 Qg1 Qpn. repeat split; lia.
- split; [|split; exact I].
cbn [f_atoms atoms_ok lnbs_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U9, U20, E27. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Rs1 Rpi. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trbsegs lnb_Bx lnbs_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, lnbs_SH. constructor; [|constructor].
apply (shent_ok_of_range trbsegs (w_H W) mem E lnb_Bx 20 cur 1 cur 0 1).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md pg pn _ _ HAR HinG); clear - HG0 Hcur0 Hcur1 Qpn; lia.
+ unfold U, lnb_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U20.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pg pn HAR HinG) as Hgimg.
revert Hy Hia Hgimg HG0 Hcur0 Hcur1 Qpn Qg0 Qg1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
assert (HAE : env_agree 38 E E) by (apply env_agree_refl).
assert (AWR : forall Ex cs1 cs2, bv_unsigned (ew Ex 20) = cur ->
awr_ok Ex [YQ0b.mkRegion (Some 9%nat) 192 208 0 0 cs1; YQ0b.mkRegion (Some 20%nat) 0 1 0 1 cs2]
STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own).
{ intros Ex cs1 cs2 HUx. apply awr_ok_cons_ro; [cbn; lia|].
eapply awr_ok_cons_gen; [reflexivity | exact HUx | | apply awr_ok_nil].
cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. replace a with (pg + (a - pg)) by lia. apply HGW; [exact HinG | clear - Ha HG0 Hcur0 Hcur1 Qpn; lia]. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LNP_STORE) mem (seg_rom trbsegs))) in HJ, SHOK.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK lnb_Bspan LNB_BR. { cbn [ss_mem]. unfold lnbs_mem. apply AWR. exact U20. }
rename HFr into HFr1; rename HG into HGr1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 38 E Ex) by (env_agree_chain HAE) end.
assert (KW1 : forall x, 0 <= x < 2 ^ 64 -> ~ (cur <= x < cur + 1) -> aview trbsegs (w_H W) (ms_mem msA) x = aview trbsegs (w_H W) mem x).
{ intros x Hx Hnw. apply (lg_kept_win _ _ _ _ _ 20%nat cur 0 1 HFr1); [exact lnbs_rs | exact U20 | exact Hx | clear - Hnw; lia]. }
assert (FIN : forall E' ss' ms' md' pc', @st_ok trbsegs fy E' ss' (restrict (w_H W) ms') -> env_agree 38 E E' ->
ss_pc ss' = pc' -> ss_resv ss' = None ->
sr_get (ss_regs ss') 20 = SOff 20 1 -> sr_get (ss_regs ss') 24 = SOff 24 1 -> sr_get (ss_regs ss') 22 = SOff 22 (-1) ->
(sr_get (ss_regs ss') 25 = SAlu ALU_ADD (SOff 25 0) (SOff 37 0) \/ sr_get (ss_regs ss') 25 = SAlu ALU_ADD (SOff 37 0) (SOff 25 0)) ->
(sr_get (ss_regs ss') 26 = SAlu ALU_ADD (SOff 26 0) (SOff 36 0) \/ sr_get (ss_regs ss') 26 = SAlu ALU_ADD (SOff 36 0) (SOff 26 0)) ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LNBS_KEEP = true ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (cur <= x < cur + 1) -> aview trbsegs (w_H W) (ms_mem ms') x = aview trbsegs (w_H W) mem x) ->
(forall x, apresent (w_H W) mem x -> apresent (w_H W) (ms_mem ms') x) ->
SRr trbsegs W (mkCfg ms' md') (LNBS_post fy regs mem pc' cnt s9v s10v fmt bfmt)).
{ intros E' ss' ms' md' pc' HS' [EA ED] Hpc' Hrv' Q20 Q24 Q22 Q25 Q26 QK HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; fmt; bfmt] ++ [])) E') by (split; [intros j Hj; rewrite EA by lia; reflexivity | rewrite ED; reflexivity]).
pose proof (regs_kept_of_st_ok trbsegs E' ss' _ regs _ LNBS_KEEP HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
assert (UX : forall j x, (j < 38)%nat -> bv_unsigned (ew E j) = x mod 2 ^ 64 -> U E' (SOff j 0) = x mod 2 ^ 64).
{ intros j x Hj Hu. rewrite U_SOff, EA, Hu, Z.add_0_r by exact Hj. unfold zcanon, M64. apply Z.mod_mod. lia. }
rewrite (st_ok_restrict_mkst trbsegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|]. split; [exact HJ'|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (20%bv : bv 5) HS'), Q20; cbn [sv_denot]; rewrite EA, U20 by lia; reflexivity|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (24%bv : bv 5) HS'), Q24; cbn [sv_denot]; rewrite EA, U24 by lia; reflexivity|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (22%bv : bv 5) HS'), Q22; cbn [sv_denot]; rewrite EA, U22 by lia; unfold w64; f_equal; lia|].
split.
{ rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (25%bv : bv 5) HS').
destruct Q25 as [-> | ->]; [ apply lnb_wrap_add | rewrite <- (Z.add_comm bfmt s9v) at 1; replace (s9v + bfmt) with (bfmt + s9v) by lia; apply lnb_wrap_add ];
first [ exact (UX 25%nat s9v ltac:(lia) U25) | apply (UX 37%nat bfmt ltac:(lia)); rewrite A37; symmetry; apply Z.mod_small; exact Hbfmt ]. }
split.
{ rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (26%bv : bv 5) HS').
destruct Q26 as [-> | ->]; [ apply lnb_wrap_add | replace (s10v + fmt) with (fmt + s10v) by lia; apply lnb_wrap_add ];
first [ exact (UX 26%nat s10v ltac:(lia) U26) | apply (UX 36%nat fmt ltac:(lia)); rewrite A36; symmetry; apply Z.mod_small; exact Hfmt ]. }
split; [exact HKR|]. split; [exact Hk' | exact Hp']. }
assert (U22X : forall Ex, env_agree 38 E Ex -> U Ex (SOff 22 (-1)) = cnt - 1).
{ intros Ex [EA _]. rewrite U_SOff, EA, U22 by lia. apply zcanon_id. unfold M64. clear - Hcnt. lia. }
srr_branch_tok trbtbl_lib_ok HS SHOK lnb_Bspan.
- rewrite branch_ne_U, (U22X _ HAEx), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
apply Bool.negb_true_iff in Hc. rewrite Hc.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (U20X : bv_unsigned (ew Ex 20) = cur) by (first [exact U20 | rewrite (proj1 HAEx) by lia; exact U20]) end.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK lnb_Bspan LNP_HEAD. { apply AWR. exact U20X. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 38 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ LNP_HEAD HS HAEy); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | first [left; reflexivity | right; reflexivity]
| first [left; reflexivity | right; reflexivity] | vm_compute; reflexivity | exact HJ | | ].
+ intros x Hx Hnw. rewrite (lg_kept_win _ _ _ _ _ 20%nat cur 0 1 HFr ltac:(lnb_rs_tac) U20X x Hx ltac:(clear - Hnw; lia)). exact (KW1 x Hx Hnw).
+ intros x Hx. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HGr1 Hx).
- rewrite branch_ne_U, (U22X _ HAEx), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
apply Bool.negb_false_iff in Hc. rewrite Hc.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (U20X : bv_unsigned (ew Ex 20) = cur) by (first [exact U20 | rewrite (proj1 HAEx) by lia; exact U20]) end.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK lnb_Bspan LNB_EXIT. { apply AWR. exact U20X. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 38 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ LNB_EXIT HS HAEy); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | first [left; reflexivity | right; reflexivity]
| first [left; reflexivity | right; reflexivity] | vm_compute; reflexivity | exact HJ | | ].
+ intros x Hx Hnw. rewrite (lg_kept_win _ _ _ _ _ 20%nat cur 0 1 HFr ltac:(lnb_rs_tac) U20X x Hx ltac:(clear - Hnw; lia)). exact (KW1 x Hx Hnw).
+ intros x Hx. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HGr1 Hx).
Qed.
End d.
End c.

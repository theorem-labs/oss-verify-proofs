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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCji.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LDG_A : Z := 0x8403c.
Definition LDG_RET : Z := 0x84068.
Definition LDG_KHEAD : Z := 0x840c8.
Definition LDGA_KEEP : list (bv 5) := [2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 19; 21; 22; 23; 24; 25; 27; 28; 29; 30; 31]%bv.
Definition LDGB_KEEP : list (bv 5) := [2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 19; 21; 22; 23; 24; 25; 27; 28; 29]%bv.
Lemma ldg_leaves_nodes : forall t n, In n (tree_leaves t) -> In n (tree_nodes t).
Proof.
induction t as [|m|m l IHl r IHr]; intros n Hn; cbn [tree_leaves tree_nodes] in *; [contradiction | exact Hn |].
right. apply in_or_app. apply in_app_or in Hn as [H|H]; [left; exact (IHl n H) | right; exact (IHr n H)].
Qed.
Section c.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trbsegs).
Variables (s1v flt nF : Z).
Hypothesis HinF : In (flt, nF) (ablocks B lyc Sc).
Hypothesis Hs1lo : sp0 - STK <= s1v. Hypothesis Hs1hi : s1v + 408 <= sp0.
Definition ldg_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\ frm_zero (@fp_csr fy) /\ getr regs 27 = w64 SB /\ getr regs 9 = w64 s1v.
Local Ltac ldg_sr_get E HAEy :=
lazymatch goal with |- sv_denot ?Ey (sr_get ?rs ?r) = _ =>
let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v; try rewrite (sv_denot_agree 37 E Ey v HAEy ltac:(vm_compute; reflexivity)) end.
Local Ltac ldg_sr_get42 E HAEy :=
lazymatch goal with |- sv_denot ?Ey (sr_get ?rs ?r) = _ =>
let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v; try rewrite (sv_denot_agree 42 E Ey v HAEy ltac:(vm_compute; reflexivity)) end.
Definition ldg_Bx : sv := SOff 27 0.
Definition ldg_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma ldg_stack : forall fy regs mem md, ldg_base fy regs mem md -> 2 ^ 46 <= s1v /\ s1v + 408 <= 2 ^ 47 /\ alloc_ceiling <= s1v.
Proof.
intros fy regs mem md (HJ & _). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1. lia.
Qed.
Definition ldga_mem : smem := [ YQ0b.mkRegion (Some 9%nat) 240 248 0 0 [YQ0b.mkChunk 240 (CVal 8 (SOff 36 0))] ].
Definition ldga_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (11%nat, mkAF 0 (2^29) 0); (22%nat, mkAF (2^64 - 1 - 140737479966720) (2^64 - 1 - 4096) 0);
(23%nat, mkAF 4096 140737479966720 4); (27%nat, mkAF SB SB 0) ] [] [].
Definition ss_LDGA : sstate := mkSS LDG_A sr_atoms ldga_mem None ldga_facts.
Lemma ldga_rs_ro : forall rr, In rr ldga_mem -> YQ0b.r_whi rr <= YQ0b.r_wlo rr.
Proof. intros rr [<- | []]. cbn. lia. Qed.
Definition LDGA_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (m root : Z) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 A_get_leave_node_index) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 1 = Z_to_bv 64 LDG_RET /\ getr regs' 10 = w64 root /\ getr regs' 11 = w64 (flt + 4 * m) /\
getr regs' 18 = getr regs 26 /\ getr regs' 26 = getr regs 31 /\ getr regs' 20 = getr regs 1 /\
(forall r : bv 5, In r LDGA_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma LDGA_run : forall (fy : FPState) (regs : bvmap 5 word) mem md (m root : Z),
ldg_base fy regs mem md -> 0 <= m < 2 ^ 29 -> 4 * m + 12 <= nF -> 0 <= root < 2 ^ 64 ->
getr regs 11 = w64 m -> getr regs 23 = w64 flt -> getr regs 22 = w64 (2 ^ 64 - 1 - flt) ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 240) 8 root ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDG_A) mem (seg_rom trbsegs)) md) (LDGA_post fy regs mem m root).
Proof.
intros fy regs mem md m root HB Hm Hlen Hroot G11 G23 G22 Vroot.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (ldg_stack fy regs mem md HB) as Rs1. pose proof asan_consts as (C1 & _).
pose proof HB as (HJ & Hfrm & G27 & G9). pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (Qf16 & Qf0 & Qf1 & _ & _ & _ & Hnf0).
pose proof (req_size_pos nF ltac:(lia)) as [_ QnF].
set (E := Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; root] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; 0; root] j = Some x -> ew E (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E; apply Ereg_vals; exact Hj).
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs1; lia).
assert (U11 : bv_unsigned (ew E 11) = m) by (rewrite (HE0 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; clear - Hm; lia).
assert (U22 : bv_unsigned (ew E 22) = 2 ^ 64 - 1 - flt) by (rewrite (HE0 22%nat 22%bv eq_refl), G22; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hm Hlen; lia).
assert (U23 : bv_unsigned (ew E 23) = flt) by (rewrite (HE0 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hm Hlen; lia).
assert (E27 : ew E 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (U36 : bv_unsigned (ew E 36) = root) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact Hroot).
assert (HS : @st_ok trbsegs fy E ss_LDGA (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDG_A) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDGA. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ldga_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U9.
split; [clear - Rs1; lia|]. split; [clear - Rs1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E _ s1v 240 8 _ root); [cbn [sv_denot]; rewrite U36, Z.add_0_r; reflexivity | zside | zside | exact Vroot].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok ldga_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U9, U11, U22, U23, E27. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Rs1 Hm Hlen Qf0 Qf1 Qf16 QnF C1. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trbsegs ldg_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 37 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LDG_A) mem (seg_rom trbsegs))) in HJ, SHOK.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK ldg_Bspan A_get_leave_node_index. { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 37 E Ey) by (env_agree_chain HAE) end.
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; root] ++ [])) Ey) by (destruct HAEy as [EA ED]; split; [intros j Hj; first [reflexivity | rewrite EA by lia; reflexivity] | first [reflexivity | rewrite ED; reflexivity]]) end.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ LDGA_KEEP HS HAE' ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|]. split; [exact HJ|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (1%bv : bv 5) HS); reflexivity|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (10%bv : bv 5) HS);
ldg_sr_get E HAEy;
cbn [sv_denot]; rewrite U36, Z.add_0_r; reflexivity|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (11%bv : bv 5) HS);
ldg_sr_get E HAEy;
unfold w64; apply lg_denot_of_U; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SAlu; cbn [zalu_raw]; rewrite !U_SOff, U_SLit, U11, U23, !Z.add_0_r;
rewrite (zcanon_id m), (zcanon_id flt) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hm Hlen; lia); change (Z.land (zcanon 2) 63) with 2;
rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 2) with 4; rewrite (zcanon_id (m * 4)) by (unfold M64; clear - Hm; lia);
rewrite zcanon_id by (unfold M64; clear - Qf0 Qf1 QnF C1 Hm Hlen; lia); lia|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (18%bv : bv 5) HS);
ldg_sr_get E HAEy;
cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact (HE0 26%nat 26%bv eq_refl)|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (26%bv : bv 5) HS);
ldg_sr_get E HAEy;
cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact (HE0 31%nat 31%bv eq_refl)|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (20%bv : bv 5) HS);
ldg_sr_get E HAEy;
cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact (HE0 1%nat 1%bv eq_refl)|].
split; [exact HKR|].
split; [intros x Hx; exact (lg_kept_ro _ _ _ _ _ HFr ldga_rs_ro x Hx) | intros x Hx; exact (apresent_grows _ _ _ _ HG Hx)].
Qed.
Definition ldgb_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 192 408 0 0 [YQ0b.mkChunk 192 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 232 (CVal 8 (SOff 37 0)); YQ0b.mkChunk 312 (CVal 8 (SOff 38 0));
YQ0b.mkChunk 376 (CVal 8 (SOff 40 0)); YQ0b.mkChunk 392 (CVal 8 (SOff 41 0)); YQ0b.mkChunk 400 (CVal 8 (SLit 1))];
YQ0b.mkRegion (Some 39%nat) 0 1 0 1 [] ].
Definition ldgb_alias : sv := SAlu ALU_ADD (SOff 25 0) (SOff 38 0).
Definition ldgb_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (10%nat, mkAF 0 255 0); (25%nat, mkAF 0 (2^29) 0); (27%nat, mkAF SB SB 0);
(38%nat, mkAF 4096 140737479966720 0); (39%nat, mkAF 4096 140737479966720 0) ] [ mkAC BC_GEU (SOff 39 0) (SOff 38 0) ] [ (ldgb_alias, SOff 39 0) ].
Definition ss_LDGB : sstate := mkSS LDG_RET sr_atoms ldgb_mem None ldgb_facts.
Definition ldgb_SH : list shent := [ mkSHE 39 0 1 ].
Section B.
Variables (fmt Wd pimg d4 pal pg pn i : Z).
Hypothesis HinG : In (pg, pn) (ablocks B lyc Sc). Hypothesis HG0 : pg <= pimg. Hypothesis HG1 : pimg + i < pg + pn.
Hypothesis Hi : 0 <= i < 2 ^ 29.
Hypothesis Hfmt : 0 <= fmt < 2 ^ 64. Hypothesis HWd : 0 <= Wd < 2 ^ 64. Hypothesis Hd4 : 0 <= d4 < 2 ^ 64. Hypothesis Hpal : 0 <= pal < 2 ^ 64.
Hypothesis HGW : forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j).
Definition ldgb_slots (mem : word -> option byte) : Prop :=
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 192) 8 fmt /\ val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 232) 8 Wd /\
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 312) 8 pimg /\ val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 376) 8 d4 /\
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 392) 8 pal /\ val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 400) 8 1.
Definition ldgb_Q (regs regs' : bvmap 5 word) : Prop :=
getr regs' 1 = getr regs 20 /\ getr regs' 31 = getr regs 26 /\ getr regs' 26 = getr regs 18 /\ getr regs' 15 = getr regs 26 /\
getr regs' 18 = w64 fmt /\ getr regs' 20 = w64 d4 /\ getr regs' 30 = w64 Wd /\ getr regs' 16 = w64 pal /\
getr regs' 11 = w64 (pimg + i) /\ getr regs' 12 = Z_to_bv 64 (SB + (pimg + i) / 8) /\ getr regs' 13 = w64 (i + 1) /\ getr regs' 14 = w64 3.
Definition LDGB_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 LDG_KHEAD) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
ldgb_Q regs regs' /\
(forall r : bv 5, In r LDGB_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i <= a < pimg + i + 1) -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma LDGB_run : forall (fy : FPState) (regs : bvmap 5 word) mem md (cidx : Z),
ldg_base fy regs mem md -> 0 <= cidx < 256 -> getr regs 10 = w64 cidx -> getr regs 25 = w64 i -> ldgb_slots mem ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDG_RET) mem (seg_rom trbsegs)) md) (LDGB_post fy regs mem).
Proof.
intros fy regs mem md cidx HB Hcidx G10 G25 (V192 & V232 & V312 & V376 & V392 & V400).
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (ldg_stack fy regs mem md HB) as Rs1. pose proof asan_consts as (C1 & _).
pose proof HB as (HJ & Hfrm & G27 & G9). pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Qg0 & Qg1 & _ & Hgpres & _ & Hpn0).
pose proof (req_size_pos pn ltac:(lia)) as [_ Qpn].
set (E := Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; fmt; Wd; pimg; pimg + i; d4; pal] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; 0; fmt; Wd; pimg; pimg + i; d4; pal] j = Some x -> ew E (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E; apply Ereg_vals; exact Hj).
assert (Rpi : 4096 <= pimg /\ pimg + i < 140737479966720) by (clear - HG0 HG1 Hi Qg0 Qg1 Qpn C1; lia).
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs1; lia).
assert (U10 : bv_unsigned (ew E 10) = cidx) by (rewrite (HE0 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; clear - Hcidx; lia).
assert (U25 : bv_unsigned (ew E 25) = i) by (rewrite (HE0 25%nat 25%bv eq_refl), G25; apply unsigned_lit_small; clear - Hi; lia).
assert (E27 : ew E 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (U27 : bv_unsigned (ew E 27) = SB) by (rewrite E27; apply unsigned_lit_small; unfold SB; lia).
assert (A36 : bv_unsigned (ew E 36) = fmt) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact Hfmt).
assert (A37 : bv_unsigned (ew E 37) = Wd) by (pose proof (HV 5%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact HWd).
assert (A38 : bv_unsigned (ew E 38) = pimg) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpi Hi; lia).
assert (A39 : bv_unsigned (ew E 39) = pimg + i) by (pose proof (HV 7%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpi Hi; lia).
assert (A40 : bv_unsigned (ew E 40) = d4) by (pose proof (HV 8%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact Hd4).
assert (A41 : bv_unsigned (ew E 41) = pal) by (pose proof (HV 9%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact Hpal).
assert (DN : forall j x, bv_unsigned (ew E j) = x -> sv_denot E (SOff j 0) = Z_to_bv 64 x) by (intros j x Hj; cbn [sv_denot]; rewrite Hj, Z.add_0_r; reflexivity).
assert (HS : @st_ok trbsegs fy E ss_LDGB (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDG_RET) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDGB. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ldgb_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U9.
split; [clear - Rs1; lia|]. split; [clear - Rs1; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trbsegs E _ s1v 192 8 _ fmt); [exact (DN _ _ A36) | zside | zside | exact V192].
* apply (chunk_ok_val trbsegs E _ s1v 232 8 _ Wd); [exact (DN _ _ A37) | zside | zside | exact V232].
* apply (chunk_ok_val trbsegs E _ s1v 312 8 _ pimg); [exact (DN _ _ A38) | zside | zside | exact V312].
* apply (chunk_ok_val trbsegs E _ s1v 376 8 _ d4); [exact (DN _ _ A40) | zside | zside | exact V376].
* apply (chunk_ok_val trbsegs E _ s1v 392 8 _ pal); [exact (DN _ _ A41) | zside | zside | exact V392].
* apply (chunk_ok_val trbsegs E _ s1v 400 8 _ 1); [cbn [sv_denot]; reflexivity | zside | zside | exact V400].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite A39.
split; [clear - Rpi Hi; lia|]. split; [clear - Rpi; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trbsegs). apply (proj1 (Hgpres (pimg + i + o) ltac:(clear - Ho HG0 HG1 Hi Qpn; lia))).
- apply pairwise_disjoint_of_extents. unfold ldgb_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E. rewrite U9, A39.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. clear - Rs1 Rpi C1 HG1 Qg1 Qpn. repeat split; lia.
- split; [|split; [split; [|exact I] | split; [|exact I]]].
+ cbn [f_atoms atoms_ok ldgb_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U9, U10, U25, E27, A38, A39. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Rs1 Hcidx Hi Rpi. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
+ unfold acond_ok. cbn [ac_c ac_a ac_b]. fold E. rewrite YO3v.branch_geu_U, !U_SOff, A38, A39, !Z.add_0_r.
rewrite !zcanon_id by (unfold M64; clear - Rpi Hi; lia). apply Bool.negb_true_iff, Z.ltb_ge. clear - Hi. lia.
+ fold E. unfold ldgb_alias. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U25, A38, A39, !Z.add_0_r.
rewrite (zcanon_id i), (zcanon_id pimg) by (unfold M64; clear - Rpi Hi; lia). f_equal. lia. }
assert (SHOK : sh_ok trbsegs ldg_Bx ldgb_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, ldgb_SH. constructor; [|constructor].
apply (shent_ok_of_range trbsegs (w_H W) mem E ldg_Bx 39 (pimg + i) 1 (pimg + i) 0 1).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md pg pn _ _ HAR HinG); clear - HG0 HG1 Hi Qpn; lia.
+ unfold U, ldg_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A39.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pg pn HAR HinG) as Himg.
revert Hy Hia Himg HG0 HG1 Hi Qpn Qg0 Qg1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
assert (HAE : env_agree 42 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LDG_RET) mem (seg_rom trbsegs))) in HJ, SHOK.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK ldg_Bspan LDG_KHEAD.
{ apply awr_ok_cons_ro; [cbn; lia|]. eapply awr_ok_cons_gen; [reflexivity | exact A39 | | apply awr_ok_nil].
cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. replace a with (pg + (a - pg)) by lia. apply HGW; [exact HinG | clear - Ha HG0 HG1 Hi Qpn; lia]. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 42 E Ey) by (env_agree_chain HAE) end.
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; fmt; Wd; pimg; pimg + i; d4; pal] ++ [])) Ey)
by (destruct HAEy as [EA ED]; split; [intros j Hj; first [reflexivity | rewrite EA by lia; reflexivity] | first [reflexivity | rewrite ED; reflexivity]]) end.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ LDGB_KEEP HS HAE' ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
assert (A39y : forall Ey, env_agree 42 E Ey -> bv_unsigned (ew Ey 39) = pimg + i) by (intros Ey [EA _]; rewrite EA by lia; exact A39).
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|]. split; [exact HJ|].
split.
{ unfold ldgb_Q. repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- getr _ ?r = _ => rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms r HS) end; ldg_sr_get42 E HAEy.
- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (HE0 20%nat 20%bv eq_refl).
- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (HE0 26%nat 26%bv eq_refl).
- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (HE0 18%nat 18%bv eq_refl).
- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (HE0 26%nat 26%bv eq_refl).
- exact (DN _ _ A36).
- exact (DN _ _ A40).
- exact (DN _ _ A37).
- exact (DN _ _ A41).
- exact (DN _ _ A39).
- apply lg_denot_of_U. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, A39, U27, !Z.add_0_r.
rewrite (zcanon_id (pimg + i)), (zcanon_id SB) by (unfold M64, SB; clear - Rpi Hi; lia). change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hq : 0 <= (pimg + i) / 8 <= pimg + i) by (split; [apply Z.div_pos; clear - Rpi Hi; lia | apply Z.div_le_upper_bound; clear - Rpi Hi; lia]).
rewrite (zcanon_id ((pimg + i) / 8)) by (unfold M64; clear - Hq Rpi; lia).
rewrite zcanon_id by (unfold M64, SB; clear - Hq Rpi; lia). lia.
- cbn [sv_denot]. rewrite U25. reflexivity.
- cbn [sv_denot]. reflexivity. }
split; [exact HKR|].
split; [| intros x Hx; exact (apresent_grows _ _ _ _ HG Hx)].
intros x Hx Hnw. apply (lg_kept_win _ _ _ _ _ 39%nat (pimg + i) 0 1 HFr); [| exact (A39y _ HAEy) | exact Hx | clear - Hnw; lia].
intros rr Hin. cbn [ss_mem In] in Hin. repeat (destruct Hin as [<- | Hin]); try contradiction;
first [ left; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia | right; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; repeat split; first [reflexivity | lia] ].
Qed.
End B.
End c.
Definition LDG_KEEP : list (bv 5) := [2; 3; 4; 8; 9; 19; 21; 22; 23; 24; 25; 27]%bv.
Lemma ldg_cs : forall (regs regs' : bvmap 5 word) z, aregs_preserved regs regs' -> acallee_saved z -> forall r : bv 5, bv_unsigned r = z -> getr regs' r = getr regs r.
Proof.
intros regs regs' z HP Hz r Hr. replace r with (Z_to_bv 5 z); [exact (HP z Hz)|].
apply bv_eq. rewrite Z_to_bv_unsigned, <- Hr. unfold bv_wrap. apply Z.mod_small. exact (bv_unsigned_in_range 5 r).
Qed.
Lemma rga_ldi_leaf {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trbsegs B -> (forall fx : FPState, @tglni_spec fx rc B) ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v flt nF fmt Wd pimg d4 pal pg pn i m (t : tree) (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> frm_zero (@fp_csr fy) ->
In (flt, nF) (ablocks B lyc Sc) -> sp0 - STK <= s1v - 16 -> s1v + 408 <= sp0 -> s1v mod 16 = 0 ->
In (pg, pn) (ablocks B lyc Sc) -> pg <= pimg -> pimg + i < pg + pn -> 0 <= i < 2 ^ 29 ->
0 <= fmt < 2 ^ 64 -> 0 <= Wd < 2 ^ 64 -> 0 <= d4 < 2 ^ 64 -> 0 <= pal < 2 ^ 64 ->
(forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j)) ->
0 <= m < 2 ^ 29 -> 4 * m + 12 <= nF ->
tree_full t -> tree_forall tnode_wf t -> tree_at trbsegs (mrestrict (w_H W) memc) t -> (forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc)) ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 240) 8 (troot t) -> 0 <= troot t < 2 ^ 64 ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 192) 8 fmt -> val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 232) 8 Wd ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 312) 8 pimg -> val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 376) 8 d4 ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 392) 8 pal -> val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 400) 8 1 ->
getr regs 2 = w64 s1v -> getr regs 9 = w64 s1v -> getr regs 27 = w64 SB -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 11 = w64 m -> getr regs 23 = w64 flt -> getr regs 22 = w64 (2 ^ 64 - 1 - flt) -> getr regs 25 = w64 i ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDG_A) memc (seg_rom trbsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LDG_KHEAD) mem2 (seg_rom trbsegs)) md2 /\
frm_zero (@fp_csr fy') /\
(forall r : bv 5, In r TGLNI_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
getr regs2 1 = getr regs 1 /\ getr regs2 31 = getr regs 31 /\ getr regs2 26 = getr regs 26 /\ getr regs2 15 = getr regs 31 /\
getr regs2 18 = w64 fmt /\ getr regs2 20 = w64 d4 /\ getr regs2 30 = w64 Wd /\ getr regs2 16 = w64 pal /\
getr regs2 11 = w64 (pimg + i) /\ getr regs2 12 = Z_to_bv 64 (SB + (pimg + i) / 8) /\ getr regs2 13 = w64 (i + 1) /\ getr regs2 14 = w64 3 /\
(forall r : bv 5, In r LDG_KEEP -> getr regs2 r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i <= a < pimg + i + 1) -> ~ (s1v - 16 <= a < s1v) -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS TGLNI STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v flt nF fmt Wd pimg d4 pal pg pn i m t fy regs memc mdc
HJ Hfrm HinF Hs1lo Hs1hi Hs16 HinG HG0 HG1 Hi Hfmt HWd Hd4 Hpal HGW Hm Hlen Hfull Hwf Hat Htb V240 Hroot V192 V232 V312 V376 V392 V400
G2 G9 G27 G3 G4 G11 G23 G22 G25.
pose proof asan_consts as (C1 & _).
assert (HB : ldg_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v fy regs memc mdc) by (repeat (split; [assumption|]); assumption).
assert (Rs1 : 2 ^ 46 <= s1v /\ s1v + 408 <= 2 ^ 47 /\ alloc_ceiling <= s1v) by (apply (ldg_stack B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v ltac:(clear - Hs1lo; lia) Hs1hi fy regs memc mdc HB)).
eapply SRr_bind; [exact (LDGA_run B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v flt nF HinF ltac:(clear - Hs1lo; lia) Hs1hi fy regs memc mdc m (troot t) HB Hm Hlen Hroot G11 G23 G22 V240)|].
intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HJ1 & R1 & R10 & R11 & R18 & R26 & R20 & HK1 & HM1 & HX1).
assert (Hat1 : tree_at trbsegs (mrestrict (w_H W) mem1) t).
{ apply (tree_at_frame trbsegs _ _ t Hat). intros n a Hn Ha. apply (mbyte_of_aview trbsegs). apply HM1.
pose proof HJ as (HAR & _). assert (Hnb : In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc)) by (apply Htb; rewrite tree_blocks_nodes; apply in_map_iff; exists n; auto).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hnb) as (_ & Q0 & Q1 & _). pose proof (req_size_pos NODE_SIZE ltac:(unfold NODE_SIZE; lia)) as [_ Qr].
clear - Ha Q0 Q1 Qr C1. lia. }
assert (Hsp1 : spZ regs1 = s1v) by (unfold spZ; rewrite (HK1 (2%bv : bv 5) ltac:(cbv; tauto)), G2; apply unsigned_lit_small; clear - Rs1; lia).
eapply SRr_bind.
{ eapply (TGLNI fy STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 flt nF (flt + 4 * m) t HJ1).
- rewrite R1. apply ret_ok_even; vm_compute; reflexivity.
- unfold raZ. rewrite R1, unsigned_lit_small by (unfold LDG_RET; clear; lia). unfold LDG_RET. clear. lia.
- rewrite Hsp1. exact Hs16.
- rewrite Hsp1. unfold TGLNI_STK. exact Hs1lo.
- rewrite Hsp1. clear - Hs1hi. lia.
- exact Hfrm.
- exact R10.
- exact R11.
- exact HinF.
- clear - Hm. lia.
- clear - Hlen. lia.
- pose proof HJ as (HAR & _). destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (Qf16 & _).
replace (flt + 4 * m) with (flt + m * 4) by lia. rewrite Z.mod_add by lia.
clear - Qf16. pose proof (Z.div_mod flt 16 ltac:(lia)). replace flt with (4 * (4 * (flt / 16))) by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
- exact Hfull.
- exact Hwf.
- exact Hat1.
- exact Htb. }
cbv beta. intros W2 c2 _ (-> & fy2 & regs2 & mem2 & md2 & -> & Hfrm2 & HF2 & HJ2 & HP2 & (nl & Hnl & R10') & HM2 & HX2).
assert (Hcidx : 0 <= tn_cidx nl < 256).
{ unfold tree_forall in Hwf. rewrite Forall_forall in Hwf. destruct (Hwf nl (ldg_leaves_nodes t nl Hnl)) as (_ & Hc & _). exact Hc. }
assert (CS : forall (r : bv 5) z, acallee_saved z -> bv_unsigned r = z -> getr regs2 r = getr regs1 r) by (intros r z Hz Hr; exact (ldg_cs regs1 regs2 z HP2 Hz r Hr)).
assert (HB2 : ldg_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v fy2 regs2 mem2 md2).
{ split; [exact HJ2|]. split; [exact Hfrm2|].
split; [rewrite (CS (27%bv : bv 5) 27 ltac:(unfold acallee_saved; lia) eq_refl), (HK1 (27%bv : bv 5) ltac:(cbv; tauto)); exact G27|].
rewrite (CS (9%bv : bv 5) 9 ltac:(unfold acallee_saved; lia) eq_refl), (HK1 (9%bv : bv 5) ltac:(cbv; tauto)). exact G9. }
assert (KS : forall a, s1v + 192 <= a < s1v + 408 -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) memc a).
{ intros a Ha. rewrite (HM2 a ltac:(clear - Ha Rs1; lia) ltac:(rewrite Hsp1; unfold TGLNI_STK; clear - Ha; lia)). apply HM1. clear - Ha Rs1. lia. }
assert (SL : forall off v, 192 <= off -> off + 8 <= 408 -> val_mem trbsegs (mrestrict (w_H W) memc) (s1v + off) 8 v -> val_mem trbsegs (mrestrict (w_H W) mem2) (s1v + off) 8 v).
{ intros off v Ho1 Ho2 V. apply (YCcz.val_mem_kept trbsegs (w_H W) (w_H W) memc mem2 (s1v + off) 8 v); [|exact V]. intros kk Hkk. apply KS. clear - Hkk Ho1 Ho2. lia. }
rewrite R1.
eapply SRr_mono.
{ apply (LDGB_run B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v ltac:(clear - Hs1lo; lia) Hs1hi fmt Wd pimg d4 pal pg pn i HinG HG0 HG1 Hi Hfmt HWd Hd4 Hpal HGW
fy2 regs2 mem2 md2 (tn_cidx nl) HB2 Hcidx R10').
- rewrite (CS (25%bv : bv 5) 25 ltac:(unfold acallee_saved; lia) eq_refl), (HK1 (25%bv : bv 5) ltac:(cbv; tauto)). exact G25.
- unfold ldgb_slots. repeat split; apply SL; first [lia | assumption]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & (Q1 & Q31 & Q26 & Q15 & Q18 & Q20 & Q30 & Q16 & Q11 & Q12 & Q13 & Q14) & HK3 & HM3 & HX3).
split; [reflexivity|]. exists fy2, regs3, mem3, md3. split; [reflexivity|]. split; [exact Hfrm2|]. split; [exact HF2|]. split; [exact HJ3|].
split; [rewrite Q1, (CS (20%bv : bv 5) 20 ltac:(unfold acallee_saved; lia) eq_refl); exact R20|].
split; [rewrite Q31, (CS (26%bv : bv 5) 26 ltac:(unfold acallee_saved; lia) eq_refl); exact R26|].
split; [rewrite Q26, (CS (18%bv : bv 5) 18 ltac:(unfold acallee_saved; lia) eq_refl); exact R18|].
split; [rewrite Q15, (CS (26%bv : bv 5) 26 ltac:(unfold acallee_saved; lia) eq_refl); exact R26|].
do 8 (split; [assumption|]).
split.
{ intros r Hr. cbv [LDG_KEEP In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]]]]];
[ rewrite (HK3 (2%bv : bv 5) ltac:(cbv; tauto)), (CS (2%bv : bv 5) 2 ltac:(unfold acallee_saved; lia) eq_refl); apply HK1; cbv; tauto
| rewrite (HK3 (3%bv : bv 5) ltac:(cbv; tauto)), (CS (3%bv : bv 5) 3 ltac:(unfold acallee_saved; lia) eq_refl); apply HK1; cbv; tauto
| rewrite (HK3 (4%bv : bv 5) ltac:(cbv; tauto)), (CS (4%bv : bv 5) 4 ltac:(unfold acallee_saved; lia) eq_refl); apply HK1; cbv; tauto
| rewrite (HK3 (8%bv : bv 5) ltac:(cbv; tauto)), (CS (8%bv : bv 5) 8 ltac:(unfold acallee_saved; lia) eq_refl); apply HK1; cbv; tauto
| rewrite (HK3 (9%bv : bv 5) ltac:(cbv; tauto)), (CS (9%bv : bv 5) 9 ltac:(unfold acallee_saved; lia) eq_refl); apply HK1; cbv; tauto
| rewrite (HK3 (19%bv : bv 5) ltac:(cbv; tauto)), (CS (19%bv : bv 5) 19 ltac:(unfold acallee_saved; lia) eq_refl); apply HK1; cbv; tauto
| rewrite (HK3 (21%bv : bv 5) ltac:(cbv; tauto)), (CS (21%bv : bv 5) 21 ltac:(unfold acallee_saved; lia) eq_refl); apply HK1; cbv; tauto
| rewrite (HK3 (22%bv : bv 5) ltac:(cbv; tauto)), (CS (22%bv : bv 5) 22 ltac:(unfold acallee_saved; lia) eq_refl); apply HK1; cbv; tauto
| rewrite (HK3 (23%bv : bv 5) ltac:(cbv; tauto)), (CS (23%bv : bv 5) 23 ltac:(unfold acallee_saved; lia) eq_refl); apply HK1; cbv; tauto
| rewrite (HK3 (24%bv : bv 5) ltac:(cbv; tauto)), (CS (24%bv : bv 5) 24 ltac:(unfold acallee_saved; lia) eq_refl); apply HK1; cbv; tauto
| rewrite (HK3 (25%bv : bv 5) ltac:(cbv; tauto)), (CS (25%bv : bv 5) 25 ltac:(unfold acallee_saved; lia) eq_refl); apply HK1; cbv; tauto
| rewrite (HK3 (27%bv : bv 5) ltac:(cbv; tauto)), (CS (27%bv : bv 5) 27 ltac:(unfold acallee_saved; lia) eq_refl); apply HK1; cbv; tauto ]. }
split; [| intros a Ha; apply HX3; apply HX2; apply HX1; exact Ha].
intros a Ha Hn1 Hn2. rewrite (HM3 a Ha Hn1), (HM2 a Ha ltac:(rewrite Hsp1; unfold TGLNI_STK; exact Hn2)). exact (HM1 a Ha).
Qed.

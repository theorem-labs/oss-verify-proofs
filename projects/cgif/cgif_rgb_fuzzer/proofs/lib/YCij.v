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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfx YCe9 YCi1 YCib YCil YCiq YCig YCih YCii.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g YM00 YM07 YM05 YM04 YM01 YM02 YM06 YI0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Abbreviation D := fmt_double.
Definition LAY_NTF : layout_t :=
[(96, 8%N); (104, 8%N); (112, 8%N); (120, 8%N); (128, 8%N); (136, 8%N); (144, 8%N); (152, 8%N); (160, 8%N); (168, 8%N); (176, 8%N); (184, 8%N)].
Definition NTF_REGS : list (bv 5) := [26; 25; 24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%bv.
Definition ntf_vals (regs0 : bvmap 5 word) : list Z := map (fun r : bv 5 => bv_unsigned (getr regs0 r)) NTF_REGS.
Definition TN_RET0 : Z := 0x85414.
Definition TN_RET : Z := 0x85600.
Section g.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k1 : Z).
Variables (ly2 : alayout) (S2 : astate) (W2 : world trbsegs) (memM : word -> option byte).
Variables (regs0 : bvmap 5 word) (palp frp nln imin imax cidx res : Z) (pal fr : list Z) (pb pm fb fm : Z).
Local Abbreviation spc := (spZ regs0 - 192).
Hypothesis Hii : 0 <= imin <= imax.
Hypothesis Himax : imax < 2 ^ 30.
Hypothesis Hlenp : 3 * (imax + 1) <= zlen pal.
Hypothesis Hlenf : imax + 1 <= zlen fr.
Hypothesis Hfr1 : forall i, imin <= i <= imax -> 1 <= getz fr i.
Hypothesis Hsum : wsum (node_list pal fr imin imax 0) <= RGB_NMAX.
Hypothesis HinP : In (pb, pm) (ablocks B ly2 S2). Hypothesis HpP0 : pb <= palp. Hypothesis HpP1 : palp + zlen pal <= pb + pm.
Hypothesis HinF : In (fb, fm) (ablocks B ly2 S2). Hypothesis HfF0 : fb <= frp. Hypothesis HfF1 : frp + 4 * zlen fr <= fb + fm.
Hypothesis Hfr4 : frp mod 4 = 0.
Hypothesis HinN : In (res, NODE_SIZE) (ablocks B ly2 S2).
Hypothesis HnPF : (res, NODE_SIZE) <> (pb, pm). Hypothesis HnFF : (res, NODE_SIZE) <> (fb, fm). Hypothesis HPF : (pb, pm) <> (fb, fm).
Hypothesis HpaM : arr8 trbsegs (mrestrict (w_H W2) memM) palp pal.
Hypothesis HfaM : arr32 trbsegs (mrestrict (w_H W2) memM) frp fr.
Hypothesis Hbud : sp0 - STK <= spZ regs0 - TNTN_STK. Hypothesis Hsptop : spZ regs0 <= sp0. Hypothesis Hal16 : spZ regs0 mod 16 = 0.
Hypothesis HNW : forall blc i lyq, In (res, NODE_SIZE) blc -> 0 <= i < 56 -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq own (res + i).
Local Abbreviation ntn_inv := (YCig.ntn_inv B STK sp0 FP ly S W0 mem0 md0 own k1 ly2 S2 W2 memM regs0 palp frp nln imax cidx res).
Local Abbreviation nt_kept_win := (YCig.nt_kept_win regs0 frp).
Local Abbreviation u64_rangeN8 := (YCig.u64_rangeN8 regs0 frp).
Lemma ntn_palv : forall j, (j < length pal)%nat -> 0 <= nth j pal 0 < 256.
Proof. intros j Hj. exact (proj2 (HpaM j Hj)). Qed.
Lemma ntn_frv : forall j, (j < length fr)%nat -> 0 <= nth j fr 0 < 2 ^ 32.
Proof. intros j Hj. exact (proj2 (HfaM j Hj)). Qed.
Lemma ntn_env : forall fy regs mem md, ntn_inv fy regs mem md ->
alloc_ceiling + 16384 <= spc /\ spZ regs0 <= 2 ^ 47 /\ spc mod 16 = 0 /\
4096 <= pb /\ pb + req_size pm <= alloc_ceiling /\ 4096 <= fb /\ fb + req_size fm <= alloc_ceiling /\
4096 <= res /\ res + 56 <= alloc_ceiling /\ res mod 16 = 0 /\ pm <= req_size pm /\ fm <= req_size fm /\
140735332483072 <= alloc_ceiling <= 140737479966720.
Proof. intros fy regs mem md HI. exact (YCig.ntn_env B LAWS STK sp0 FP ly S W0 mem0 md0 own k1 ly2 S2 W2 memM regs0 palp frp nln imax cidx res pb pm fb fm HinP HinF HfF0 HinN Hbud Hsptop Hal16 fy regs mem md HI). Qed.
Lemma ntn_blk_kept : forall fy regs mem md, ntn_inv fy regs mem md ->
forall b m, In (b, m) (ablocks B ly2 S2) -> (b, m) <> (res, NODE_SIZE) -> rg_blk_kept (w_H W2) (w_H W2) memM mem b (req_size m).
Proof. intros fy regs mem md HI. exact (YCig.ntn_blk_kept B LAWS STK sp0 FP ly S W0 mem0 md0 own k1 ly2 S2 W2 memM regs0 palp frp nln imax cidx res HinN Hbud fy regs mem md HI). Qed.
Lemma ntn_arrs : forall fy regs mem md, ntn_inv fy regs mem md ->
arr8 trbsegs (mrestrict (w_H W2) mem) palp pal /\ arr32 trbsegs (mrestrict (w_H W2) mem) frp fr.
Proof.
intros fy regs mem md HI.
exact (YCig.ntn_arrs B LAWS STK sp0 FP ly S W0 mem0 md0 own k1 ly2 S2 W2 memM regs0 palp frp nln imax cidx res pal fr pb pm fb fm HinP HpP0 HpP1 HinF HfF0 HfF1 HinN HnPF HnFF HpaM HfaM Hbud fy regs mem md HI).
Qed.
Local Ltac rreg_byA HS r v H :=
lazymatch type of HS with st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v); [refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v) | ] end.
Local Ltac aj_branchF tblok HS :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let why := sym_whyF segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (st_okF_branch segs E ss ms _ c a b HS); clear HS;
let Hc := fresh "Hc" in intros Hc HS
| _ => fail "aj_branchF: state is not stuck at a branch:" why
end
end
end.
Lemma nt_val_mem_low_of_chunk : forall E mem base off (n : N) (e : sv),
YQ0b.chunk_ok trbsegs E mem base (YQ0b.mkChunk off (CVal n e)) -> (Z.of_N n <= 8) ->
val_mem trbsegs mem (base + off) (N.to_nat n) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N n)).
Proof.
intros E mem base off n e H Hn k Hk. unfold YQ0b.chunk_ok in H. cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len YQ0b.cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [YQ0b.cbyte] in Hb1.
unfold YQ0b.byte_of_word in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
unfold YP0g.le_byte. rewrite N_nat_Z. rewrite Z.mod_mod by lia.
set (v := bv_unsigned (sv_denot E e)).
rewrite !Z.shiftr_div_pow2 by lia.
apply Z.bits_inj'. intros m Hm.
destruct (Z_lt_le_dec m 8) as [Hm8|Hm8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.div_pow2_bits by lia.
assert (Hlt : m + 8 * Z.of_nat k < 8 * Z.of_N n) by nia.
rewrite !(Z.mod_pow2_bits_low _ _ _ Hlt). reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Definition saved_ok (mem : word -> option byte) : Prop :=
obj_at trbsegs (mrestrict (w_H W2) mem) spc LAY_NTF (ntf_vals regs0).
Lemma saved_ok_kept : forall mem mem', saved_ok mem ->
(forall a, spc + 96 <= a < spc + 192 -> aview trbsegs (w_H W2) mem' a = aview trbsegs (w_H W2) mem a) -> saved_ok mem'.
Proof.
intros mem mem' Hs Hk. unfold saved_ok in *. apply (obj_at_transport trbsegs _ _ spc LAY_NTF _ Hs).
intros f i Hf Hi. apply (mbyte_of_aview trbsegs). apply Hk.
unfold LAY_NTF in Hf. cbn [In] in Hf.
repeat (destruct Hf as [<- | Hf]; [cbn [fst snd Z.of_N] in Hi |- *; lia|]). destruct Hf.
Qed.
Variables (n0 : Z).
Hypothesis Hnl1 : spZ regs0 <= nln. Hypothesis Hnl2 : nln + 2 <= sp0.
Hypothesis Hnl_al : nln mod 8 = 2.
Hypothesis Hn0 : 0 <= n0 < 2 ^ 16 - 1.
Hypothesis Hcidx : 0 <= cidx < 256.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Definition tl_mem : smem :=
[ YQ0b.mkRegion (Some 2%nat) 0 192 0 0 (obj_chunks_from LAY_NTF 32);
YQ0b.mkRegion (Some 9%nat) 0 NODE_SIZE 48 51 [];
YQ0b.mkRegion (Some 8%nat) 0 2 0 2 [YQ0b.mkChunk 0 (CVal 2 (SOff 44 0))] ].
Definition tl_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF 4096 140737479966720 4); (8%nat, mkAF (2^46) (2^47 - 6) 1);
(13%nat, mkAF 0 2 0); (18%nat, mkAF 0 255 0); (23%nat, mkAF SB SB 0); (44%nat, mkAF 0 65534 0) ] [] [].
Definition ss_TL : sstate := mkSS TN_TAIL sr_atoms tl_mem None tl_facts.
Definition tl_SH : list shent := [ mkSHE 9 0 NODE_SIZE; mkSHE 8 0 2 ].
Definition tl_extra : list word := map (Z_to_bv 64) (ntf_vals regs0 ++ [n0]).
Definition TL_post (mem : word -> option byte) (cut : Z) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W2 /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (getr regs0 1) mem' (seg_rom trbsegs)) md' /\ frm_zero (@fp_csr fy') /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem' md' (k1 + 1) /\
aregs_preserved regs0 regs' /\ getr regs' 10 = w64 res /\
val_mem trbsegs (mrestrict (w_H W2) mem') (res + 48) 1 cut /\ val_mem trbsegs (mrestrict (w_H W2) mem') (res + 49) 1 cidx /\
val_mem trbsegs (mrestrict (w_H W2) mem') (res + 50) 1 1 /\ val_mem trbsegs (mrestrict (w_H W2) mem') nln 2 (n0 + 1) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (res + 48 <= a < res + 51) -> ~ (nln <= a < nln + 2) ->
aview trbsegs (w_H W2) mem' a = aview trbsegs (w_H W2) mem a) /\
(forall a, apresent (w_H W2) mem a -> apresent (w_H W2) mem' a).
Lemma ntn_tail : forall (fy : FPState) (regs : bvmap 5 word) mem md (cut : Z),
ntn_inv fy regs mem md -> getr regs 13 = w64 cut -> 0 <= cut <= 2 ->
saved_ok mem ->
val_mem trbsegs (mrestrict (w_H W2) mem) nln 2 n0 ->
range_addressable (aview trbsegs (w_H W2) mem) SHADOW_OFF nln 2 ->
SRr trbsegs W2 (mkCfg (@mkst fy regs (Z_to_bv 64 TN_TAIL) mem (seg_rom trbsegs)) md) (TL_post mem cut).
Proof.
intros fy regs mem md cut HI G13 Hcut HSV Vn HRA.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (ntn_env fy regs mem md HI) as (Qsp & Qsp47 & Qal & Qpb0 & Qpb1 & Qfb0 & Qfb1 & Qr0 & Qr1 & Qr16 & Qpm & Qfm & C1).
pose proof HI as (HJ & Hfrm & G2 & G8 & G9 & G18 & G19 & G21 & G22 & G23 & G24 & G25 & G26 & GK & KEPT & PRES).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : TNTN_STK = 16576) by reflexivity.
assert (HnlB : sp0 - STK <= nln /\ nln + 2 <= sp0 /\ 2 ^ 46 <= nln /\ nln <= 2 ^ 47 - 6 /\ alloc_ceiling + 16384 + 192 <= nln).
{ pose proof (Z.div_mod nln 8 ltac:(lia)) as Hdm. rewrite Hnl_al in Hdm. clear - Hnl1 Hnl2 Hbud Qsp Hshi H47 C1 WS Hdm. lia. }
destruct HnlB as (HnlB0 & _ & Hnl46 & Hnl47 & HnlC).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res NODE_SIZE HAR HinN) as (_ & _ & _ & _ & Hnpres & _). change (req_size NODE_SIZE) with 56 in Hnpres.
set (E := Ereg regs tl_extra).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HVF : forall j v, nth_error (ntf_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. unfold tl_extra. rewrite map_app. apply Ereg_vals. exact Hj. }
assert (E43 : ew E 44 = Z_to_bv 64 n0) by (subst E; exact (ew_Ereg_extra regs _ 12)).
assert (U2 : bv_unsigned (ew E 2) = spc) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Qsp Qsp47 C1; lia).
assert (U9 : bv_unsigned (ew E 9) = res) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Qr0 Qr1 C1; lia).
assert (U8 : bv_unsigned (ew E 8) = nln) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; clear - Hnl46 Hnl47; lia).
assert (U13 : bv_unsigned (ew E 13) = cut) by (rewrite (HE 13%nat 13%bv eq_refl), G13; apply unsigned_lit_small; clear - Hcut; lia).
assert (U18 : bv_unsigned (ew E 18) = cidx) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - Hcidx; lia).
assert (E23 : ew E 23 = w64 SB) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (U43 : bv_unsigned (ew E 44) = n0) by (rewrite E43; apply unsigned_lit_small; clear - Hn0; lia).
assert (HS : @st_ok trbsegs fy E ss_TL (restrict (w_H W2) (@mkst fy regs (Z_to_bv 64 TN_TAIL) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_TL. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold tl_mem. repeat apply Forall_cons; try apply Forall_nil.
+ eapply (region_ok_obj trbsegs _ _ 2 spc); [exact U2 | clear - Qsp C1; lia | clear - Qsp47; lia | exact HSV | reflexivity | exact HVF | intros i Hi; lia].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U9.
unfold NODE_SIZE. split; [clear - Qr0; lia|]. split; [clear - Qr1 C1; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trbsegs). apply (proj1 (Hnpres (res + o) ltac:(clear - Ho; lia))).
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U8.
split; [clear - Hnl46; lia|]. split; [clear - Hnl47; lia|]. split.
{ intros o Ho. apply (apresent_writable trbsegs). apply Hpres. clear - Ho HnlB0 Hnl2. lia. }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E _ nln 0 2 _ n0); [cbn [sv_denot]; fold E; rewrite U43, Z.add_0_r; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vn].
- apply pairwise_disjoint_of_extents. unfold tl_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E. rewrite U2, U9, U8. unfold NODE_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Qsp Qr1 Hnl1 Hnl2 HnlC. repeat split; lia.
- split; [|split; exact I].
cbn [tl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
rewrite U2, U9, U8, U13, U18, E23, U43. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 1) with 2. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert (Hnl_al2 : nln mod 2 = 0) by (clear - Hnl_al; pose proof (Z.mod_mod_divide nln 8 2 ltac:(exists 4; reflexivity)) as X; rewrite Hnl_al in X; rewrite <- X; reflexivity).
clear - Qsp Qsp47 Qal Qr0 Qr1 Qr16 C1 Hnl46 Hnl47 Hnl_al2 Hcut Hcidx Hn0. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trbsegs l1_Bx tl_SH E (mrestrict (w_H W2) mem)).
{ unfold sh_ok, tl_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 mem md E l1_Bx 9 res NODE_SIZE 0 NODE_SIZE HAR HinN).
+ unfold U, l1_Bx. cbn [sv_denot]. rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U9.
+ lia.
+ change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia.
- apply (shent_ok_of_range trbsegs (w_H W2) mem E l1_Bx 8 nln 2 nln 0 2 HRA).
+ unfold U, l1_Bx. cbn [sv_denot]. rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U8.
+ lia.
+ lia.
+ intros x Hx. revert Hx Hnl46 Hnl47 HnlC C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK nt_Bspan TN_RET.
{ unfold tl_mem. apply awr_ok_cons_ro; [cbn; lia|].
eapply awr_ok_cons_gen; [reflexivity | exact U9 | |].
{ cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. replace a with (res + (a - res)) by lia. apply HNW; [exact HinN | clear - Ha; lia]. }
eapply awr_ok_cons_gen; [reflexivity | exact U8 | | apply awr_ok_nil].
cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. left. clear - Ha HnlB0 Hnl2. lia. }
pose proof (st_ok_region_nth _ _ _ 1%nat _ HS ltac:(reflexivity)) as HR1. cbn [ms_mem restrict] in HR1.
pose proof (st_ok_region_nth _ _ _ 2%nat _ HS ltac:(reflexivity)) as HR2. cbn [ms_mem restrict] in HR2.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (AG : forall n, (n < 45)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite !ew_ewset_other by lia; reflexivity) end.
assert (FV : forall j (r : bv 5), nth_error NTF_REGS j = Some r -> ew E (32 + j) = getr regs0 r).
{ intros j r Hj. rewrite (HVF j (bv_unsigned (getr regs0 r))); [apply Z_to_bv_bv_unsigned|]. unfold ntf_vals. rewrite nth_error_map, Hj. reflexivity. }
pose proof (FV 0%nat _ eq_refl) as F32. pose proof (FV 1%nat _ eq_refl) as F33. pose proof (FV 2%nat _ eq_refl) as F34.
pose proof (FV 3%nat _ eq_refl) as F35. pose proof (FV 4%nat _ eq_refl) as F36. pose proof (FV 5%nat _ eq_refl) as F37.
pose proof (FV 6%nat _ eq_refl) as F38. pose proof (FV 7%nat _ eq_refl) as F39. pose proof (FV 8%nat _ eq_refl) as F40.
pose proof (FV 9%nat _ eq_refl) as F41. pose proof (FV 10%nat _ eq_refl) as F42. pose proof (FV 11%nat _ eq_refl) as F43.
cbn [Nat.add] in F32, F33, F34, F35, F36, F37, F38, F39, F40, F41, F42, F43.
rreg HS (1%bv : bv 5) Qra. rreg HS (10%bv : bv 5) Qa0.
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold TL_post. split; [reflexivity|].
exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [rewrite Qra, F43, Hra; reflexivity|].
split; [exact Hfrm|].
split; [cbn [ms_mem]; apply (ajournal_materialize trbsegs B LAWS Hsegs); exact HJ|].
split.
{
intros r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hr.
repeat (destruct Hc as [-> | Hc]); [ | | | | | | | | | | | | | | subst r].
+ assert (X : getr (ms_regs ms) (2%bv : bv 5) = getr regs0 (2%bv : bv 5)); [|exact X]. rreg HS (2%bv : bv 5) Rk. rewrite Rk, U2.
replace (spc + 192) with (spZ regs0) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
+ assert (X : getr (ms_regs ms) (3%bv : bv 5) = getr regs0 (3%bv : bv 5)); [|exact X]. rreg HS (3%bv : bv 5) Rk. rewrite Rk, (HE 3%nat 3%bv eq_refl). apply GK. cbv. tauto.
+ assert (X : getr (ms_regs ms) (4%bv : bv 5) = getr regs0 (4%bv : bv 5)); [|exact X]. rreg HS (4%bv : bv 5) Rk. rewrite Rk, (HE 4%nat 4%bv eq_refl). apply GK. cbv. tauto.
+ assert (X : getr (ms_regs ms) (8%bv : bv 5) = getr regs0 (8%bv : bv 5)); [|exact X]. rreg HS (8%bv : bv 5) Rk. rewrite Rk. exact F42.
+ assert (X : getr (ms_regs ms) (9%bv : bv 5) = getr regs0 (9%bv : bv 5)); [|exact X]. rreg HS (9%bv : bv 5) Rk. rewrite Rk. exact F41.
+ assert (X : getr (ms_regs ms) (18%bv : bv 5) = getr regs0 (18%bv : bv 5)); [|exact X]. rreg HS (18%bv : bv 5) Rk. rewrite Rk. exact F40.
+ assert (X : getr (ms_regs ms) (19%bv : bv 5) = getr regs0 (19%bv : bv 5)); [|exact X]. rreg HS (19%bv : bv 5) Rk. rewrite Rk. exact F39.
+ assert (X : getr (ms_regs ms) (20%bv : bv 5) = getr regs0 (20%bv : bv 5)); [|exact X]. rreg HS (20%bv : bv 5) Rk. rewrite Rk. exact F38.
+ assert (X : getr (ms_regs ms) (21%bv : bv 5) = getr regs0 (21%bv : bv 5)); [|exact X]. rreg HS (21%bv : bv 5) Rk. rewrite Rk. exact F37.
+ assert (X : getr (ms_regs ms) (22%bv : bv 5) = getr regs0 (22%bv : bv 5)); [|exact X]. rreg HS (22%bv : bv 5) Rk. rewrite Rk. exact F36.
+ assert (X : getr (ms_regs ms) (23%bv : bv 5) = getr regs0 (23%bv : bv 5)); [|exact X]. rreg HS (23%bv : bv 5) Rk. rewrite Rk. exact F35.
+ assert (X : getr (ms_regs ms) (24%bv : bv 5) = getr regs0 (24%bv : bv 5)); [|exact X]. rreg HS (24%bv : bv 5) Rk. rewrite Rk. exact F34.
+ assert (X : getr (ms_regs ms) (25%bv : bv 5) = getr regs0 (25%bv : bv 5)); [|exact X]. rreg HS (25%bv : bv 5) Rk. rewrite Rk. exact F33.
+ assert (X : getr (ms_regs ms) (26%bv : bv 5) = getr regs0 (26%bv : bv 5)); [|exact X]. rreg HS (26%bv : bv 5) Rk. rewrite Rk. exact F32.
+ assert (X : getr (ms_regs ms) (27%bv : bv 5) = getr regs0 (27%bv : bv 5)); [|exact X]. rreg HS (27%bv : bv 5) Rk. rewrite Rk, (HE 27%nat 27%bv eq_refl). apply GK. cbv. tauto. }
split; [rewrite Qa0, (HE 9%nat 9%bv eq_refl); exact G9|].
cbn [ms_mem].
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E1 := Ex) in * end.
assert (U9' : bv_unsigned (ew E1 9) = res) by (rewrite AG by lia; exact U9).
assert (U8' : bv_unsigned (ew E1 8) = nln) by (rewrite AG by lia; exact U8).
split.
{ lazymatch type of HR1 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
apply (field_of_region E1 _ 9 res cs lo hi wlo whi 48 1%N (SOff 13 0) cut HR1 U9'); [cbn; tauto | | cbn; clear - Hcut; lia | cbn; lia] end.
cbn [sv_denot]. rewrite AG by lia. rewrite U13, Z.add_0_r. reflexivity. }
split.
{ lazymatch type of HR1 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
apply (field_of_region E1 _ 9 res cs lo hi wlo whi 49 1%N (SOff 18 0) cidx HR1 U9'); [cbn; tauto | | cbn; clear - Hcidx; lia | cbn; lia] end.
cbn [sv_denot]. rewrite AG by lia. rewrite U18, Z.add_0_r. reflexivity. }
split.
{ lazymatch type of HR1 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
apply (field_of_region E1 _ 9 res cs lo hi wlo whi 50 1%N (SLit 1) 1 HR1 U9'); [cbn; tauto | reflexivity | cbn; lia | cbn; lia] end. }
split.
{ destruct HR2 as (_ & _ & _ & Hcs). cbn [YQ0b.r_chunks YQ0b.r_base base_val] in Hcs. rewrite U8' in Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ ltac:(left; reflexivity)) as Hck.
pose proof (nt_val_mem_low_of_chunk E1 _ nln 0 2%N _ Hck ltac:(cbn; lia)) as V. rewrite Z.add_0_r in V.
replace (bv_unsigned _ mod _) with (n0 + 1) in V; [exact V|].
change (bv_unsigned ?x) with (U E1 (SAlu ALU_ADD (SExt true 16 (SOff 44 0)) (SLit 1))).
assert (E43' : ew E1 44 = Z_to_bv 64 n0) by (rewrite AG by lia; exact E43).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SExt, U_SLit, (U_atom E1 44 n0 E43') by (clear - Hn0; lia).
change (2 ^ Z.of_N 16) with (2 ^ 16). change (8 * Z.of_N 2) with 16.
unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.mul Z.modulo Z.div Z.sub Z.pow].
clear - Hn0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
change (2 ^ 16) with 65536. change (2 ^ 64) with 18446744073709551616. change (Z.of_N 64) with 64. change (Z.of_N 16) with 16.
change (2 ^ 64) with 18446744073709551616. change (2 ^ (16 - 1)) with 32768.
nia. }
split.
- intros a Ha Hnn Hnl. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). cbn [ss_mem ss_TL tl_mem] in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr.
+ clear - Hr; lia.
+ rewrite U9 in Hr. clear - Hr Hnn. lia.
+ rewrite U8 in Hr. clear - Hr Hnl. lia.
- intros a Ha. exact (apresent_grows _ _ _ _ HG Ha).
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Hypothesis AMEMSET : forall fx : FPState, @aintrin_realizes fx rc trbsegs B OSet A_asan_memset.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B). Hypothesis Htp : getr regs0 4 = w64 (as_tp B).
Lemma ntd_lxor_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. pose proof (Z.sub_lxor_2rlandn (2 ^ 64 - 1) x) as H.
assert (Z.land (Z.lnot (2 ^ 64 - 1)) x = 0).
{ replace (Z.lnot (2 ^ 64 - 1)) with (- (2 ^ 64)) by reflexivity.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_dec n 64).
- replace (- (2 ^ 64)) with (Z.shiftl (-1) 64) by reflexivity. rewrite Z.shiftl_spec_low by lia. reflexivity.
- rewrite (Z.bits_above_log2 x); [apply Bool.andb_false_r | lia |].
destruct (Z.eq_dec x 0); [subst; cbn; lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia | lia]. }
rewrite Z.lxor_comm. lia.
Qed.
Lemma p1_memset : forall (fy : FPState) (regsT : bvmap 5 word) memT mdT (dofs ret : Z),
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT (k1 + 1) ->
getr regsT 10 = w64 (spc + dofs) -> getr regsT 11 = w64 0 -> getr regsT 12 = w64 24 ->
getr regsT 1 = Z_to_bv 64 ret -> YK0s.ret_ok (Z_to_bv 64 ret) ->
getr regsT 2 = w64 spc -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
0 <= dofs -> dofs + 24 <= 96 ->
SRr trbsegs W2 (mkCfg (@mkst fy regsT (Z_to_bv 64 A_asan_memset) memT (seg_rom trbsegs)) mdT)
(fun W' c' => W' = W2 /\ exists regs' mem' md',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 ret) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem' md' (k1 + 1) /\
aregs_preserved regsT regs' /\
(forall i, 0 <= i < 24 -> aview trbsegs (w_H W2) mem' (spc + dofs + i) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + dofs <= a < spc + dofs + 24) -> ~ (spc - ESTACK <= a < spc) ->
aview trbsegs (w_H W2) mem' a = aview trbsegs (w_H W2) memT a) /\
(forall a, apresent (w_H W2) memT a -> apresent (w_H W2) mem' a)).
Proof.
intros fy regsT memT mdT dofs ret HJ Ga0 Ga1 Ga2 Gra Hret Gsp Ggp Gtp Hd0 Hd1.
pose proof trb_segs_low as Hsegs.
pose proof HJ as (HAR & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo2 & Ehi2 & _).
pose proof asan_consts as (C1 & _).
assert (WS : TNTN_STK = 16576) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (Qsp : alloc_ceiling + 16384 <= spc) by (clear - Hbud Hslo Hceil WS; lia).
assert (Qsp47 : spZ regs0 <= 2 ^ 47) by (clear - Hsptop Hshi H47; lia).
assert (Qal : spc mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
destruct (rg_stack_shadow B LAWS W2 ly2 S2 memT mdT (spc + dofs) 24 HAR
ltac:(rewrite Elo2; clear - Hbud Hslo WS Hd0; lia) ltac:(rewrite Ehi2; clear - Hsptop Hshi Hd1; lia) ltac:(lia)) as [HRA HHV].
eapply SRr_mono.
{ eapply (aj_intrin_at trbsegs B LAWS Hsegs OSet A_asan_memset (AMEMSET fy) W2 regsT memT STK sp0 FP ly S W0 mem0 md0 own
ly2 S2 mdT (k1 + 1) (spc + dofs) 0 24 (spc - sp0) (Z_to_bv 64 ret) HJ).
- exact Ga0.
- exact Ga1.
- exact Ga2.
- lia.
- clear - Qsp C1 Hd0. lia.
- clear - Qsp47 Hd1. lia.
- unfold spZ at 1. rewrite Gsp. unfold w64. rewrite unsigned_lit_small by (clear - Qsp Qsp47 C1; lia). lia.
- rewrite Zminus_mod, Qal, Hsp0al. reflexivity.
- clear - Hsptop. lia.
- rewrite HES. clear - Hbud WS. lia.
- exact Ggp.
- exact Gtp.
- exact Gra.
- exact Hret.
- intros a Ha. split; [left; clear - Ha Hbud Hsptop WS Hd0 Hd1; lia | rewrite HES; clear - Ha Hd0; lia].
- eapply rg_stack_amem; [exact HAR | rewrite Elo2; clear - Hbud Hslo WS Hd0; lia | rewrite Ehi2; clear - Hsptop Hshi Hd1; lia].
- exact HRA.
- exact HHV.
- exact I. }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HJ' & HP' & _ & Heff & Hfr & Hpres').
split; [reflexivity|]. exists regs', mem', md'. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP'|].
split; [intros i Hi; rewrite (Heff i Hi); reflexivity|].
split; [|exact Hpres'].
intros a Ha Hn1 Hn2. apply Hfr; [exact Ha | exact Hn1 |]. replace (sp0 + (spc - sp0)) with spc by lia. exact Hn2.
Qed.
Definition p1_mid (zs : list Z) (mem : word -> option byte) : Prop :=
(forall a, 0 <= a < 2 ^ 64 -> ~ (res + 40 <= a < res + 48) -> ~ (spc - ESTACK <= a < spc + 96) ->
aview trbsegs (w_H W2) mem a = aview trbsegs (w_H W2) memM a) /\
(forall a, apresent (w_H W2) memM a -> apresent (w_H W2) mem a) /\
val_mem trbsegs (mrestrict (w_H W2) mem) (res + 40) 4 imin /\ val_mem trbsegs (mrestrict (w_H W2) mem) (res + 44) 4 imax /\
(forall d i, In d zs -> 0 <= i < 24 -> aview trbsegs (w_H W2) mem (spc + d + i) = Some 0).
Definition p1_env : Prop := 4096 <= res /\ res + 56 <= alloc_ceiling /\ alloc_ceiling + 16384 <= spc /\ spZ regs0 <= 2 ^ 47.
Lemma p1_mid_run : forall zs mem mem', p1_env -> (forall d, In d zs -> 0 <= d /\ d + 24 <= 96) -> p1_mid zs mem ->
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W2) mem' a = aview trbsegs (w_H W2) mem a) ->
(forall a, apresent (w_H W2) mem a -> apresent (w_H W2) mem' a) -> p1_mid zs mem'.
Proof.
intros zs mem mem' (Qr0 & Qr1 & Qsp & Qsp47) Hzs (K & P & V0 & V1 & Zs) Hk Hp.
pose proof asan_consts as (C1 & _).
assert (KN : rg_blk_kept (w_H W2) (w_H W2) mem mem' res 56) by (intros i Hi; apply Hk; clear - Hi Qr0 Qr1 C1; lia).
split; [intros a Ha H1 H2; rewrite (Hk a Ha); exact (K a Ha H1 H2)|].
split; [intros a Ha; apply Hp; apply P; exact Ha|].
split; [apply (rg_val_mem_blk_kept (w_H W2) (w_H W2) mem mem' res 56 (res + 40) 4 imin V0 KN); [clear; lia | cbn; clear; lia]|].
split; [apply (rg_val_mem_blk_kept (w_H W2) (w_H W2) mem mem' res 56 (res + 44) 4 imax V1 KN); [clear; lia | cbn; clear; lia]|].
intros d i Hd Hi. destruct (Hzs d Hd) as [Hd0 Hd1]. rewrite Hk by (clear - Hi Hd0 Hd1 Qsp Qsp47 C1; lia). exact (Zs d i Hd Hi).
Qed.
Lemma p1_mid_set : forall zs mem mem' d, p1_env -> (forall d', In d' zs -> 0 <= d' /\ d' + 24 <= 96 /\ (d' + 24 <= d \/ d + 24 <= d')) ->
0 <= d -> d + 24 <= 96 -> p1_mid zs mem ->
(forall i, 0 <= i < 24 -> aview trbsegs (w_H W2) mem' (spc + d + i) = Some 0) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + d <= a < spc + d + 24) -> ~ (spc - ESTACK <= a < spc) ->
aview trbsegs (w_H W2) mem' a = aview trbsegs (w_H W2) mem a) ->
(forall a, apresent (w_H W2) mem a -> apresent (w_H W2) mem' a) -> p1_mid (d :: zs) mem'.
Proof.
intros zs mem mem' d (Qr0 & Qr1 & Qsp & Qsp47) Hzs Hd0 Hd1 (K & P & V0 & V1 & Zs) Hz Hk Hp.
pose proof asan_consts as (C1 & _). assert (HES : ESTACK = 4096) by reflexivity.
assert (KN : rg_blk_kept (w_H W2) (w_H W2) mem mem' res 56).
{ intros i Hi. apply Hk; [clear - Hi Qr0 Qr1 C1; lia | clear - Hi Qr1 Qsp Hd0; lia | rewrite HES; clear - Hi Qr1 Qsp; lia]. }
split.
{ intros a Ha H1 H2. rewrite Hk; [exact (K a Ha H1 H2) | exact Ha | clear - H2 Hd0 Hd1 HES; lia | clear - H2; lia]. }
split; [intros a Ha; apply Hp; apply P; exact Ha|].
split; [apply (rg_val_mem_blk_kept (w_H W2) (w_H W2) mem mem' res 56 (res + 40) 4 imin V0 KN); [clear; lia | cbn; clear; lia]|].
split; [apply (rg_val_mem_blk_kept (w_H W2) (w_H W2) mem mem' res 56 (res + 44) 4 imax V1 KN); [clear; lia | cbn; clear; lia]|].
intros d' i [<- | Hd'] Hi; [exact (Hz i Hi)|].
destruct (Hzs d' Hd') as (Hd0' & Hd1' & Hdj).
rewrite Hk; [exact (Zs d' i Hd' Hi) | clear - Hi Hd0' Hd1' Qsp Qsp47 C1; lia | clear - Hi Hdj; lia | rewrite HES; clear - Hi Hd0'; lia].
Qed.
Definition p1_mem : smem := [ YQ0b.mkRegion (Some 10%nat) 0 NODE_SIZE 40 48 [] ].
Definition p1_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4); (19%nat, mkAF 0 (2^30) 0); (20%nat, mkAF 0 (2^30) 0);
(22%nat, mkAF 4096 140737479966720 0); (23%nat, mkAF SB SB 0) ]
[ mkAC BC_GEU (SOff 19 0) (SOff 20 0) ] [].
Definition ss_P1 : sstate := mkSS TN_RET0 sr_atoms p1_mem None p1_facts.
Definition p1_SH : list shent := [ mkSHE 10 0 NODE_SIZE ].
Definition P1_post : world trbsegs -> config -> Prop :=
fun W' c' => W' = W2 /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 TN_L1) mem' (seg_rom trbsegs)) md' /\
ntn_inv fy' regs' mem' md' /\
getr regs' 14 = w64 imin /\ getr regs' 11 = w64 (3 * imin) /\ getr regs' 12 = w64 (2 ^ 64 - 1 - frp) /\ getr regs' 13 = w64 1 /\
getr regs' 20 = w64 imin /\
(forall j, 0 <= j < 12 -> val_mem trbsegs (mrestrict (w_H W2) mem') (spc + 8 * j) 8 0) /\
val_mem trbsegs (mrestrict (w_H W2) mem') (res + 40) 4 imin /\ val_mem trbsegs (mrestrict (w_H W2) mem') (res + 44) 4 imax /\
saved_ok mem'.
Lemma ntn_p1 : forall (fy : FPState) (regs : bvmap 5 word) md,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memM md (k1 + 1) ->
frm_zero (@fp_csr fy) ->
getr regs 2 = w64 spc -> getr regs 8 = w64 nln -> getr regs 10 = w64 res -> getr regs 18 = w64 cidx -> getr regs 19 = w64 imax ->
getr regs 20 = w64 imin -> getr regs 21 = w64 frp -> getr regs 22 = w64 palp -> getr regs 23 = w64 SB ->
(forall rr : bv 5, In rr NT_KEPT -> getr regs rr = getr regs0 rr) ->
saved_ok memM ->
SRr trbsegs W2 (mkCfg (@mkst fy regs (Z_to_bv 64 TN_RET0) memM (seg_rom trbsegs)) md) P1_post.
Proof.
intros fy regs md HJ Hfrm G2 G8 G10 G18 G19 G20 G21 G22 G23 GK HSV.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HJ as (HAR & Hly2 & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _).
assert (WS : TNTN_STK = 16576) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res NODE_SIZE HAR HinN) as (Qr16 & Qr0 & Qr1 & _ & Hnpres & _). change (req_size NODE_SIZE) with 56 in Qr1, Hnpres.
assert (Qsp : alloc_ceiling + 16384 <= spc) by (clear - Hbud Hslo Hceil WS; lia).
assert (Qsp47 : spZ regs0 <= 2 ^ 47) by (clear - Hsptop Hshi H47; lia).
assert (Qal : spc mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
set (E := Ereg regs []).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U2 : bv_unsigned (ew E 2) = spc) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Qsp Qsp47 C1; lia).
assert (U10 : bv_unsigned (ew E 10) = res) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; clear - Qr0 Qr1 C1; lia).
assert (U19 : bv_unsigned (ew E 19) = imax) by (rewrite (HE 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; clear - Hii Himax; lia).
assert (U20 : bv_unsigned (ew E 20) = imin) by (rewrite (HE 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; clear - Hii Himax; lia).
assert (E23 : ew E 23 = w64 SB) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR HinP) as (_ & Qpb0 & Qpb1 & _ & _ & _ & Hpm0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ fb fm HAR HinF) as (_ & Qfb0 & Qfb1 & _ & _ & _ & Hfm0).
pose proof (req_size_pos pm ltac:(lia)) as [_ Qpm]. pose proof (req_size_pos fm ltac:(lia)) as [_ Qfm].
assert (Rpalp : 4096 <= palp /\ palp + zlen pal <= 140737479966720) by (clear - HpP0 HpP1 Qpb0 Qpb1 Qpm C1; lia).
assert (Rfrp : 4096 <= frp /\ frp + 4 * zlen fr <= 140737479966720) by (clear - HfF0 HfF1 Qfb0 Qfb1 Qfm C1; lia).
assert (U22 : bv_unsigned (ew E 22) = palp) by (rewrite (HE 22%nat 22%bv eq_refl), G22; apply unsigned_lit_small; clear - Rpalp Hlenp Hii; lia).
assert (HS : @st_ok trbsegs fy E ss_P1 (restrict (w_H W2) (@mkst fy regs (Z_to_bv 64 TN_RET0) memM (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_P1. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold p1_mem. repeat apply Forall_cons; try apply Forall_nil.
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U10.
unfold NODE_SIZE. split; [clear - Qr0; lia|]. split; [clear - Qr1 C1; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trbsegs). apply (proj1 (Hnpres (res + o) ltac:(clear - Ho; lia))).
- apply pairwise_disjoint_of_extents. unfold p1_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [|exact I]].
+ cbn [p1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
rewrite U2, U10, U19, U20, U22, E23. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Qsp Qsp47 Qal Qr0 Qr1 Qr16 C1 Hii Himax Rpalp Hlenp. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [p1_facts f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. split; [|exact I]. fold E.
rewrite branch_geu_U, !U_SOff, U19, U20, !Z.add_0_r, !zcanon_id by (unfold M64; clear - Hii Himax; lia).
apply Bool.negb_true_iff. apply Z.ltb_ge. clear - Hii. lia. }
assert (SHOK : sh_ok trbsegs l1_Bx p1_SH E (mrestrict (w_H W2) memM)).
{ unfold sh_ok, p1_SH. constructor; [|constructor].
apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 memM md E l1_Bx 10 res NODE_SIZE 0 NODE_SIZE HAR HinN).
- unfold U, l1_Bx. cbn [sv_denot]. rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U10.
- lia.
- change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia. }
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK nt_Bspan A_asan_memset.
{ unfold p1_mem. eapply awr_ok_cons_gen; [reflexivity | exact U10 | | apply awr_ok_nil].
cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. replace a with (res + (a - res)) by lia. apply HNW; [exact HinN | clear - Ha; lia]. }
pose proof (st_ok_region_nth _ _ _ 0%nat _ HS ltac:(reflexivity)) as HR0. cbn [ms_mem restrict] in HR0.
assert (Vmin1 : val_mem trbsegs (mrestrict (w_H W2) (ms_mem ms)) (res + 40) 4 imin).
{ lazymatch type of HR0 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
apply (field_of_region E _ 10 res cs lo hi wlo whi 40 4%N (SOff 20 0) imin HR0 U10); [cbn; tauto | | | cbn; lia] end.
- cbn [sv_denot]. rewrite U20, Z.add_0_r. reflexivity.
- cbn. clear - Hii Himax. lia. }
assert (Vmax1 : val_mem trbsegs (mrestrict (w_H W2) (ms_mem ms)) (res + 44) 4 imax).
{ lazymatch type of HR0 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
apply (field_of_region E _ 10 res cs lo hi wlo whi 44 4%N (SOff 19 0) imax HR0 U10); [cbn; tauto | | | cbn; lia] end.
- cbn [sv_denot]. rewrite U19, Z.add_0_r. reflexivity.
- cbn. clear - Hii Himax. lia. }
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> ~ (res + 40 <= a < res + 48) -> aview trbsegs (w_H W2) (ms_mem ms) a = aview trbsegs (w_H W2) memM a).
{ intros a Ha Hnw. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). cbn [ss_mem ss_P1 p1_mem In] in Hin. destruct Hin as [<- | []].
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr. rewrite U10 in Hr. clear - Hr Hnw. lia. }
assert (PR1 : forall a, apresent (w_H W2) memM a -> apresent (w_H W2) (ms_mem ms) a) by (intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)).
clear HF HFr HG HR0.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (Ggp : getr regs 3 = w64 (as_gp B)) by (rewrite (GK (3%bv : bv 5) ltac:(cbv; tauto)); exact Hgp).
assert (Gtp : getr regs 4 = w64 (as_tp B)) by (rewrite (GK (4%bv : bv 5) ltac:(cbv; tauto)); exact Htp).
assert (PE : p1_env) by (unfold p1_env; clear - Qr0 Qr1 Qsp Qsp47; lia).
assert (M1 : p1_mid [] (ms_mem ms)).
{ split; [intros a Ha H1 _; exact (KW1 a Ha H1)|]. split; [exact PR1|]. split; [exact Vmin1|]. split; [exact Vmax1|]. intros d i []. }
clear KW1 PR1 Vmin1 Vmax1.
rreg HS (10%bv : bv 5) Qa0. rreg HS (11%bv : bv 5) Qa1. rreg HS (12%bv : bv 5) Qa2. rreg HS (1%bv : bv 5) Qra.
rreg HS (2%bv : bv 5) Qsp2. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 337168) with (Z_to_bv 64 A_asan_memset).
eapply SRr_bind.
{ eapply (p1_memset fy _ _ _ 24 0x85468 HJ);
[ first [rewrite Qa0, ?(AG 2%nat) by lia; rewrite U2; reflexivity | rewrite Qa0, ?(AG 2%nat) by lia; rewrite (HE 2%nat 2%bv eq_refl), G2; unfold w64; f_equal; lia] | exact Qa1 | exact Qa2 | exact Qra | vm_compute; reflexivity
| rewrite Qsp2, ?(AG 2%nat) by lia; rewrite (HE 2%nat 2%bv eq_refl); exact G2
| rewrite Qgp, ?(AG 3%nat) by lia; rewrite (HE 3%nat 3%bv eq_refl); exact Ggp
| rewrite Qtp, ?(AG 4%nat) by lia; rewrite (HE 4%nat 4%bv eq_refl); exact Gtp | lia | lia ]. }
cbv beta. intros W' c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Zn2 & KM2 & PM2).
clear Qa0 Qa1 Qa2 Qra Qsp2 Qgp Qtp.
reseat HS HJ2 HP2 (@nil nat) AG ltac:(idtac).
lazymatch type of M1 with p1_mid ?zs ?m0 =>
pose proof (p1_mid_set zs m0 mem2 24 PE ltac:(intros d' Hd'; cbn [In] in Hd'; lia) ltac:(lia) ltac:(lia) M1 Zn2 KM2 PM2) as M2 end.
clear M1 Zn2 KM2 PM2 HJ SHOK.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msx) => assert (SHOK : sh_ok trbsegs l1_Bx [] Ex (mrestrict (w_H W2) (ms_mem msx))) by constructor end.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ2 end.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK nt_Bspan A_asan_memset.
{ apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr, HG.
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
lazymatch type of M2 with p1_mid ?zs _ => pose proof (p1_mid_run zs m0 m1 PE ltac:(intros d' Hd'; cbn [In] in Hd'; lia) M2
ltac:(intros a Ha; apply aview_eq_of; apply HFr; rewrite unsigned_lit_small by lia; intros (rr & Hin & _); destruct Hin)
ltac:(intros a Ha; exact (apresent_grows _ _ _ _ HG Ha))) as M2r end end.
clear HF HFr HG M2.
rreg HS (10%bv : bv 5) Qa0. rreg HS (11%bv : bv 5) Qa1. rreg HS (12%bv : bv 5) Qa2. rreg HS (1%bv : bv 5) Qra.
rreg HS (2%bv : bv 5) Qsp2. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 337168) with (Z_to_bv 64 A_asan_memset).
eapply SRr_bind.
{ eapply (p1_memset fy _ _ _ 0 0x85478 HJ2);
[ first [rewrite Qa0, ?(AG 2%nat) by lia; rewrite U2; reflexivity | rewrite Qa0, ?(AG 2%nat) by lia; rewrite (HE 2%nat 2%bv eq_refl), G2; unfold w64; f_equal; lia] | exact Qa1 | exact Qa2 | exact Qra | vm_compute; reflexivity
| rewrite Qsp2, ?(AG 2%nat) by lia; rewrite (HE 2%nat 2%bv eq_refl); exact G2
| rewrite Qgp, ?(AG 3%nat) by lia; rewrite (HE 3%nat 3%bv eq_refl); exact Ggp
| rewrite Qtp, ?(AG 4%nat) by lia; rewrite (HE 4%nat 4%bv eq_refl); exact Gtp | lia | lia ]. }
cbv beta. intros W' c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Zn3 & KM3 & PM3).
clear Qa0 Qa1 Qa2 Qra Qsp2 Qgp Qtp.
reseat HS HJ3 HP3 (@nil nat) AG ltac:(idtac).
lazymatch type of M2r with p1_mid ?zs ?m0 =>
pose proof (p1_mid_set zs m0 mem3 0 PE ltac:(intros d' Hd'; cbn [In] in Hd'; lia) ltac:(lia) ltac:(lia) M2r Zn3 KM3 PM3) as M3 end.
clear M2r Zn3 KM3 PM3 HJ2 SHOK.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msx) => assert (SHOK : sh_ok trbsegs l1_Bx [] Ex (mrestrict (w_H W2) (ms_mem msx))) by constructor end.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ3 end.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK nt_Bspan A_asan_memset.
{ apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr, HG.
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
lazymatch type of M3 with p1_mid ?zs _ => pose proof (p1_mid_run zs m0 m1 PE ltac:(intros d' Hd'; cbn [In] in Hd'; lia) M3
ltac:(intros a Ha; apply aview_eq_of; apply HFr; rewrite unsigned_lit_small by lia; intros (rr & Hin & _); destruct Hin)
ltac:(intros a Ha; exact (apresent_grows _ _ _ _ HG Ha))) as M3r end end.
clear HF HFr HG M3.
rreg HS (10%bv : bv 5) Qa0. rreg HS (11%bv : bv 5) Qa1. rreg HS (12%bv : bv 5) Qa2. rreg HS (1%bv : bv 5) Qra.
rreg HS (2%bv : bv 5) Qsp2. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 337168) with (Z_to_bv 64 A_asan_memset).
eapply SRr_bind.
{ eapply (p1_memset fy _ _ _ 72 0x8548c HJ3);
[ first [rewrite Qa0, ?(AG 2%nat) by lia; rewrite U2; reflexivity | rewrite Qa0, ?(AG 2%nat) by lia; rewrite (HE 2%nat 2%bv eq_refl), G2; unfold w64; f_equal; lia] | exact Qa1 | exact Qa2 | exact Qra | vm_compute; reflexivity
| rewrite Qsp2, ?(AG 2%nat) by lia; rewrite (HE 2%nat 2%bv eq_refl); exact G2
| rewrite Qgp, ?(AG 3%nat) by lia; rewrite (HE 3%nat 3%bv eq_refl); exact Ggp
| rewrite Qtp, ?(AG 4%nat) by lia; rewrite (HE 4%nat 4%bv eq_refl); exact Gtp | lia | lia ]. }
cbv beta. intros W' c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Zn4 & KM4 & PM4).
clear Qa0 Qa1 Qa2 Qra Qsp2 Qgp Qtp.
reseat HS HJ4 HP4 (@nil nat) AG ltac:(idtac).
lazymatch type of M3r with p1_mid ?zs ?m0 =>
pose proof (p1_mid_set zs m0 mem4 72 PE ltac:(intros d' Hd'; cbn [In] in Hd'; lia) ltac:(lia) ltac:(lia) M3r Zn4 KM4 PM4) as M4 end.
clear M3r Zn4 KM4 PM4 HJ3 SHOK.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msx) => assert (SHOK : sh_ok trbsegs l1_Bx [] Ex (mrestrict (w_H W2) (ms_mem msx))) by constructor end.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ4 end.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK nt_Bspan A_asan_memset.
{ apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr, HG.
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
lazymatch type of M4 with p1_mid ?zs _ => pose proof (p1_mid_run zs m0 m1 PE ltac:(intros d' Hd'; cbn [In] in Hd'; lia) M4
ltac:(intros a Ha; apply aview_eq_of; apply HFr; rewrite unsigned_lit_small by lia; intros (rr & Hin & _); destruct Hin)
ltac:(intros a Ha; exact (apresent_grows _ _ _ _ HG Ha))) as M4r end end.
clear HF HFr HG M4.
rreg HS (10%bv : bv 5) Qa0. rreg HS (11%bv : bv 5) Qa1. rreg HS (12%bv : bv 5) Qa2. rreg HS (1%bv : bv 5) Qra.
rreg HS (2%bv : bv 5) Qsp2. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 337168) with (Z_to_bv 64 A_asan_memset).
eapply SRr_bind.
{ eapply (p1_memset fy _ _ _ 48 0x854a0 HJ4);
[ first [rewrite Qa0, ?(AG 2%nat) by lia; rewrite U2; reflexivity | rewrite Qa0, ?(AG 2%nat) by lia; rewrite (HE 2%nat 2%bv eq_refl), G2; unfold w64; f_equal; lia] | exact Qa1 | exact Qa2 | exact Qra | vm_compute; reflexivity
| rewrite Qsp2, ?(AG 2%nat) by lia; rewrite (HE 2%nat 2%bv eq_refl); exact G2
| rewrite Qgp, ?(AG 3%nat) by lia; rewrite (HE 3%nat 3%bv eq_refl); exact Ggp
| rewrite Qtp, ?(AG 4%nat) by lia; rewrite (HE 4%nat 4%bv eq_refl); exact Gtp | lia | lia ]. }
cbv beta. intros W' c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Zn5 & KM5 & PM5).
clear Qa0 Qa1 Qa2 Qra Qsp2 Qgp Qtp.
reseat HS HJ5 HP5 (@nil nat) AG ltac:(idtac).
lazymatch type of M4r with p1_mid ?zs ?m0 =>
pose proof (p1_mid_set zs m0 mem5 48 PE ltac:(intros d' Hd'; cbn [In] in Hd'; lia) ltac:(lia) ltac:(lia) M4r Zn5 KM5 PM5) as M5 end.
clear M4r Zn5 KM5 PM5 HJ4 SHOK.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msx) => assert (SHOK : sh_ok trbsegs l1_Bx [] Ex (mrestrict (w_H W2) (ms_mem msx))) by constructor end.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ5 end.
aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK nt_Bspan TN_L1.
{ apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr, HG.
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
lazymatch type of M5 with p1_mid ?zs _ => pose proof (p1_mid_run zs m0 m1 PE ltac:(intros d' Hd'; cbn [In] in Hd'; lia) M5
ltac:(intros a Ha; apply aview_eq_of; apply HFr; rewrite unsigned_lit_small by lia; intros (rr & Hin & _); destruct Hin)
ltac:(intros a Ha; exact (apresent_grows _ _ _ _ HG Ha))) as M6 end end.
clear HF HFr HG M5.
destruct M6 as (K6 & P6 & Vmin6 & Vmax6 & Z6).
assert (HES : ESTACK = 4096) by reflexivity.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msF := msx) in * end.
rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4. rreg HS (8%bv : bv 5) Q8. rreg HS (9%bv : bv 5) Q9.
rreg HS (18%bv : bv 5) Q18. rreg HS (19%bv : bv 5) Q19. rreg HS (20%bv : bv 5) Q20. rreg HS (21%bv : bv 5) Q21. rreg HS (22%bv : bv 5) Q22.
rreg HS (23%bv : bv 5) Q23. rreg HS (24%bv : bv 5) Q24. rreg HS (25%bv : bv 5) Q25. rreg HS (26%bv : bv 5) Q26. rreg HS (27%bv : bv 5) Q27.
rreg HS (13%bv : bv 5) Q13. rreg HS (14%bv : bv 5) Q14.
rreg_byA HS (11%bv : bv 5) (Z_to_bv 64 (3 * imin)) Q11.
{ apply denot_of_U'. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SOff, U_SLit. rewrite (AG 20%nat) by lia. rewrite U20, Z.add_0_r.
rewrite (zcanon_id imin), (zcanon_id 3) by (unfold M64; clear - Hii Himax; lia). rewrite zcanon_id by (unfold M64; clear - Hii Himax; lia). lia. }
rreg_byA HS (12%bv : bv 5) (Z_to_bv 64 (2 ^ 64 - 1 - frp)) Q12.
{ apply denot_of_U'. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit. rewrite (AG 21%nat) by lia.
rewrite (HE 21%nat 21%bv eq_refl), G21. unfold w64. rewrite unsigned_lit_small by (clear - Rfrp Hlenf Hii; lia). rewrite Z.add_0_r.
rewrite (zcanon_id frp) by (unfold M64; clear - Rfrp Hlenf Hii; lia). change (zcanon (-1)) with (2 ^ 64 - 1).
rewrite ntd_lxor_ones64 by (clear - Rfrp Hlenf Hii; lia). apply zcanon_id. unfold M64. clear - Rfrp Hlenf Hii. lia. }
rewrite (st_ok_restrict_mkst trbsegs (w_H W2) _ _ msF HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs msF), (ms_mem msF). eexists. split; [reflexivity|].
split.
{ split; [exact HJ5|]. split; [exact Hfrm|].
split; [rewrite Q2, (AG 2%nat) by lia; rewrite (HE 2%nat 2%bv eq_refl); exact G2|].
split; [rewrite Q8, (AG 8%nat) by lia; rewrite (HE 8%nat 8%bv eq_refl); exact G8|].
split; [rewrite Q9, (AG 10%nat) by lia; rewrite (HE 10%nat 10%bv eq_refl); exact G10|].
split; [rewrite Q18, (AG 18%nat) by lia; rewrite (HE 18%nat 18%bv eq_refl); exact G18|].
split; [rewrite Q19, (AG 19%nat) by lia; rewrite (HE 19%nat 19%bv eq_refl); exact G19|].
split; [rewrite Q21, (AG 21%nat) by lia; rewrite (HE 21%nat 21%bv eq_refl); exact G21|].
split; [rewrite Q22, (AG 22%nat) by lia; rewrite (HE 22%nat 22%bv eq_refl); exact G22|].
split; [rewrite Q23, (AG 23%nat) by lia; rewrite (HE 23%nat 23%bv eq_refl); exact G23|].
split; [rewrite Q24; reflexivity|].
split; [rewrite Q25, (AG 2%nat) by lia; rewrite U2; reflexivity|].
split; [rewrite Q26, (AG 2%nat) by lia; rewrite U2; reflexivity|].
split.
{ intros rr Hrr. cbv [NT_KEPT In] in Hrr.
destruct Hrr as [<- | [<- | [<- | []]]];
[ rewrite Q3, (AG 3%nat) by lia; rewrite (HE 3%nat 3%bv eq_refl); apply GK; cbv; tauto
| rewrite Q4, (AG 4%nat) by lia; rewrite (HE 4%nat 4%bv eq_refl); apply GK; cbv; tauto
| rewrite Q27, (AG 27%nat) by lia; rewrite (HE 27%nat 27%bv eq_refl); apply GK; cbv; tauto ]. }
split.
- intros a Ha Hns Hnn. apply K6; [exact Ha | unfold NODE_SIZE in Hnn; clear - Hnn; lia | rewrite HES; clear - Hns WS; lia].
- exact P6. }
split; [rewrite Q14, (AG 20%nat) by lia; rewrite (HE 20%nat 20%bv eq_refl); exact G20|].
split; [exact Q11|].
split; [exact Q12|].
split; [rewrite Q13; reflexivity|].
split; [rewrite Q20, (AG 20%nat) by lia; rewrite (HE 20%nat 20%bv eq_refl); exact G20|].
split.
{ intros j Hj. apply val_mem_zero8. intros i Hi.
assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11) by (clear - Hj; lia).
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]].
- replace (spc + 8 * 0 + i) with (spc + 0 + (0 + i)) by lia. apply Z6; [cbn; tauto | clear - Hi; lia].
- replace (spc + 8 * 1 + i) with (spc + 0 + (8 + i)) by lia. apply Z6; [cbn; tauto | clear - Hi; lia].
- replace (spc + 8 * 2 + i) with (spc + 0 + (16 + i)) by lia. apply Z6; [cbn; tauto | clear - Hi; lia].
- replace (spc + 8 * 3 + i) with (spc + 24 + (0 + i)) by lia. apply Z6; [cbn; tauto | clear - Hi; lia].
- replace (spc + 8 * 4 + i) with (spc + 24 + (8 + i)) by lia. apply Z6; [cbn; tauto | clear - Hi; lia].
- replace (spc + 8 * 5 + i) with (spc + 24 + (16 + i)) by lia. apply Z6; [cbn; tauto | clear - Hi; lia].
- replace (spc + 8 * 6 + i) with (spc + 48 + (0 + i)) by lia. apply Z6; [cbn; tauto | clear - Hi; lia].
- replace (spc + 8 * 7 + i) with (spc + 48 + (8 + i)) by lia. apply Z6; [cbn; tauto | clear - Hi; lia].
- replace (spc + 8 * 8 + i) with (spc + 48 + (16 + i)) by lia. apply Z6; [cbn; tauto | clear - Hi; lia].
- replace (spc + 8 * 9 + i) with (spc + 72 + (0 + i)) by lia. apply Z6; [cbn; tauto | clear - Hi; lia].
- replace (spc + 8 * 10 + i) with (spc + 72 + (8 + i)) by lia. apply Z6; [cbn; tauto | clear - Hi; lia].
- replace (spc + 8 * 11 + i) with (spc + 72 + (16 + i)) by lia. apply Z6; [cbn; tauto | clear - Hi; lia]. }
split; [exact Vmin6|]. split; [exact Vmax6|].
apply (saved_ok_kept memM _ HSV). intros a Ha. apply K6; [clear - Ha Qsp Qsp47 C1; lia | clear - Ha Qr1 Qsp; lia | clear - Ha; lia].
Qed.
End g.

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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC20 YC4z.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP14 YI08 YI0c YI0g YI0d YI0f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC68 YC60 YC5y YC61 YC5z YC65.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LDL_INVR : list (bv 5) := [31; 25; 9; 7; 15; 17; 29; 28; 30; 11; 5]%bv.
Definition LDL_CLOB : list (bv 5) := [1; 6; 10; 12; 13; 14; 16; 20; 21; 22; 23; 24; 26; 27]%bv.
Definition LDL_KEEP : list (bv 5) := [2; 3; 4; 5; 7; 8; 9; 11; 15; 17; 18; 19; 25; 28; 29; 30; 31]%bv.
Definition LDL_FKEEP : list (bv 5) := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Section c.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trasegs).
Variables (flt nF s1v fmt N Wd pal pimg pg pn v40 v96 v128 g15 g30 d2 d3 d4 cid pos : Z) (t : tree).
Hypothesis HinF : In (flt, nF) (ablocks B lyc Sc).
Hypothesis HFW : forall blc lyq ownq j, In (flt, nF) blc -> 0 <= j < req_size nF -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (flt + j).
Hypothesis Hs1lo : sp0 - STK <= s1v. Hypothesis Hs1hi : s1v + 384 <= sp0.
Hypothesis Hfmt : 3 <= fmt < 2 ^ 29. Hypothesis HN : 0 < N <= 2 ^ 29. Hypothesis HfN : fmt * N <= 2 ^ 29.
Hypothesis HWd : 0 < Wd < 2 ^ 31.
Hypothesis Hfr : In (cid, pos) (frames Sc). Hypothesis Hpal0 : frame_addr lyc cid pos <= pal. Hypothesis Hpal1 : pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid.
Hypothesis Hd2 : 0 <= d2 < 2 ^ 29. Hypothesis Hd3 : 0 <= d3 < 2 ^ 29. Hypothesis Hd4 : 0 <= d4 < 2 ^ 29.
Hypothesis Hg15 : 0 <= g15 < 2 ^ 64. Hypothesis Hg30 : 0 <= g30 < 2 ^ 64.
Hypothesis Hv40 : 0 <= v40 < 2 ^ 64. Hypothesis Hv96 : 0 <= v96 < 2 ^ 64. Hypothesis Hv128 : 0 <= v128 < 2 ^ 64.
Hypothesis HinG : In (pg, pn) (ablocks B lyc Sc). Hypothesis HG0 : pg <= pimg. Hypothesis HG1 : pimg + N <= pg + pn.
Hypothesis HGF : (pg, pn) <> (flt, nF).
Hypothesis HGW : forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j).
Hypothesis Hfull : tree_full t. Hypothesis Hwf : tree_forall tnode_wf t.
Hypothesis Htin : forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc).
Hypothesis Htnf : forall b, In b (tree_blocks t) -> b <> (flt, nF).
Hypothesis Htng : forall b, In b (tree_blocks t) -> b <> (pg, pn).
Hypothesis HlenC : 4 * (fmt * N) <= nF.
Hypothesis HK1 : forall i j, 0 <= i < N -> 0 <= j < 3 -> i mod Wd < g15 -> 4 * (fmt * i + j + fmt) + 4 <= nF.
Hypothesis HK2 : forall i j, 0 <= i < N -> 0 <= j < 3 -> i < g30 -> 4 * (fmt * i + j + d2) + 4 <= nF.
Hypothesis HK3 : forall i j, 0 <= i < N -> 0 <= j < 3 -> i < g30 -> i mod Wd <> 0 -> 4 * (fmt * i + j + d3) + 4 <= nF.
Hypothesis HK4 : forall i j, 0 <= i < N -> 0 <= j < 3 -> i < g30 -> i mod Wd < g15 -> 4 * (fmt * i + j + d4) + 4 <= nF.
Definition ldl_regs (regs : bvmap 5 word) : Prop :=
getr regs 31 = w64 flt /\ getr regs 25 = w64 SB /\ getr regs 9 = w64 s1v /\ getr regs 7 = w64 N /\ getr regs 15 = w64 g15 /\
getr regs 17 = w64 d2 /\ getr regs 29 = w64 d3 /\ getr regs 28 = w64 d4 /\ getr regs 30 = w64 g30 /\
getr regs 11 = w64 (troot t + 50) /\ getr regs 5 = Z_to_bv 64 (SB + (troot t + 50) / 8).
Definition ldl_mem (mem : word -> option byte) : Prop :=
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 40) 8 v40 /\ val_mem trasegs (mrestrict (w_H W) mem) (s1v + 96) 8 v96 /\
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 128) 8 v128 /\ val_mem trasegs (mrestrict (w_H W) mem) (s1v + 160) 8 Wd /\
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 240) 8 (troot t) /\ val_mem trasegs (mrestrict (w_H W) mem) (s1v + 296) 8 fmt /\
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 360) 8 pal /\ val_mem trasegs (mrestrict (w_H W) mem) (s1v + 376) 8 pimg /\
tree_at trasegs (mrestrict (w_H W) mem) t.
Definition ldl_inv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (i : Z) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\ frm_zero (@fp_csr fy) /\
ldl_regs regs /\ getr regs 10 = w64 fmt /\ getr regs 16 = w64 i /\ getr regs 14 = w64 (fmt * i) /\
getr regs 24 = w64 v128 /\ getr regs 26 = w64 v96 /\ getr regs 27 = w64 v40 /\ ldl_mem mem.
Lemma ldl_regs_kept : forall regs regs' : bvmap 5 word, (forall r : bv 5, In r LDL_INVR -> getr regs' r = getr regs r) -> ldl_regs regs -> ldl_regs regs'.
Proof.
intros regs regs' HK (R31 & R25 & R9 & R7 & R15 & R17 & R29 & R28 & R30 & R11 & R5). unfold ldl_regs.
rewrite (HK (31%bv : bv 5) ltac:(cbv; tauto)), (HK (25%bv : bv 5) ltac:(cbv; tauto)), (HK (9%bv : bv 5) ltac:(cbv; tauto)),
(HK (7%bv : bv 5) ltac:(cbv; tauto)), (HK (15%bv : bv 5) ltac:(cbv; tauto)), (HK (17%bv : bv 5) ltac:(cbv; tauto)),
(HK (29%bv : bv 5) ltac:(cbv; tauto)), (HK (28%bv : bv 5) ltac:(cbv; tauto)), (HK (30%bv : bv 5) ltac:(cbv; tauto)),
(HK (11%bv : bv 5) ltac:(cbv; tauto)), (HK (5%bv : bv 5) ltac:(cbv; tauto)).
repeat split; assumption.
Qed.
Lemma ldl_mem_kept : forall (mem mem' : word -> option byte) md,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> ~ (pg <= a < pg + pn) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
ldl_mem mem -> ldl_mem mem'.
Proof.
intros mem mem' md HJ HM (V40 & V96 & V128 & V160 & V240 & V296 & V360 & V376 & Hat). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Hg4096 & Hgceil & _ & _ & _ & Hpn0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & Hf4096 & Hfceil & _ & _ & _ & Hnf0).
pose proof (req_size_pos pn ltac:(lia)) as [_ Hrg]. pose proof (req_size_pos nF ltac:(lia)) as [_ Hrf].
assert (Rs : 2 ^ 46 <= s1v /\ s1v + 384 <= 2 ^ 47 /\ alloc_ceiling <= s1v) by (clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1; lia).
assert (SLOT : forall off v, 0 <= off -> off + 8 <= 384 -> val_mem trasegs (mrestrict (w_H W) mem) (s1v + off) 8 v -> val_mem trasegs (mrestrict (w_H W) mem') (s1v + off) 8 v).
{ intros off v Ho0 Ho1 V. apply (YC04.val_mem_kept trasegs (w_H W) (w_H W) mem mem' (s1v + off) 8 v); [|exact V].
intros j Hj. apply HM; [clear - Hj Rs Ho0 Ho1; lia | clear - Hj Rs Ho0 Ho1 Hfceil Hrf; lia | clear - Hj Rs Ho0 Ho1 Hgceil Hrg; lia]. }
split; [apply SLOT; [lia | lia | exact V40]|]. split; [apply SLOT; [lia | lia | exact V96]|]. split; [apply SLOT; [lia | lia | exact V128]|].
split; [apply SLOT; [lia | lia | exact V160]|]. split; [apply SLOT; [lia | lia | exact V240]|]. split; [apply SLOT; [lia | lia | exact V296]|].
split; [apply SLOT; [lia | lia | exact V360]|]. split; [apply SLOT; [lia | lia | exact V376]|].
apply (rg_tree_at_kept (w_H W) (w_H W) mem mem' t Hat). intros b sz Hb j Hj.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b sz HAR (Htin _ Hb)) as (_ & Hb4096 & Hbceil & _).
pose proof (sep_blocks trasegs _ LAWS lyc Sc _ _ _ b sz pg pn HAR (Htin _ Hb) HinG (Htng _ Hb)) as Hd1. unfold zdisjoint in Hd1. cbn [fst snd] in Hd1.
pose proof (sep_blocks trasegs _ LAWS lyc Sc _ _ _ b sz flt nF HAR (Htin _ Hb) HinF (Htnf _ Hb)) as Hd2'. unfold zdisjoint in Hd2'. cbn [fst snd] in Hd2'.
apply HM; [clear - Hj Hb4096 Hbceil C1; lia | clear - Hj Hd2' Hrf; lia | clear - Hj Hd1 Hrg; lia].
Qed.
Definition LDL_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc i' : Z) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trasegs)) md' /\
ldl_inv fy' regs' mem' md' i' /\
(forall r : bv 5, In r LDL_KEEP -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LDL_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> ~ (pg <= a < pg + pn) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma ldl_post_trans : forall fy regs mem (fy1 : FPState) regs1 mem1 pc i' W' c',
(forall r : bv 5, In r LDL_KEEP -> getr regs1 r = getr regs r) ->
(forall r : bv 5, In r LDL_FKEEP -> reg_get (@fp_regs fy1) r = reg_get (@fp_regs fy) r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> ~ (pg <= a < pg + pn) -> aview trasegs (w_H W) mem1 a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
LDL_post fy1 regs1 mem1 pc i' W' c' -> LDL_post fy regs mem pc i' W' c'.
Proof.
intros fy regs mem fy1 regs1 mem1 pc i' W' c' K1 F1 M1 X1 (HW & fy' & regs' & mem' & md' & Hc & HI & K & F & M & X).
split; [exact HW|]. exists fy', regs', mem', md'. split; [exact Hc|]. split; [exact HI|].
split; [intros r Hr; rewrite (K r Hr); exact (K1 r Hr)|]. split; [intros r Hr; rewrite (F r Hr); exact (F1 r Hr)|].
split; [intros a Ha Hn1 Hn2; rewrite (M a Ha Hn1 Hn2); exact (M1 a Ha Hn1 Hn2)|]. intros a Ha. apply X. apply X1. exact Ha.
Qed.
Definition ldl_mid (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (i : Z) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\ frm_zero (@fp_csr fy) /\
ldl_regs regs /\ getr regs 10 = w64 fmt /\ getr regs 22 = w64 (i + 1) /\ getr regs 14 = w64 (fmt * i) /\
getr regs 24 = w64 v128 /\ getr regs 26 = w64 v96 /\ getr regs 27 = w64 v40 /\ ldl_mem mem.
Lemma LDL_T2 : forall (i : Z) (fy : FPState) regs mem md, 0 <= i < N -> ldl_mid fy regs mem md i ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDGS_T2) mem (seg_rom trasegs)) md)
(LDL_post fy regs mem (if i + 1 =? N then LDGS_EXIT else LDGS_LH) (i + 1)).
Proof.
intros i fy regs mem md Hi (HJ & Hfrm & HR & G10 & G22 & G14 & G24 & G26 & G27 & HMm).
pose proof HR as (R31 & R25 & R9 & R7 & _).
assert (Hfi : 0 <= fmt * i /\ fmt * i <= fmt * (N - 1) /\ fmt * (N - 1) + fmt = fmt * N).
{ split; [apply Z.mul_nonneg_nonneg; lia|]. split; [apply Z.mul_le_mono_nonneg_l; lia | lia]. }
assert (HB : ldgs_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v fy regs mem md) by (split; [exact HJ|]; split; [exact Hfrm|]; split; assumption).
eapply SRr_mono; [exact (LDGS_T2_run B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v fy regs mem md (fmt * i) fmt (i + 1) N HB G14 G10 G22 R7
ltac:(clear - Hfi HfN Hfmt; lia) ltac:(clear - Hfmt; lia) ltac:(clear - Hi HN; lia) ltac:(clear - HN; lia))|].
intros W' c' _ (HW & fy' & regs' & mem' & md' & Hc & (HJ' & Hfrm' & _) & (R14' & R16') & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs', mem', md'. split; [exact Hc|].
split.
{ split; [exact HJ'|]. split; [exact Hfrm'|].
split; [apply (ldl_regs_kept regs regs'); [intros r Hr; apply HK; revert Hr; clear; cbv [LDL_INVR LDGS_KEEP_T2 In]; tauto | exact HR]|].
split; [rewrite (HK (10%bv : bv 5) ltac:(cbv; tauto)); exact G10|]. split; [exact R16'|].
split; [rewrite R14'; unfold w64; f_equal; lia|].
split; [rewrite (HK (24%bv : bv 5) ltac:(cbv; tauto)); exact G24|]. split; [rewrite (HK (26%bv : bv 5) ltac:(cbv; tauto)); exact G26|].
split; [rewrite (HK (27%bv : bv 5) ltac:(cbv; tauto)); exact G27|].
apply (ldl_mem_kept mem mem' md HJ); [intros a Ha _ _; exact (HM a Ha) | exact HMm]. }
split; [intros r Hr; apply HK; revert Hr; clear; cbv [LDL_KEEP LDGS_KEEP_T2 In]; tauto|].
split; [intros r _; apply HF|]. split; [intros a Ha _ _; exact (HM a Ha) | exact HX].
Qed.
Definition LDL_CORER : list (bv 5) := (14%bv : bv 5) :: (16%bv : bv 5) :: LDL_INVR.
Definition ldl_core (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (i : Z) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\ frm_zero (@fp_csr fy) /\
ldl_regs regs /\ getr regs 16 = w64 i /\ getr regs 14 = w64 (fmt * i) /\ ldl_mem mem.
Lemma ldl_core_kept : forall (fy : FPState) regs mem md i (fy' : FPState) regs' mem' md',
ldl_core fy regs mem md i ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k -> frm_zero (@fp_csr fy') ->
(forall r : bv 5, In r LDL_CORER -> getr regs' r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> ~ (pg <= a < pg + pn) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
ldl_core fy' regs' mem' md' i.
Proof.
intros fy regs mem md i fy' regs' mem' md' (HJ & Hfrm & HR & G16 & G14 & HMm) HJ' Hfrm' HK HM.
split; [exact HJ'|]. split; [exact Hfrm'|].
split; [apply (ldl_regs_kept regs regs'); [intros r Hr; apply HK; right; right; exact Hr | exact HR]|].
split; [rewrite (HK (16%bv : bv 5) ltac:(cbv; tauto)); exact G16|]. split; [rewrite (HK (14%bv : bv 5) ltac:(cbv; tauto)); exact G14|].
exact (ldl_mem_kept mem mem' md HJ HM HMm).
Qed.
Section e.
Variable i : Z.
Hypothesis Hi : 0 <= i < N.
Lemma ldl_fi : 0 <= fmt * i /\ fmt * i + fmt <= fmt * N.
Proof. split; [apply Z.mul_nonneg_nonneg; lia|]. replace (fmt * i + fmt) with (fmt * (i + 1)) by lia. apply Z.mul_le_mono_nonneg_l; lia. Qed.
Lemma LDL_K : forall (fy : FPState) regs mem md, ldl_core fy regs mem md i ->
getr regs 24 = w64 3 -> getr regs 26 = w64 (fmt * i) -> getr regs 27 = w64 pal -> getr regs 12 = w64 (pimg + i) ->
getr regs 20 = Z_to_bv 64 (SB + (pimg + i) / 8) -> getr regs 23 = w64 (i mod Wd) -> getr regs 22 = w64 (i + 1) ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_HEAD) mem (seg_rom trasegs)) md)
(LDL_post fy regs mem (if i + 1 =? N then LDGS_EXIT else LDGS_LH) (i + 1)).
Proof.
intros fy regs mem md HC G24 G26 G27 G12 G20 G23 G22. pose proof HC as (HJ & Hfrm & HR & G16 & G14 & HMm).
pose proof HR as (R31 & R25 & R9 & R7 & R15 & R17 & R29 & R28 & R30 & R11 & R5).
pose proof HMm as (V40 & V96 & V128 & V160 & V240 & V296 & V360 & V376 & Hat).
pose proof ldl_fi as (Hfi0 & Hfi1).
pose proof (Z.mod_pos_bound i Wd ltac:(lia)) as Hmod.
eapply SRr_bind.
{ apply (rga_ldi_kloop B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF pg pn (pimg + i) cid pos s1v fmt d2 d3 d4 g15 i (i mod Wd) g30 3 (fmt * i) pal
fy regs mem md HJ Hfrm HinF HFW HinG ltac:(lia) ltac:(lia) HGF Hfr Hpal0 ltac:(lia) ltac:(lia) ltac:(lia) V296
ltac:(lia) Hd2 Hd3 Hd4 Hg15 ltac:(lia) ltac:(lia) Hg30 ltac:(lia) Hfi0 ltac:(clear - Hfi1 HfN Hfmt; lia)).
- intros j Hj. clear - Hj Hfi1 HlenC Hfmt. lia.
- intros j Hj Hg. exact (HK1 i j Hi Hj Hg).
- intros j Hj Hg. exact (HK2 i j Hi Hj Hg).
- intros j Hj Hg Hg'. exact (HK3 i j Hi Hj Hg Hg').
- intros j Hj Hg Hg'. exact (HK4 i j Hi Hj Hg Hg').
- exact G24. - exact G26. - exact G27. - exact R9. - exact G12. - exact G20. - exact R15. - exact G16. - exact G23. - exact R30.
- exact R17. - exact R29. - exact R28. - exact R31. - exact R25. }
intros W1 c1 _ (-> & fy1 & regs1 & mem1 & md1 & -> & Hfrm1 & HJ1 & HK1' & HF1 & _ & _ & _ & HM1 & HX1).
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> ~ (pg <= a < pg + pn) -> aview trasegs (w_H W) mem1 a = aview trasegs (w_H W) mem a)
by (intros a Ha Hn1 _; exact (HM1 a Ha Hn1)).
assert (HC1 : ldl_core fy1 regs1 mem1 md1 i).
{ apply (ldl_core_kept fy regs mem md i fy1 regs1 mem1 md1 HC HJ1 Hfrm1); [|exact M1].
intros r Hr. apply HK1'. revert Hr. clear. cbv [LDL_CORER LDL_INVR In]. intros Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
pose proof HC1 as (_ & _ & HR1 & G16a & G14a & HMm1). pose proof HR1 as (_ & R25a & R9a & _).
pose proof HMm1 as (V40a & V96a & V128a & _ & _ & V296a & _).
assert (HB1 : ldgs_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v fy1 regs1 mem1 md1) by (split; [exact HJ1|]; split; [exact Hfrm1|]; split; assumption).
eapply SRr_bind; [exact (LDGS_T1_run B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v Hs1lo Hs1hi fy1 regs1 mem1 md1 v40 v96 v128 fmt HB1 Hv40 Hv96 Hv128 ltac:(lia) V40a V96a V128a V296a)|].
intros W2 c2 _ (-> & fy2 & regs2 & mem2 & md2 & -> & (HJ2 & Hfrm2 & _) & (Q27 & Q26 & Q24 & Q10) & HK2' & HF2 & HM2 & HX2).
assert (M2 : forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> ~ (pg <= a < pg + pn) -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) mem1 a)
by (intros a Ha _ _; exact (HM2 a Ha)).
assert (HC2 : ldl_core fy2 regs2 mem2 md2 i).
{ apply (ldl_core_kept fy1 regs1 mem1 md1 i fy2 regs2 mem2 md2 HC1 HJ2 Hfrm2); [|exact M2].
intros r Hr. apply HK2'. revert Hr. clear. cbv [LDL_CORER LDL_INVR LDGS_KEEP_T1 In]. tauto. }
assert (HMID : ldl_mid fy2 regs2 mem2 md2 i).
{ destruct HC2 as (HJc & Hfrmc & HRc & _ & G14c & HMmc). split; [exact HJc|]. split; [exact Hfrmc|]. split; [exact HRc|]. split; [exact Q10|].
split; [rewrite (HK2' (22%bv : bv 5) ltac:(cbv; tauto)), (HK1' (22%bv : bv 5) eq_refl); exact G22|].
split; [exact G14c|]. split; [exact Q24|]. split; [exact Q26|]. split; [exact Q27 | exact HMmc]. }
eapply SRr_mono; [exact (LDL_T2 i fy2 regs2 mem2 md2 Hi HMID)|].
intros W3 c3 _ H. apply (ldl_post_trans fy regs mem fy2 regs2 mem2 _ _ W3 c3); [| | | | exact H].
- intros r Hr. rewrite (HK2' r ltac:(revert Hr; clear; cbv [LDL_KEEP LDGS_KEEP_T1 In]; tauto)). apply HK1'. revert Hr. clear. cbv [LDL_KEEP In]. intros Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr.
- intros r Hr. rewrite (HF2 r). apply HF1. revert Hr. clear. cbv [LDL_FKEEP LDK_FKEEP In]. tauto.
- intros a Ha Hn1 Hn2. rewrite (M2 a Ha Hn1 Hn2). exact (M1 a Ha Hn1 Hn2).
- intros a Ha. apply HX2. apply HX1. exact Ha.
Qed.
Lemma LDL_LEAF : forall (fy : FPState) regs mem md (nl : tnode), ldl_core fy regs mem md i ->
getr regs 21 = w64 (tn_addr nl) -> In nl (tree_leaves t) ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDGL_LEAF) mem (seg_rom trasegs)) md)
(LDL_post fy regs mem (if i + 1 =? N then LDGS_EXIT else LDGS_LH) (i + 1)).
Proof.
intros fy regs mem md nl HC G21 Hnl. pose proof HC as (HJ & Hfrm & HR & G16 & G14 & HMm).
pose proof HR as (R31 & R25 & R9 & R7 & R15 & R17 & R29 & R28 & R30 & R11 & R5).
pose proof HMm as (V40 & V96 & V128 & V160 & V240 & V296 & V360 & V376 & Hat).
destruct (lnl_leaf_obj _ t nl Hat Hnl) as (c0 & c1 & lv & Ond & Hlen3 & Hnb).
pose proof HJ as (HAR & _). pose proof asan_consts as (C1 & _).
destruct (frames_bounds trasegs B LAWS lyc Sc W mem md cid pos HAR Hfr) as (Hfr0 & Hfrc & _).
eapply SRr_bind.
{ exact (rga_ldi_leaf B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v (tn_addr nl) Wd pal pimg pg pn i nl c0 c1 lv fy regs mem md HJ Hfrm Hs1lo Hs1hi
(Htin _ Hnb) HinG HG0 ltac:(lia) (Htng _ Hnb) ltac:(lia) HWd ltac:(clear - Hpal0 Hpal1 Hfr0 Hfrc C1; lia) HGW V160 V360 V376 Ond Hlen3 G21 G16 R25 R9). }
intros W1 c1' _ (-> & fy1 & regs1 & mem1 & md1 & -> & Hfrm1 & HJ1 & Q12 & Q20 & Q23 & Q22 & Q24 & Q26 & Q27 & Q10 & HK1' & HF1 & HM1 & HX1).
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> ~ (pg <= a < pg + pn) -> aview trasegs (w_H W) mem1 a = aview trasegs (w_H W) mem a)
by (intros a Ha _ Hn2; apply HM1; [exact Ha | clear - Hn2 HG0 HG1 Hi; lia]).
assert (HC1 : ldl_core fy1 regs1 mem1 md1 i).
{ apply (ldl_core_kept fy regs mem md i fy1 regs1 mem1 md1 HC HJ1 Hfrm1); [|exact M1].
intros r Hr. apply HK1'. revert Hr. clear. cbv [LDL_CORER LDL_INVR LDGL_KEEP In]. tauto. }
eapply SRr_mono; [exact (LDL_K fy1 regs1 mem1 md1 HC1 Q24 ltac:(rewrite Q26; exact G14) Q27 Q12 Q20 Q23 Q22)|].
intros W3 c3 _ H. apply (ldl_post_trans fy regs mem fy1 regs1 mem1 _ _ W3 c3); [| | exact M1 | exact HX1 | exact H].
- intros r Hr. apply HK1'. revert Hr. clear. cbv [LDL_KEEP LDGL_KEEP In]. tauto.
- intros r _. apply HF1.
Qed.
Lemma LDL_ROOT : forall (fy : FPState) regs mem md, ldl_core fy regs mem md i ->
getr regs 13 = w64 (fmt * i) -> getr regs 10 = w64 (troot t) ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDG_ROOT) mem (seg_rom trasegs)) md)
(LDL_post fy regs mem (if i + 1 =? N then LDGS_EXIT else LDGS_LH) (i + 1)).
Proof.
intros fy regs mem md HC G13 G10. pose proof HC as (HJ & Hfrm & HR & G16 & G14 & HMm).
pose proof HR as (R31 & R25 & R9 & R7 & R15 & R17 & R29 & R28 & R30 & R11 & R5).
pose proof HMm as (V40 & V96 & V128 & V160 & V240 & V296 & V360 & V376 & Hat).
pose proof ldl_fi as (Hfi0 & Hfi1).
destruct (lnl_root_obj _ t Hfull Hat) as (n & c0 & c1 & leafv & Eroot & Hnb & Hlen3 & Ond & Hcase).
rewrite Eroot in G10, R11, R5.
assert (Hlv : leafv = 0 \/ leafv = 1) by (destruct Hcase as [[-> _] | [-> _]]; [right | left]; reflexivity).
eapply SRr_bind.
{ exact (rga_ldi_root B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF (tn_addr n) (fmt * i) n c0 c1 leafv fy regs mem md HJ Hfrm HinF (Htin _ Hnb)
ltac:(clear - Hfi0 Hfi1 HfN Hfmt; lia) ltac:(clear - Hfi1 HlenC Hfmt; lia) Ond Hlen3 Hlv G13 G10 R11 R5 R31 R25). }
intros W1 c1' _ (-> & fy1 & regs1 & mem1 & md1 & -> & Hfrm1 & HJ1 & HK1' & HF1 & R21 & R20 & HM1 & HX1).
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> ~ (pg <= a < pg + pn) -> aview trasegs (w_H W) mem1 a = aview trasegs (w_H W) mem a)
by (intros a Ha _ _; exact (HM1 a Ha)).
assert (HC1 : ldl_core fy1 regs1 mem1 md1 i).
{ apply (ldl_core_kept fy regs mem md i fy1 regs1 mem1 md1 HC HJ1 Hfrm1); [|exact M1].
intros r Hr. apply HK1'. revert Hr. clear. cbv [LDL_CORER LDL_INVR In]. intros Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
assert (K1 : forall r : bv 5, In r LDL_KEEP -> getr regs1 r = getr regs r).
{ intros r Hr. apply HK1'. revert Hr. clear. cbv [LDL_KEEP In]. intros Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
assert (F1 : forall r : bv 5, In r LDL_FKEEP -> reg_get (@fp_regs fy1) r = reg_get (@fp_regs fy) r) by (intros r _; apply HF1).
destruct Hcase as [[-> Et] | [-> (l & r0 & Et)]]; cbn [Z.eqb].
-
eapply SRr_mono; [exact (LDL_LEAF fy1 regs1 mem1 md1 n HC1 R21 ltac:(rewrite Et; left; reflexivity))|].
intros W3 c3 _ H. exact (ldl_post_trans fy regs mem fy1 regs1 mem1 _ _ W3 c3 K1 F1 M1 HX1 H).
-
pose proof HC1 as (_ & _ & HR1 & _ & _ & HMm1). pose proof HR1 as (_ & R25a & _). pose proof HMm1 as (_ & _ & _ & _ & _ & _ & _ & _ & Hat1).
pose proof HJ1 as (HAR1 & _). destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR1 HinF) as (Hf16 & _).
assert (Hr4 : (flt + 4 * (fmt * i)) mod 4 = 0).
{ replace (flt + 4 * (fmt * i)) with (flt + (fmt * i) * 4) by lia. rewrite Z.mod_add by lia.
clear - Hf16. pose proof (Z.mod_pos_bound flt 16 ltac:(lia)). pose proof (Z.div_mod flt 16 ltac:(lia)).
replace flt with (4 * (4 * (flt / 16))) by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
eapply SRr_bind.
{ exact (rga_ldi_descent B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF (flt + 4 * (fmt * i)) t fy1 regs1 mem1 md1 HJ1 Hfrm1 HinF
ltac:(clear - Hfi0; lia) ltac:(clear - Hfi1 HlenC Hfmt; lia) Hr4 Hfull Hwf Hat1 Htin Htnf ltac:(exists n, l, r0; exact Et)
ltac:(rewrite Eroot; exact R21) (R20 eq_refl) R25a). }
intros W2 c2 _ (-> & fy2 & regs2 & mem2 & md2 & -> & Hfrm2 & HJ2 & HK2' & HF2 & (nl & Hnl & R21b) & HM2 & HX2).
assert (M2 : forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> ~ (pg <= a < pg + pn) -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) mem1 a)
by (intros a Ha _ _; exact (HM2 a Ha)).
assert (HC2 : ldl_core fy2 regs2 mem2 md2 i).
{ apply (ldl_core_kept fy1 regs1 mem1 md1 i fy2 regs2 mem2 md2 HC1 HJ2 Hfrm2); [|exact M2].
intros r Hr. apply HK2'. revert Hr. clear. cbv [LDL_CORER LDL_INVR In]. intros Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
eapply SRr_mono; [exact (LDL_LEAF fy2 regs2 mem2 md2 nl HC2 R21b Hnl)|].
intros W3 c3 _ H. apply (ldl_post_trans fy regs mem fy2 regs2 mem2 _ _ W3 c3); [| | | | exact H].
+ intros r Hr. rewrite <- (K1 r Hr). apply HK2'. revert Hr. clear. cbv [LDL_KEEP In]. intros Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr.
+ intros r Hr. rewrite <- (F1 r Hr). apply HF2. revert Hr. clear. cbv [LDL_FKEEP LDD_FKEEP In]. tauto.
+ intros a Ha Hn1 Hn2. rewrite (M2 a Ha Hn1 Hn2). exact (M1 a Ha Hn1 Hn2).
+ intros a Ha. apply HX2. apply HX1. exact Ha.
Qed.
Lemma LDL_CLAMP : forall (fy : FPState) regs mem md, ldl_core fy regs mem md i ->
getr regs 20 = w64 3 -> getr regs 21 = w64 (fmt * i) -> getr regs 13 = w64 (fmt * i) -> getr regs 10 = w64 (troot t) ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDC_HEAD) mem (seg_rom trasegs)) md)
(LDL_post fy regs mem (if i + 1 =? N then LDGS_EXIT else LDGS_LH) (i + 1)).
Proof.
intros fy regs mem md HC G20 G21 G13 G10. pose proof HC as (HJ & Hfrm & HR & G16 & G14 & HMm).
pose proof HR as (R31 & R25 & _). pose proof ldl_fi as (Hfi0 & Hfi1).
eapply SRr_bind.
{ exact (rga_ldi_clamp B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF 3 (fmt * i) fy regs mem md HJ Hfrm HinF HFW ltac:(lia) Hfi0
ltac:(clear - Hfi1 HfN Hfmt; lia) ltac:(clear - Hfi1 HlenC Hfmt; lia) G20 G21 R31 R25). }
intros W1 c1' _ (-> & fy1 & regs1 & mem1 & md1 & -> & Hfrm1 & HJ1 & HK1' & HF1 & _ & _ & HM1 & HX1).
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> ~ (pg <= a < pg + pn) -> aview trasegs (w_H W) mem1 a = aview trasegs (w_H W) mem a)
by (intros a Ha Hn1 _; apply HM1; [exact Ha | clear - Hn1 Hfi0 Hfi1 HlenC Hfmt; lia]).
assert (HC1 : ldl_core fy1 regs1 mem1 md1 i).
{ apply (ldl_core_kept fy regs mem md i fy1 regs1 mem1 md1 HC HJ1 Hfrm1); [|exact M1].
intros r Hr. apply HK1'. revert Hr. clear. cbv [LDL_CORER LDL_INVR In]. intros Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
eapply SRr_mono; [exact (LDL_ROOT fy1 regs1 mem1 md1 HC1 ltac:(rewrite (HK1' (13%bv : bv 5) eq_refl); exact G13) ltac:(rewrite (HK1' (10%bv : bv 5) eq_refl); exact G10))|].
intros W3 c3 _ H. apply (ldl_post_trans fy regs mem fy1 regs1 mem1 _ _ W3 c3); [| | exact M1 | exact HX1 | exact H].
- intros r Hr. apply HK1'. revert Hr. clear. cbv [LDL_KEEP In]. intros Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr.
- intros r Hr. apply HF1. revert Hr. clear. cbv [LDL_FKEEP LDC_FKEEP In]. tauto.
Qed.
Lemma LDL_C0 : forall (fy : FPState) regs mem md, ldl_core fy regs mem md i -> getr regs 10 = w64 fmt ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDGS_C0) mem (seg_rom trasegs)) md)
(LDL_post fy regs mem (if i + 1 =? N then LDGS_EXIT else LDGS_LH) (i + 1)).
Proof.
intros fy regs mem md HC G10. pose proof HC as (HJ & Hfrm & HR & G16 & G14 & HMm).
pose proof HR as (R31 & R25 & R9 & _). pose proof HMm as (V40 & V96 & V128 & V160 & V240 & V296 & V360 & V376 & Hat).
destruct (lnl_root_obj _ t Hfull Hat) as (n & c0 & c1 & leafv & Eroot & Hnb & _ & _ & _).
pose proof HJ as (HAR & _). pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR (Htin _ Hnb)) as (_ & Hn4096 & Hnceil & _). change (req_size NODE_SIZE) with 56 in Hnceil.
assert (HB : ldgs_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v fy regs mem md) by (split; [exact HJ|]; split; [exact Hfrm|]; split; assumption).
eapply SRr_bind.
{ exact (LDGS_C0_run B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v Hs1lo Hs1hi fy regs mem md fmt i (troot t) HB G10 G16 ltac:(lia) ltac:(lia)
ltac:(rewrite Eroot; clear - Hn4096 Hnceil C1; lia) V240). }
intros W1 c1' _ (-> & fy1 & regs1 & mem1 & md1 & -> & (HJ1 & Hfrm1 & _) & (Q13 & Q20 & Q21 & Q10) & HK1' & HF1 & HM1 & HX1).
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> ~ (pg <= a < pg + pn) -> aview trasegs (w_H W) mem1 a = aview trasegs (w_H W) mem a)
by (intros a Ha _ _; exact (HM1 a Ha)).
assert (HC1 : ldl_core fy1 regs1 mem1 md1 i).
{ apply (ldl_core_kept fy regs mem md i fy1 regs1 mem1 md1 HC HJ1 Hfrm1); [|exact M1].
intros r Hr. apply HK1'. revert Hr. clear. cbv [LDL_CORER LDL_INVR LDGS_KEEP_C0 In]. tauto. }
eapply SRr_mono; [exact (LDL_CLAMP fy1 regs1 mem1 md1 HC1 Q20 ltac:(rewrite Q21; exact G14) Q13 Q10)|].
intros W3 c3 _ H. apply (ldl_post_trans fy regs mem fy1 regs1 mem1 _ _ W3 c3); [| | exact M1 | exact HX1 | exact H].
- intros r Hr. apply HK1'. revert Hr. clear. cbv [LDL_KEEP LDGS_KEEP_C0 In]. tauto.
- intros r _. apply HF1.
Qed.
Lemma LDL_pixel : forall (fy : FPState) regs mem md, ldl_inv fy regs mem md i ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDGA_LH) mem (seg_rom trasegs)) md)
(LDL_post fy regs mem (if i + 1 =? N then LDGS_EXIT else LDGS_LH) (i + 1)).
Proof.
intros fy regs mem md (HJ & Hfrm & HR & G10 & G16 & G14 & G24 & G26 & G27 & HMm).
pose proof HR as (R31 & R25 & R9 & _). pose proof HMm as (V40 & V96 & V128 & V160 & V240 & V296 & V360 & V376 & Hat).
assert (HC : ldl_core fy regs mem md i) by (split; [exact HJ|]; split; [exact Hfrm|]; split; [exact HR|]; split; [exact G16|]; split; [exact G14 | exact HMm]).
eapply SRr_bind.
{ apply (rga_ldi_head B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v pimg pg pn i fmt fy regs mem md HJ Hfrm HinF Hs1lo Hs1hi HinG HG0
ltac:(lia) HGF ltac:(lia) HGW ltac:(lia)); [ | exact V376 | exact G10 | exact G16 | exact R31 | exact R25 | exact R9 ].
intros H4. pose proof HlenC as Hl. rewrite H4 in Hl. clear - Hl Hi. lia. }
intros W1 c1' _ (-> & d & fy1 & regs1 & mem1 & md1 & -> & Hfrm1 & HJ1 & R10 & R22 & HK1' & HF1 & HM1 & HX1).
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> ~ (pg <= a < pg + pn) -> aview trasegs (w_H W) mem1 a = aview trasegs (w_H W) mem a)
by (intros a Ha _ Hn2; apply HM1; [exact Ha | clear - Hn2 HG0 HG1 Hi; lia]).
assert (HC1 : ldl_core fy1 regs1 mem1 md1 i).
{ apply (ldl_core_kept fy regs mem md i fy1 regs1 mem1 md1 HC HJ1 Hfrm1); [|exact M1].
intros r Hr. apply HK1'. revert Hr. clear. cbv [LDL_CORER LDL_INVR LDGA_KEEP In]. tauto. }
assert (K1 : forall r : bv 5, In r LDL_KEEP -> getr regs1 r = getr regs r) by (intros r Hr; apply HK1'; revert Hr; clear; cbv [LDL_KEEP LDGA_KEEP In]; tauto).
assert (F1 : forall r : bv 5, In r LDL_FKEEP -> reg_get (@fp_regs fy1) r = reg_get (@fp_regs fy) r) by (intros r Hr; apply HF1; revert Hr; clear; cbv [LDL_FKEEP LDGA_FKEEP In]; tauto).
destruct d.
- eapply SRr_mono; [exact (LDL_C0 fy1 regs1 mem1 md1 HC1 ltac:(rewrite R10; exact G10))|].
intros W3 c3 _ H. exact (ldl_post_trans fy regs mem fy1 regs1 mem1 _ _ W3 c3 K1 F1 M1 HX1 H).
- assert (HMID : ldl_mid fy1 regs1 mem1 md1 i).
{ destruct HC1 as (HJc & Hfrmc & HRc & _ & G14c & HMmc). split; [exact HJc|]. split; [exact Hfrmc|]. split; [exact HRc|].
split; [rewrite R10; exact G10|]. split; [exact R22|]. split; [exact G14c|].
split; [rewrite (HK1' (24%bv : bv 5) ltac:(cbv; tauto)); exact G24|]. split; [rewrite (HK1' (26%bv : bv 5) ltac:(cbv; tauto)); exact G26|].
split; [rewrite (HK1' (27%bv : bv 5) ltac:(cbv; tauto)); exact G27 | exact HMmc]. }
eapply SRr_mono; [exact (LDL_T2 i fy1 regs1 mem1 md1 Hi HMID)|].
intros W3 c3 _ H. exact (ldl_post_trans fy regs mem fy1 regs1 mem1 _ _ W3 c3 K1 F1 M1 HX1 H).
Qed.
End e.
Lemma LDL_loop : forall (n : nat) (fy : FPState) regs mem md (i : Z),
Z.of_nat n = N - 1 - i -> 0 <= i < N -> ldl_inv fy regs mem md i ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDGA_LH) mem (seg_rom trasegs)) md) (LDL_post fy regs mem LDGS_EXIT N).
Proof.
induction n as [|n IH]; intros fy regs mem md i Hn Hi HI.
- assert (Hlast : i + 1 = N) by lia.
eapply SRr_mono; [exact (LDL_pixel i Hi fy regs mem md HI)|].
intros W' c' _ (HW & fy' & regs' & mem' & md' & Hc & HI' & HK & HF & HM & HX).
replace (i + 1 =? N) with true in Hc by (symmetry; apply Z.eqb_eq; exact Hlast). rewrite Hlast in HI'.
split; [exact HW|]. exists fy', regs', mem', md'. split; [exact Hc|]. split; [exact HI'|]. split; [exact HK|]. split; [exact HF|]. split; [exact HM | exact HX].
- eapply SRr_bind; [exact (LDL_pixel i Hi fy regs mem md HI)|].
intros W' c' _ (-> & fy1 & regs1 & mem1 & md1 & Hc & HI1 & HKa & HFa & HMa & HXa).
replace (i + 1 =? N) with false in Hc by (symmetry; apply Z.eqb_neq; lia). subst c'.
eapply SRr_mono; [exact (IH fy1 regs1 mem1 md1 (i + 1) ltac:(lia) ltac:(lia) HI1)|].
intros W'' c'' _ H. exact (ldl_post_trans fy regs mem fy1 regs1 mem1 _ _ W'' c'' HKa HFa HMa HXa H).
Qed.
End c.
Lemma ldl_clob_cases : forall r : bv 5, reg_in r LDL_CLOB = false -> r = 0%bv \/ In r LDL_KEEP.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Lemma rga_ldi_loop {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trasegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v fmt N Wd pal pimg pg pn v40 v96 v128 g15 g30 d2 d3 d4 cid pos (t : tree) i0
(fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> frm_zero (@fp_csr fy) ->
In (flt, nF) (ablocks B lyc Sc) ->
(forall blc lyq ownq j, In (flt, nF) blc -> 0 <= j < req_size nF -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (flt + j)) ->
sp0 - STK <= s1v -> s1v + 384 <= sp0 -> 3 <= fmt < 2 ^ 29 -> 0 < N <= 2 ^ 29 -> fmt * N <= 2 ^ 29 -> 0 < Wd < 2 ^ 31 ->
In (cid, pos) (frames Sc) -> frame_addr lyc cid pos <= pal -> pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
0 <= d2 < 2 ^ 29 -> 0 <= d3 < 2 ^ 29 -> 0 <= d4 < 2 ^ 29 -> 0 <= g15 < 2 ^ 64 -> 0 <= g30 < 2 ^ 64 ->
0 <= v40 < 2 ^ 64 -> 0 <= v96 < 2 ^ 64 -> 0 <= v128 < 2 ^ 64 ->
In (pg, pn) (ablocks B lyc Sc) -> pg <= pimg -> pimg + N <= pg + pn -> (pg, pn) <> (flt, nF) ->
(forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j)) ->
tree_full t -> tree_forall tnode_wf t ->
(forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc)) -> (forall b, In b (tree_blocks t) -> b <> (flt, nF)) ->
(forall b, In b (tree_blocks t) -> b <> (pg, pn)) ->
4 * (fmt * N) <= nF ->
(forall i j, 0 <= i < N -> 0 <= j < 3 -> i mod Wd < g15 -> 4 * (fmt * i + j + fmt) + 4 <= nF) ->
(forall i j, 0 <= i < N -> 0 <= j < 3 -> i < g30 -> 4 * (fmt * i + j + d2) + 4 <= nF) ->
(forall i j, 0 <= i < N -> 0 <= j < 3 -> i < g30 -> i mod Wd <> 0 -> 4 * (fmt * i + j + d3) + 4 <= nF) ->
(forall i j, 0 <= i < N -> 0 <= j < 3 -> i < g30 -> i mod Wd < g15 -> 4 * (fmt * i + j + d4) + 4 <= nF) ->
tree_at trasegs (mrestrict (w_H W) memc) t ->
val_mem trasegs (mrestrict (w_H W) memc) (s1v + 40) 8 v40 -> val_mem trasegs (mrestrict (w_H W) memc) (s1v + 96) 8 v96 ->
val_mem trasegs (mrestrict (w_H W) memc) (s1v + 128) 8 v128 -> val_mem trasegs (mrestrict (w_H W) memc) (s1v + 160) 8 Wd ->
val_mem trasegs (mrestrict (w_H W) memc) (s1v + 240) 8 (troot t) -> val_mem trasegs (mrestrict (w_H W) memc) (s1v + 296) 8 fmt ->
val_mem trasegs (mrestrict (w_H W) memc) (s1v + 360) 8 pal -> val_mem trasegs (mrestrict (w_H W) memc) (s1v + 376) 8 pimg ->
0 <= i0 < N -> getr regs 16 = w64 i0 -> getr regs 14 = w64 (fmt * i0) -> getr regs 10 = w64 fmt -> getr regs 7 = w64 N ->
getr regs 15 = w64 g15 -> getr regs 30 = w64 g30 -> getr regs 17 = w64 d2 -> getr regs 29 = w64 d3 -> getr regs 28 = w64 d4 ->
getr regs 11 = w64 (troot t + 50) -> getr regs 5 = Z_to_bv 64 (SB + (troot t + 50) / 8) ->
getr regs 24 = w64 v128 -> getr regs 26 = w64 v96 -> getr regs 27 = w64 v40 ->
getr regs 31 = w64 flt -> getr regs 25 = w64 SB -> getr regs 9 = w64 s1v ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDGA_LH) memc (seg_rom trasegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LDGS_EXIT) mem2 (seg_rom trasegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LDL_CLOB = false -> getr regs2 r = getr regs r) /\
(forall r : bv 5, In r LDL_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
getr regs2 16 = w64 N /\ getr regs2 14 = w64 (fmt * N) /\ getr regs2 10 = w64 fmt /\
getr regs2 24 = w64 v128 /\ getr regs2 26 = w64 v96 /\ getr regs2 27 = w64 v40 /\
tree_at trasegs (mrestrict (w_H W) mem2) t /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> ~ (pg <= a < pg + pn) -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v fmt N Wd pal pimg pg pn v40 v96 v128 g15 g30 d2 d3 d4 cid pos t i0 fy regs memc mdc
HJ Hfrm HinF HFW Hs1lo Hs1hi Hfmt HN HfN HWd Hfr Hpal0 Hpal1 Hd2 Hd3 Hd4 Hg15 Hg30 Hv40 Hv96 Hv128 HinG HG0 HG1 HGF HGW Hfull Hwf Htin Htnf Htng HlenC
HK1 HK2 HK3 HK4 Hat V40 V96 V128 V160 V240 V296 V360 V376 Hi0 G16 G14 G10 G7 G15 G30 G17 G29 G28 G11 G5 G24 G26 G27 G31 G25 G9.
eapply SRr_mono.
{ apply (LDL_loop B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v fmt N Wd pal pimg pg pn v40 v96 v128 g15 g30 d2 d3 d4 cid pos t
HinF HFW Hs1lo Hs1hi Hfmt HN HfN HWd Hfr Hpal0 Hpal1 Hd2 Hd3 Hd4 Hg15 Hg30 Hv40 Hv96 Hv128 HinG HG0 HG1 HGF HGW Hfull Hwf Htin Htnf Htng HlenC
HK1 HK2 HK3 HK4 (Z.to_nat (N - 1 - i0)) fy regs memc mdc i0 ltac:(lia) Hi0).
unfold ldl_inv, ldl_regs, ldl_mem. repeat match goal with |- _ /\ _ => split end; assumption. }
intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc2 & (HJ2 & Hfrm2 & _ & R10 & R16 & R14 & R24 & R26 & R27 & (_ & _ & _ & _ & _ & _ & _ & _ & Hat2)) & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc2|]. split; [exact Hfrm2|]. split; [exact HJ2|].
split.
{ intros r Hr. destruct (ldl_clob_cases r Hr) as [-> | Hin]; [|exact (HK r Hin)]. rewrite !getr_zero. reflexivity. }
split; [exact HF|]. split; [exact R16|]. split; [exact R14|]. split; [exact R10|]. split; [exact R24|]. split; [exact R26|]. split; [exact R27|].
split; [exact Hat2|]. split; [exact HM | exact HX].
Qed.

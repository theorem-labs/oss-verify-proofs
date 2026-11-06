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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCji YCjb YCjc YCj9 YCja.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LDL_INVR : list (bv 5) := [1; 2; 3; 4; 9; 22; 23; 24; 26; 27]%bv.
Definition LDL_CORER : list (bv 5) := (25%bv : bv 5) :: (31%bv : bv 5) :: LDL_INVR.
Definition LDL_FINV : list (bv 5) := [8; 9; 18]%bv.
Definition LDL_CLOB : list (bv 5) := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 25; 28; 29; 30; 31]%bv.
Definition LDL_KEEP : list (bv 5) := [1; 2; 3; 4; 8; 9; 19; 21; 22; 23; 24; 26; 27]%bv.
Definition LDL_FKEEP : list (bv 5) := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma ldl_root_blk : forall t : tree, tree_full t -> In (troot t, NODE_SIZE) (tree_blocks t).
Proof. intros t Hf. destruct t as [|n|n l r]; [destruct Hf | left; reflexivity | left; reflexivity]. Qed.
Section c.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis TGLNI : forall fx : FPState, @tglni_spec fx rc B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trbsegs).
Variables (flt nF s1v fmt N Wd pal pimg pg pn g24 g408 d2 d3 d4 cid pos : Z) (t : tree).
Hypothesis HinF : In (flt, nF) (ablocks B lyc Sc).
Hypothesis HFW : forall blc lyq ownq j, In (flt, nF) blc -> 0 <= j < req_size nF -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (flt + j).
Hypothesis Hs1lo : sp0 - STK <= s1v - 16. Hypothesis Hs1hi : s1v + 416 <= sp0. Hypothesis Hs16 : s1v mod 16 = 0.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4. Hypothesis HN : 0 < N <= 2 ^ 29. Hypothesis HfN : fmt * N <= 2 ^ 29.
Hypothesis HWd : 1 <= Wd < 2 ^ 31.
Hypothesis Hfr : In (cid, pos) (frames Sc). Hypothesis Hpal0 : frame_addr lyc cid pos <= pal. Hypothesis Hpal1 : pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid.
Hypothesis Hd2 : 0 <= d2 < 2 ^ 29. Hypothesis Hd3 : 0 <= d3 < 2 ^ 29. Hypothesis Hd4 : 0 <= d4 < 2 ^ 29.
Hypothesis Hg24 : 0 <= g24 < 2 ^ 64. Hypothesis Hg408 : 0 <= g408 < 2 ^ 64.
Hypothesis HinG : In (pg, pn) (ablocks B lyc Sc). Hypothesis HG0 : pg <= pimg. Hypothesis HG1 : pimg + N <= pg + pn.
Hypothesis HGF : (pg, pn) <> (flt, nF).
Hypothesis HGW : forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j).
Hypothesis Hfull : tree_full t. Hypothesis Hwf : tree_forall tnode_wf t.
Hypothesis Htin : forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc).
Hypothesis Htnf : forall b, In b (tree_blocks t) -> b <> (flt, nF).
Hypothesis Htng : forall b, In b (tree_blocks t) -> b <> (pg, pn).
Hypothesis HlenC : 4 * (fmt * N) <= nF.
Hypothesis HK1 : forall i j, 0 <= i < N -> 0 <= j < 3 -> i mod Wd < g24 -> 4 * (fmt * i + j + fmt) + 4 <= nF.
Hypothesis HK2 : forall i j, 0 <= i < N -> 0 <= j < 3 -> i < g408 -> 3 <= d2 /\ 4 * (fmt * i + j + d2) + 4 <= nF.
Hypothesis HK3 : forall i j, 0 <= i < N -> 0 <= j < 3 -> i < g408 -> i mod Wd <> 0 -> 3 <= d3 /\ 4 * (fmt * i + j + d3) + 4 <= nF.
Hypothesis HK4 : forall i j, 0 <= i < N -> 0 <= j < 3 -> i < g408 -> i mod Wd < g24 -> 3 <= d4 /\ 4 * (fmt * i + j + d4) + 4 <= nF.
Definition ldl_regs (regs : bvmap 5 word) : Prop :=
getr regs 1 = w64 d3 /\ getr regs 2 = w64 s1v /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ getr regs 9 = w64 s1v /\
getr regs 22 = w64 (2 ^ 64 - 1 - flt) /\ getr regs 23 = w64 flt /\ getr regs 24 = w64 g24 /\ getr regs 26 = w64 d2 /\ getr regs 27 = w64 SB.
Definition ldl_fp (fy : FPState) : Prop :=
reg_get (@fp_regs fy) (8%bv : bv 5) = nan_box (Z_to_bv 32 0) /\ reg_get (@fp_regs fy) (9%bv : bv 5) = nan_box (Z_to_bv 32 S255) /\
reg_get (@fp_regs fy) (18%bv : bv 5) = nan_box (Z_to_bv 32 Shi).
Definition ldl_mem (mem : word -> option byte) : Prop :=
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 192) 8 fmt /\ val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 232) 8 Wd /\
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 240) 8 (troot t) /\ val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 312) 8 pimg /\
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 376) 8 d4 /\ val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 384) 8 N /\
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 392) 8 pal /\ val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 400) 8 1 /\
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 408) 8 g408 /\ val_mem trbsegs (mrestrict (w_H W) mem) LDK_ROL 4 Slo /\
tree_at trbsegs (mrestrict (w_H W) mem) t.
Definition ldl_core (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (i : Z) : Prop :=
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\ frm_zero (@fp_csr fy) /\
ldl_regs regs /\ ldl_fp fy /\ getr regs 25 = w64 i /\ getr regs 31 = w64 (fmt * i) /\ ldl_mem mem.
Definition ldl_inv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (i : Z) : Prop :=
ldl_core fy regs mem md i /\ getr regs 18 = w64 fmt.
Lemma ldl_regs_kept : forall regs regs' : bvmap 5 word, (forall r : bv 5, In r LDL_INVR -> getr regs' r = getr regs r) -> ldl_regs regs -> ldl_regs regs'.
Proof.
intros regs regs' HK (R1 & R2 & R3 & R4 & R9 & R22 & R23 & R24 & R26 & R27). unfold ldl_regs.
rewrite (HK (1%bv : bv 5) ltac:(cbv; tauto)), (HK (2%bv : bv 5) ltac:(cbv; tauto)), (HK (3%bv : bv 5) ltac:(cbv; tauto)),
(HK (4%bv : bv 5) ltac:(cbv; tauto)), (HK (9%bv : bv 5) ltac:(cbv; tauto)), (HK (22%bv : bv 5) ltac:(cbv; tauto)),
(HK (23%bv : bv 5) ltac:(cbv; tauto)), (HK (24%bv : bv 5) ltac:(cbv; tauto)), (HK (26%bv : bv 5) ltac:(cbv; tauto)),
(HK (27%bv : bv 5) ltac:(cbv; tauto)).
repeat split; assumption.
Qed.
Lemma ldl_fp_kept : forall fy fy' : FPState, (forall r : bv 5, In r LDL_FINV -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) -> ldl_fp fy -> ldl_fp fy'.
Proof.
intros fy fy' HF (F8 & F9 & F18). unfold ldl_fp.
rewrite (HF (8%bv : bv 5) ltac:(cbv; tauto)), (HF (9%bv : bv 5) ltac:(cbv; tauto)), (HF (18%bv : bv 5) ltac:(cbv; tauto)). repeat split; assumption.
Qed.
Definition ldl_outside (a : Z) : Prop := ~ (flt <= a < flt + nF) /\ ~ (pg <= a < pg + pn) /\ ~ (s1v - 16 <= a < s1v).
Lemma ldl_mem_kept : forall (mem mem' : word -> option byte) md,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
(forall a, 0 <= a < 2 ^ 64 -> ldl_outside a -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) ->
ldl_mem mem -> ldl_mem mem'.
Proof.
intros mem mem' md HJ HM (V192 & V232 & V240 & V312 & V376 & V384 & V392 & V400 & V408 & Vrol & Hat). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Hg4096 & Hgceil & _ & _ & _ & Hpn0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & Hf4096 & Hfceil & _ & _ & _ & Hnf0).
pose proof (req_size_pos pn ltac:(lia)) as [_ Hrg]. pose proof (req_size_pos nF ltac:(lia)) as [_ Hrf].
pose proof (blk_off_img _ _ _ _ _ _ pg pn HAR HinG) as Hgimg. pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Hfimg.
assert (Rs : 2 ^ 46 <= s1v - 16 /\ s1v + 416 <= 2 ^ 47 /\ alloc_ceiling <= s1v - 16) by (clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1; lia).
assert (SLOT : forall off v, 0 <= off -> off + 8 <= 416 -> val_mem trbsegs (mrestrict (w_H W) mem) (s1v + off) 8 v -> val_mem trbsegs (mrestrict (w_H W) mem') (s1v + off) 8 v).
{ intros off v Ho0 Ho1 V. apply (YCcz.val_mem_kept trbsegs (w_H W) (w_H W) mem mem' (s1v + off) 8 v); [|exact V].
intros j Hj. apply HM; [clear - Hj Rs Ho0 Ho1; lia|]. unfold ldl_outside. clear - Hj Rs Ho0 Ho1 Hfceil Hrf Hgceil Hrg. repeat split; lia. }
split; [apply SLOT; [lia | lia | exact V192]|]. split; [apply SLOT; [lia | lia | exact V232]|]. split; [apply SLOT; [lia | lia | exact V240]|].
split; [apply SLOT; [lia | lia | exact V312]|]. split; [apply SLOT; [lia | lia | exact V376]|]. split; [apply SLOT; [lia | lia | exact V384]|].
split; [apply SLOT; [lia | lia | exact V392]|]. split; [apply SLOT; [lia | lia | exact V400]|]. split; [apply SLOT; [lia | lia | exact V408]|].
split.
{ apply (YCcz.val_mem_kept trbsegs (w_H W) (w_H W) mem mem' LDK_ROL 4 Slo); [|exact Vrol].
intros j Hj. apply HM; [unfold LDK_ROL; clear - Hj; lia|]. unfold ldl_outside.
revert Hgimg Hfimg Hj Rs Hrf Hrg Hf4096 Hg4096. clear. unfold off_img, LDK_ROL. intros. repeat split; lia. }
apply (rg_tree_at_kept (w_H W) (w_H W) mem mem' t Hat). intros b sz Hb j Hj.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b sz HAR (Htin _ Hb)) as (_ & Hb4096 & Hbceil & _).
pose proof (sep_blocks trbsegs _ LAWS lyc Sc _ _ _ b sz pg pn HAR (Htin _ Hb) HinG (Htng _ Hb)) as Hd1. unfold zdisjoint in Hd1. cbn [fst snd] in Hd1.
pose proof (sep_blocks trbsegs _ LAWS lyc Sc _ _ _ b sz flt nF HAR (Htin _ Hb) HinF (Htnf _ Hb)) as Hd2'. unfold zdisjoint in Hd2'. cbn [fst snd] in Hd2'.
apply HM; [clear - Hj Hb4096 Hbceil C1; lia|]. unfold ldl_outside. clear - Hj Hd1 Hd2' Hrf Hrg Hbceil Rs. repeat split; lia.
Qed.
Definition LDL_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc i' : Z) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trbsegs)) md' /\
ldl_inv fy' regs' mem' md' i' /\
(forall r : bv 5, In r LDL_KEEP -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LDL_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ldl_outside a -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma ldl_post_trans : forall fy regs mem (fy1 : FPState) regs1 mem1 pc i' W' c',
(forall r : bv 5, In r LDL_KEEP -> getr regs1 r = getr regs r) ->
(forall r : bv 5, In r LDL_FKEEP -> reg_get (@fp_regs fy1) r = reg_get (@fp_regs fy) r) ->
(forall a, 0 <= a < 2 ^ 64 -> ldl_outside a -> aview trbsegs (w_H W) mem1 a = aview trbsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
LDL_post fy1 regs1 mem1 pc i' W' c' -> LDL_post fy regs mem pc i' W' c'.
Proof.
intros fy regs mem fy1 regs1 mem1 pc i' W' c' K1 F1 M1 X1 (HW & fy' & regs' & mem' & md' & Hc & HI & K & F & M & X).
split; [exact HW|]. exists fy', regs', mem', md'. split; [exact Hc|]. split; [exact HI|].
split; [intros r Hr; rewrite (K r Hr); exact (K1 r Hr)|]. split; [intros r Hr; rewrite (F r Hr); exact (F1 r Hr)|].
split; [intros a Ha Hn; rewrite (M a Ha Hn); exact (M1 a Ha Hn)|]. intros a Ha. apply X. apply X1. exact Ha.
Qed.
Lemma ldl_core_kept : forall (fy : FPState) regs mem md i (fy' : FPState) regs' mem' md',
ldl_core fy regs mem md i ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k -> frm_zero (@fp_csr fy') ->
(forall r : bv 5, In r LDL_CORER -> getr regs' r = getr regs r) ->
(forall r : bv 5, In r LDL_FINV -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) ->
(forall a, 0 <= a < 2 ^ 64 -> ldl_outside a -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) ->
ldl_core fy' regs' mem' md' i.
Proof.
intros fy regs mem md i fy' regs' mem' md' (HJ & Hfrm & HR & HFp & G25 & G31 & HMm) HJ' Hfrm' HK HF HM.
split; [exact HJ'|]. split; [exact Hfrm'|].
split; [apply (ldl_regs_kept regs regs'); [intros r Hr; apply HK; right; right; exact Hr | exact HR]|].
split; [exact (ldl_fp_kept fy fy' HF HFp)|].
split; [rewrite (HK (25%bv : bv 5) ltac:(cbv; tauto)); exact G25|]. split; [rewrite (HK (31%bv : bv 5) ltac:(cbv; tauto)); exact G31|].
exact (ldl_mem_kept mem mem' md HJ HM HMm).
Qed.
Lemma ldl_stk : forall fy regs mem md i, ldl_core fy regs mem md i -> 2 ^ 46 <= s1v - 16 /\ s1v + 416 <= 2 ^ 47 /\ alloc_ceiling <= s1v - 16.
Proof.
intros fy regs mem md i (HJ & _). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1. lia.
Qed.
Section d.
Variable i : Z.
Hypothesis Hi : 0 <= i < N.
Lemma ldl_fi : 0 <= fmt * i /\ fmt * i + fmt <= fmt * N /\ 3 <= fmt <= 4.
Proof.
assert (H34 : 3 <= fmt <= 4) by (clear - Hfmt; lia).
split; [apply Z.mul_nonneg_nonneg; lia|]. split; [|exact H34]. replace (fmt * i + fmt) with (fmt * (i + 1)) by lia. apply Z.mul_le_mono_nonneg_l; lia.
Qed.
Lemma LDL_T : forall (fy : FPState) regs mem md, ldl_core fy regs mem md i -> getr regs 18 = w64 fmt -> getr regs 13 = w64 (i + 1) ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDH_TAIL) mem (seg_rom trbsegs)) md)
(LDL_post fy regs mem (if i + 1 =? N then LDH_EXIT else LDH_HEAD) (i + 1)).
Proof.
intros fy regs mem md HC G18 G13. pose proof HC as (HJ & Hfrm & HR & HFp & G25 & G31 & HMm).
pose proof HR as (R1 & R2 & R3 & R4 & R9 & R22 & R23 & R24 & R26 & R27).
pose proof HMm as (V192 & V232 & V240 & V312 & V376 & V384 & V392 & V400 & V408 & Vrol & Hat).
pose proof ldl_fi as (Hfi0 & Hfi1 & H34).
assert (HB : ldh_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v fy regs mem md) by (split; [exact HJ|]; split; [exact Hfrm|]; split; assumption).
eapply SRr_mono; [exact (LDH_tail B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v ltac:(clear - Hs1lo; lia) ltac:(clear - Hs1hi; lia) fy regs mem md (fmt * i) fmt (i + 1) N HB G31 G18 G13
ltac:(clear - Hfi0 Hfi1 HfN H34; lia) ltac:(clear - H34; lia) ltac:(clear - Hi HN; lia) ltac:(clear - HN; lia) V384)|].
intros W' c' _ (HW & regs' & mem' & md' & Hc & HJ' & R31' & R25' & HK & HM & HX).
split; [exact HW|]. exists fy, regs', mem', md'. split; [exact Hc|].
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ldl_outside a -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) by (intros a Ha _; exact (HM a Ha)).
split.
{ split.
- split; [exact HJ'|]. split; [exact Hfrm|].
split; [apply (ldl_regs_kept regs regs'); [intros r Hr; apply HK; revert Hr; clear; cbv [LDL_INVR LDT_KEEP In]; tauto | exact HR]|].
split; [exact HFp|]. split; [exact R25'|]. split; [rewrite R31'; unfold w64; f_equal; lia|].
exact (ldl_mem_kept mem mem' md HJ M1 HMm).
- rewrite (HK (18%bv : bv 5) ltac:(cbv; tauto)). exact G18. }
split; [intros r Hr; apply HK; revert Hr; clear; cbv [LDL_KEEP LDT_KEEP In]; tauto|].
split; [intros r _; reflexivity|]. split; [exact M1 | exact HX].
Qed.
Definition ldl_clamped (mem : word -> option byte) : Prop :=
forall j, 0 <= j < 3 -> exists cv, val_mem trbsegs (mrestrict (w_H W) mem) (flt + 4 * (fmt * i + j)) 4 cv /\ 0 <= cv < 2 ^ 32 /\ s_in cv 0 255.
Lemma LDL_K : forall (fy : FPState) regs mem md, ldl_core fy regs mem md i -> getr regs 18 = w64 fmt -> getr regs 13 = w64 (i + 1) ->
getr regs 14 = w64 3 -> getr regs 15 = w64 (fmt * i) -> getr regs 16 = w64 pal -> getr regs 11 = w64 (pimg + i) ->
getr regs 12 = Z_to_bv 64 (SB + (pimg + i) / 8) -> getr regs 30 = w64 Wd -> getr regs 20 = w64 d4 -> ldl_clamped mem ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_HEAD) mem (seg_rom trbsegs)) md)
(LDL_post fy regs mem (if i + 1 =? N then LDH_EXIT else LDH_HEAD) (i + 1)).
Proof.
intros fy regs mem md HC G18 G13 G14 G15 G16 G11 G12 G30 G20 Hcl. pose proof HC as (HJ & Hfrm & HR & HFp & G25 & G31 & HMm).
pose proof HR as (R1 & R2 & R3 & R4 & R9 & R22 & R23 & R24 & R26 & R27). pose proof HFp as (F8 & F9 & F18).
pose proof HMm as (V192 & V232 & V240 & V312 & V376 & V384 & V392 & V400 & V408 & Vrol & Hat).
pose proof ldl_fi as (Hfi0 & Hfi1 & H34).
eapply SRr_bind.
{ apply (rga_ldi_kloop B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF pg pn (pimg + i) cid pos s1v fmt d2 d3 d4 g24 g408 Wd i 3 (fmt * i) pal
fy regs mem md HJ Hfrm HinF HFW HinG ltac:(clear - HG0 Hi; lia) ltac:(clear - HG1 Hi; lia) HGF Hfr Hpal0 ltac:(clear - Hpal1; lia)
ltac:(clear - Hs1lo; lia) Hs1hi V408 ltac:(clear - H34; lia) Hd2 Hd3 Hd4 Hg24 Hg408 HWd ltac:(clear - Hi HN; lia) ltac:(clear; lia) Hfi0
ltac:(clear - Hfi1 HfN H34; lia)).
- intros j Hj. clear - Hj Hfi1 HlenC H34. lia.
- intros j Hj Hg. split; [clear - H34; lia | exact (HK1 i j Hi Hj Hg)].
- intros j Hj Hg. exact (HK2 i j Hi Hj Hg).
- intros j Hj Hg Hg'. exact (HK3 i j Hi Hj Hg Hg').
- intros j Hj Hg Hg'. exact (HK4 i j Hi Hj Hg Hg').
- exact Hcl. - exact Vrol. - exact F18.
- exact G14. - exact G15. - exact G16. - exact R9. - exact G11. - exact G12. - exact R24. - exact G25. - exact G30.
- exact G18. - exact R26. - exact R1. - exact G20. - exact R23. - exact R27. - exact R22. }
intros W1 c1 _ (-> & fy1 & regs1 & mem1 & md1 & -> & Hfrm1 & HJ1 & HK1' & HF1 & _ & _ & _ & HM1 & HX1).
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ldl_outside a -> aview trbsegs (w_H W) mem1 a = aview trbsegs (w_H W) mem a)
by (intros a Ha (Hn1 & _); exact (HM1 a Ha Hn1)).
assert (K1 : forall r : bv 5, In r (18%bv :: 13%bv :: LDL_CORER ++ LDL_KEEP) -> getr regs1 r = getr regs r).
{ intros r Hr. apply HK1'. revert Hr. clear. cbv [LDL_CORER LDL_INVR LDL_KEEP app In]. intros Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
assert (F1 : forall r : bv 5, In r LDL_FKEEP -> reg_get (@fp_regs fy1) r = reg_get (@fp_regs fy) r) by (intros r Hr; apply HF1; revert Hr; clear; cbv [LDL_FKEEP LDK_FKEEP In]; tauto).
assert (HC1 : ldl_core fy1 regs1 mem1 md1 i).
{ apply (ldl_core_kept fy regs mem md i fy1 regs1 mem1 md1 HC HJ1 Hfrm1); [| |exact M1].
- intros r Hr. apply K1. right; right. apply in_or_app. left. exact Hr.
- intros r Hr. apply F1. revert Hr. clear. cbv [LDL_FINV LDL_FKEEP In]. tauto. }
eapply SRr_mono; [exact (LDL_T fy1 regs1 mem1 md1 HC1 ltac:(rewrite (K1 (18%bv : bv 5) ltac:(left; reflexivity)); exact G18)
ltac:(rewrite (K1 (13%bv : bv 5) ltac:(right; left; reflexivity)); exact G13))|].
intros W3 c3 _ H. apply (ldl_post_trans fy regs mem fy1 regs1 mem1 _ _ W3 c3); [| exact F1 | exact M1 | exact HX1 | exact H].
intros r Hr. apply K1. right; right. apply in_or_app. right. exact Hr.
Qed.
Lemma LDL_LEAF : forall (fy : FPState) regs mem md, ldl_core fy regs mem md i -> getr regs 11 = w64 (fmt * i) -> ldl_clamped mem ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDG_A) mem (seg_rom trbsegs)) md)
(LDL_post fy regs mem (if i + 1 =? N then LDH_EXIT else LDH_HEAD) (i + 1)).
Proof.
intros fy regs mem md HC G11 Hcl. pose proof HC as (HJ & Hfrm & HR & HFp & G25 & G31 & HMm).
pose proof HR as (R1 & R2 & R3 & R4 & R9 & R22 & R23 & R24 & R26 & R27).
pose proof HMm as (V192 & V232 & V240 & V312 & V376 & V384 & V392 & V400 & V408 & Vrol & Hat).
pose proof ldl_fi as (Hfi0 & Hfi1 & H34). pose proof (ldl_stk fy regs mem md i HC) as Rs.
pose proof HJ as (HAR & _). pose proof asan_consts as (C1 & _).
destruct (frames_bounds trbsegs B LAWS lyc Sc W mem md cid pos HAR Hfr) as (Hfr0 & Hfrc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (troot t) NODE_SIZE HAR (Htin _ (ldl_root_blk t Hfull))) as (_ & Hn4096 & Hnceil & _).
change (req_size NODE_SIZE) with 56 in Hnceil.
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & Hf4096 & Hfceil & _ & _ & _ & Hnf0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Hg4096 & Hgceil & _ & _ & _ & Hpn0).
pose proof (req_size_pos nF ltac:(lia)) as [_ Hrf]. pose proof (req_size_pos pn ltac:(lia)) as [_ Hrg].
pose proof (sep_blocks trbsegs _ LAWS lyc Sc _ _ _ pg pn flt nF HAR HinG HinF HGF) as Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
eapply SRr_bind.
{ exact (rga_ldi_leaf B LAWS TGLNI STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v flt nF fmt Wd pimg d4 pal pg pn i (fmt * i) t fy regs mem md HJ Hfrm HinF Hs1lo
ltac:(clear - Hs1hi; lia) Hs16 HinG HG0 ltac:(clear - HG1 Hi; lia) ltac:(clear - Hi HN; lia) ltac:(clear - H34; lia) ltac:(clear - HWd; lia) ltac:(clear - Hd4; lia)
ltac:(clear - Hpal0 Hpal1 Hfr0 Hfrc C1; lia) HGW ltac:(clear - Hfi0 Hfi1 HfN H34; lia) ltac:(clear - Hfi1 HlenC H34; lia)
Hfull Hwf Hat Htin V240 ltac:(clear - Hn4096 Hnceil C1; lia) V192 V232 V312 V376 V392 V400 R2 R9 R27 R3 R4 G11 R23 R22 G25). }
intros W1 c1' _ (-> & fy1 & regs1 & mem1 & md1 & -> & Hfrm1 & HF1 & HJ1 & Q1 & Q31 & Q26 & Q15 & Q18 & Q20 & Q30 & Q16 & Q11 & Q12 & Q13 & Q14 & HK1' & HM1 & HX1).
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ldl_outside a -> aview trbsegs (w_H W) mem1 a = aview trbsegs (w_H W) mem a).
{ intros a Ha (_ & Hn2 & Hn3). apply HM1; [exact Ha | clear - Hn2 HG0 HG1 Hi; lia | exact Hn3]. }
assert (K1 : forall r : bv 5, In r (LDL_CORER ++ LDL_KEEP) -> getr regs1 r = getr regs r).
{ intros r Hr. apply in_app_or in Hr. cbv [LDL_CORER LDL_INVR LDL_KEEP In] in Hr.
assert (Hc : r = 1%bv \/ r = 31%bv \/ r = 26%bv \/ In r LDG_KEEP) by (clear - Hr; cbv [LDG_KEEP In]; intuition auto).
destruct Hc as [-> | [-> | [-> | Hc]]]; [exact Q1 | exact Q31 | exact Q26 | exact (HK1' r Hc)]. }
assert (F1 : forall r : bv 5, In r LDL_FKEEP -> reg_get (@fp_regs fy1) r = reg_get (@fp_regs fy) r) by (intros r Hr; apply HF1; revert Hr; clear; cbv [LDL_FKEEP TGLNI_FKEEP In]; tauto).
assert (HC1 : ldl_core fy1 regs1 mem1 md1 i).
{ apply (ldl_core_kept fy regs mem md i fy1 regs1 mem1 md1 HC HJ1 Hfrm1); [| |exact M1].
- intros r Hr. apply K1. apply in_or_app. left. exact Hr.
- intros r Hr. apply F1. revert Hr. clear. cbv [LDL_FINV LDL_FKEEP In]. tauto. }
assert (Hcl1 : ldl_clamped mem1).
{ intros j Hj. destruct (Hcl j Hj) as (cv & Vcv & Hcv). exists cv. split; [|exact Hcv].
apply (YCcz.val_mem_kept trbsegs (w_H W) (w_H W) mem mem1 _ 4 cv); [|exact Vcv].
intros x Hx. change (Z.of_nat 4) with 4 in Hx.
apply HM1; clear - Hx Hj Hfi0 Hfi1 HlenC Hsep Hrf Hrg HG0 HG1 Hi H34 Hf4096 Hfceil Rs C1; lia. }
eapply SRr_mono; [exact (LDL_K fy1 regs1 mem1 md1 HC1 Q18 Q13 Q14 ltac:(rewrite Q15; exact G31) Q16 Q11 Q12 Q30 Q20 Hcl1)|].
intros W3 c3 _ H. apply (ldl_post_trans fy regs mem fy1 regs1 mem1 _ _ W3 c3); [| exact F1 | exact M1 | exact HX1 | exact H].
intros r Hr. apply K1. apply in_or_app. right. exact Hr.
Qed.
Lemma LDL_CLAMP : forall (fy : FPState) regs mem md, ldl_core fy regs mem md i ->
getr regs 12 = w64 3 -> getr regs 13 = w64 (fmt * i) -> getr regs 11 = w64 (fmt * i) ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDC_HEAD) mem (seg_rom trbsegs)) md)
(LDL_post fy regs mem (if i + 1 =? N then LDH_EXIT else LDH_HEAD) (i + 1)).
Proof.
intros fy regs mem md HC G12 G13 G11. pose proof HC as (HJ & Hfrm & HR & HFp & G25 & G31 & HMm).
pose proof HR as (R1 & R2 & R3 & R4 & R9 & R22 & R23 & R24 & R26 & R27). pose proof HFp as (F8 & F9 & F18).
pose proof ldl_fi as (Hfi0 & Hfi1 & H34).
eapply SRr_bind.
{ exact (rga_ldi_clamp B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF 3 (fmt * i) fy regs mem md HJ Hfrm HinF HFW ltac:(clear; lia) Hfi0
ltac:(clear - Hfi1 HfN H34; lia) ltac:(clear - Hfi1 HlenC H34; lia) G12 G13 R23 R27 R22 F8 F9). }
intros W1 c1' _ (-> & fy1 & regs1 & mem1 & md1 & -> & Hfrm1 & HJ1 & HK1' & HF1 & _ & _ & HM1 & HX1 & Hvals).
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ldl_outside a -> aview trbsegs (w_H W) mem1 a = aview trbsegs (w_H W) mem a)
by (intros a Ha (Hn1 & _); apply HM1; [exact Ha | clear - Hn1 Hfi0 Hfi1 HlenC H34; lia]).
assert (K1 : forall r : bv 5, In r (11%bv :: LDL_CORER ++ LDL_KEEP) -> getr regs1 r = getr regs r).
{ intros r Hr. apply HK1'. revert Hr. clear. cbv [LDL_CORER LDL_INVR LDL_KEEP app In]. intros Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
assert (F1 : forall r : bv 5, In r LDL_FKEEP -> reg_get (@fp_regs fy1) r = reg_get (@fp_regs fy) r) by (intros r Hr; apply HF1; revert Hr; clear; cbv [LDL_FKEEP LDC_FKEEP In]; tauto).
assert (HC1 : ldl_core fy1 regs1 mem1 md1 i).
{ apply (ldl_core_kept fy regs mem md i fy1 regs1 mem1 md1 HC HJ1 Hfrm1); [| |exact M1].
- intros r Hr. apply K1. right. apply in_or_app. left. exact Hr.
- intros r Hr. apply F1. revert Hr. clear. cbv [LDL_FINV LDL_FKEEP In]. tauto. }
assert (Hcl1 : ldl_clamped mem1) by (intros j Hj; apply (Hvals (fmt * i + j)); clear - Hj; lia).
eapply SRr_mono; [exact (LDL_LEAF fy1 regs1 mem1 md1 HC1 ltac:(rewrite (K1 (11%bv : bv 5) ltac:(left; reflexivity)); exact G11) Hcl1)|].
intros W3 c3 _ H. apply (ldl_post_trans fy regs mem fy1 regs1 mem1 _ _ W3 c3); [| exact F1 | exact M1 | exact HX1 | exact H].
intros r Hr. apply K1. right. apply in_or_app. right. exact Hr.
Qed.
Lemma LDL_pixel : forall (fy : FPState) regs mem md, ldl_inv fy regs mem md i ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDH_HEAD) mem (seg_rom trbsegs)) md)
(LDL_post fy regs mem (if i + 1 =? N then LDH_EXIT else LDH_HEAD) (i + 1)).
Proof.
intros fy regs mem md (HC & G18). pose proof HC as (HJ & Hfrm & HR & HFp & G25 & G31 & HMm).
pose proof HR as (R1 & R2 & R3 & R4 & R9 & R22 & R23 & R24 & R26 & R27).
pose proof HMm as (V192 & V232 & V240 & V312 & V376 & V384 & V392 & V400 & V408 & Vrol & Hat).
pose proof ldl_fi as (Hfi0 & Hfi1 & H34).
assert (HB : ldh_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v fy regs mem md) by (split; [exact HJ|]; split; [exact Hfrm|]; split; assumption).
assert (Hi29 : 0 <= i < 2 ^ 29) by (clear - Hi HN; lia).
assert (STEP : SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDH_HEAD) mem (seg_rom trbsegs)) md) (LDH_post B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pimg i fmt fy regs mem)).
{ destruct Hfmt as [E3 | E4].
- rewrite E3. rewrite E3 in G18. exact (LDH_head3 B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v pimg i Hi29 fy regs mem md HB G18 G25).
- rewrite E4. rewrite E4 in G18.
exact (LDH_head4 B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v flt nF pimg pg pn i HinF HinG HG0 ltac:(clear - HG1 Hi; lia)
ltac:(intros X; apply HGF; symmetry; exact X) Hi29 ltac:(clear - Hs1lo; lia) ltac:(clear - Hs1hi; lia) HGW fy regs mem md HB
ltac:(clear - HlenC Hi E4; lia) G18 G25 R23 R22 V312 V400). }
eapply SRr_bind; [exact STEP|].
intros W1 c1' _ (-> & fy1 & regs1 & mem1 & md1 & tr & -> & HJ1 & Hfrm1 & Harm & HK1' & HF1 & HM1 & HX1).
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ldl_outside a -> aview trbsegs (w_H W) mem1 a = aview trbsegs (w_H W) mem a).
{ intros a Ha (_ & Hn2 & _). apply HM1; [exact Ha | clear - Hn2 HG0 HG1 Hi; lia]. }
assert (K1 : forall r : bv 5, In r (18%bv :: LDL_CORER ++ LDL_KEEP) -> getr regs1 r = getr regs r).
{ intros r Hr. apply HK1'. revert Hr. clear. cbv [LDL_CORER LDL_INVR LDL_KEEP LDH_KEEP app In]. tauto. }
assert (F1 : forall r : bv 5, In r LDL_FKEEP -> reg_get (@fp_regs fy1) r = reg_get (@fp_regs fy) r) by (intros r Hr; apply HF1; revert Hr; clear; cbv [LDL_FKEEP LDH_FKEEP In]; tauto).
assert (HC1 : ldl_core fy1 regs1 mem1 md1 i).
{ apply (ldl_core_kept fy regs mem md i fy1 regs1 mem1 md1 HC HJ1 Hfrm1); [| |exact M1].
- intros r Hr. apply K1. right. apply in_or_app. left. exact Hr.
- intros r Hr. apply F1. revert Hr. clear. cbv [LDL_FINV LDL_FKEEP In]. tauto. }
assert (G18' : getr regs1 18 = w64 fmt) by (rewrite (K1 (18%bv : bv 5) ltac:(left; reflexivity)); exact G18).
destruct tr.
- destruct Harm as (_ & Q13).
eapply SRr_mono; [exact (LDL_T fy1 regs1 mem1 md1 HC1 G18' Q13)|].
intros W3 c3 _ H. apply (ldl_post_trans fy regs mem fy1 regs1 mem1 _ _ W3 c3); [| exact F1 | exact M1 | exact HX1 | exact H].
intros r Hr. apply K1. right. apply in_or_app. right. exact Hr.
- destruct Harm as (Q11 & Q12 & Q13).
eapply SRr_mono; [exact (LDL_CLAMP fy1 regs1 mem1 md1 HC1 Q12 ltac:(rewrite Q13; exact G31) Q11)|].
intros W3 c3 _ H. apply (ldl_post_trans fy regs mem fy1 regs1 mem1 _ _ W3 c3); [| exact F1 | exact M1 | exact HX1 | exact H].
intros r Hr. apply K1. right. apply in_or_app. right. exact Hr.
Qed.
End d.
Lemma LDL_loop : forall (n : nat) (fy : FPState) regs mem md (i : Z),
Z.of_nat n = N - 1 - i -> 0 <= i < N -> ldl_inv fy regs mem md i ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDH_HEAD) mem (seg_rom trbsegs)) md) (LDL_post fy regs mem LDH_EXIT N).
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
Lemma rga_ldi_loop {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trbsegs B -> (forall fx : FPState, @tglni_spec fx rc B) ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v fmt N Wd pal pimg pg pn g24 g408 d2 d3 d4 cid pos (t : tree) i0
(fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> frm_zero (@fp_csr fy) ->
In (flt, nF) (ablocks B lyc Sc) ->
(forall blc lyq ownq j, In (flt, nF) blc -> 0 <= j < req_size nF -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (flt + j)) ->
sp0 - STK <= s1v - 16 -> s1v + 416 <= sp0 -> s1v mod 16 = 0 ->
(fmt = 3 \/ fmt = 4) -> 0 < N <= 2 ^ 29 -> fmt * N <= 2 ^ 29 -> 1 <= Wd < 2 ^ 31 ->
In (cid, pos) (frames Sc) -> frame_addr lyc cid pos <= pal -> pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
0 <= d2 < 2 ^ 29 -> 0 <= d3 < 2 ^ 29 -> 0 <= d4 < 2 ^ 29 -> 0 <= g24 < 2 ^ 64 -> 0 <= g408 < 2 ^ 64 ->
In (pg, pn) (ablocks B lyc Sc) -> pg <= pimg -> pimg + N <= pg + pn -> (pg, pn) <> (flt, nF) ->
(forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j)) ->
tree_full t -> tree_forall tnode_wf t ->
(forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc)) -> (forall b, In b (tree_blocks t) -> b <> (flt, nF)) ->
(forall b, In b (tree_blocks t) -> b <> (pg, pn)) ->
4 * (fmt * N) <= nF ->
(forall i j, 0 <= i < N -> 0 <= j < 3 -> i mod Wd < g24 -> 4 * (fmt * i + j + fmt) + 4 <= nF) ->
(forall i j, 0 <= i < N -> 0 <= j < 3 -> i < g408 -> 3 <= d2 /\ 4 * (fmt * i + j + d2) + 4 <= nF) ->
(forall i j, 0 <= i < N -> 0 <= j < 3 -> i < g408 -> i mod Wd <> 0 -> 3 <= d3 /\ 4 * (fmt * i + j + d3) + 4 <= nF) ->
(forall i j, 0 <= i < N -> 0 <= j < 3 -> i < g408 -> i mod Wd < g24 -> 3 <= d4 /\ 4 * (fmt * i + j + d4) + 4 <= nF) ->
tree_at trbsegs (mrestrict (w_H W) memc) t ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 192) 8 fmt -> val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 232) 8 Wd ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 240) 8 (troot t) -> val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 312) 8 pimg ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 376) 8 d4 -> val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 384) 8 N ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 392) 8 pal -> val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 400) 8 1 ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 408) 8 g408 -> val_mem trbsegs (mrestrict (w_H W) memc) LDK_ROL 4 Slo ->
reg_get (@fp_regs fy) (8%bv : bv 5) = nan_box (Z_to_bv 32 0) -> reg_get (@fp_regs fy) (9%bv : bv 5) = nan_box (Z_to_bv 32 S255) ->
reg_get (@fp_regs fy) (18%bv : bv 5) = nan_box (Z_to_bv 32 Shi) ->
0 <= i0 < N -> getr regs 25 = w64 i0 -> getr regs 31 = w64 (fmt * i0) -> getr regs 18 = w64 fmt ->
getr regs 1 = w64 d3 -> getr regs 2 = w64 s1v -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 9 = w64 s1v ->
getr regs 22 = w64 (2 ^ 64 - 1 - flt) -> getr regs 23 = w64 flt -> getr regs 24 = w64 g24 -> getr regs 26 = w64 d2 -> getr regs 27 = w64 SB ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDH_HEAD) memc (seg_rom trbsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LDH_EXIT) mem2 (seg_rom trbsegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LDL_CLOB = false -> getr regs2 r = getr regs r) /\
(forall r : bv 5, In r LDL_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
getr regs2 25 = w64 N /\ getr regs2 31 = w64 (fmt * N) /\ getr regs2 18 = w64 fmt /\
tree_at trbsegs (mrestrict (w_H W) mem2) t /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> ~ (pg <= a < pg + pn) -> ~ (s1v - 16 <= a < s1v) ->
aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS TGLNI STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v fmt N Wd pal pimg pg pn g24 g408 d2 d3 d4 cid pos t i0 fy regs memc mdc
HJ Hfrm HinF HFW Hs1lo Hs1hi Hs16 Hfmt HN HfN HWd Hfr Hpal0 Hpal1 Hd2 Hd3 Hd4 Hg24 Hg408 HinG HG0 HG1 HGF HGW Hfull Hwf Htin Htnf Htng HlenC
HK1 HK2 HK3 HK4 Hat V192 V232 V240 V312 V376 V384 V392 V400 V408 Vrol F8 F9 F18 Hi0 G25 G31 G18 G1 G2 G3 G4 G9 G22 G23 G24 G26 G27.
eapply SRr_mono.
{ apply (LDL_loop B LAWS TGLNI STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v fmt N Wd pal pimg pg pn g24 g408 d2 d3 d4 cid pos t
HinF HFW Hs1lo Hs1hi Hs16 Hfmt HN HfN HWd Hfr Hpal0 Hpal1 Hd2 Hd3 Hd4 Hg24 Hg408 HinG HG0 HG1 HGF HGW Hfull Hwf Htin Htnf Htng HlenC
HK1 HK2 HK3 HK4 (Z.to_nat (N - 1 - i0)) fy regs memc mdc i0 ltac:(lia) Hi0).
unfold ldl_inv, ldl_core, ldl_regs, ldl_fp, ldl_mem. repeat match goal with |- _ /\ _ => split end; assumption. }
intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc2 & ((HJ2 & Hfrm2 & _ & _ & R25 & R31 & (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hat2)) & R18) & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc2|]. split; [exact Hfrm2|]. split; [exact HJ2|].
split.
{ intros r Hr. destruct (ldl_clob_cases r Hr) as [-> | Hin]; [|exact (HK r Hin)]. rewrite !getr_zero. reflexivity. }
split; [exact HF|]. split; [exact R25|]. split; [exact R31|]. split; [exact R18|].
split; [exact Hat2|]. split; [|exact HX].
intros a Ha Hn1 Hn2 Hn3. apply HM; [exact Ha|]. unfold ldl_outside. repeat split; assumption.
Qed.

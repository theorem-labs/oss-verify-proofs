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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCji YCj9 YCjd.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCjg YCje.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LNL_INVR : list (bv 5) := [2; 3; 4; 9; 18; 23; 27]%bv.
Definition LNL_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 22; 24; 25; 26; 28; 29; 30; 31]%bv.
Definition LNL_KEEP : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 23; 27]%bv.
Definition LNL_FKEEP : list (bv 5) := LNP_FKEEP.
Section c.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis TGLNI : forall fx : FPState, @tglni_spec fx rc B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trbsegs).
Variables (flt nF s1v ha fmt N pbef bfmt bb bn pimg pg pn : Z) (t : tree).
Hypothesis HinF : In (flt, nF) (ablocks B lyc Sc).
Hypothesis Hs1lo : sp0 - STK <= s1v - 16. Hypothesis Hs1hi : s1v + 416 <= sp0. Hypothesis Hs16 : s1v mod 16 = 0.
Hypothesis Hha : 0 <= ha < 2 ^ 64. Hypothesis Hfmt : 0 < fmt < 2 ^ 29. Hypothesis HN : 0 < N <= 2 ^ 29. Hypothesis HfN : fmt * N <= 2 ^ 29.
Hypothesis Hpbef : 0 <= pbef < 2 ^ 64. Hypothesis Hbfmt : 0 <= bfmt < 2 ^ 64.
Hypothesis HlenA : ha <> 0 -> 4 * (fmt * N) <= nF /\ fmt = 4.
Hypothesis Hlen : 4 * (fmt * (N - 1)) + 12 <= nF.
Hypothesis HBef : ha = 0 -> pbef <> 0 ->
0 <= bfmt <= 4 /\ bfmt * N < 2 ^ 29 /\ In (bb, bn) (ablocks B lyc Sc) /\ bb <= pbef /\ pbef + bfmt * (N - 1) + 3 <= bb + bn /\ (bb, bn) <> (flt, nF).
Hypothesis HinG : In (pg, pn) (ablocks B lyc Sc). Hypothesis HG0 : pg <= pimg. Hypothesis HG1 : pimg + N <= pg + pn.
Hypothesis HGW : forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j).
Hypothesis Hfull : tree_full t. Hypothesis Hwf : tree_forall tnode_wf t.
Hypothesis Htin : forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc).
Hypothesis Htng : forall b, In b (tree_blocks t) -> b <> (pg, pn).
Definition lnl_regs (regs : bvmap 5 word) : Prop :=
getr regs 2 = w64 s1v /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ getr regs 9 = w64 s1v /\
getr regs 18 = w64 (2 ^ 64 - 1 - flt) /\ getr regs 23 = w64 flt /\ getr regs 27 = w64 SB.
Definition lnl_mem (mem : word -> option byte) : Prop :=
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 168) 8 ha /\ val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 184) 8 pbef /\
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 192) 8 fmt /\ val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 200) 8 bfmt /\
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 240) 8 (troot t) /\ val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 312) 8 pimg /\
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 408) 8 (2 ^ 64 - 1 - pbef) /\
tree_at trbsegs (mrestrict (w_H W) mem) t.
Definition lnl_inv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (i : Z) : Prop :=
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\ frm_zero (@fp_csr fy) /\
lnl_regs regs /\ getr regs 26 = Z_to_bv 64 (fmt * i + 1) /\ getr regs 25 = Z_to_bv 64 (bfmt * i + 2) /\ getr regs 22 = w64 (N - i) /\
getr regs 20 = w64 (pimg + i) /\ getr regs 24 = w64 (pimg + i) /\ lnl_mem mem.
Lemma lnl_regs_kept : forall regs regs' : bvmap 5 word, (forall r : bv 5, In r LNL_INVR -> getr regs' r = getr regs r) -> lnl_regs regs -> lnl_regs regs'.
Proof.
intros regs regs' HK (R2 & R3 & R4 & R9 & R18 & R23 & R27). unfold lnl_regs.
rewrite (HK (2%bv : bv 5) ltac:(cbv; tauto)), (HK (3%bv : bv 5) ltac:(cbv; tauto)), (HK (4%bv : bv 5) ltac:(cbv; tauto)),
(HK (9%bv : bv 5) ltac:(cbv; tauto)), (HK (18%bv : bv 5) ltac:(cbv; tauto)), (HK (23%bv : bv 5) ltac:(cbv; tauto)),
(HK (27%bv : bv 5) ltac:(cbv; tauto)).
repeat split; assumption.
Qed.
Definition lnl_outside (a : Z) : Prop := ~ (pg <= a < pg + pn) /\ ~ (s1v - 16 <= a < s1v).
Lemma lnl_mem_kept : forall (mem mem' : word -> option byte) md,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
(forall a, 0 <= a < 2 ^ 64 -> lnl_outside a -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) ->
lnl_mem mem -> lnl_mem mem'.
Proof.
intros mem mem' md HJ HM (V168 & V184 & V192 & V200 & V240 & V312 & V408 & Hat). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Hg4096 & Hgceil & _ & _ & _ & Hpn0).
pose proof (req_size_pos pn ltac:(lia)) as [_ Hrg].
assert (Rs : 2 ^ 46 <= s1v - 16 /\ s1v + 416 <= 2 ^ 47 /\ alloc_ceiling <= s1v - 16) by (clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1; lia).
assert (SLOT : forall off v, 0 <= off -> off + 8 <= 416 -> val_mem trbsegs (mrestrict (w_H W) mem) (s1v + off) 8 v -> val_mem trbsegs (mrestrict (w_H W) mem') (s1v + off) 8 v).
{ intros off v Ho0 Ho1 V. apply (YCcz.val_mem_kept trbsegs (w_H W) (w_H W) mem mem' (s1v + off) 8 v); [|exact V].
intros j Hj. apply HM; [clear - Hj Rs Ho0 Ho1; lia|]. unfold lnl_outside. clear - Hj Rs Ho0 Ho1 Hgceil Hrg. repeat split; lia. }
split; [apply SLOT; [lia | lia | exact V168]|]. split; [apply SLOT; [lia | lia | exact V184]|]. split; [apply SLOT; [lia | lia | exact V192]|].
split; [apply SLOT; [lia | lia | exact V200]|]. split; [apply SLOT; [lia | lia | exact V240]|]. split; [apply SLOT; [lia | lia | exact V312]|].
split; [apply SLOT; [lia | lia | exact V408]|].
apply (rg_tree_at_kept (w_H W) (w_H W) mem mem' t Hat). intros b sz Hb j Hj.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b sz HAR (Htin _ Hb)) as (_ & Hb4096 & Hbceil & _).
pose proof (sep_blocks trbsegs _ LAWS lyc Sc _ _ _ b sz pg pn HAR (Htin _ Hb) HinG (Htng _ Hb)) as Hd1. unfold zdisjoint in Hd1. cbn [fst snd] in Hd1.
apply HM; [clear - Hj Hb4096 Hbceil C1; lia|]. unfold lnl_outside. clear - Hj Hd1 Hrg Hbceil Rs. repeat split; lia.
Qed.
Definition LNL_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc i0 i' : Z) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trbsegs)) md' /\
lnl_inv fy' regs' mem' md' i' /\
(forall r : bv 5, In r LNL_KEEP -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LNL_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i0 <= a < pimg + i') -> ~ (s1v - 16 <= a < s1v) -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma LNL_pixel : forall (i : Z) (fy : FPState) regs mem md, 0 <= i < N -> lnl_inv fy regs mem md i ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_HEAD) mem (seg_rom trbsegs)) md)
(LNL_post fy regs mem (if i + 1 =? N then LNB_EXIT else LNP_HEAD) i (i + 1)).
Proof.
intros i fy regs mem md Hi (HJ & Hfrm & HR & G26 & G25 & G22 & G20 & G24 & HMm).
pose proof HR as (R2 & R3 & R4 & R9 & R18 & R23 & R27).
pose proof HMm as (V168 & V184 & V192 & V200 & V240 & V312 & V408 & Hat).
pose proof asan_consts as (C1 & _). pose proof HJ as (HAR & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (Rs : 2 ^ 46 <= s1v - 16 /\ s1v + 416 <= 2 ^ 47 /\ alloc_ceiling <= s1v - 16) by (clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1; lia).
assert (Hfi : 0 <= fmt * i /\ fmt * i <= fmt * (N - 1) /\ fmt * (N - 1) + fmt = fmt * N).
{ split; [apply Z.mul_nonneg_nonneg; lia|]. split; [apply Z.mul_le_mono_nonneg_l; lia | lia]. }
destruct Hfi as (Hfi0 & Hfi1 & Hfi2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (troot t) NODE_SIZE HAR (Htin _ (ldl_root_blk t Hfull))) as (_ & Hn4096 & Hnceil & _).
change (req_size NODE_SIZE) with 56 in Hnceil.
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (Hf16 & Hf4096 & Hfceil & _ & _ & _ & Hnf0).
pose proof (req_size_pos nF ltac:(lia)) as [_ Hrf].
eapply SRr_bind.
{ apply (rga_lnd_cmp B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v ha (fmt * i) (bfmt * i) pbef bb bn (pimg + i) pimg pg pn fy regs mem md HJ Hfrm HinF
ltac:(clear - Hs1lo; lia) Hs1hi Hha ltac:(clear - Hfi0 Hfi1 Hfi2 HfN Hfmt; lia) Hpbef).
- intros Hh. destruct (HlenA Hh) as (Hl & E4). clear - Hl E4 Hi. rewrite E4 in *. lia.
- intros _ _. clear - Hlen Hfi1. lia.
- intros Hh Hp. destruct (HBef Hh Hp) as (Hb4 & HbN & HinB & HB0 & HB1 & HBF).
assert (Hbi : 0 <= bfmt * i /\ bfmt * i <= bfmt * (N - 1)) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
split; [clear - Hbi HbN Hb4 HN; nia|]. split; [exact HinB|]. split; [exact HB0|]. split; [clear - Hbi HB1; lia | exact HBF].
- exact HinG. - exact HG0. - clear - Hi; lia. - clear - Hi HG1; lia.
- exact V168. - exact V184. - exact V312. - exact V408.
- rewrite G26. reflexivity. - rewrite G25. reflexivity. - exact G24. - exact R23. - exact R18. - exact R27. - exact R9. }
intros W1 c1 _ (-> & d & fy1 & regs1 & mem1 & md1 & -> & Hfrm1 & HJ1 & HK1 & HF1 & R12 & H10 & HM1 & HX1).
assert (K1 : forall r : bv 5, In r (20%bv :: 22%bv :: 24%bv :: 25%bv :: 26%bv :: LNL_INVR ++ LNL_KEEP) -> getr regs1 r = getr regs r).
{ intros r Hr. apply HK1. revert Hr. clear. cbv [LNL_INVR LNL_KEEP app In]. intros Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
assert (HMm1 : lnl_mem mem1) by (apply (lnl_mem_kept mem mem1 md HJ); [intros a Ha _; exact (HM1 a Ha) | exact HMm]).
pose proof HMm1 as (V168a & V184a & V192a & V200a & V240a & V312a & V408a & Hat1).
assert (STORE : forall (fy2 : FPState) regs2 mem2 md2,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k -> frm_zero (@fp_csr fy2) ->
(forall r : bv 5, In r (20%bv :: 22%bv :: 24%bv :: 25%bv :: 26%bv :: LNL_INVR ++ LNL_KEEP) -> getr regs2 r = getr regs r) ->
(forall r : bv 5, In r LNL_FKEEP -> reg_get (@fp_regs fy2) r = reg_get (@fp_regs fy) r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v - 16 <= a < s1v) -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
SRr trbsegs W (mkCfg (@mkst fy2 regs2 (Z_to_bv 64 LNP_STORE) mem2 (seg_rom trbsegs)) md2)
(LNL_post fy regs mem (if i + 1 =? N then LNB_EXIT else LNP_HEAD) i (i + 1))).
{ intros fy2 regs2 mem2 md2 HJ2 Hfrm2 K2 F2 M2 X2.
assert (HMm2 : lnl_mem mem2) by (apply (lnl_mem_kept mem mem2 md HJ); [intros a Ha (_ & Hn); exact (M2 a Ha Hn) | exact HMm]).
pose proof HMm2 as (V168b & V184b & V192b & V200b & V240b & V312b & V408b & Hat2).
assert (HB2 : lnb_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v fy2 regs2 mem2 md2).
{ split; [exact HJ2|]. split; [exact Hfrm2|]. split; [rewrite (K2 (27%bv : bv 5) ltac:(cbv; tauto)); exact R27 | rewrite (K2 (9%bv : bv 5) ltac:(cbv; tauto)); exact R9]. }
eapply SRr_mono.
{ apply (LNBS_run B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v ltac:(clear - Hs1lo; lia) Hs1hi (pimg + i) pimg pg pn HinG HG0 ltac:(clear - Hi; lia) ltac:(clear - Hi HG1; lia) HGW
fy2 regs2 mem2 md2 (N - i) (bfmt * i + 2) (fmt * i + 1) fmt bfmt HB2).
- rewrite (K2 (20%bv : bv 5) ltac:(cbv; tauto)). exact G20.
- rewrite (K2 (24%bv : bv 5) ltac:(cbv; tauto)). exact G24.
- rewrite (K2 (22%bv : bv 5) ltac:(cbv; tauto)). exact G22.
- clear - Hi HN. lia.
- rewrite (K2 (25%bv : bv 5) ltac:(cbv; tauto)). exact G25.
- rewrite (K2 (26%bv : bv 5) ltac:(cbv; tauto)). exact G26.
- clear - Hfmt. lia. - exact Hbfmt. - exact V192b. - exact V200b. }
intros W3 c3 _ (-> & regs3 & mem3 & md3 & Hc3 & HJ3 & Q20 & Q24 & Q22 & Q25 & Q26 & HK3 & HM3 & HX3).
replace (N - i - 1 =? 0) with (i + 1 =? N) in Hc3 by (clear; destruct (Z.eqb_spec (i + 1) N), (Z.eqb_spec (N - i - 1) 0); lia).
split; [reflexivity|]. exists fy2, regs3, mem3, md3. split; [exact Hc3|].
assert (M3 : forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i <= a < pimg + (i + 1)) -> ~ (s1v - 16 <= a < s1v) -> aview trbsegs (w_H W) mem3 a = aview trbsegs (w_H W) mem a).
{ intros a Ha Hn1 Hn2. rewrite (HM3 a Ha ltac:(clear - Hn1; lia)). exact (M2 a Ha Hn2). }
split.
{ split; [exact HJ3|]. split; [exact Hfrm2|].
split; [apply (lnl_regs_kept regs regs3); [|exact HR]; intros r Hr; rewrite (HK3 r ltac:(revert Hr; clear; cbv [LNL_INVR LNBS_KEEP In]; tauto));
apply K2; right; right; right; right; right; apply in_or_app; left; exact Hr|].
split; [rewrite Q26; f_equal; lia|]. split; [rewrite Q25; f_equal; lia|]. split; [rewrite Q22; unfold w64; f_equal; lia|].
split; [rewrite Q20; unfold w64; f_equal; lia|]. split; [rewrite Q24; unfold w64; f_equal; lia|].
apply (lnl_mem_kept mem mem3 md HJ); [|exact HMm]. intros a Ha (Hn1 & Hn2). apply M3; [exact Ha | clear - Hn1 HG0 HG1 Hi; lia | exact Hn2]. }
split; [intros r Hr; rewrite (HK3 r ltac:(revert Hr; clear; cbv [LNL_KEEP LNBS_KEEP In]; tauto)); apply K2; right; right; right; right; right; apply in_or_app; right; exact Hr|].
split; [exact F2|]. split; [exact M3|]. intros a Ha. apply HX3. apply X2. exact Ha. }
destruct d.
-
assert (HB1 : lnb_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v fy1 regs1 mem1 md1).
{ split; [exact HJ1|]. split; [exact Hfrm1|]. split; [rewrite (K1 (27%bv : bv 5) ltac:(cbv; tauto)); exact R27 | rewrite (K1 (9%bv : bv 5) ltac:(cbv; tauto)); exact R9]. }
eapply SRr_bind.
{ apply (LNBA_run B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v HinF ltac:(clear - Hs1lo; lia) Hs1hi fy1 regs1 mem1 md1 (fmt * i) (troot t) HB1
ltac:(clear - Hfi0 Hfi1 Hfi2 HfN Hfmt; lia) ltac:(clear - Hlen Hfi1; lia) ltac:(clear - Hn4096 Hnceil C1; lia) R12).
- rewrite (K1 (23%bv : bv 5) ltac:(cbv; tauto)). exact R23.
- rewrite (K1 (18%bv : bv 5) ltac:(cbv; tauto)). exact R18.
- exact V240a. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Q1 & Q10 & Q11 & HK2 & HM2 & HX2).
assert (Hat2 : tree_at trbsegs (mrestrict (w_H W) mem2) t).
{ apply (rg_tree_at_kept (w_H W) (w_H W) mem1 mem2 t Hat1). intros b sz Hb j Hj. apply HM2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b sz HAR (Htin _ Hb)) as (_ & Hb4096 & Hbceil & _). clear - Hj Hb4096 Hbceil C1. lia. }
assert (Hsp2 : spZ regs2 = s1v).
{ unfold spZ. rewrite (HK2 (2%bv : bv 5) ltac:(cbv; tauto)), (K1 (2%bv : bv 5) ltac:(cbv; tauto)), R2. apply unsigned_lit_small. clear - Rs. lia. }
eapply SRr_bind.
{ eapply (TGLNI fy1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k regs2 flt nF (flt + 4 * (fmt * i)) t HJ2).
- rewrite Q1. apply ret_ok_even; vm_compute; reflexivity.
- unfold raZ. rewrite Q1, unsigned_lit_small by (unfold LNB_RET; clear; lia). unfold LNB_RET. clear. lia.
- rewrite Hsp2. exact Hs16.
- rewrite Hsp2. unfold TGLNI_STK. exact Hs1lo.
- rewrite Hsp2. clear - Hs1hi. lia.
- exact Hfrm1.
- exact Q10.
- exact Q11.
- exact HinF.
- clear - Hfi0. lia.
- clear - Hlen Hfi1. lia.
- replace (flt + 4 * (fmt * i)) with (flt + (fmt * i) * 4) by lia. rewrite Z.mod_add by lia.
clear - Hf16. pose proof (Z.div_mod flt 16 ltac:(lia)). replace flt with (4 * (4 * (flt / 16))) by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
- exact Hfull.
- exact Hwf.
- exact Hat2.
- exact Htin. }
cbv beta. intros W3 c3 _ (-> & fy3 & regs3 & mem3 & md3 & -> & Hfrm3 & HF3 & HJ3 & HP3 & _ & HM3 & HX3).
assert (CS : forall (r : bv 5) z, acallee_saved z -> bv_unsigned r = z -> getr regs3 r = getr regs2 r) by (intros r z Hz Hr; exact (ldg_cs regs2 regs3 z HP3 Hz r Hr)).
assert (K3 : forall r : bv 5, In r (20%bv :: 22%bv :: 24%bv :: 25%bv :: 26%bv :: LNL_INVR ++ LNL_KEEP) -> getr regs3 r = getr regs r).
{ intros r Hr. rewrite <- (K1 r Hr). cbv [LNL_INVR LNL_KEEP app In] in Hr.
repeat (destruct Hr as [<- | Hr]; [lazymatch goal with |- getr regs3 ?r = _ => let z := eval vm_compute in (bv_unsigned r) in rewrite (CS r z ltac:(unfold acallee_saved; lia) eq_refl) end; apply HK2; cbv; tauto|]). destruct Hr. }
assert (M3 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v - 16 <= a < s1v) -> aview trbsegs (w_H W) mem3 a = aview trbsegs (w_H W) mem a).
{ intros a Ha Hn. rewrite (HM3 a Ha ltac:(rewrite Hsp2; unfold TGLNI_STK; exact Hn)), (HM2 a Ha). exact (HM1 a Ha). }
assert (HMm3 : lnl_mem mem3) by (apply (lnl_mem_kept mem mem3 md HJ); [intros a Ha (_ & Hn); exact (M3 a Ha Hn) | exact HMm]).
pose proof HMm3 as (_ & _ & _ & _ & _ & V312c & _).
assert (HB3 : lnb_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v fy3 regs3 mem3 md3).
{ split; [exact HJ3|]. split; [exact Hfrm3|]. split; [rewrite (K3 (27%bv : bv 5) ltac:(cbv; tauto)); exact R27 | rewrite (K3 (9%bv : bv 5) ltac:(cbv; tauto)); exact R9]. }
rewrite Q1.
eapply SRr_bind.
{ apply (LNBB_run B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v ltac:(clear - Hs1lo; lia) Hs1hi (pimg + i) pimg pg pn HinG HG0 ltac:(clear - Hi; lia) ltac:(clear - Hi HG1; lia)
fy3 regs3 mem3 md3 HB3); [rewrite (K3 (24%bv : bv 5) ltac:(cbv; tauto)); exact G24 | exact V312c]. }
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HK4 & HM4 & HX4).
apply (STORE fy3 regs4 mem4 md4 HJ4 Hfrm3).
+ intros r Hr. rewrite <- (K3 r Hr). apply HK4. revert Hr. clear. cbv [LNL_INVR LNL_KEEP LNBB_KEEP app In]. tauto.
+ intros r Hr. rewrite (HF3 r ltac:(revert Hr; clear; cbv [LNL_FKEEP LNP_FKEEP TGLNI_FKEEP In]; tauto)). exact (HF1 r Hr).
+ intros a Ha Hn. rewrite (HM4 a Ha). exact (M3 a Ha Hn).
+ intros a Ha. apply HX4. apply HX3. apply HX2. apply HX1. exact Ha.
-
apply (STORE fy1 regs1 mem1 md1 HJ1 Hfrm1 K1 HF1); [intros a Ha _; exact (HM1 a Ha) | exact HX1].
Qed.
Lemma lnl_post_trans : forall fy regs mem (fy1 : FPState) regs1 mem1 pc i0 i1 i' W' c', i0 <= i1 -> i1 <= i' ->
(forall r : bv 5, In r LNL_KEEP -> getr regs1 r = getr regs r) ->
(forall r : bv 5, In r LNL_FKEEP -> reg_get (@fp_regs fy1) r = reg_get (@fp_regs fy) r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i0 <= a < pimg + i1) -> ~ (s1v - 16 <= a < s1v) -> aview trbsegs (w_H W) mem1 a = aview trbsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
LNL_post fy1 regs1 mem1 pc i1 i' W' c' -> LNL_post fy regs mem pc i0 i' W' c'.
Proof.
intros fy regs mem fy1 regs1 mem1 pc i0 i1 i' W' c' H01 H1' K1 F1 M1 X1 (HW & fy' & regs' & mem' & md' & Hc & HI & K & F & M & X).
split; [exact HW|]. exists fy', regs', mem', md'. split; [exact Hc|]. split; [exact HI|].
split; [intros r Hr; rewrite (K r Hr); exact (K1 r Hr)|]. split; [intros r Hr; rewrite (F r Hr); exact (F1 r Hr)|].
split; [|intros a Ha; apply X; apply X1; exact Ha].
intros a Ha Hn1 Hn2. rewrite (M a Ha ltac:(clear - Hn1 H01; lia) Hn2). apply (M1 a Ha ltac:(clear - Hn1 H1'; lia) Hn2).
Qed.
Lemma LNL_loop : forall (n : nat) (fy : FPState) regs mem md (i : Z),
Z.of_nat n = N - 1 - i -> 0 <= i < N -> lnl_inv fy regs mem md i ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_HEAD) mem (seg_rom trbsegs)) md) (LNL_post fy regs mem LNB_EXIT i N).
Proof.
induction n as [|n IH]; intros fy regs mem md i Hn Hi HI.
- assert (Hlast : i + 1 = N) by lia.
eapply SRr_mono; [exact (LNL_pixel i fy regs mem md Hi HI)|].
intros W' c' _ (HW & fy' & regs' & mem' & md' & Hc & HI' & HK & HF & HM & HX).
replace (i + 1 =? N) with true in Hc by (symmetry; apply Z.eqb_eq; exact Hlast). rewrite Hlast in HI', HM.
split; [exact HW|]. exists fy', regs', mem', md'. split; [exact Hc|]. split; [exact HI'|]. split; [exact HK|]. split; [exact HF|]. split; [exact HM | exact HX].
- eapply SRr_bind; [exact (LNL_pixel i fy regs mem md Hi HI)|].
intros W' c' _ (-> & fy1 & regs1 & mem1 & md1 & Hc & HI1 & HKa & HFa & HMa & HXa).
replace (i + 1 =? N) with false in Hc by (symmetry; apply Z.eqb_neq; lia). subst c'.
eapply SRr_mono; [exact (IH fy1 regs1 mem1 md1 (i + 1) ltac:(lia) ltac:(lia) HI1)|].
intros W'' c'' _ H. exact (lnl_post_trans fy regs mem fy1 regs1 mem1 _ i (i + 1) N W'' c'' ltac:(lia) ltac:(lia) HKa HFa HMa HXa H).
Qed.
End c.
Lemma lnl_clob_cases : forall r : bv 5, reg_in r LNL_CLOB = false -> r = 0%bv \/ In r LNL_KEEP.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Lemma rga_lnd_loop {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trbsegs B -> (forall fx : FPState, @tglni_spec fx rc B) ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v ha fmt N pbef bfmt bb bn pimg pg pn (t : tree) i0 (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> frm_zero (@fp_csr fy) ->
In (flt, nF) (ablocks B lyc Sc) -> sp0 - STK <= s1v - 16 -> s1v + 416 <= sp0 -> s1v mod 16 = 0 ->
0 <= ha < 2 ^ 64 -> 0 < fmt < 2 ^ 29 -> 0 < N <= 2 ^ 29 -> fmt * N <= 2 ^ 29 -> 0 <= pbef < 2 ^ 64 -> 0 <= bfmt < 2 ^ 64 ->
(ha <> 0 -> 4 * (fmt * N) <= nF /\ fmt = 4) -> 4 * (fmt * (N - 1)) + 12 <= nF ->
(ha = 0 -> pbef <> 0 ->
0 <= bfmt <= 4 /\ bfmt * N < 2 ^ 29 /\ In (bb, bn) (ablocks B lyc Sc) /\ bb <= pbef /\ pbef + bfmt * (N - 1) + 3 <= bb + bn /\ (bb, bn) <> (flt, nF)) ->
In (pg, pn) (ablocks B lyc Sc) -> pg <= pimg -> pimg + N <= pg + pn ->
(forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j)) ->
tree_full t -> tree_forall tnode_wf t ->
(forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc)) -> (forall b, In b (tree_blocks t) -> b <> (pg, pn)) ->
tree_at trbsegs (mrestrict (w_H W) memc) t ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 168) 8 ha -> val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 184) 8 pbef ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 192) 8 fmt -> val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 200) 8 bfmt ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 240) 8 (troot t) -> val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 312) 8 pimg ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 408) 8 (2 ^ 64 - 1 - pbef) ->
0 <= i0 < N -> getr regs 26 = Z_to_bv 64 (fmt * i0 + 1) -> getr regs 25 = Z_to_bv 64 (bfmt * i0 + 2) -> getr regs 22 = w64 (N - i0) ->
getr regs 20 = w64 (pimg + i0) -> getr regs 24 = w64 (pimg + i0) ->
getr regs 2 = w64 s1v -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 9 = w64 s1v ->
getr regs 18 = w64 (2 ^ 64 - 1 - flt) -> getr regs 23 = w64 flt -> getr regs 27 = w64 SB ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_HEAD) memc (seg_rom trbsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LNB_EXIT) mem2 (seg_rom trbsegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LNL_CLOB = false -> getr regs2 r = getr regs r) /\
(forall r : bv 5, In r LNL_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
getr regs2 22 = w64 0 /\ getr regs2 20 = w64 (pimg + N) /\ getr regs2 24 = w64 (pimg + N) /\
tree_at trbsegs (mrestrict (w_H W) mem2) t /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i0 <= a < pimg + N) -> ~ (s1v - 16 <= a < s1v) -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS TGLNI STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v ha fmt N pbef bfmt bb bn pimg pg pn t i0 fy regs memc mdc
HJ Hfrm HinF Hs1lo Hs1hi Hs16 Hha Hfmt HN HfN Hpbef Hbfmt HlenA Hlen HBef HinG HG0 HG1 HGW Hfull Hwf Htin Htng Hat V168 V184 V192 V200 V240 V312 V408
Hi0 G26 G25 G22 G20 G24 G2 G3 G4 G9 G18 G23 G27.
assert (HI : lnl_inv B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt s1v ha fmt N pbef bfmt pimg t fy regs memc mdc i0).
{ unfold lnl_inv, lnl_regs, lnl_mem. repeat match goal with |- _ /\ _ => split end; assumption. }
eapply SRr_mono; [exact (LNL_loop B LAWS TGLNI STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v ha fmt N pbef bfmt bb bn pimg pg pn t
HinF Hs1lo Hs1hi Hs16 Hha Hfmt HN HfN Hpbef Hbfmt HlenA Hlen HBef HinG HG0 HG1 HGW Hfull Hwf Htin Htng
(Z.to_nat (N - 1 - i0)) fy regs memc mdc i0 ltac:(lia) Hi0 HI)|].
intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc2 & (HJ2 & Hfrm2 & _ & _ & _ & R22 & R20 & R24 & (_ & _ & _ & _ & _ & _ & _ & Hat2)) & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc2|]. split; [exact Hfrm2|]. split; [exact HJ2|].
split.
{ intros r Hr. destruct (lnl_clob_cases r Hr) as [-> | Hin]; [|exact (HK r Hin)]. rewrite !getr_zero. reflexivity. }
split; [exact HF|]. split; [rewrite R22; unfold w64; f_equal; lia|]. split; [exact R20|]. split; [exact R24|].
split; [exact Hat2|]. split; [exact HM | exact HX].
Qed.

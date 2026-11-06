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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC68 YC66 YC63 YC64.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LNL_INVR : list (bv 5) := [9; 10; 11; 15; 16; 17; 25; 29; 31]%bv.
Definition LNL_CLOB : list (bv 5) := [5; 6; 7; 12; 13; 14; 28]%bv.
Definition LNL_KEEP : list (bv 5) := [1; 2; 3; 4; 8; 9; 10; 11; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%bv.
Definition LNL_FKEEP : list (bv 5) := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma lnl_leaf_obj : forall m t nl, tree_at trasegs m t -> In nl (tree_leaves t) ->
exists c0 c1 leafv, obj_at trasegs m (tn_addr nl) LAY_Node (node_vals c0 c1 nl leafv) /\ length (tn_mean nl) = 3%nat /\ In (tn_addr nl, NODE_SIZE) (tree_blocks t).
Proof.
intros m. induction t as [|n|n l IHl r IHr]; intros nl Hat Hin; cbn [tree_leaves tree_at tree_blocks] in *.
- destruct Hin.
- destruct Hin as [<- | []]. destruct Hat as (_ & Hlen & c0 & c1 & Ho). exists c0, c1, 1. split; [exact Ho|]. split; [exact Hlen | left; reflexivity].
- destruct Hat as (_ & _ & _ & Hl & Hr). apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
+ destruct (IHl nl Hl Hin) as (c0 & c1 & lv & Ho & Hlen & Hb). exists c0, c1, lv. split; [exact Ho|]. split; [exact Hlen|]. right. apply in_app_iff. left. exact Hb.
+ destruct (IHr nl Hr Hin) as (c0 & c1 & lv & Ho & Hlen & Hb). exists c0, c1, lv. split; [exact Ho|]. split; [exact Hlen|]. right. apply in_app_iff. right. exact Hb.
Qed.
Lemma lnl_root_obj : forall m t, tree_full t -> tree_at trasegs m t ->
exists n c0 c1 leafv, troot t = tn_addr n /\ In (tn_addr n, NODE_SIZE) (tree_blocks t) /\ length (tn_mean n) = 3%nat /\
obj_at trasegs m (tn_addr n) LAY_Node (node_vals c0 c1 n leafv) /\
((leafv = 1 /\ t = TLeaf n) \/ (leafv = 0 /\ exists l r, t = TNode n l r)).
Proof.
intros m t Hf Hat. destruct t as [|n|n l r]; [destruct Hf | |]; cbn [tree_at troot tree_blocks] in *.
- destruct Hat as (_ & Hlen & c0 & c1 & Ho). exists n, c0, c1, 1. split; [reflexivity|]. split; [left; reflexivity|]. split; [exact Hlen|]. split; [exact Ho|]. left. split; reflexivity.
- destruct Hat as (_ & Hlen & Ho & _ & _). exists n, (troot l), (troot r), 0. split; [reflexivity|]. split; [left; reflexivity|]. split; [exact Hlen|]. split; [exact Ho|]. right. split; [reflexivity|]. exists l, r. reflexivity.
Qed.
Section c.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trasegs).
Variables (flt nF s1v ha fmt N pbef bfmt bb bn pimg pg pn : Z) (t : tree).
Hypothesis HinF : In (flt, nF) (ablocks B lyc Sc).
Hypothesis Hs1lo : sp0 - STK <= s1v. Hypothesis Hs1hi : s1v + 384 <= sp0.
Hypothesis Hha : 0 <= ha < 2 ^ 64. Hypothesis Hfmt : 0 < fmt < 2 ^ 29. Hypothesis HN : 0 < N <= 2 ^ 29. Hypothesis HfN : fmt * N <= 2 ^ 29.
Hypothesis Hpbef : 0 <= pbef < 2 ^ 64.
Hypothesis HlenA : ha <> 0 -> 4 * (fmt * N) <= nF /\ fmt = 4.
Hypothesis Hlen : 4 * (fmt * (N - 1)) + 12 <= nF.
Hypothesis HBef : ha = 0 -> pbef <> 0 ->
0 <= bfmt <= 4 /\ bfmt * N < 2 ^ 29 /\ In (bb, bn) (ablocks B lyc Sc) /\ bb <= pbef /\ pbef + bfmt * (N - 1) + 3 <= bb + bn /\ (bb, bn) <> (flt, nF).
Hypothesis HinG : In (pg, pn) (ablocks B lyc Sc). Hypothesis HG0 : pg <= pimg. Hypothesis HG1 : pimg + N <= pg + pn.
Hypothesis HGW : forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j).
Hypothesis Hfull : tree_full t. Hypothesis Hwf : tree_forall tnode_wf t.
Hypothesis Htin : forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc).
Hypothesis Htnf : forall b, In b (tree_blocks t) -> b <> (flt, nF).
Hypothesis Htng : forall b, In b (tree_blocks t) -> b <> (pg, pn).
Definition lnl_regs (regs : bvmap 5 word) : Prop :=
getr regs 31 = w64 flt /\ getr regs 25 = w64 SB /\ getr regs 9 = w64 s1v /\ getr regs 10 = w64 ha /\ getr regs 29 = w64 fmt /\
getr regs 15 = w64 N /\ getr regs 11 = w64 (troot t + 50) /\ getr regs 17 = Z_to_bv 64 (SB + (troot t + 50) / 8) /\
getr regs 16 = Z_to_bv 64 (Z.land (troot t + 50) 7).
Definition lnl_mem (mem : word -> option byte) : Prop :=
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 176) 8 pbef /\ val_mem trasegs (mrestrict (w_H W) mem) (s1v + 240) 8 (troot t) /\
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 256) 8 bfmt /\ val_mem trasegs (mrestrict (w_H W) mem) (s1v + 376) 8 pimg /\
tree_at trasegs (mrestrict (w_H W) mem) t.
Definition lnl_inv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (i : Z) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\ frm_zero (@fp_csr fy) /\
lnl_regs regs /\ getr regs 14 = w64 i /\ lnl_mem mem.
Lemma lnl_regs_kept : forall regs regs' : bvmap 5 word, (forall r : bv 5, In r LNL_INVR -> getr regs' r = getr regs r) -> lnl_regs regs -> lnl_regs regs'.
Proof.
intros regs regs' HK (R31 & R25 & R9 & R10 & R29 & R15 & R11 & R17 & R16). unfold lnl_regs.
rewrite (HK (31%bv : bv 5) ltac:(cbv; tauto)), (HK (25%bv : bv 5) ltac:(cbv; tauto)), (HK (9%bv : bv 5) ltac:(cbv; tauto)),
(HK (10%bv : bv 5) ltac:(cbv; tauto)), (HK (29%bv : bv 5) ltac:(cbv; tauto)), (HK (15%bv : bv 5) ltac:(cbv; tauto)),
(HK (11%bv : bv 5) ltac:(cbv; tauto)), (HK (17%bv : bv 5) ltac:(cbv; tauto)), (HK (16%bv : bv 5) ltac:(cbv; tauto)).
repeat split; assumption.
Qed.
Lemma lnl_mem_kept : forall (mem mem' : word -> option byte) md lo hi,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
(lo = hi \/ (pg <= lo /\ hi <= pg + pn)) -> lnl_mem mem -> lnl_mem mem'.
Proof.
intros mem mem' md lo hi HJ HM Hlh (V176 & V240 & V256 & V376 & Hat). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Hg4096 & Hgceil & _ & _ & _ & Hpn0).
pose proof (req_size_pos pn ltac:(lia)) as [_ Hrg].
assert (Rs : 2 ^ 46 <= s1v /\ s1v + 384 <= 2 ^ 47 /\ alloc_ceiling <= s1v) by (clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1; lia).
assert (SLOT : forall off v, 0 <= off -> off + 8 <= 384 -> val_mem trasegs (mrestrict (w_H W) mem) (s1v + off) 8 v -> val_mem trasegs (mrestrict (w_H W) mem') (s1v + off) 8 v).
{ intros off v Ho0 Ho1 V. apply (YC04.val_mem_kept trasegs (w_H W) (w_H W) mem mem' (s1v + off) 8 v); [|exact V].
intros j Hj. apply HM; [clear - Hj Rs Ho0 Ho1; lia|]. destruct Hlh as [-> | [Hl Hh]]; [lia|]. clear - Hj Rs Ho0 Ho1 Hl Hh Hgceil Hrg. lia. }
split; [apply SLOT; [lia | lia | exact V176]|]. split; [apply SLOT; [lia | lia | exact V240]|].
split; [apply SLOT; [lia | lia | exact V256]|]. split; [apply SLOT; [lia | lia | exact V376]|].
apply (rg_tree_at_kept (w_H W) (w_H W) mem mem' t Hat). intros b sz Hb j Hj.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b sz HAR (Htin _ Hb)) as (_ & Hb4096 & Hbceil & _).
apply HM; [clear - Hj Hb4096 Hbceil C1; lia|]. destruct Hlh as [-> | [Hl Hh]]; [lia|].
pose proof (sep_blocks trasegs _ LAWS lyc Sc _ _ _ b sz pg pn HAR (Htin _ Hb) HinG (Htng _ Hb)) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
clear - Hj Hl Hh Hd Hrg. lia.
Qed.
Definition LNL_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc i' lo hi : Z) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trasegs)) md' /\
lnl_inv fy' regs' mem' md' i' /\
(forall r : bv 5, In r LNL_KEEP -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LNL_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma lnl_post_trans : forall fy regs mem (fy1 : FPState) regs1 mem1 pc i' lo hi W' c',
(forall r : bv 5, In r LNL_KEEP -> getr regs1 r = getr regs r) ->
(forall r : bv 5, In r LNL_FKEEP -> reg_get (@fp_regs fy1) r = reg_get (@fp_regs fy) r) ->
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem1 a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
LNL_post fy1 regs1 mem1 pc i' lo hi W' c' -> LNL_post fy regs mem pc i' lo hi W' c'.
Proof.
intros fy regs mem fy1 regs1 mem1 pc i' lo hi W' c' K1 F1 M1 X1 (HW & fy' & regs' & mem' & md' & Hc & HI & K & F & M & X).
split; [exact HW|]. exists fy', regs', mem', md'. split; [exact Hc|]. split; [exact HI|].
split; [intros r Hr; rewrite (K r Hr); exact (K1 r Hr)|]. split; [intros r Hr; rewrite (F r Hr); exact (F1 r Hr)|].
split; [intros a Ha Hn; rewrite (M a Ha Hn); exact (M1 a Ha)|]. intros a Ha. apply X. apply X1. exact Ha.
Qed.
Local Ltac lnl_inK := cbv [LNL_KEEP LNL_INVR In]; tauto.
Section e.
Variable i : Z.
Hypothesis Hi : 0 <= i < N.
Lemma LNL_store_tail : forall (fy : FPState) regs mem md, lnl_inv fy regs mem md i ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNS_STORE) mem (seg_rom trasegs)) md)
(LNL_post fy regs mem (if i + 1 =? N then LNS_EXIT else LNS_NEXT) (i + 1) (pimg + i) (pimg + i + 1)).
Proof.
intros fy regs mem md (HJ & Hfrm & HR & G14 & HMm). pose proof HR as (R31 & R25 & R9 & R10 & R29 & R15 & R11 & R17 & R16).
pose proof HMm as (V176 & V240 & V256 & V376 & Hat).
eapply SRr_mono; [exact (rga_lnd_store B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v pimg pg pn i N fy regs mem md HJ Hfrm Hs1lo Hs1hi HinG HG0
ltac:(lia) ltac:(lia) ltac:(lia) HGW V376 R9 G14 R15 R25)|].
intros W' c' _ (HW & fy' & regs' & mem' & md' & Hc & Hfrm' & HJ' & R14' & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs', mem', md'. split; [exact Hc|].
split.
{ split; [exact HJ'|]. split; [exact Hfrm'|].
split; [apply (lnl_regs_kept regs regs'); [intros r Hr; apply HK; revert Hr; clear; cbv [LNL_INVR LNS_KEEP2 In]; tauto | exact HR]|].
split; [exact R14'|]. apply (lnl_mem_kept mem mem' md (pimg + i) (pimg + i + 1) HJ HM); [right; lia | exact HMm]. }
split; [intros r Hr; apply HK; revert Hr; clear; cbv [LNL_KEEP LNS_KEEP2 In]; tauto|].
split; [intros r _; apply HF|]. split; [exact HM | exact HX].
Qed.
Lemma LNL_leaf_tail : forall (fy : FPState) regs mem md (nl : tnode) c0 c1 leafv, lnl_inv fy regs mem md i ->
getr regs 6 = w64 (tn_addr nl) -> In (tn_addr nl, NODE_SIZE) (tree_blocks t) ->
obj_at trasegs (mrestrict (w_H W) mem) (tn_addr nl) LAY_Node (node_vals c0 c1 nl leafv) -> length (tn_mean nl) = 3%nat ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNS_LEAF) mem (seg_rom trasegs)) md)
(LNL_post fy regs mem (if i + 1 =? N then LNS_EXIT else LNS_NEXT) (i + 1) (pimg + i) (pimg + i + 1)).
Proof.
intros fy regs mem md nl c0 c1 leafv HI G6 Hnb Ond Hlen3. pose proof HI as (HJ & Hfrm & HR & G14 & HMm).
pose proof HR as (R31 & R25 & R9 & R10 & R29 & R15 & R11 & R17 & R16).
eapply SRr_bind; [exact (rga_lnd_leaf B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W (tn_addr nl) nl c0 c1 leafv fy regs mem md HJ Hfrm (Htin _ Hnb) Ond Hlen3 G6 R25)|].
intros W' c' _ (-> & fy1 & regs1 & mem1 & md1 & -> & Hfrm1 & HJ1 & HK1 & HF1 & HM1 & HX1).
assert (HI1 : lnl_inv fy1 regs1 mem1 md1 i).
{ split; [exact HJ1|]. split; [exact Hfrm1|].
split; [apply (lnl_regs_kept regs regs1); [intros r Hr; apply HK1; revert Hr; clear; cbv [LNL_INVR LNS_KEEP1 In]; tauto | exact HR]|].
split; [rewrite (HK1 (14%bv : bv 5) ltac:(cbv; tauto)); exact G14|].
apply (lnl_mem_kept mem mem1 md 0 0 HJ (fun a Ha _ => HM1 a Ha)); [left; reflexivity | exact HMm]. }
eapply SRr_mono; [exact (LNL_store_tail fy1 regs1 mem1 md1 HI1)|].
intros W'' c'' _ H. apply (lnl_post_trans fy regs mem fy1 regs1 mem1 _ _ _ _ W'' c''); [| | exact HM1 | exact HX1 | exact H].
- intros r Hr. apply HK1. revert Hr. clear. cbv [LNL_KEEP LNS_KEEP1 In]. tauto.
- intros r _. apply HF1.
Qed.
Lemma LNL_pixel : forall (fy : FPState) regs mem md, lnl_inv fy regs mem md i ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_HEAD) mem (seg_rom trasegs)) md)
(LNL_post fy regs mem (if i + 1 =? N then LNS_EXIT else LNS_NEXT) (i + 1) (pimg + i) (pimg + i + 1)).
Proof.
intros fy regs mem md HI. pose proof HI as (HJ & Hfrm & HR & G14 & HMm).
pose proof HR as (R31 & R25 & R9 & R10 & R29 & R15 & R11 & R17 & R16).
pose proof HMm as (V176 & V240 & V256 & V376 & Hat).
assert (Hfi : 0 <= fmt * i /\ fmt * i <= fmt * (N - 1) /\ fmt * (N - 1) + fmt = fmt * N).
{ split; [apply Z.mul_nonneg_nonneg; lia|]. split; [apply Z.mul_le_mono_nonneg_l; lia | lia]. }
assert (Ht0 : fmt * i < 2 ^ 29) by (clear - Hfi HfN Hfmt HN; lia).
eapply SRr_bind.
{ apply (rga_lnd_cmp B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v ha fmt i pbef bfmt bb bn fy regs mem md HJ Hfrm HinF Hs1lo Hs1hi Hha ltac:(lia)
ltac:(lia) Ht0 Hpbef); [ | | | exact V176 | exact V256 | exact R10 | exact R29 | exact G14 | exact R31 | exact R25 | exact R9 ].
- intros Hh. destruct (HlenA Hh) as [Hl H4]. rewrite H4 in Hl. rewrite H4. clear - Hl Hi. lia.
- intros _ _. clear - Hlen Hfi. lia.
- intros Hh Hp. destruct (HBef Hh Hp) as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6).
assert (Hbi : 0 <= bfmt * i /\ bfmt * i <= bfmt * (N - 1) /\ bfmt * (N - 1) + bfmt = bfmt * N).
{ split; [apply Z.mul_nonneg_nonneg; lia|]. split; [apply Z.mul_le_mono_nonneg_l; lia | lia]. }
split; [exact Hb1|]. split; [clear - Hbi Hb2 Hb1 HN; lia|]. split; [exact Hb3|]. split; [exact Hb4|]. split; [clear - Hbi Hb5; lia | exact Hb6]. }
intros W1 c1 _ (-> & d & fy1 & regs1 & mem1 & md1 & -> & Hfrm1 & HJ1 & HK1 & HF1 & R5 & H13 & HM1 & HX1).
assert (HI1 : lnl_inv fy1 regs1 mem1 md1 i).
{ split; [exact HJ1|]. split; [exact Hfrm1|].
split; [apply (lnl_regs_kept regs regs1); [intros r Hr; apply HK1; revert Hr; clear; cbv [LNL_INVR In]; intros Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr | exact HR]|].
split; [rewrite (HK1 (14%bv : bv 5) eq_refl); exact G14|].
apply (lnl_mem_kept mem mem1 md 0 0 HJ (fun a Ha _ => HM1 a Ha)); [left; reflexivity | exact HMm]. }
assert (K1 : forall r : bv 5, In r LNL_KEEP -> getr regs1 r = getr regs r).
{ intros r Hr. apply HK1. revert Hr. clear. cbv [LNL_KEEP In]. intros Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
assert (F1 : forall r : bv 5, In r LNL_FKEEP -> reg_get (@fp_regs fy1) r = reg_get (@fp_regs fy) r).
{ intros r Hr. apply HF1. revert Hr. clear. cbv [LNL_FKEEP LNP_FKEEP In]. tauto. }
destruct d.
2:{
eapply SRr_mono; [exact (LNL_store_tail fy1 regs1 mem1 md1 HI1)|].
intros W'' c'' _ H. exact (lnl_post_trans fy regs mem fy1 regs1 mem1 _ _ _ _ W'' c'' K1 F1 HM1 HX1 H). }
pose proof HI1 as (_ & _ & HR1 & G14' & HMm1). pose proof HR1 as (R31' & R25' & R9' & R10' & R29' & R15' & R11' & R17' & R16').
pose proof HMm1 as (V176' & V240' & V256' & V376' & Hat1).
destruct (lnl_root_obj _ t Hfull Hat1) as (n & c0 & c1 & leafv & Eroot & Hnb & Hlen3 & Ond & Hcase).
rewrite Eroot in R11', R17', R16', V240'.
assert (Hlv : leafv = 0 \/ leafv = 1) by (destruct Hcase as [[-> _] | [-> _]]; [right | left]; reflexivity).
eapply SRr_bind.
{ exact (rga_lnd_root B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v (tn_addr n) (fmt * i) n c0 c1 leafv fy1 regs1 mem1 md1 HJ1 Hfrm1 HinF Hs1lo Hs1hi
(Htin _ Hnb) ltac:(lia) ltac:(clear - Hlen Hfi; lia) V240' Ond Hlen3 Hlv R5 R11' R17' R16' R31' R25' R9'). }
intros W2 c2 _ (-> & fy2 & regs2 & mem2 & md2 & -> & Hfrm2 & HJ2 & HK2 & HF2 & R6 & R5b & HM2 & HX2).
assert (HI2 : lnl_inv fy2 regs2 mem2 md2 i).
{ split; [exact HJ2|]. split; [exact Hfrm2|].
split; [apply (lnl_regs_kept regs1 regs2); [intros r Hr; apply HK2; revert Hr; clear; cbv [LNL_INVR In]; intros Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr | exact HR1]|].
split; [rewrite (HK2 (14%bv : bv 5) eq_refl); exact G14'|].
apply (lnl_mem_kept mem1 mem2 md1 0 0 HJ1 (fun a Ha _ => HM2 a Ha)); [left; reflexivity | exact HMm1]. }
assert (K2 : forall r : bv 5, In r LNL_KEEP -> getr regs2 r = getr regs r).
{ intros r Hr. rewrite <- (K1 r Hr). apply HK2. revert Hr. clear. cbv [LNL_KEEP In]. intros Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
assert (F2 : forall r : bv 5, In r LNL_FKEEP -> reg_get (@fp_regs fy2) r = reg_get (@fp_regs fy) r) by (intros r Hr; rewrite (HF2 r); exact (F1 r Hr)).
assert (M2 : forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) mem a) by (intros a Ha; rewrite (HM2 a Ha); exact (HM1 a Ha)).
assert (X2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) by (intros a Ha; apply HX2; apply HX1; exact Ha).
pose proof HI2 as (_ & _ & HR2 & G14b & HMm2). pose proof HMm2 as (_ & _ & _ & _ & Hat2).
destruct Hcase as [[-> Et] | [-> (l & r & Et)]]; cbn [Z.eqb] in R5b |- *.
-
assert (Ond2 : obj_at trasegs (mrestrict (w_H W) mem2) (tn_addr n) LAY_Node (node_vals c0 c1 n 1)).
{ destruct (lnl_leaf_obj _ t n Hat2 ltac:(rewrite Et; left; reflexivity)) as (c0' & c1' & lv' & Ho' & _ & _).
apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem1 mem2 (tn_addr n) LAY_Node _ NODE_SIZE Ond (proj1 lay_inside_Node)).
intros j Hj. apply HM2. pose proof HJ1 as (HAR1 & _). pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR1 (Htin _ Hnb)) as (_ & Hb4096 & Hbceil & _). change (req_size NODE_SIZE) with 56 in Hbceil. unfold NODE_SIZE in Hj. lia. }
eapply SRr_mono; [exact (LNL_leaf_tail fy2 regs2 mem2 md2 n c0 c1 1 HI2 R6 Hnb Ond2 Hlen3)|].
intros W'' c'' _ H. exact (lnl_post_trans fy regs mem fy2 regs2 mem2 _ _ _ _ W'' c'' K2 F2 M2 X2 H).
-
pose proof HJ2 as (HAR2 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR2 HinF) as (Hf16 & _).
assert (Hr4 : (flt + 4 * (fmt * i)) mod 4 = 0).
{ replace (flt + 4 * (fmt * i)) with (flt + (fmt * i) * 4) by lia. rewrite Z.mod_add by lia.
clear - Hf16. pose proof (Z.mod_pos_bound flt 16 ltac:(lia)). pose proof (Z.div_mod flt 16 ltac:(lia)).
replace flt with (4 * (4 * (flt / 16))) by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
pose proof HR2 as (R31b & R25b & _).
eapply SRr_bind.
{ exact (rga_lnd_descent B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF (flt + 4 * (fmt * i)) t fy2 regs2 mem2 md2 HJ2 Hfrm2 HinF
ltac:(clear - Hfi; lia) ltac:(clear - Hlen Hfi; lia) Hr4 Hfull Hwf Hat2 Htin Htnf ltac:(exists n, l, r; exact Et)
ltac:(rewrite Eroot; exact R6) R5b R25b). }
intros W3 c3 _ (-> & fy3 & regs3 & mem3 & md3 & -> & Hfrm3 & HJ3 & HK3 & HF3 & (nl & Hnl & R6c) & HM3 & HX3).
assert (HI3 : lnl_inv fy3 regs3 mem3 md3 i).
{ split; [exact HJ3|]. split; [exact Hfrm3|].
split; [apply (lnl_regs_kept regs2 regs3); [intros r0 Hr; apply HK3; revert Hr; clear; cbv [LNL_INVR In]; intros Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr | exact HR2]|].
split; [rewrite (HK3 (14%bv : bv 5) eq_refl); exact G14b|].
apply (lnl_mem_kept mem2 mem3 md2 0 0 HJ2 (fun a Ha _ => HM3 a Ha)); [left; reflexivity | exact HMm2]. }
pose proof HI3 as (_ & _ & _ & _ & (_ & _ & _ & _ & Hat3)).
destruct (lnl_leaf_obj _ t nl Hat3 Hnl) as (c0' & c1' & lv' & Ond3 & Hlen3' & Hnb3).
eapply SRr_mono; [exact (LNL_leaf_tail fy3 regs3 mem3 md3 nl c0' c1' lv' HI3 R6c Hnb3 Ond3 Hlen3')|].
intros W'' c'' _ H. apply (lnl_post_trans fy regs mem fy3 regs3 mem3 _ _ _ _ W'' c''); [| | | | exact H].
+ intros r0 Hr. rewrite <- (K2 r0 Hr). apply HK3. revert Hr. clear. cbv [LNL_KEEP In]. intros Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr.
+ intros r0 Hr. rewrite <- (F2 r0 Hr). apply HF3. revert Hr. clear. cbv [LNL_FKEEP LND_FKEEP In]. tauto.
+ intros a Ha. rewrite (HM3 a Ha). exact (M2 a Ha).
+ intros a Ha. apply HX3. apply X2. exact Ha.
Qed.
End e.
Lemma LNL_loop : forall (n : nat) (fy : FPState) regs mem md (i : Z),
Z.of_nat n = N - 1 - i -> 0 <= i < N -> lnl_inv fy regs mem md i ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_HEAD) mem (seg_rom trasegs)) md) (LNL_post fy regs mem LNS_EXIT N (pimg + i) (pimg + N)).
Proof.
induction n as [|n IH]; intros fy regs mem md i Hn Hi HI.
- assert (Hlast : i + 1 = N) by lia.
eapply SRr_mono; [exact (LNL_pixel i Hi fy regs mem md HI)|].
intros W' c' _ (HW & fy' & regs' & mem' & md' & Hc & HI' & HK & HF & HM & HX).
replace (i + 1 =? N) with true in Hc by (symmetry; apply Z.eqb_eq; exact Hlast). rewrite Hlast in HI'.
split; [exact HW|]. exists fy', regs', mem', md'. split; [exact Hc|]. split; [exact HI'|]. split; [exact HK|]. split; [exact HF|].
split; [intros a Ha Hna; apply HM; [exact Ha | lia] | exact HX].
- eapply SRr_bind; [exact (LNL_pixel i Hi fy regs mem md HI)|].
intros W' c' _ (-> & fy1 & regs1 & mem1 & md1 & Hc & HI1 & HK1 & HF1 & HM1 & HX1).
replace (i + 1 =? N) with false in Hc by (symmetry; apply Z.eqb_neq; lia). subst c'.
eapply SRr_mono; [exact (IH fy1 regs1 mem1 md1 (i + 1) ltac:(lia) ltac:(lia) HI1)|].
intros W'' c'' _ (HW & fy' & regs' & mem' & md' & Hc' & HI' & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs', mem', md'. split; [exact Hc'|]. split; [exact HI'|].
split; [intros r Hr; rewrite (HK r Hr); exact (HK1 r Hr)|]. split; [intros r Hr; rewrite (HF r Hr); exact (HF1 r Hr)|].
split; [intros a Ha Hna; rewrite (HM a Ha ltac:(lia)); apply HM1; [exact Ha | lia]|].
intros a Ha. apply HX. apply HX1. exact Ha.
Qed.
End c.
Lemma lnl_clob_cases : forall r : bv 5, reg_in r LNL_CLOB = false -> r = 0%bv \/ In r LNL_KEEP.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Lemma rga_lnd_loop {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trasegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v ha fmt N pbef bfmt bb bn pimg pg pn (t : tree) i0 (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> frm_zero (@fp_csr fy) ->
In (flt, nF) (ablocks B lyc Sc) -> sp0 - STK <= s1v -> s1v + 384 <= sp0 ->
0 <= ha < 2 ^ 64 -> 0 < fmt < 2 ^ 29 -> 0 < N <= 2 ^ 29 -> fmt * N <= 2 ^ 29 -> 0 <= pbef < 2 ^ 64 ->
(ha <> 0 -> 4 * (fmt * N) <= nF /\ fmt = 4) -> 4 * (fmt * (N - 1)) + 12 <= nF ->
(ha = 0 -> pbef <> 0 ->
0 <= bfmt <= 4 /\ bfmt * N < 2 ^ 29 /\ In (bb, bn) (ablocks B lyc Sc) /\ bb <= pbef /\ pbef + bfmt * (N - 1) + 3 <= bb + bn /\ (bb, bn) <> (flt, nF)) ->
In (pg, pn) (ablocks B lyc Sc) -> pg <= pimg -> pimg + N <= pg + pn ->
(forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j)) ->
tree_full t -> tree_forall tnode_wf t ->
(forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc)) -> (forall b, In b (tree_blocks t) -> b <> (flt, nF)) ->
(forall b, In b (tree_blocks t) -> b <> (pg, pn)) ->
tree_at trasegs (mrestrict (w_H W) memc) t ->
val_mem trasegs (mrestrict (w_H W) memc) (s1v + 176) 8 pbef -> val_mem trasegs (mrestrict (w_H W) memc) (s1v + 240) 8 (troot t) ->
val_mem trasegs (mrestrict (w_H W) memc) (s1v + 256) 8 bfmt -> val_mem trasegs (mrestrict (w_H W) memc) (s1v + 376) 8 pimg ->
0 <= i0 < N -> getr regs 14 = w64 i0 -> getr regs 15 = w64 N -> getr regs 10 = w64 ha -> getr regs 29 = w64 fmt ->
getr regs 11 = w64 (troot t + 50) -> getr regs 17 = Z_to_bv 64 (SB + (troot t + 50) / 8) -> getr regs 16 = Z_to_bv 64 (Z.land (troot t + 50) 7) ->
getr regs 31 = w64 flt -> getr regs 25 = w64 SB -> getr regs 9 = w64 s1v ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_HEAD) memc (seg_rom trasegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LNS_EXIT) mem2 (seg_rom trasegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LNL_CLOB = false -> getr regs2 r = getr regs r) /\
(forall r : bv 5, In r LNL_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
getr regs2 14 = w64 N /\ tree_at trasegs (mrestrict (w_H W) mem2) t /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i0 <= a < pimg + N) -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v ha fmt N pbef bfmt bb bn pimg pg pn t i0 fy regs memc mdc
HJ Hfrm HinF Hs1lo Hs1hi Hha Hfmt HN HfN Hpbef HlenA Hlen HBef HinG HG0 HG1 HGW Hfull Hwf Htin Htnf Htng Hat V176 V240 V256 V376
Hi0 G14 G15 G10 G29 G11 G17 G16 G31 G25 G9.
assert (HI : lnl_inv B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt s1v ha fmt N pbef bfmt pimg t fy regs memc mdc i0).
{ split; [exact HJ|]. split; [exact Hfrm|]. split; [repeat (split; [assumption|]); assumption|]. split; [exact G14|]. repeat (split; [assumption|]). assumption. }
eapply SRr_mono; [exact (LNL_loop B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v ha fmt N pbef bfmt bb bn pimg pg pn t
HinF Hs1lo Hs1hi Hha Hfmt HN HfN Hpbef HlenA Hlen HBef HinG HG0 HG1 HGW Hfull Hwf Htin Htnf Htng
(Z.to_nat (N - 1 - i0)) fy regs memc mdc i0 ltac:(lia) Hi0 HI)|].
intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc2 & (HJ2 & Hfrm2 & _ & R14 & (_ & _ & _ & _ & Hat2)) & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc2|]. split; [exact Hfrm2|]. split; [exact HJ2|].
split.
{ intros r Hr. destruct (lnl_clob_cases r Hr) as [-> | Hin]; [|exact (HK r Hin)]. rewrite !getr_zero. reflexivity. }
split; [exact HF|]. split; [exact R14|]. split; [exact Hat2|]. split; [exact HM | exact HX].
Qed.

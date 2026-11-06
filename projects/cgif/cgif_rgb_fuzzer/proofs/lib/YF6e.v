(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG02 YG06 YG03 YG0h YG10 YG0u YG0d YG0y YG0w YG0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF0k YF6m YF6b YF6i YF6k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF07 YF0r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. img_refl. Qed.
Lemma amreal_ask_depot {imgk : img} {R} : forall trc s (k : Z -> itree astate R) (Wx : world tfxsegs) c Q,
SRr tfxsegs Wx c (fun W1 c1 => exists z, aok s (KDepot trc) z /\ amreal tfxsegs (k z) W1 c1 Q) ->
amreal tfxsegs (IAsk (KDepot trc) s k) Wx c Q.
Proof. intros trc s k Wx c Q H. img_exact H. Qed.
Lemma match_nonnull {A} : forall (q : sptr) (a b : A), q <> PNull -> match q with PNull => a | _ => b end = b.
Proof. intros q a b H. destruct q; [img_try (congruence) | img_refl | img_refl | img_refl]. Qed.
Ltac inlist := cbn [In]; repeat (first [ left; img_refl | right ]); fail.
Section f. Context {imgk : img}.
Variable B : asyms.
Lemma depot_mem_ok_agree : forall ly S S' rd rd',
Wf (as_universe B) S -> universe_ok (as_universe B) -> st_depot S' = st_depot S ->
(forall a, depot_footprint B ly a -> rd' a = rd a) -> depot_mem_ok B ly S rd -> depot_mem_ok B ly S' rd'.
Proof.
intros ly S S' rd rd' W HU HD AG (DC & DO & DV).
assert (NB : depot_ids S <= 4097).
{ unfold depot_ids. pose proof (wf_depot _ _ _ _ _ W) as [ND INC]. pose proof (NoDup_incl_length ND INC). destruct HU as (U1 & _). unfold DEPOT_MAX in U1. img_lia. }
assert (ED : depot_cells ly S' = depot_cells ly S) by (img_try (unfold depot_cells, depot_ids, depot_frames; rewrite HD; img_refl)).
split; [|img_try (split)].
- rewrite ED. img_apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly rd); [img_try (img_exact (proj1 (Forall_forall _ _) DC c Hc))|].
intros k Hk. img_apply AG. unfold depot_cells in Hc. cbn [In] in Hc. unfold depot_footprint, d_map1, d_nuniq, s_total, s_block0, kNodesBlockSize, kStoreBlockSize in *.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hk |- *; img_lia.
- destruct DO as (heads & links & D1 & D2 & D3). exists heads, links. unfold depot_ids, depot_traces in *. rewrite HD. split; [|img_try (split; [|img_exact D3])].
+ intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [img_try (img_exact H1)|]. intros k Hk. rewrite AG; [img_try (img_exact (H2 k Hk))|].
unfold depot_footprint, d_tab_words, d_map1 in *. left. img_lia.
+ intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [img_try (img_exact H1)|].
split; intros k Hk; rewrite AG; auto; unfold depot_footprint, kNodesBlockSize; right; left; img_lia.
- img_apply Forall_forall. intros r Hr i Hi. rewrite AG; [img_try (img_exact (proj1 (Forall_forall _ _) DV r Hr i Hi))|].
cbn [In] in Hr. unfold depot_footprint, d_map1, d_nuniq, kNodesBlockSize, kStoreBlockSize in *.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn in Hi |- *; img_lia.
Qed.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (p : sptr) (n : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly (0x53640 + D_2c4) regs ch.
Let sp0 : Z := bv_unsigned (getr regs 2).
Let pa : Z := sptr_addr B ly p.
Let nn : Z := req_size n.
Hypothesis PRE : acall_pre tfxsegs B ly S W regs mem md ch.
Hypothesis HBLK : In (p, n) (blocks S).
Hypothesis HA0 : getr regs 10 = w64 pa.
Hypothesis HU : In tr (as_universe B).
Variables (lastb : batch) (initr : list batch).
Hypothesis ARM : rev (qc_list (st_qthread S)) = lastb :: initr /\ Z.of_nat (length (b_items lastb)) < kBatchSlots /\
qc_bytes (st_qthread S) + nn <= kQuarantineCacheMax.
Hypothesis IA1 : tfx_ialloc_spec.
Hypothesis U1 : tfx_unwind_spec.
Hypothesis D1 : tfx_depot_spec B.
Variables (hb1 j1 j2 j3 : Z).
Hypothesis FH : free_hyps W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S).
Variable regsD : bvmap 5 word.
Hypothesis REGSD : forall extra : list word, regs_ok (Ereg regs extra) REGS_DC regsD.
Hypothesis STKD : forall extra : list word, nth 4 extra (w64 0) = w64 (Z.of_nat (length tr)) ->
Forall (region_ok tfxsegs (Ereg regs extra) (mrestrict (w_H W) mem)) [R_OBJ; R_SCR; R_TOP].
Hypothesis HQ12 : 4096 <= bv_unsigned (getr regs 12) <= 2 ^ 47.
Hypothesis Hii : st_internal_inited S = true.
Hypothesis TRQ0 : YF6i.TRACEQ W ly regs ch mem.
Definition rfree_leaf (r : unit * astate) (W' : world tfxsegs) (c' : config) : Prop :=
free_leaf tfxsegs B ly S W regs mem md p n r W' c' /\
exists regs' mem' md', c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\ getr regs' 10 = getr regs 12.
Let s1 : astate := set_internal_inited true (set_nev (st_nev S + 1) S).
Lemma s1_wf : Wf (as_universe B) s1.
Proof.
destruct PRE as ((M & _ & _) & Hev & _).
img_apply (WfP_weaken _ 1 1 1); try img_lia. unfold s1. img_apply WfP_set_internal_inited. img_apply WfP_tick; [img_try (img_exact (am_wf B ly S _ M)) | img_try (img_exact Hev)].
Qed.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Definition low_ok {imgk : img} (a w : Z) : bool :=
(TFX_IMG_LO <=? a) && ((a + w <=? TFX_IAL_LO) || (TFX_IAL_HI <=? a) && (a + w <=? TFX_IAL_FLAG) || (TFX_IAL_FLAG + 4 <=? a) && (a + w <=? TFX_IMG_END)
|| (SHADOW_OFF + TFX_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFX_IMG_END / 8)).
Definition const_loc_ok {imgk : img} (c : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w c)) in
match c_at c with
| ANum a => low_ok a w
| AT k => (0 <=? k) && (k + w <=? 80)
| AC k => (0 <=? k) && (k + w <=? 256)
| ATsd k => low_ok (TFX_TSD + k) w
| ATp k => low_ok (TFX_TP + k) w
| AInst k => low_ok (TFX_INST + k) w
| AD k => (0 <=? k) && (k + w <=? 4096)
| _ => false
end.
Lemma Tfx_const_loc : forallb const_loc_ok (Tfx_const ly) = true.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma CONST_OUT : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) ->
~ YF6m.WIN ly regs pa lastb (aeval B ly (c_at c) + i) /\ ~ YF6m.IZONE (aeval B ly (c_at c) + i) /\
0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). img_apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) Tfx_const_loc c Hc) as K. unfold const_loc_ok in K.
assert (LOW : forall a, low_ok a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ YF6m.WIN ly regs pa lastb (a + i) /\ ~ YF6m.IZONE (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L. unfold low_ok in L. set (w := Z.max 1 (Z.of_nat (c_w c))) in *.
assert (R : (TFX_IMG_LO <= a /\ a + w <= TFX_IAL_LO) \/ (TFX_IAL_HI <= a /\ a + w <= TFX_IAL_FLAG) \/ (TFX_IAL_FLAG + 4 <= a /\ a + w <= TFX_IMG_END) \/
(SHADOW_OFF + TFX_IMG_LO / 8 <= a /\ a + w <= SHADOW_OFF + TFX_IMG_END / 8)) by img_lia.
clear L. unfold YF6m.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_IMG_LO, TFX_IMG_END, SHADOW_OFF in *.
img_change (65536 / 8) with 8192 in R. img_change ((6287360 + D_1000) / 8) with (785920 + D_200) in R.
split; [|img_lia]. destruct R as [R|[R|[R|R]]].
1-3: img_apply (YF6m.notWIN_img W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); unfold TFX_IMG_LO, TFX_IMG_END; img_lia.
img_apply (YF6m.notWIN_shb W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); unfold kLowShadowBeg, kHighMemBeg; img_lia. }
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- pose proof (YF6m.LYB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (LB & _). ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in LB.
split; [img_try (img_apply (YF6m.notWIN_Thead W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); img_lia)|].
unfold YF6m.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG. img_lia.
- pose proof (YF6m.LYB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (_ & _ & _ & _ & _ & _ & LB & _). ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in LB.
split; [img_try (img_apply (YF6m.notWIN_C W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); img_lia)|].
unfold YF6m.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG. img_lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- pose proof (YF6m.LYBD W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (HD1 & HD2 & _). ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HD1, HD2.
split; [img_try (img_apply (YF6m.notWIN_D W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); img_lia)|].
unfold YF6m.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG. img_lia.
Qed.
Lemma DFP_RANGE : forall a, depot_footprint B ly a -> 0 <= a < 2 ^ 64.
Proof.
destruct PRE as ((M & _) & _). pose proof (YF6m.LYB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as LB.
intros a Ha. unfold depot_footprint in Ha. rewrite (ts_depot _ TB), (ts_store _ TB) in Ha.
ceil; unfold zone3, TFX_DEPOT, TFX_STORE, d_map1, kHighMemBeg, ASAN_CEIL, kNodesBlockSize, kStoreBlockSize in *. img_lia.
Qed.
Lemma DFP_OUT : forall a, depot_footprint B ly a -> ~ YF6m.WIN ly regs pa lastb a /\ ~ YF6m.IZONE a /\ YF6m.DZONE ly a.
Proof.
pose proof (YF6m.LYB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as LB.
intros a Ha. unfold depot_footprint in Ha. rewrite (ts_depot _ TB), (ts_store _ TB) in Ha. unfold YF6m.IZONE, YF6m.DZONE.
pose proof LB as (_ & _ & _ & _ & _ & _ & _ & _ & ZNB & _ & ZSB & _). unfold zone3, zone3cases in ZNB, ZSB.
ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, TFX_DEPOT, TFX_STORE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, d_map1, kHighMemBeg, ASAN_CEIL, kNodesBlockSize, kStoreBlockSize in *.
destruct Ha as [Ha|[Ha|[Ha|Ha]]].
- split; [img_try (img_apply (YF6m.notWIN_img W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); unfold TFX_IMG_LO, TFX_IMG_END; img_lia) | img_lia].
- split; [img_try (img_apply (YF6m.notWIN_NB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); unfold kNodesBlockSize; img_lia) | img_lia].
- split; [img_try (img_apply (YF6m.notWIN_SB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); unfold kStoreBlockSize; img_lia) | img_lia].
- split; [img_try (img_apply (YF6m.notWIN_img W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH); unfold TFX_IMG_LO, TFX_IMG_END; img_lia) | img_lia].
Qed.
Lemma CONST_ZONE : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) ->
~ (YF6m.SPv pa <= aeval B ly (c_at c) + i < YF6m.SPv pa + YF6m.CNT8v nn)) (as_const B ly).
Proof.
rewrite (ts_const _ TB). img_apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) Tfx_const_loc c Hc) as K. unfold const_loc_ok in K.
pose proof (YF6m.LYB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (ZT & _ & _ & _ & _ & _ & ZC & _).
pose proof (YF6m.LYBD W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (ZD & _).
pose proof (YF6m.derived_ranges W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (_ & _ & SH1 & SH2 & SH3 & P8 & N81 & N82 & N83 & _).
pose proof (fh_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (_ & _ & ZP).
unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize, YF6m.N8v in ZT, ZC, ZD, ZP.
unfold YF6m.CNT8v, YF6m.N8v in *. rewrite SH3 in *. ceil. unfold ASAN_CEIL, kHighMemBeg, SHADOW_OFF in *.
assert (LOW : forall a, low_ok a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ (2147450880 + pa / 8 <= a + i < 2147450880 + pa / 8 + (nn + 7) / 8 * 8 / 8)).
{ intros a L. unfold low_ok in L. set (w := Z.max 1 (Z.of_nat (c_w c))) in *.
assert (R : (TFX_IMG_LO <= a /\ a + w <= TFX_IAL_LO) \/ (TFX_IAL_HI <= a /\ a + w <= TFX_IAL_FLAG) \/ (TFX_IAL_FLAG + 4 <= a /\ a + w <= TFX_IMG_END) \/
(SHADOW_OFF + TFX_IMG_LO / 8 <= a /\ a + w <= SHADOW_OFF + TFX_IMG_END / 8)) by img_lia.
clear L K. unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_IMG_LO, TFX_IMG_END, SHADOW_OFF in R. img_change (65536 / 8) with 8192 in R. img_change ((6287360 + D_1000) / 8) with (785920 + D_200) in R.
assert (R' : (65536 <= a /\ a + w <= (6287360 + D_1000)) \/ (2147450880 + 8192 <= a /\ a + w <= 2147450880 + (785920 + D_200))) by (img_try (clear - R; img_lia)). clear R. rename R' into R.
rewrite Z_div_mult in * by img_lia. pose proof (Z.div_pos pa 8 ltac:(img_lia) ltac:(img_lia)).
destruct R as [R|R]; [img_lia|].
destruct ZP as [Z1|[Z2|Z3]].
- assert (Y : (pa + (nn + 7) / 8 * 8) / 8 <= 65536 / 8) by (img_try (img_apply Z.div_le_mono; img_lia)). rewrite Z.div_add in Y by img_lia. img_change (65536 / 8) with 8192 in Y. img_lia.
- assert (Y : (6287360 + D_1000) / 8 <= pa / 8) by (img_try (img_apply Z.div_le_mono; img_lia)). img_change ((6287360 + D_1000) / 8) with (785920 + D_200) in Y. img_lia.
- assert (Y : 17594333495296 / 8 <= pa / 8) by (img_try (img_apply Z.div_le_mono; img_lia)). img_change (17594333495296 / 8) with 2199291686912 in Y. img_lia. }
rewrite Z_div_mult in * by img_lia. pose proof (Z.div_pos pa 8 ltac:(img_lia) ltac:(img_lia)).
destruct (c_at c); try discriminate K; cbn [aeval]; try (apply LOW, K).
- clear LOW. assert (Y : (pa + (nn + 7) / 8 * 8) / 8 <= 140737479966720 / 8) by (img_try (img_apply Z.div_le_mono; img_lia)). rewrite Z.div_add in Y by img_lia. img_change (140737479966720 / 8) with 17592184995840 in Y. img_lia.
- clear LOW. assert (Y : (pa + (nn + 7) / 8 * 8) / 8 <= 140737479966720 / 8) by (img_try (img_apply Z.div_le_mono; img_lia)). rewrite Z.div_add in Y by img_lia. img_change (140737479966720 / 8) with 17592184995840 in Y. img_lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- clear LOW. assert (Y : (pa + (nn + 7) / 8 * 8) / 8 <= 140737479966720 / 8) by (img_try (img_apply Z.div_le_mono; img_lia)). rewrite Z.div_add in Y by img_lia. img_change (140737479966720 / 8) with 17592184995840 in Y. img_lia.
Qed.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfxsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfxsegs H m (a + Z.of_nat kk) = Some (YG0h.le_byte v w kk).
Proof.
intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. img_change (YG0h.le_byte v w kk) with (YP0g.le_byte v w kk). f_equal. img_apply unsigned_lit_small8.
unfold YP0g.le_byte. img_apply Z.mod_pos_bound. img_lia.
Qed.
Definition fin_hyp : Prop := forall z k (msD : machine_state) mem4 W' c',
find_user (st_chunks S) p = Some k ->
aok s1 (KDepot tr) z ->
MEQI W ly regs mem pa lastb (ms_mem msD) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msD) a) ->
(forall x : word, ~ (sp0 - 2256 - DEP_STK <= bv_unsigned x < sp0 - 2256) -> ~ depot_footprint B ly (bv_unsigned x) -> mem4 x = ms_mem msD x) ->
(forall a, apresent (w_H W) (ms_mem msD) a -> apresent (w_H W) mem4 a) ->
depot_mem_ok B ly (depot_after z tr s1) (aview tfxsegs (w_H W) mem4) ->
Forall (cell_holds B ly (aview tfxsegs (w_H W) mem4)) (as_const B ly) ->
YF6k.at_RET W ly regs md pa nn hb1 (st_qthread S) lastb mem4 W' c' ->
let k' := {| ck_beg := ck_beg k; ck_req := ck_req k; ck_state := CQuarantined |} in
let sd := depot_after z tr s1 in
rfree_leaf (tt, set_qthread (qc_push (st_qthread S) k' None) (set_chunks (upd_chunk (st_chunks sd) k') sd)) W' c'.
Lemma FINH : fin_hyp.
Proof.
intros z k msD mem4 W' c' Hf AOK MEQD PRESD Hfr4 Hpr4 DEPOK HC4 HR.
destruct PRE as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT). destruct HAR as (M & LED & BUD & MW & HSH).
pose proof (find_user_block _ 0 0 0 S p n (am_wf B ly S _ M) HBLK) as (k0 & Hf0 & Hk & Hst & Hu & Hr). rewrite Hf in Hf0. injection Hf0 as <-.
destruct ARM as (Hrev & Hroom & Hcache).
destruct HR as (-> & regs' & mem' & mat & -> & CS & A0 & EQS4 & PRES' & PRESW & VALS).
pose proof (fh_Hhb1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as HB1. pose proof (fh_Hhb1m _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as HB1M. unfold YF6m.HB1MASK in HB1M.
cbv zeta. set (rd := aview tfxsegs (w_H W) mem) in *. set (rd' := aview tfxsegs (w_H W) mem').
assert (Epa : pa = sptr_addr B ly (ck_user k)) by (img_try (unfold pa; rewrite Hu; img_refl)).
assert (Enn : nn = ck_n k) by (img_try (unfold nn, ck_n; rewrite Hr; img_refl)).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (YF0r.ext_rounded B ly S rd M k lastb Hk) as (ER & NN1 & NN2 & NN3).
assert (HSP : ly_stk_lo ly + ASTACK <= sp0 <= ly_stk_hi ly) by (img_try (unfold spZ in *; unfold sp0; img_lia)).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YF0r.D B ly k lastb sp0 a -> rd' a = rd a).
{ intros a Ha ND. (subst rd rd'; cbv beta). img_apply aview_same.
assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (img_try (img_apply unsigned_lit_small; img_exact Ha)).
unfold YF0r.D, YF0r.DT, YF0r.DK, YF0r.DB, YF0r.DS, YF0r.DI, YF0r.DH in ND. rewrite <- Epa, <- Enn in ND.
assert (NW : ~ YF6m.WIN ly regs pa lastb a).
{ intros X. img_apply ND. clear ND. unfold YF6m.WIN, YF6m.WINT, YF6m.WINB, YF6m.Bv, YF6m.SLOTv, YF6m.BCv, YF6m.Bv in X. fold sp0 in X.
destruct X as [X|[X|X]]; [img_try (do 3 right; left; img_exact X) | img_try (left; clear - X; unfold YF0r.DT; img_lia) | img_try (right)].
destruct X as [X|[X|[X|X]]]; [img_try (left; left; img_exact X) | img_try (left; right; img_exact X) | img_try (right; left; left; img_exact X) | img_try (right; left; right; img_exact X)]. }
rewrite (proj1 EQS4 (Z_to_bv 64 a)); rewrite ?Ux.
2:{ intros X. img_apply NW. img_exact (YF6m.WIN2_WIN ly regs pa lastb a X). }
2:{ intros X. img_apply ND. do 6 right. clear - X NN2. unfold YF6m.SPv, YF6m.CNT8v, YF6m.N8v, shadow_addr in *. rewrite Z_div_mult in X by img_lia. img_lia. }
rewrite Hfr4; rewrite ?Ux.
2:{ intros X. img_apply ND. do 3 right; left. clear - X. unfold YF0r.DS, DEP_STK, ASTACK in *. img_lia. }
2:{ intros X. img_apply ND. do 5 right; left; img_exact X. }
img_apply (proj1 MEQD); rewrite ?Ux; [img_try (img_exact NW)|].
intros X. img_apply ND. do 4 right; left. unfold YF6m.IZONE in X. unfold YF0r.DI. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB). img_exact X. }
assert (EM : forall lo hi a, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (img_try (intros; img_lia)).
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. (subst rd rd'; cbv beta). unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [img_try (img_exact (Hv HN))|].
destruct (seg_rom tfxsegs x) eqn:ROM; [img_try (destruct (mem' x); discriminate)|].
destruct (mem' x) as [|] eqn:E'; [img_try (discriminate)|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [img_try (clear Hv) | img_try (img_exact (Hv eq_refl))].
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (img_try ((subst a'; cbv beta); img_apply u64_range)).
assert (Ex : Z_to_bv 64 a' = x) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
assert (NIMG : ~ (0x10000 <= a' < (0x5ff000 + D_1000))).
{ intros X. img_apply (tfx_rom_all a' X). rewrite Ex. img_exact ROM. }
assert (PRX : forall m, apresent (w_H W) m a' -> m x = None -> False).
{ intros m [_ [bb Hb]] Hm. rewrite Ex in Hb. congruence. }
destruct (EM (YF6m.SPv pa) (YF6m.SPv pa + YF6m.CNT8v nn) a') as [C1|C1].
{ rewrite (proj2 EQS4 x C1) in E'. discriminate. }
assert (EMW : YF6m.WIN ly regs pa lastb a' \/ ~ YF6m.WIN ly regs pa lastb a').
{ unfold YF6m.WIN, YF6m.WINT, YF6m.WINB. clear - EM.
repeat match goal with |- (?A \/ ?Bq) \/ ~ _ => first [ destruct (EM _ _ a' : A \/ ~ A) as [?|?]; [img_try (left; left; assumption)|] | idtac ];
cut ((Bq) \/ ~ (Bq)); [img_try (tauto)|] end. img_apply EM. }
destruct EMW as [C2|C2].
{ unfold YF6m.WIN in C2. destruct C2 as [C2|C2]; [img_try (img_apply (PRX mem' (PRES' a' C2) E')) | img_try (img_apply (PRX mem' (PRESW a' C2) E'))]. }
assert (E4 : mem4 x = None).
{ rewrite <- E'. symmetry. img_apply (proj1 EQS4 x); [img_try (intros X; img_apply C2; img_exact (YF6m.WIN2_WIN ly regs pa lastb a' X)) | img_try (img_exact C1)]. }
assert (EMD : depot_footprint B ly a' \/ ~ depot_footprint B ly a') by (img_try (unfold depot_footprint; clear - EM;
destruct (EM (as_depot B) (as_depot B + d_map1 + 8 * 32768) a'); [img_try (tauto)|]; destruct (EM (ly_NB ly) (ly_NB ly + kNodesBlockSize) a'); [img_try (tauto)|];
destruct (EM (ly_SB ly) (ly_SB ly + kStoreBlockSize) a'); [img_try (tauto)|]; destruct (EM (as_store B) (as_store B + 64) a'); tauto)).
destruct EMD as [C3|C3].
{ destruct DEPOK as (_ & _ & DV). rewrite Forall_forall in DV.
assert (BLK : forall e len, In (e, len) [(ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8); (ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize)] ->
aeval B ly e <= a' < aeval B ly e + len -> False).
{ intros e len Hin Hrg. pose proof (DV _ Hin (a' - aeval B ly e) ltac:(img_try (cbn [fst snd]; img_lia))) as V. cbn [fst snd] in V.
replace (aeval B ly e + (a' - aeval B ly e)) with a' in V by img_lia. img_apply V. unfold aview, mbyte, mrestrict. rewrite Ex, Hx, E4, ROM. img_refl. }
unfold depot_footprint in C3. rewrite (ts_depot _ TB), (ts_store _ TB) in C3. unfold TFX_DEPOT, TFX_STORE, d_map1 in C3.
destruct C3 as [C3|[C3|[C3|C3]]].
- img_apply NIMG. img_lia.
- img_apply (BLK (ANB 0) kNodesBlockSize); [img_try (cbn; tauto) | img_try (cbn [aeval]; img_lia)].
- img_apply (BLK (ASB 0) kStoreBlockSize); [img_try (cbn; tauto) | img_try (cbn [aeval]; img_lia)].
- img_apply NIMG. img_lia. }
assert (ED : ms_mem msD x = None).
{ rewrite <- E4. symmetry. img_apply Hfr4; [|img_try (img_exact C3)]. intros X. img_apply C2. unfold YF6m.WIN. left. clear - X. unfold DEP_STK, ASTACK in *. (subst a'; cbv beta). fold sp0. img_lia. }
destruct (EM TFX_IAL_LO TFX_IAL_HI a') as [C4|C4]; [img_try (img_apply NIMG; unfold TFX_IAL_LO, TFX_IAL_HI in C4; img_lia)|].
destruct (EM TFX_IAL_FLAG (TFX_IAL_FLAG + 4) a') as [C5|C5]; [img_try (img_apply NIMG; unfold TFX_IAL_FLAG in C5; img_lia)|].
rewrite (proj1 MEQD x) in ED; [img_try (congruence) | img_try (img_exact C2) | img_try (unfold YF6m.IZONE; tauto)]. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (img_try (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; img_lia)). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; img_lia)).
assert (Ux : bv_unsigned x = a) by (img_try ((subst x; cbv beta); img_apply unsigned_lit_small; img_exact Ha')).
assert (ROM : seg_rom tfxsegs x = None) by (img_try ((subst x; cbv beta); img_apply seg_rom_none_high; clear - Ha; unfold TFX_IMG_END, kLowShadowBeg, kHighShadowEnd in *; img_lia)).
assert (PRX : forall m, apresent (w_H W) m a -> False) by (img_try (intros m [Hh _]; fold x in Hh; rewrite Hx in Hh; discriminate)).
assert (C1 : ~ (YF6m.SPv pa <= a < YF6m.SPv pa + YF6m.CNT8v nn)).
{ intros C1. img_exact (PRX mem (fh_Hsh_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH a C1)). }
assert (C2 : ~ YF6m.WIN ly regs pa lastb a).
{ intros C2. unfold YF6m.WIN in C2. destruct C2 as [C2|C2]; [img_try (img_exact (PRX mem' (PRES' a C2))) | img_try (img_exact (PRX mem' (PRESW a C2)))]. }
assert (C3 : ~ depot_footprint B ly a).
{ intros C3. destruct DEPOK as (_ & _ & DV). rewrite Forall_forall in DV.
assert (BLK : forall e len, In (e, len) [(ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8); (ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize)] ->
aeval B ly e <= a < aeval B ly e + len -> False).
{ intros e len Hin Hrg. pose proof (DV _ Hin (a - aeval B ly e) ltac:(img_try (cbn [fst snd]; img_lia))) as V. cbn [fst snd] in V.
replace (aeval B ly e + (a - aeval B ly e)) with a in V by img_lia. img_apply V. unfold aview, mbyte, mrestrict. fold x. rewrite ROM, Hx. img_refl. }
unfold depot_footprint in C3. rewrite (ts_depot _ TB), (ts_store _ TB) in C3. unfold TFX_DEPOT, TFX_STORE, d_map1 in C3.
destruct C3 as [C3|[C3|[C3|C3]]].
- clear - C3 Ha. unfold kLowShadowBeg in Ha. img_lia.
- img_apply (BLK (ANB 0) kNodesBlockSize); [img_try (cbn; tauto) | img_try (cbn [aeval]; img_lia)].
- img_apply (BLK (ASB 0) kStoreBlockSize); [img_try (cbn; tauto) | img_try (cbn [aeval]; img_lia)].
- clear - C3 Ha. unfold kLowShadowBeg in Ha. img_lia. }
rewrite (proj1 EQS4 x); rewrite ?Ux; [| img_try (intros X; img_apply C2; img_exact (YF6m.WIN2_WIN ly regs pa lastb a X)) | img_try (img_exact C1)].
rewrite Hfr4; rewrite ?Ux; [| img_try (intros X; img_apply (PRX (ms_mem msD)); img_apply PRESD; clear - X; unfold DEP_STK, ASTACK in *; fold sp0; img_lia) | img_try (img_exact C3)].
img_apply (proj1 MEQD x); rewrite ?Ux; [img_try (img_exact C2)|].
unfold YF6m.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG. clear - Ha. unfold kLowShadowBeg in Ha. img_lia. }
cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
assert (NEW_hdr : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user k) - 16 + Z.of_nat i) = Some (YG0h.le_byte (3 + 256 * hb1) 4 i)).
{ intros i Hi. (subst rd'; cbv beta). rewrite <- Epa. img_exact (val_mem_aview _ _ _ _ _ i V1 Hi). }
assert (NEW_n : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user k) - 12 + Z.of_nat i) = Some (YG0h.le_byte (ck_n k) 4 i)).
{ intros i Hi. (subst rd'; cbv beta). rewrite <- Epa, <- Enn. img_exact (val_mem_aview _ _ _ _ _ i V2 Hi). }
assert (NEW_qs : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + Z.of_nat i) = Some (YG0h.le_byte (Z.of_nat (length (qc_list (st_qthread S)))) 8 i)).
{ intros i Hi. (subst rd'; cbv beta). img_exact (val_mem_aview _ _ _ _ _ i V3 Hi). }
assert (NEW_qf : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + 8 + Z.of_nat i) =
Some (YG0h.le_byte (match qc_list (st_qthread S) with [] => 0 | b0 :: _ => ly_space ly + b_self b0 end) 8 i)).
{ intros i Hi. (subst rd'; cbv beta). img_exact (val_mem_aview _ _ _ _ _ i V4 Hi). }
assert (NEW_ql : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + 16 + Z.of_nat i) = Some (YG0h.le_byte (ly_space ly + b_self lastb) 8 i)).
{ intros i Hi. (subst rd'; cbv beta). img_exact (val_mem_aview _ _ _ _ _ i V5 Hi). }
assert (NEW_qb : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + 24 + Z.of_nat i) = Some (YG0h.le_byte (qc_bytes (st_qthread S) + ck_n k) 8 i)).
{ intros i Hi. (subst rd'; cbv beta). rewrite <- Enn. img_exact (val_mem_aview _ _ _ _ _ i V6 Hi). }
assert (NEW_unw : rd' (ly_T ly + t_unwinding) = Some 0).
{ (subst rd'; cbv beta). rewrite <- (Z.add_0_r (ly_T ly + t_unwinding)). img_exact (val_mem_aview _ _ _ _ _ 0 V7 ltac:(img_lia)). }
assert (NEW_bb : forall i, (i < 8)%nat -> rd' (ly_space ly + b_self lastb + 8 + Z.of_nat i) = Some (YG0h.le_byte (b_bytes lastb + ck_n k) 8 i)).
{ intros i Hi. (subst rd'; cbv beta). rewrite <- Enn. img_exact (val_mem_aview _ _ _ _ _ i V8 Hi). }
assert (NEW_bc : forall i, (i < 8)%nat -> rd' (ly_space ly + b_self lastb + 16 + Z.of_nat i) = Some (YG0h.le_byte (Z.of_nat (length (b_items lastb)) + 1) 8 i)).
{ intros i Hi. (subst rd'; cbv beta). img_exact (val_mem_aview _ _ _ _ _ i V9 Hi). }
assert (NEW_slot : forall i, (i < 8)%nat -> rd' (ly_space ly + b_self lastb + 24 + 8 * Z.of_nat (length (b_items lastb)) + Z.of_nat i) =
Some (YG0h.le_byte (sptr_addr B ly (ck_user k) - 16) 8 i)).
{ intros i Hi. (subst rd'; cbv beta). rewrite <- Epa. img_exact (val_mem_aview _ _ _ _ _ i V10 Hi). }
assert (NEW_sh : forall a, YF0r.DH B ly k a -> rd a <> None -> rd' a = Some shHeapFreed).
{ intros a Hd Hv. (subst rd rd'; cbv beta). unfold YF0r.DH in Hd. rewrite <- Epa, <- Enn in Hd.
pose proof (fh_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as HP. unfold YF6m.N8v in HP.
assert (Ha : 0 <= a < 2 ^ 64).
{ clear - Hd HP NN2 NN3 Enn. rewrite <- Enn in *. ceil; unfold zone3, shadow_addr, SHADOW_OFF, kHighMemBeg, ASAN_CEIL in *.
pose proof (Z.div_pos pa 8 ltac:(img_lia) ltac:(img_lia)). pose proof (Z.div_le_upper_bound pa 8 pa ltac:(img_lia) ltac:(img_lia)). img_lia. }
unfold aview, mbyte, mrestrict in Hv |- *.
assert (ROM : seg_rom tfxsegs (Z_to_bv 64 a) = None).
{ img_apply seg_rom_none_high. unfold TFX_IMG_END. unfold shadow_addr, SHADOW_OFF in Hd. pose proof (Z.div_pos pa 8 ltac:(img_try (unfold zone3 in HP; img_lia)) ltac:(img_lia)). img_lia. }
destruct (w_H W (Z_to_bv 64 a)) eqn:Hx; [img_try (rewrite ROM in Hv; exfalso; img_exact (Hv eq_refl))|].
rewrite (proj2 EQS4 (Z_to_bv 64 a)); [img_refl|]. rewrite unsigned_lit_small by img_exact Ha.
unfold YF6m.SPv, YF6m.CNT8v, YF6m.N8v. unfold shadow_addr in Hd. rewrite Z_div_mult by img_lia. img_exact Hd. }
assert (AGI : forall a, YF6m.IZONE a -> mem' (Z_to_bv 64 a) = ms_mem msD (Z_to_bv 64 a)).
{ intros a Hz. assert (Ha : 0 <= a < 2 ^ 64) by (img_try (unfold YF6m.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG in Hz; img_lia)).
pose proof (fh_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as HP.
assert (NW : ~ YF6m.WIN ly regs pa lastb a).
{ img_apply (YF6m.notWIN_img W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH).
clear - Hz. unfold YF6m.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_IMG_LO, TFX_IMG_END in *. img_lia. }
rewrite (proj1 EQS4 (Z_to_bv 64 a)); rewrite ?unsigned_lit_small by img_exact Ha.
2:{ intros X. img_apply NW. img_exact (YF6m.WIN2_WIN ly regs pa lastb a X). }
2:{ clear - Hz HP. unfold zone3, YF6m.IZONE, YF6m.SPv, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, kHighMemBeg, SHADOW_OFF in *.
pose proof (Z.div_pos pa 8 ltac:(img_lia) ltac:(img_lia)) as X. img_lia. }
img_apply Hfr4; rewrite ?unsigned_lit_small by img_exact Ha.
- pose proof (lo_top ly (am_layout B ly S _ M)) as (_ & _ & _ & _ & _ & _ & T7). clear - Hz HSP T7.
unfold YF6m.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, kHighMemBeg, ASTACK, DEP_STK in *. img_lia.
- intros X. destruct (DFP_OUT a X) as (_ & NI & _). img_exact (NI Hz). }
assert (IAL : Forall (cell_holds B ly rd') (ialloc_cells B (YF0r.S' S k z tr)) /\ Forall (range_zero B ly rd') (ialloc_zero B)).
{ destruct MEQD as [_ IP]. unfold YF6m.IAL_POST in IP. cbv zeta in IP. destruct IP as (I1 & I2 & I3 & I4 & I5).
assert (XF : forall a0 (w : nat) v, YF6m.IZONE a0 -> (forall kk, (kk < w)%nat -> YF6m.IZONE (a0 + Z.of_nat kk)) ->
val_mem tfxsegs (mrestrict (w_H W) (ms_mem msD)) a0 w v -> val_mem tfxsegs (mrestrict (w_H W) mem') a0 w v).
{ intros a0 w v _ Hz Hv. eapply val_mem_frame; [|img_try (img_exact Hv)]. intros kk Hkk. apply AGI, Hz, Hkk. }
unfold ialloc_cells, ialloc_zero. rewrite (YF0r.S'_inited S k z tr), (ts_ial_flag _ TB), (ts_ial_lo _ TB), (ts_ial_w _ TB), (ts_ial_hi _ TB).
assert (ZF : YF6m.IZONE TFX_IAL_FLAG /\ YF6m.IZONE (TFX_IAL_FLAG + 1) /\ (forall kk, (kk < 8)%nat -> YF6m.IZONE (TFX_IAL_W + Z.of_nat kk)) /\
(forall kk, (kk < 8)%nat -> YF6m.IZONE (TFX_IAL_W + 8 + Z.of_nat kk))).
{ unfold YF6m.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_IAL_W. splits; intros; img_lia. }
destruct ZF as (Z1 & Z2 & Z3 & Z4). (subst rd'; cbv beta). split.
- img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|img_lia].
assert (ZZ : forall kk : nat, (kk < 1)%nat -> YF6m.IZONE (TFX_IAL_FLAG + Z.of_nat kk)) by (img_try (intros [|] ?; [img_try (rewrite Z.add_0_r; img_exact Z1) | img_try (exfalso; img_lia)])).
img_apply (val_mem_aview _ _ _ _ _ 0 (XF _ _ _ Z1 ZZ I1)). img_lia. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|img_lia].
assert (ZZ : forall kk : nat, (kk < 1)%nat -> YF6m.IZONE (TFX_IAL_FLAG + 1 + Z.of_nat kk)) by (img_try (intros [|] ?; [img_try (rewrite Z.add_0_r; img_exact Z2) | img_try (exfalso; img_lia)])).
img_apply (val_mem_aview _ _ _ _ _ 0 (XF _ _ _ Z2 ZZ I2)). img_lia. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB). replace (TFX_IAL_LO + (TFX_IAL_W - TFX_IAL_LO)) with TFX_IAL_W by img_lia.
intros kk Hkk. pose proof (Z3 0%nat ltac:(lia)) as Z3_0; change (Z.of_nat 0) with 0 in Z3_0; rewrite Z.add_0_r in Z3_0. img_exact (val_mem_aview _ _ _ _ _ kk (XF _ _ _ Z3_0 Z3 I3) Hkk). }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB). replace (TFX_IAL_LO + (TFX_IAL_W - TFX_IAL_LO + 8)) with (TFX_IAL_W + 8) by img_lia.
replace (TFX_IAL_LO + (TFX_IAL_W - TFX_IAL_LO + 16)) with (TFX_IAL_W + 16) by img_lia.
intros kk Hkk. pose proof (Z4 0%nat ltac:(lia)) as Z4_0; change (Z.of_nat 0) with 0 in Z4_0; rewrite Z.add_0_r in Z4_0. img_exact (val_mem_aview _ _ _ _ _ kk (XF _ _ _ Z4_0 Z4 I4) Hkk). }
- assert (ZR : forall a0, TFX_IAL_LO <= a0 < TFX_IAL_W \/ TFX_IAL_W + 16 <= a0 < TFX_IAL_HI -> aview tfxsegs (w_H W) mem' a0 = Some 0).
{ intros a0 Ha0. unfold aview. rewrite (mbyte_mrestrict_same (w_H W) (ms_mem msD) mem' a0).
- rewrite (I5 a0 Ha0). img_refl.
- img_apply AGI. unfold YF6m.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W in *. img_lia. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])]; intros i Hi; cbn [fst snd aeval] in Hi |- *; rewrite (ts_ial_lo _ TB); img_apply ZR; unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W in *; img_lia. }
pose proof (fh_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as HP. unfold YF6m.N8v in HP.
assert (SHB : kLowShadowBeg <= YF6m.SPv pa /\ YF6m.SPv pa + YF6m.CNT8v nn <= kHighMemBeg).
{ unfold YF6m.SPv, YF6m.CNT8v, YF6m.N8v. rewrite Z_div_mult by img_lia. unfold zone3 in HP.
pose proof (YF0r.hs_bounds lastb pa ltac:(img_lia) ltac:(img_try (ceil; unfold kHighMemEnd, ASAN_CEIL in *; img_lia))) as [X1 _].
pose proof (YF0r.hs_bounds lastb (pa + (nn + 7) / 8 * 8 - 8) ltac:(img_try (rewrite <- Enn in *; img_lia)) ltac:(img_try (ceil; unfold kHighMemEnd, ASAN_CEIL in *; img_lia))) as [_ X2].
unfold shadow_addr in X1, X2. replace (pa + (nn + 7) / 8 * 8 - 8) with (pa + ((nn + 7) / 8 - 1) * 8) in X2 by img_lia. rewrite Z.div_add in X2 by img_lia. img_lia. }
assert (AG4 : forall a, 0 <= a < 2 ^ 64 -> ~ YF6m.WIN ly regs pa lastb a -> ~ (YF6m.SPv pa <= a < YF6m.SPv pa + YF6m.CNT8v nn) ->
aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem4 a).
{ intros a Ha NW HZ. img_apply aview_same. img_apply (proj1 EQS4); rewrite unsigned_lit_small by img_exact Ha; [|img_try (img_exact HZ)].
intros X. img_apply NW. img_exact (YF6m.WIN2_WIN ly regs pa lastb a X). }
assert (DEP : depot_mem_ok B ly (depot_after z tr s1) rd').
{ eapply (depot_mem_ok_agree ly (depot_after z tr s1) (depot_after z tr s1)); [| img_try (img_exact (am_universe B ly S _ M)) | img_refl | | img_try (img_exact DEPOK)].
- img_apply (WfP_weaken _ 1 1 1); try img_lia. img_exact (YF0r.sd_wf B ly S rd M lastb z tr Hev AOK HU).
- intros a Ha. (subst rd'; cbv beta).
pose proof (YF6m.LYB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (_ & _ & _ & _ & _ & _ & _ & _ & ZNB & _ & ZSB & _).
img_apply AG4; [img_try (img_exact (DFP_RANGE a Ha)) | img_try (img_exact (proj1 (DFP_OUT a Ha))) |].
unfold depot_footprint in Ha. rewrite (ts_depot _ TB), (ts_store _ TB) in Ha. clear - Ha ZNB ZSB SHB.
unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, TFX_DEPOT, TFX_STORE, d_map1, kLowShadowBeg, kHighMemBeg, kNodesBlockSize, kStoreBlockSize in *. img_lia. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ img_apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly (aview tfxsegs (w_H W) mem4)); [img_try (img_exact (proj1 (Forall_forall _ _) HC4 c Hc))|].
intros i Hi. (subst rd'; cbv beta). destruct (proj1 (Forall_forall _ _) CONST_OUT c Hc i Hi) as (X1 & X2 & X3). img_apply AG4; [img_try (img_exact X3) | img_try (img_exact X1) |].
img_exact (proj1 (Forall_forall _ _) CONST_ZONE c Hc i Hi). }
pose proof (free_fin_ARm B TB ly S rd rd' M k lastb initr hb1 Hk Hst Hrev Hroom (conj HB1 HB1M) z tr Hev AOK HU sp0 HSP (img_cover_of_ledger ly S md LED) AG VIS
NEW_hdr NEW_n NEW_qs NEW_qf NEW_ql NEW_qb NEW_unw NEW_bb NEW_bc NEW_slot NEW_sh IAL DEP CONST') as M'.
split; [| img_try (exists regs', mem', (with_vm_backing (m_vm_lazy md) mat md); split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; img_refl | img_exact A0])].
exists ly, regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split.
{ unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. img_refl. }
split. 2:{ img_apply (YF0r.qtight_S' B ly S rd M k lastb initr Hk Hst Hrev z tr); [img_try (rewrite <- Enn; img_exact Hcache) | img_try (img_exact HQT)]. }
split; [|img_try (split; [img_apply layout_le_refl | split; [img_apply wle_refl | split; [|split; [|split]]]])].
- split; [img_try (img_exact M') | img_try (split; [|split; [|split]])].
+ eapply ALedger_same; [img_try (img_exact (YF0r.ALedger_S' B ly S rd M k Hk z tr tfxsegs md LED)) | img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_apply eager_used_wvb)].
+ destruct BUD as [BUD PIN]. split; [| img_try (img_exact (YF0r.asecA_S' B ly S rd M k Hk z tr _ PIN))].
eapply Z.le_trans; [img_try (img_exact BUD) | img_try (img_exact (YF0r.abudget_le B ly S rd M k lastb Hk z tr))].
+ eapply amwf_same; [img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_exact MW)].
+ eapply (ahs_transfer tfxsegs B ly S _ (w_H W) mem mem' (al_img_env tfxsegs ly S md (am_layout B ly S _ M) LED) M HSH VIS HSK).
* eapply (aclient_band_same_frames B ly S); [img_try (img_exact M') | img_try (unfold frames, depot_after, s1; cbn [st_fs set_qthread set_chunks set_depot set_internal_inited set_nev fst snd]; destruct (z =? 0); img_refl)].
*   img_exact (YF0r.sec_extents' B ly S rd M k Hk z tr).
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. img_apply AG; [img_try (clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; img_lia)|].
unfold YF0r.D, YF0r.DT, YF0r.DK, YF0r.DB, YF0r.DS, YF0r.DI, YF0r.DH. rewrite <- Epa, <- Enn.
pose proof (YF6m.LYB W ly regs mem ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FH) as (LT1 & _ & LP1 & LP2 & _ & _ & _ & _ & LNB & _ & LSB & _ & _ & _ & _ & _ & LSK).
pose proof (fh_HB _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (HBv1 & HBv2 & _). unfold YF6m.Bv in HBv1, HBv2.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg.
unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize in LT1, LNB, LSB. unfold kHighMemBeg in LT1, LP1, LNB, LSB, LSK.
intros [X|[X|[X|[X|[X|[X|X]]]]]].
-- clear - X SBg LT1. unfold t_qc, t_unwinding, t_stats in X. img_lia.
-- rewrite Epa, G4 in X. clear - X SBg G1 G5 ER NN1 NN3 Enn. rewrite <- Enn in *. ceil. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G1. img_lia.
-- clear - X SBg LP1 LP2 HBv1. img_lia.
-- clear - X SBg LSK HSP. unfold ASTACK in *. img_lia.
-- rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB) in X. clear - X SBg. unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG in X. img_lia.
-- unfold depot_footprint in X. rewrite (ts_depot _ TB), (ts_store _ TB) in X. clear - X SBg LNB LSB. ceil. unfold TFX_DEPOT, TFX_STORE, d_map1, kNodesBlockSize, kStoreBlockSize, ASAN_CEIL in *. img_lia.
-- assert (PA8 : pa mod 8 = 0) by (img_try (rewrite Epa, G4; clear - G3 G6; img_apply Z.mod_divide; [img_lia|]; apply Z.mod_divide in G3 as [q3 Hq3]; [|img_lia]; apply Z.mod_divide in G6 as [q6 Hq6]; [|img_lia]; exists (2 * q3 + 2 * q6); img_lia)).
refine (hfree_shadow_off_range B ly S rd k pa nn g M Hk _ _ PA8 _ Hg HF X); rewrite ?Epa, ?G4; clear - G5 ER NN1 NN3 Enn; rewrite ?Enn in *; img_lia.
- intros r Hr'. img_apply CS. unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia.
clear - R. unfold CALLEE_SAVED.
repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; (subst r; cbv beta); cbn [In]; repeat (first [left; img_apply bv_eq; (img_case; vm_compute); img_refl | right]).
- unfold same_io. destruct md; cbn; repeat split; img_refl.
- intros a Ha NO NO' NS NE. img_apply AG; [img_try (img_exact Ha)|]. intros HD.
destruct (YF0r.D_owned B TB ly S rd rd' M k lastb initr hb1 Hk Hrev Hroom (conj HB1 HB1M) z tr sp0 HSP (img_cover_of_ledger ly S md LED) M' a (proj1 Ha) HD) as [O|[O|O]];
[img_try (img_exact (NO O)) | img_try (img_exact (NO' O)) | img_try (img_apply NS; unfold ascratch; left; img_exact O)].
- img_exact PRES'.
Qed.
Theorem afree_common_arm :
amreal tfxsegs (free p tr S) W (cfg_at tfxsegs (0x3244c + D_150) regsD mem md) rfree_leaf.
Proof.
destruct PRE as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT).
destruct HAR as (M & LED & BUD & MW & HSH).
pose proof (find_user_block _ 0 0 0 S p n (am_wf B ly S _ M) HBLK) as (k & Hf & Hk & Hst & Hu & Hr).
destruct ARM as (Hrev & Hroom & Hcache).
set (BODY := fun s' : astate =>
(match p with
| PNull => ret ()
| _ => s <- get;;
match find_user (st_chunks s) p with
| Some k0 =>
mcheck match ck_state k0 with CAllocated => true | CQuarantined => false end 201300;;
depot_put tr;;
modify (fun s0 : astate => set_chunks (upd_chunk (st_chunks s0) {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |}) s0);;
enqueue {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |};; maybe_drain
| None => fail (FCheck 201312)
end
end) s').
assert (SPLIT : amreal tfxsegs (BODY s1) W (cfg_at tfxsegs (0x3244c + D_150) regsD mem md) rfree_leaf ->
amreal tfxsegs (free p tr S) W (cfg_at tfxsegs (0x3244c + D_150) regsD mem md) rfree_leaf).
{ intros MAIN. unfold free. cbn [bind ret tick modify mcheck ibind get put set_nev set_internal_inited st_internal_inited].
destruct (st_internal_inited S) eqn:E; cbn [ibind ret modify].
- replace (set_nev (st_nev S + 1) S) with s1; [img_try (img_exact MAIN)|]. unfold s1. generalize E. generalize S. clear. intros S0 E0. destruct S0; cbn in E0 |- *. (subst; cbv beta). img_refl.
- img_exact MAIN. }
img_apply SPLIT. clear SPLIT. (subst BODY; cbv beta). cbn beta.
set (k' := {| ck_beg := ck_beg k; ck_req := ck_req k; ck_state := CQuarantined |}).
assert (MAIN : amreal tfxsegs ((s <- get;;
match find_user (st_chunks s) p with
| Some k0 =>
mcheck match ck_state k0 with CAllocated => true | CQuarantined => false end 201300;;
depot_put tr;;
modify (fun s0 : astate => set_chunks (upd_chunk (st_chunks s0) {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |}) s0);;
enqueue {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |};; maybe_drain
| None => fail (FCheck 201312)
end) s1) W (cfg_at tfxsegs (0x3244c + D_150) regsD mem md) rfree_leaf).
2:{ rewrite match_nonnull; [img_try (img_exact MAIN)|]. intros Hp0.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ (am_wf B ly S _ M)) k Hk) as CK.
revert Hu. rewrite Hp0. unfold ck_user. destruct CK as [_ CK]. destruct (ck_beg k); cbn; try discriminate; destruct CK. }
cbn [bind get ret ibind]. img_change (st_chunks s1) with (st_chunks S). rewrite Hf, Hst. cbn [mcheck ret ibind].
unfold depot_put. cbn [bind askz ibind].
img_apply amreal_ask_depot.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_bind; [img_try (img_exact (segB W ly regs mem md ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) (m_vm_materialized md) FH regsD
(REGSD (YF6m.XW ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3)) (STKD (YF6m.XW ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3) eq_refl)
HQ12 Hii HPRES TRQ0))|].
intros W2 c2 _ (-> & msD & matD & E3 & -> & HshD & HEn3 & HS & MEQD & TRQ & PRESD).
rewrite HshD. eapply SRr_bind.
{ pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E3 _ _ HS eq_refl) as Hsh.
assert (AGD : forall a, ~ YF6m.WIN ly regs pa lastb a -> ~ YF6m.IZONE a -> 0 <= a < 2 ^ 64 ->
aview tfxsegs (w_H W) (ms_mem msD) a = aview tfxsegs (w_H W) mem a).
{ intros a Hw Hz Ha. img_apply aview_same. img_apply (proj1 MEQD); rewrite unsigned_lit_small by img_exact Ha; assumption. }
rreg HS (2%bv : bv 5) R2. rewrite (HEn3 2%nat ltac:(img_try ((img_case; cbv); img_lia))), (YF6m.E2 ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3) in R2.
pose proof (lo_top ly (am_layout B ly S _ M)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
apply (D1 W ly s1 (ms_regs msD) (ms_mem msD) _ (sp0 - 2120) tr (am_layout B ly S _ M) (img_cover_of_ledger ly S md (proj1 (proj2 (proj1 PRE)))) s1_wf HU).
-
img_apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly (aview tfxsegs (w_H W) mem)).
+ img_exact (proj1 (Forall_forall _ _) (am_const B ly S _ M) c Hc).
+ intros i Hi. destruct (proj1 (Forall_forall _ _) CONST_OUT c Hc i Hi) as (X1 & X2 & X3). img_apply AGD; assumption.
-
assert (DM : depot_mem_ok B ly S (aview tfxsegs (w_H W) mem)).
{ split; [|img_try (split)].
- img_apply Forall_forall. intros c Hc. img_apply (proj1 (Forall_forall _ _) (am_cells B ly S _ M)). unfold acells. rewrite !in_app_iff. tauto.
- img_exact (am_depot B ly S _ M).
- pose proof (am_junk B ly S _ M) as J. pose proof (am_areas B ly S _ M) as A. rewrite Forall_forall in J, A.
repeat img_apply Forall_cons; try img_apply Forall_nil;
first [ img_apply J; unfold ajunk; do 2 right; repeat (img_apply in_or_app; first [ left; inlist | right ]); inlist
| img_apply A; unfold aareas; repeat (img_apply in_or_app; first [ left; inlist | right ]); inlist ]. }
eapply (depot_mem_ok_agree ly S s1); [img_try (img_exact (am_wf B ly S _ M)) | img_try (img_exact (am_universe B ly S _ M)) | img_refl | | img_try (img_exact DM)].
intros a Ha. destruct (DFP_OUT a Ha) as (X1 & X2 & X3). img_apply AGD; [img_try (img_exact X1) | img_try (img_exact X2) | img_try (img_exact (DFP_RANGE a Ha))].
- rreg HS (10%bv : bv 5) R; rewrite R, (HEn3 2%nat ltac:(img_try ((img_case; cbv); img_lia))), (YF6m.E2 ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3). unfold sp0; f_equal; img_lia.
- rreg HS (11%bv : bv 5) R; rewrite R, (HEn3 36%nat ltac:(img_try ((img_case; cbv); img_lia))), (YF6m.EaLEN ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3). img_refl.
- rreg HS (3%bv : bv 5) R; rewrite R, (HEn3 3%nat ltac:(img_try ((img_case; cbv); img_lia))), (YF6m.Er ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 3 3%bv eq_refl). img_exact Hgp.
- rreg HS (4%bv : bv 5) R; rewrite R. rewrite (ts_tp _ TB) in Htp. img_refl.
- rreg HS (1%bv : bv 5) R; rewrite R. img_apply YK0s.ret_ok_even. img_refl.
- intros i Hi. img_apply (TRQ i Hi).
- unfold sp0. replace (bv_unsigned (getr regs 2) - 2120) with (bv_unsigned (getr regs 2) + (-265) * 8) by img_lia. rewrite Z_mod_plus_full.
img_apply (mod0_factor _ 8 2); [img_lia|]. img_exact Hal.
- unfold spZ, ASTACK in *; unfold sp0; img_lia.
-   unfold spZ, ASTACK in *; unfold sp0; img_lia.
- right. rewrite R2. unfold w64. rewrite unsigned_lit_small by (img_try (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; img_lia)). unfold sp0; img_lia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (img_try (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; img_lia)).
replace (bv_unsigned (getr regs 2) + -2256) with (bv_unsigned (getr regs 2) + (-141) * 16) by img_lia. rewrite Z_mod_plus_full. img_exact Hal.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (img_try (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; img_lia)). unfold spZ, ASTACK, DEP_STK in *; img_lia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (img_try (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; img_lia)). unfold spZ in *; img_lia.
- intros a Ha. rewrite R2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (img_try (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; img_lia)).
img_apply PRESD. unfold DEP_STK, ASTACK, sp0 in *. img_lia. }
intros W3 c3 _ (-> & z & regs4 & mem4 & mat4 & -> & AOK & HP4 & Hfr4 & Hpr4 & DEPOK & HC4). srr_norm_model.
img_apply SRr_ret. exists z. split; [img_try (img_exact AOK)|].
rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2.
rewrite Q2, (HEn3 2%nat ltac:(img_try ((img_case; cbv); img_lia))), (YF6m.E2 ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3) in Hfr4.
pose proof (lo_top ly (am_layout B ly S _ M)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
rewrite unsigned_lit_small in Hfr4 by (img_try (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; img_lia)). fold sp0 in Hfr4.
assert (DZ : forall x : word, ~ (sp0 - 2256 - DEP_STK <= bv_unsigned x < sp0 - 2256) -> ~ YF6m.DZONE ly (bv_unsigned x) -> mem4 x = ms_mem msD x).
{ intros x Hx Hd. img_apply Hfr4; [img_lia|]. intros Hf'. img_apply Hd. img_exact (proj2 (proj2 (DFP_OUT _ Hf'))). }
assert (TAIL : let sd := depot_after z tr s1 in
amreal tfxsegs ((modify (fun s0 : astate => set_chunks (upd_chunk (st_chunks s0) k') s0);; enqueue k';; maybe_drain) sd)
W (mkCfg (mkst regs4 (getr (ms_regs msD) 1) mem4 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat4 md))
rfree_leaf).
{ cbn zeta. assert (Qsd : st_qthread (depot_after z tr s1) = st_qthread S) by (img_try (unfold depot_after; destruct (z =? 0); img_refl)).
unfold enqueue, maybe_drain. cbn [bind modify ibind get st_qthread set_chunks]. rewrite Qsd.
unfold need_new_batch. rewrite Hrev. replace (Z.of_nat (length (b_items lastb)) =? kBatchSlots) with false by (img_try (symmetry; img_apply Z.eqb_neq; img_lia)).
cbn [bind ret ibind modify st_qthread set_qthread get set_chunks]. rewrite Qsd.
replace (qc_bytes (qc_push (st_qthread S) k' None) <=? kQuarantineCacheMax) with true.
2:{ symmetry. img_apply Z.leb_le. cbn [qc_push qc_bytes]. (subst k'; cbv beta). unfold nn, ck_n in *. cbn [ck_req]. rewrite Hr. img_exact Hcache. }
cbn [ret amreal]. rewrite Q1.
eapply SRr_mono.
- img_apply (segC W ly regs mem md ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) nil FH msD E3 regs4 mem4 mat4).
split; [img_try (img_exact HshD)|]. split; [img_try (img_exact HEn3)|]. split; [img_try (img_exact HS)|]. split; [img_try (img_exact HP4)|]. split; [img_try (img_exact DZ)|]. split; [img_try (img_exact Hpr4)|]. split; [img_try (img_exact MEQD) | img_try (img_exact PRESD)].
- intros W' c' _ HR. img_apply (FINH z k msD mem4 W' c' Hf AOK MEQD PRESD); [img_try (intros x Hx; img_apply Hfr4; img_lia) | img_try (img_exact Hpr4) | img_try (img_exact DEPOK) | img_try (img_exact HC4) | img_try (img_exact HR)]. }
destruct AOK as [-> | [-> _]].
- cbn [Z.eqb ret ibind]. img_exact TAIL.
- cbn [Z.eqb bind get ret ibind].
destruct (depot_ids s1 + 1 <? kDepotIdsPerBlock); cbn [mcheck ret ibind]; [|img_try (img_exact I)].
destruct (kStartFramesMax + depot_frames s1 + Z.of_nat (length tr) + 1 <? kStoreFramesPerBlock); cbn [mcheck ret put ibind]; [|img_try (img_exact I)].
img_exact TAIL.
Qed.
End f.
End d.

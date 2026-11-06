(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the step of pins_set's ASan walk through a call of xstrdup, after
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the step through a call with cl_callS and back) over fuzz_command's
   recorder. *)

(* `ps_call_x`: at the entry of the j-th xstrdup (j = 1 .. 4), the walk's invariant `ps_core P []` and the kept
   registers give, at the return, `ps_core P [(p, |x| + 1)]` for the copy p of the j-th argument x. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c mix_call_c answer_code_c pins_set_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas pins_set_s2 pins_set_s1 pins_set_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma ps_pres : forall (rg rg' : bvmap 5 word) r (b : bv 5), aregs_preserved rg rg' -> acallee_saved r ->
b = Z_to_bv 5 r -> getr rg' b = getr rg b.
Proof. intros rg rg' r b HP Hr ->. exact (HP r Hr). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis TXSTRDUP : txstrdup_spec B MT.
Hypothesis MTL : ameter_laws MT.
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).

Section entry.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (pu pf pl pv : Z) (uri files layout verdict : option (list byte)) (R : rstate)
  (O : list (Z * Z)).
Hypothesis HPRE : afn_pre SEGS B PINS_SET_STK ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis HSU : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pu uri.
Hypothesis HSF : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pf files.
Hypothesis HSL : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pl layout.
Hypothesis HSV : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pv verdict.
Hypothesis HREPA : rec_repA B ly S (rdW W mem) R O.
Hypothesis HEV : st_nev S + EV_PINS_SET R <= EV_MAX.
Hypothesis HLIVE : blocks_bytes S + LIVE_PINS_SET R uri files layout verdict <= LIVE_MAX.
Hypothesis HMOK : mo_ok MT S (XM_PINS_SET MT R uri files layout verdict).

#[local] Notation sp0 := (ps_sp0 regs).
#[local] Notation FPps := (ps_FP O).
#[local] Notation A := (ps_A uri files layout verdict).
#[local] Notation PTRS := (ps_ptrs pu pf pl pv uri files layout verdict).
#[local] Notation CORE := (ps_core B MT ly S W regs mem md uri files layout verdict R O).
#[local] Notation KEEP := (ps_keep B regs pf pl pv R).
#[local] Notation POST := (ps_post B MT ly S W regs mem md uri files layout verdict R O).

(* the recorder's footprint holds no read-only byte, and is closed to the sink *)
Lemma ps_FP_ro : forall a, in_roP SEGS RLO RHI a -> ~ inFP FPps a.
Proof.
intros a Hro Hf. destruct (cmd_ro_prog_apart a Hro) as [Himg Hnpg].
pose proof (pa_img_range _ Himg) as HR.
unfold ps_FP in Hf. apply inFP_cons in Hf as [Hf | Hf].
- apply Hnpg. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hf.
- apply inFP_cons in Hf as [Hf | Hf].
  + apply Hnpg. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hf.
  + destruct (inFP_ablocks_fp_inv O a Hf) as (q & n & Hq & Hr).
    destruct (ps_O_facts B ly S _ R O HREPA (q, n) Hq) as [_ HqS].
    destruct HPRE as (HAR & _).
    destruct (blk_off_imgP B ly S W mem md q n HAR HqS) as [Hlo | Hhi]; lia.
Qed.

Lemma ps_FP_closed : ~ YI16.sink_open_fp FPps.
Proof.
apply sink_closed_pos. unfold ps_FP. constructor; [cbn; unfold A_G_REC; lia|]. constructor; [cbn; unfold A_REC_SPILL; lia|].
unfold ablocks_fp. apply Forall_map. apply Forall_forall. intros [q n] Hq. cbn [fst].
destruct (ps_O_facts B ly S _ R O HREPA (q, n) Hq) as [_ HqS]. destruct HPRE as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q n HAR HqS) as (_ & H4096 & _). lia.
Qed.

Lemma ps_FP_cases : forall a, inFP FPps a -> Exists (in_zr a) recb_PG \/ exists q n, In (q, n) O /\ q <= a < q + req_size n.
Proof.
intros a Hf. unfold ps_FP in Hf. apply inFP_cons in Hf as [Hf | Hf].
- left. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hf.
- apply inFP_cons in Hf as [Hf | Hf].
  + left. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hf.
  + right. exact (inFP_ablocks_fp_inv O a Hf).
Qed.

(* the i-th source xstrdup copies is valid at every state the walk reaches *)
Lemma ps_src_at : forall i lyc Sc Wc memc mdc k own,
(i < 4)%nat ->
ajournal SEGS B PINS_SET_STK sp0 FPps ly S W mem md own lyc Sc Wc memc mdc k ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] (nth i PTRS 0) (Some (nth i A [])) /\
atail_vis SEGS Wc memc (nth i PTRS 0 + Z.of_nat (length (nth i A []))).
Proof.
intros i lyc Sc Wc memc mdc k own Hi HJ Hlive.
pose proof HPRE as (HAR & _).
pose proof HJ as (HAR2 & _).
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW Wc memc))
  by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ ps_FP_ro HROD).
pose proof (cmd_ro_ok_of_aro lyc Sc Wc memc mdc HAR2 HROD2) as HRO2.
pose proof (ps_O_facts B ly S _ R O HREPA) as HOF.
assert (SOME : forall p x, astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p (Some x) ->
  astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] p (Some x) /\
  atail_vis SEGS Wc memc (p + Z.of_nat (length x)))
  by (intros p x Hs; exact (ps_src_some B HB cmd_ro_prog_apart cmd_heap_tail_vis
        ly S W mem md O p x _ _ _ _ _ _ _ _ _ _ HAR Hs HJ HRO2 Hlive ps_FP_cases ps_FP_closed HOF)).
pose proof (ps_src_null B HB lyc Sc Wc memc mdc HAR2 HRO2 CMD_RO_IN) as NUL.
pose proof (ps_src_dash B HB lyc Sc Wc memc mdc HAR2 HRO2 CMD_RO_IN) as DSH.
destruct i as [|[|[|[|i]]]]; cbn [nth ps_ptrs ps_A ps_sptr]; [| | | | lia].
- destruct uri as [x|]; [exact (SOME pu x HSU) | exact NUL].
- destruct files as [x|]; [exact (SOME pf x HSF) | exact NUL].
- destruct layout as [x|]; [exact (SOME pl x HSL) | exact NUL].
- destruct verdict as [x|]; [exact (SOME pv x HSV) | exact DSH].
Qed.

Lemma ps_n_le16 : 0 <= ps_n R <= 16.
Proof. destruct HREPA as (Q0 & (_ & _ & _ & (Hl16 & _) & _) & _). unfold ps_n. lia. Qed.

Lemma ps_ret_ok : forall j, 0 <= ps_ret j < 2 ^ 40 /\ ps_ret j mod 2 = 0.
Proof.
intros j. destruct j as [|[|[|[|j]]]]; unfold ps_ret, PS_RET1, PS_RET2, PS_RET3, PS_RET4, AF_pins_set;
  (split; [lia | reflexivity]).
Qed.

(* the counts of the four copies *)
Lemma ps_xm_le : forall m, (m < 4)%nat ->
ps_xm MT uri files layout verdict m + XM_XSTRDUP MT (nth m A []) =
ps_xm MT uri files layout verdict (Datatypes.S m) /\
ps_xm MT uri files layout verdict (Datatypes.S m) <=
XM_XSTRDUP MT (sarg uri) + XM_XSTRDUP MT (sarg files) + XM_XSTRDUP MT (sarg layout) +
XM_XSTRDUP MT (darg verdict (bstr "-"%string)).
Proof.
intros m Hm. pose proof (fun y : list byte => mo_malloc_nonneg MT MTL (Z.of_nat (length y) + 1) ltac:(lia)) as NN.
destruct m as [|[|[|[|m]]]]; [| | | | lia]; unfold ps_xm, ps_A; cbn [firstn map fold_right nth];
  unfold XM_XSTRDUP in *;
  pose proof (NN (sarg uri)); pose proof (NN (sarg files)); pose proof (NN (sarg layout));
  pose proof (NN (darg verdict (bstr "-"%string))); lia.
Qed.

Lemma ps_live_le : forall m, (m < 4)%nat ->
ps_live uri files layout verdict m + LIVE_XSTRDUP (nth m A []) =
ps_live uri files layout verdict (Datatypes.S m) /\
ps_live uri files layout verdict (Datatypes.S m) <=
LIVE_XSTRDUP (sarg uri) + LIVE_XSTRDUP (sarg files) + LIVE_XSTRDUP (sarg layout) +
LIVE_XSTRDUP (darg verdict (bstr "-"%string)).
Proof.
intros m Hm. unfold LIVE_XSTRDUP.
destruct m as [|[|[|[|m]]]]; [| | | | lia]; unfold ps_live, ps_A, LIVE_XSTRDUP; cbn [firstn map fold_right nth]; lia.
Qed.

Lemma ps_call_x : forall j P lyc Sc Wc regsc memc mdc k,
(1 <= j <= 4)%nat -> length P = (j - 1)%nat ->
CORE P [] lyc Sc Wc memc mdc k ->
KEEP j regsc -> getr regsc 1 = Z_to_bv 64 (BASE + ps_ret j) -> getr regsc 10 = w64 (nth (j - 1) PTRS 0) ->
(forall ly2 S2 W2 regs2 mem2 md2 p,
   CORE P [(p, Z.of_nat (length (nth (j - 1) A [])) + 1)] ly2 S2 W2 mem2 md2 (k + 1) ->
   KEEP j regs2 -> getr regs2 10 = w64 p ->
   SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ps_ret j)) mem2 (seg_rom SEGS)) md2) POST) ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_xstrdup)) memc (seg_rom SEGS)) mdc) POST.
Proof.
intros j P lyc Sc Wc regsc memc mdc k Hj HlenP HC HK Hra Ha0 HNEXT.
destruct HC as [HJ Hk Hlen Hmo Hbb Hfr Hlive Hrec].
pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & Hnev & Hk0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (ps_ret_ok j) as [Hrj Hrj2].
destruct HK as (K2 & K3 & K4 & K8 & K18 & K22 & K23 & K24 & K21 & K20 & K19 & K9 & KHI).
assert (Hjm : (j - 1 < 4)%nat) by lia.
set (x := nth (j - 1) A []) in *. set (s := nth (j - 1) PTRS 0) in *.
destruct (ps_src_at (j - 1) lyc Sc Wc memc mdc k [] Hjm HJ Hlive) as [HSRC HTAIL].
fold x s in HSRC, HTAIL.
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW Wc memc))
  by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ ps_FP_ro HROD).
destruct (ps_xm_le (j - 1) Hjm) as [XMs XMb]. destruct (ps_live_le (j - 1) Hjm) as [LVs LVb].
fold x in XMs, LVs.
assert (XMNN : 0 <= XM_XSTRDUP MT x) by (apply (mo_malloc_nonneg MT MTL); lia).
assert (XACN : 0 <= XM_ANSWER_CODE MT (snd (pins_set_m R uri files layout verdict))).
{ unfold XM_ANSWER_CODE, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (resp (snd (pins_set_m R uri files layout verdict)))) + 1) ltac:(lia)).
  lia. }
assert (Hsp' : spZ regsc = sp0 + -80).
{ unfold spZ. rewrite K2. unfold w64, ps_sp0. rewrite unsigned_lit_small; [lia|].
  unfold ps_sp0 in *. lia. }
assert (Hc_lo : ps_c R < alloc_ceiling).
{ pose proof ps_n_le16. unfold ps_c, ps_slot_of. destruct (ps_n R =? 16); unfold A_REC_SPILL, A_G_REC, OFF_CALLS, CALL_SIZE; lia. }
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc regsc memc (Z_to_bv 64 (BASE + AF_xstrdup)) PINS_SET_STK sp0 FPps ly S W mem md []
    lyc Sc mdc k XSTRDUP_STK [] EV_XSTRDUP (-80) (getr regsc 1) [] _ HJ Hsp').
  - reflexivity.
  - lia.
  - unfold XSTRDUP_STK, ASTACK. lia.
  - unfold PINS_SET_STK. lia.
  - exact K3.
  - exact K4.
  - reflexivity.
  - rewrite Hra. apply ret_ok_codeptr_v; [exact Hrj | exact Hrj2].
  - rewrite Hra, unsigned_lit_small by lia. lia.
  - left. split; [|reflexivity]. left. unfold s0Z. rewrite K8. unfold w64. rewrite unsigned_lit_small; [exact Hc_lo|].
    pose proof ps_n_le16. unfold ps_c, ps_slot_of. destruct (ps_n R =? 16); unfold A_REC_SPILL, A_G_REC, OFF_CALLS, CALL_SIZE; lia.
  - intros HPRE1.
    pose proof (TXSTRDUP lyc Sc Wc regsc memc mdc [] s x HPRE1 HROD2 Ha0 (or_introl HSRC) HTAIL) as HX.
    unfold apost_base, cfg_at, w64 in HX. apply HX.
    + unfold EV_XSTRDUP. unfold EV_PINS_SET, EV_XSTRDUP, EV_ANSWER_CODE, EV_HAND_BACK, EV_XSTRDUP in HEV.
      rewrite length_app in Hk. cbn [length] in Hk. lia.
    + assert (LAC : 0 <= LIVE_ANSWER_CODE (snd (pins_set_m R uri files layout verdict)))
        by (unfold LIVE_ANSWER_CODE, LIVE_HAND_BACK, LIVE_XSTRDUP; lia).
      unfold LIVE_PINS_SET in HLIVE.
      rewrite length_app in Hbb. cbn [length] in Hbb. rewrite Nat.add_0_r, HlenP in Hbb. lia.
    + apply (mok_station MT S Sc (XM_PINS_SET MT R uri files layout verdict)
        (rec_spill_frees R * mo_free MT + ps_xm MT uri files layout verdict (length (P ++ []))) _ MTL HMOK Hmo XMNN).
      rewrite length_app, Nat.add_0_r, HlenP. unfold XM_PINS_SET. lia.
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (p & Hp10 & Hp4096 & HPerm & Hap & Hblk & Hstrp & Hstrs & HBBx & HMLE)).
rewrite Hra.
pose proof HJc as (HARc & _ & _ & _ & _ & Hfrc & Hnevc & _ & J9 & J10 & J11 & _).
assert (Hstkx : 80 <= PINS_SET_STK)
  by (unfold PINS_SET_STK, REC_CALLS_FREE_STK, XSTRDUP_STK, MIX_CALL_STK, ASTACK, ESTACK; lia).
assert (KF : forall a, sp0 - 80 <= a < sp0 -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. apply J9; [unfold ps_sp0 in *; lia | unfold ps_sp0 in *; lia | intros (r & [] & _)]. }
assert (HSK0 : ~ YI16.sink_open_fp (@nil (Z * Z))) by (apply sink_closed_pos; constructor).
assert (KG : forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
  rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha.
  assert (HPG : Exists (in_zr a) recb_PG)
    by (destruct Ha as [Ha|Ha]; [exact (recb_grec_in a Ha) | exact (recb_spill_in a Ha)]).
  assert (HU : ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
    by (destruct Ha as [Ha|Ha]; [exact (ps_unowned_grec B HB a Ha) | exact (ps_unowned_spill B HB a Ha)]).
  apply J11; [exact (cmd_prog_img a HPG) | exact (proj1 HU) | exact (proj2 HU) |].
  apply fp_spares_closed; [exact HSK0 | intros (r & [] & _)]. }
assert (KB : forall q m a, In (q, m) (ablocks B lyc Sc) -> q <= a < q + m -> rdW W2 mem2 a = rdW Wc memc a).
{ intros q m a Hin Ha. replace a with (q + (a - q)) by lia.
  apply (J10 q m (a - q)); [exact Hin | apply (Permutation_in _ (Permutation_sym HPerm)); right; exact Hin
  | unfold req_size; destruct (Z.eqb_spec m 0); lia | intros (r & [] & _)]. }
assert (Hcb : (A_G_REC <= ps_c R /\ ps_c R + CALL_SIZE <= A_G_REC + REC_SIZE) \/ ps_c R = A_REC_SPILL).
{ destruct (ps_slot_of_ok (ps_n R) ps_n_le16) as [(H1 & H2 & _) | H]; [left | right; exact H].
  unfold ps_c, A_G_REC, OFF_CALLS, OFF_ANSWER, REC_SIZE in *. lia. }
assert (KS : forall a, ps_c R <= a < ps_c R + CALL_SIZE -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. apply KG. destruct Hcb as [Hcb | Hcb]; [left | right]; unfold CALL_SIZE, SC_SIZE in *; lia. }
assert (HLX : 0 < LIVE_XSTRDUP x) by (unfold LIVE_XSTRDUP; lia).
assert (HIN2 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPerm)); right; exact Hpn).
assert (HNEW2 : In (p, LIVE_XSTRDUP x) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HPerm)); left; reflexivity).
(* the copy is apart from every block that was live: so it is none of them *)
assert (HFRESH : forall q m, In (q, m) (ablocks B lyc Sc) -> 0 < m -> q <> p).
{ intros q m Hin Hm Heq. pose proof (proj1 (Forall_forall _ _) Hap (q, m) Hin) as D. cbn [fst snd] in D.
  unfold iv_apart in D. subst q. lia. }
destruct Hrec as (Rb & Qb & rdb & blb & HA & HlenR & Hrr & Hsp0 & Hprot & HQb & Hcov & HNC & HFN & HNA & HND & HARGS & HNEWB).
apply (HNEXT ly2 S2 W2 regs2 mem2 md2 p).
- constructor.
  + exact HJ2.
  + rewrite !length_app in *. cbn [length] in *. lia.
  + rewrite !length_app in *. cbn [length] in *. lia.
  + pose proof (mle_station MT S Sc S2 _ _ MTL Hmo HMLE) as M.
    apply (mle_weaken MT S S2 _ _ MTL M). rewrite !length_app in *. cbn [length] in *.
    rewrite Nat.add_0_r, HlenP in *. replace (j - 1 + 1)%nat with (Datatypes.S (j - 1)) by lia. lia.
  + assert (BB2 : blocks_bytes S2 = bsum (ablocks B ly2 S2)) by (apply blocks_bytes_bsum).
    assert (BBc : blocks_bytes Sc = bsum (ablocks B lyc Sc)) by (apply blocks_bytes_bsum).
    rewrite BB2, (bsum_perm _ _ HPerm), bsum_cons, <- BBc. cbn [snd].
    rewrite !length_app in *. cbn [length] in *.
    rewrite Nat.add_0_r, HlenP in *. replace (j - 1 + 1)%nat with (Datatypes.S (j - 1)) by lia. lia.
  + intros i r Hir.
    assert (Hi : (i < 10)%nat) by (change 10%nat with (length ps_saved); apply (proj1 (nth_error_Some _ _)); rewrite Hir; discriminate).
    apply (ps_aval_mem_in (rdW Wc memc)); [exact (Hfr i r Hir) | intros y Hy; apply KF; unfold ps_sp0 in *; lia].
  + intros pn Hin Hno. exact (HIN2 pn (Hlive pn Hin Hno)).
  + exists Rb, Qb, rdb, blb.
    split; [exact HA|]. split; [exact HlenR|]. split; [exact Hrr|]. split; [exact Hsp0|].
    split.
    { intros y Hy. rewrite <- (Hprot y Hy).
      destruct Hy as [(Hy & _) | [(Hy & _) | ([q m] & Hpn & Hy)]]; [apply KG; left; exact Hy | apply KG; right; exact Hy|].
      exact (KB q m y (proj1 (HQb (q, m) Hpn)) Hy). }
    split.
    { intros pn Hpn. destruct (HQb pn Hpn) as (H1 & H2 & H3). split; [exact (HIN2 pn H1) | split; assumption]. }
    split.
    { intros pn Hpn. apply (Permutation_in _ HPerm) in Hpn. destruct Hpn as [<- | Hpn].
      - right. right. apply in_or_app. right. left. reflexivity.
      - destruct (Hcov pn Hpn) as [H | [H | H]]; [left; exact H | right; left; exact H | right; right].
        rewrite app_nil_r in H. apply in_or_app. left. exact H. }
    split.
    { intros Hn. apply (ps_aval_mem_in (rdW Wc memc)); [exact (HNC Hn)|].
      intros y Hy. apply KG. left. unfold A_G_REC, OFF_NCALLS, REC_SIZE in *. cbn in Hy. lia. }
    split; [apply (ps_aval_mem_in (rdW Wc memc)); [exact HFN | intros y Hy; apply KS; unfold CALL_SIZE; cbn in Hy; lia]|].
    split; [apply (ps_aval_mem_in (rdW Wc memc)); [exact HNA | intros y Hy; apply KS; unfold CALL_SIZE; cbn in Hy; lia]|].
    split.
    { rewrite app_nil_r in HND. apply NoDup_ListNoDup. apply NoDup_ListNoDup in HND.
      rewrite map_app. apply List.NoDup_app; [exact HND | constructor; [intros [] | constructor] |].
      intros a Ha Hb. destruct Hb as [Hb | []]. cbn [map fst] in Hb. subst a.
      apply in_map_iff in Ha as ([q m] & Hq & HinP). cbn [fst] in Hq. subst q.
      apply In_nth_error in HinP as (i & Hi).
      assert (Hi' : nth_error (P ++ []) i = Some (p, m)) by (rewrite app_nil_r; exact Hi).
      destruct (HNEWB i (p, m) Hi') as (_ & Hm & _ & HinS & _).
      cbn [snd] in Hm. exact (HFRESH p m HinS ltac:(lia) eq_refl). }
    split.
    { intros i pn Hi. apply (ps_aval_mem_in (rdW Wc memc)); [exact (HARGS i pn Hi)|].
      assert (Hil : (i < length P)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
      intros y Hy. apply KS. unfold CALL_SIZE. lia. }
    intros i pn Hi.
    destruct (Nat.lt_ge_cases i (length P)) as [Hil | Hil].
    { rewrite nth_error_app1 in Hi by exact Hil.
      assert (Hi' : nth_error (P ++ []) i = Some pn) by (rewrite app_nil_r; exact Hi).
      destruct (HNEWB i pn Hi') as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
      split; [exact N1|]. split; [exact N2|].
      split.
      { apply (ps_astr_kept (rdW Wc memc)); [exact N3|]. intros y Hy. destruct pn as [q m]. cbn [fst snd] in *.
        apply (KB q m y N4). lia. }
      split; [exact (HIN2 pn N4)|]. split; [exact N5|]. split; [exact N6|]. split; [exact N7 | exact N8]. }
    rewrite nth_error_app2 in Hi by exact Hil.
    remember (i - length P)%nat as z eqn:Ez. destruct z as [|z]; [|destruct z; discriminate Hi].
    cbn [nth_error] in Hi. injection Hi as <-.
    assert (Ei : i = (j - 1)%nat) by lia. subst i. fold x.
    split; [cbn [fst]; lia|]. split; [reflexivity|]. split; [exact Hstrp|].
    split; [exact HNEW2|].
    destruct (blk_off_imgP B ly2 S2 W2 mem2 md2 p (LIVE_XSTRDUP x) HARc HNEW2) as [Hlo | Hhi];
      (assert (Hrq : req_size (LIVE_XSTRDUP x) = LIVE_XSTRDUP x) by (unfold req_size; destruct (Z.eqb_spec (LIVE_XSTRDUP x) 0); lia));
      try rewrite Hrq in *.
    { split; [unfold iv_apart, A_G_REC, REC_SIZE, LIVE_XSTRDUP in *; cbn [fst snd]; lia|].
      split; [unfold iv_apart, A_REC_SPILL, SC_SIZE, LIVE_XSTRDUP in *; cbn [fst snd]; lia|].
      split.
      - cbn [fst]. intros Hm. apply in_map_iff in Hm as ([q m] & Hq & Hinq). cbn [fst] in Hq. subst q.
        destruct (HQb (p, m) Hinq) as (HinS & _ & Hm0). exact (HFRESH p m HinS Hm0 eq_refl).
      - destruct (in_dec recb_pair_dec (p, LIVE_XSTRDUP x) O) as [HO | HnO]; [right; exact HO | left].
        intros Hent. pose proof (Hlive _ Hent HnO) as HinS. exact (HFRESH p _ HinS HLX eq_refl). }
    { split; [unfold iv_apart, A_G_REC, REC_SIZE, LIVE_XSTRDUP in *; cbn [fst snd]; lia|].
      split; [unfold iv_apart, A_REC_SPILL, SC_SIZE, LIVE_XSTRDUP in *; cbn [fst snd]; lia|].
      split.
      - cbn [fst]. intros Hm. apply in_map_iff in Hm as ([q m] & Hq & Hinq). cbn [fst] in Hq. subst q.
        destruct (HQb (p, m) Hinq) as (HinS & _ & Hm0). exact (HFRESH p m HinS Hm0 eq_refl).
      - destruct (in_dec recb_pair_dec (p, LIVE_XSTRDUP x) O) as [HO | HnO]; [right; exact HO | left].
        intros Hent. pose proof (Hlive _ Hent HnO) as HinS. exact (HFRESH p _ HinS HLX eq_refl). }
- unfold ps_keep.
  assert (PR : forall r (b : bv 5), acallee_saved r -> b = Z_to_bv 5 r -> getr regs2 b = getr regsc b)
    by (intros r b Hr Hb; exact (ps_pres regsc regs2 r b HP2 Hr Hb)).
  rewrite (PR 2 2%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (PR 3 3%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (PR 4 4%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (PR 8 8%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (PR 18 18%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (PR 22 22%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (PR 23 23%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (PR 24 24%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (PR 21 21%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (PR 20 20%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (PR 19 19%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (PR 9 9%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  repeat (split; [assumption|]).
  intros r Hr. rewrite (PR r (Z_to_bv 5 r) ltac:(unfold acallee_saved; lia) eq_refl). exact (KHI r Hr).
- exact Hp10.
Qed.

End entry.
End e.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the tail jump of pins_set's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, 0x8c9f4 `j answer_code`; tpins_set_spec of lib/B/Prog/pins_set_c.v, statement from a Theorem Labs lane
   917ca7ac6b1), after the A walk's ps_tail (lib/A/Prog/pins_set_s10.v of a working branch 3cc8391594b):
   the body ends `ld ra,s0..s4; addi sp,sp,48; j answer_code`, so answer_code runs at pins_set's entry stack pointer
   and returns to pins_set's caller; its post is pins_set's post. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdAddr CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_calls_free_c xmalloc_c record_c arg_s_c mix_call_c hand_back_c answer_code_c pins_set_c RecBridge CmdRecBase CmdRecImg CmdRecRo CmdRecRest RecBLemmas pins_set_aux pins_set_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma pt_pres : forall (rg rg' : bvmap 5 word) r (b : bv 5), aregs_preserved rg rg' -> acallee_saved r ->
b = Z_to_bv 5 r -> getr rg' b = getr rg b.
Proof. intros rg rg' r b HP Hr ->. exact (HP r Hr). Qed.

(* the blocks answer_code frees: the ones that start where the recorder's answer does *)
Lemma pt_in_filter : forall (l : list (Z * Z)) (x : Z * Z) (old : Z),
In x (filter (fun pn => fst pn =? old) l) -> In x l /\ fst x = old.
Proof.
intros l x old. induction l as [|y l IH]; intros H; [destruct H|].
cbn in H. destruct (fst y =? old) eqn:E; cbn in H.
- destruct H as [-> | H].
  + split; [left; reflexivity | apply Z.eqb_eq; exact E].
  + destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis TRECORD : trecord_spec B MT.
Hypothesis TARG_S : targ_s_spec B MT.
Hypothesis TMIX_CALL : tmix_call_spec B MT.
Hypothesis TANSWER_CODE : tanswer_code_spec B MT.
Hypothesis MTL : ameter_laws MT.
Hypothesis HB : CmdBSyms B.
(* the per-binary image facts: a Theorem Labs lane's CmdRecImg.v cmd_img_facts_tfib at this walk's segments (pins_set_s1.v) *)
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro (SK := SK) SEGS B LAWS HB IMG.

Section entry.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (pu pf pl pv : Z) (u f l : list byte) (verdict : option (list byte)) (R : rstate)
  (O : list (Z * Z)).
Hypothesis HPRE : afn_pre SEGS B PINS_SET_STK ly S W regs mem md ch.
Hypothesis HFCSR : Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis HREP : rec_repA B ly S (rdW W mem) R O.
Hypothesis HFRM : Z.of_nat (length (frames S)) <= 8.
Hypothesis HEV : st_nev S + EV_PINS_SET R <= EV_MAX.
Hypothesis HLIVE : blocks_bytes S + LIVE_PINS_SET R (Some u) (Some f) (Some l) verdict <= LIVE_MAX.
Hypothesis HMOK : mo_ok MT S (XM_PINS_SET MT R (Some u) (Some f) (Some l) verdict).

#[local] Notation POST := (psb_post B MT ly S W regs mem md u f l verdict R O).
#[local] Notation FPps := (psb_FP O).
#[local] Notation JJ := (psb_J B ly S W regs mem md O).
#[local] Notation BOOK := (psb_book B ly S O).

(* the meter and the live bytes of the four arguments, the part of the statement's sums before answer_code *)
Definition psb_xm4 : Z := XM_RECORD MT R + XM_ARG_S MT (Some u) + XM_ARG_S MT (Some f) + XM_ARG_S MT (Some l) +
  XM_ARG_S MT (Some (darg verdict psb_dash)).
Definition psb_live4 : Z := LIVE_ARG_S (Some u) + LIVE_ARG_S (Some f) + LIVE_ARG_S (Some l) +
  LIVE_ARG_S (Some (darg verdict psb_dash)).

Lemma psb_tail : forall lyc Sc (Wc : world SEGS) memc mdc k (regs2 : bvmap 5 word) R2 O2 code,
JJ lyc Sc Wc memc mdc k ->
spZ regs2 = spZ regs -> getr regs2 1 = getr regs 1 -> aregs_preserved regs regs2 ->
getr regs2 10 = w64 code -> -2 ^ 31 <= code < 2 ^ 31 ->
rec_repA B lyc Sc (rdW Wc memc) R2 O2 -> BOOK lyc Sc O2 ->
pins_set_m R (Some u) (Some f) (Some l) verdict = rec_answer_code R2 code ->
k + EV_ANSWER_CODE <= EV_PINS_SET R ->
blocks_bytes Sc <= blocks_bytes S + psb_live4 ->
mo_le MT S Sc psb_xm4 ->
SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + AF_answer_code)) memc (seg_rom SEGS)) mdc) POST.
Proof.
intros lyc Sc Wc memc mdc k regs2 R2 O2 code HJ Hsp2 R1 HP2 H10 Hcode HREP2 (MID1 & MID2 & MID3) HMODEL Hk Hbb Hmo.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & Hnev & Hk0 & KEEPhi & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (Ecode : snd (pins_set_m R (Some u) (Some f) (Some l) verdict) = code) by (rewrite HMODEL; reflexivity).
(* the recorder's blocks at the jump are live *)
assert (HO2L : forall pn, In pn O2 -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (proj2 (psb_O_facts B lyc Sc _ R2 O2 HREP2 pn Hpn))).
(* the answer the recorder holds at the jump *)
destruct (psb_old_answer B lyc Sc Wc memc mdc R2 O2 HARc HREP2) as (old & HOLDV & HOLDB & HOLDC & HOLDNO).
(* the frame chain of the entry, carried to the jump: its words lie at or above the entry stack pointer, which no
   byte of the footprint reaches *)
assert (HCH : achain lyc (rdW Wc memc) (spZ regs + 0) (s0Z regs2) ch).
{ rewrite Z.add_0_r.
  assert (Es0 : s0Z regs2 = s0Z regs).
  { unfold s0Z.
    rewrite (pt_pres regs regs2 8 8%bv HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
    reflexivity. }
  rewrite Es0. apply (achain_ly_top ly lyc); [exact Etop|].
  apply (achain_kept ly (rdW W mem) (rdW Wc memc) (spZ regs) (s0Z regs) ch (spZ regs));
    [exact Hch | lia | lia |].
  intros a Ha. apply KEEPhi; [lia | lia |]. intros Hfp. pose proof (psb_FP_low B ly S W regs mem md ch R O HPRE HREP a Hfp). lia. }
(* gp and tp at the jump are the caller's *)
assert (R3 : getr regs2 3 = w64 (as_gp B)).
{ rewrite (pt_pres regs regs2 3 3%bv HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  exact Hgp. }
assert (R4 : getr regs2 4 = w64 (as_tp B)).
{ rewrite (pt_pres regs regs2 4 4%bv HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  exact Htp. }
(* what answer_code needs of the state it starts in *)
destruct (psb_ro_at B HB cmd_img_facts_tfib ly S W regs mem md ch R O
  HPRE HROD HREP lyc Sc Wc memc mdc k HJ) as [HRODc HROOKc].
assert (HFRc : Z.of_nat (length (frames Sc)) <= 8) by (rewrite Hfrs; exact HFRM).
assert (HEVc : st_nev Sc + EV_ANSWER_CODE <= EV_MAX) by lia.
assert (HLIVEc : blocks_bytes Sc + LIVE_ANSWER_CODE code <= LIVE_MAX).
{ pose proof HLIVE as HL. unfold LIVE_PINS_SET in HL. rewrite Ecode in HL. unfold psb_live4, psb_dash in Hbb. lia. }
assert (XACN : 0 <= XM_ANSWER_CODE MT code).
{ unfold XM_ANSWER_CODE, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length (resp code)) + 1)) ltac:(unfold LIVE_XMALLOC; lia)).
  lia. }
assert (XMEQ : psb_xm4 + XM_ANSWER_CODE MT code = XM_PINS_SET MT R (Some u) (Some f) (Some l) verdict).
{ unfold XM_PINS_SET, psb_xm4, psb_dash. rewrite Ecode. lia. }
assert (HMOKc : mo_ok MT Sc (XM_ANSWER_CODE MT code)).
{ apply (mok_station MT S Sc (XM_PINS_SET MT R (Some u) (Some f) (Some l) verdict) _ _ MTL HMOK Hmo XACN). lia. }
assert (HFPlow : forall a, inFP FPps a -> a < alloc_ceiling)
  by (intros a Hfp; pose proof (psb_FP_low B ly S W regs mem md ch R O HPRE HREP a Hfp); lia).
eapply SRr_mono.
{ eapply (callS_wideF B LAWS Wc regs2 memc _ PINS_SET_STK (spZ regs) FPps ly S W mem md []
    lyc Sc mdc k ANSWER_CODE_STK
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O2))
    EV_ANSWER_CODE 0 (getr regs2 1) ch).
  - exact HJ.
  - rewrite Hsp2. lia.
  - reflexivity.
  - lia.
  - unfold ANSWER_CODE_STK, HAND_BACK_STK, XMALLOC_STK, ASTACK, ESTACK. lia.
  - unfold PINS_SET_STK. lia.
  - exact R3.
  - exact R4.
  - reflexivity.
  - rewrite R1. exact Hra.
  - rewrite R1. exact Hra4.
  - exact HCH.
  - intros HPREa.
    exact (TANSWER_CODE lyc Sc Wc regs2 memc mdc ch code old R2 O2 HPREa HFCSR HRODc HROOKc H10 Hcode
      HREP2 HOLDV HOLDB HFRc HEVc HLIVEc HMOKc).
  - (* every byte answer_code writes is one this call may write *)
    intros a Hfp. apply inFP_cons in Hfp as [Ha | Hfp].
    + assert (Hg : A_G_REC <= a < A_G_REC + REC_SIZE) by (unfold OFF_ANSWER in Ha; unfold REC_SIZE; lia).
      apply (recb_prog_awr_m B HB cmd_prog_img); [|exact (recb_grec_in a Hg)].
      unfold psb_FP. apply inFP_cons; left; exact Hg.
    + apply inFP_ablocks_fp_inv in Hfp as (p & n & Hin & Hr).
      apply pt_in_filter in Hin as [Hin _].
      pose proof (HO2L (p, n) Hin) as HinC.
      destruct (MID3 (p, n) Hin) as [HinO | HnS].
      * right; left. split.
        -- replace a with (p + (a - p)) by lia. unfold psb_FP. apply inFP_cons; right. apply inFP_cons; right.
           exact (inFP_ablocks_fp O p n (a - p) HinO ltac:(lia)).
        -- exists p, n. split; [exact HinC | lia].
      * right; right; left. exists p, n. split; [exact HinC|]. split; [exact HnS | lia].
  - (* no byte of answer_code's footprint is in this call's stack window *)
    intros ly2 S2 W2 regs3 mem2 md2 HK a Hfp Hw Hn. exfalso.
    apply inFP_cons in Hfp as [Ha | Hfp].
    + unfold A_G_REC, OFF_ANSWER in Ha. lia.
    + apply inFP_ablocks_fp_inv in Hfp as (p & n & Hin & Hr).
      apply pt_in_filter in Hin as [Hin _].
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc (HO2L (p, n) Hin)) as (_ & _ & Hceil2 & _).
      lia. }
(* answer_code's post is this call's post *)
cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & HFR & HCS & HJ' & _ & HPR & HK).
destruct HK as (p1 & O' & Hret & Hfresh & Hblocks & HREP' & HO' & HBB' & HMLE').
unfold psb_post, apost_baseF. cbv beta.
exists fx', ly', S', regs', mem', md'.
split; [rewrite R1; reflexivity|].
split; [exact HFR|]. split; [exact HCS|].
split; [exact (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' Hk)|].
split; [exact (aregs_preserved_trans _ _ _ HP2 HPR)|].
set (nres := Z.of_nat (length (resp code)) + 1) in *.
exists (fst (rec_answer_code R2 code)), (snd (rec_answer_code R2 code)), O'.
split; [rewrite HMODEL; reflexivity|].
split; [exact Hret|].
split; [exact Hcode|].
split; [exact HREP'|].
split.
{ intros pn Hpn. apply HO' in Hpn as [[Hpn _] | ->].
  - exact (MID3 pn Hpn).
  - destruct (in_dec recb_pair_dec (p1, nres) (ablocks B ly S)) as [Hin | Hnin]; [|right; exact Hnin].
    left. destruct (in_dec recb_pair_dec (p1, nres) O) as [HinO | HninO]; [exact HinO|].
    exfalso. pose proof (MID2 (p1, nres) Hin HninO) as HinC.
    destruct (Z.eq_dec p1 old) as [Eo | Ne].
    + destruct (MID3 (p1, nres) (HOLDNO (p1, nres) HinC Eo)) as [HinO' | Hnin'];
        [exact (HninO HinO') | exact (Hnin' Hin)].
    + exact (Hfresh (p1, nres) HinC Ne eq_refl). }
split.
{ intros pn Hpn HnO. apply Hblocks. left. split; [exact (MID2 pn Hpn HnO)|].
  intros Hfst. destruct (MID3 pn (HOLDNO pn (MID2 pn Hpn HnO) Hfst)) as [HinO | Hnin];
    [exact (HnO HinO) | exact (Hnin Hpn)]. }
split.
{ intros pn Hpn. apply Hblocks in Hpn as [[Hpn Hne] | ->].
  - destruct (MID1 pn Hpn) as [H | H]; [left; exact H|].
    right. apply HO'. left. split; [exact H | exact Hne].
  - right. apply HO'. right. reflexivity. }
split.
{ unfold LIVE_PINS_SET. rewrite Ecode. unfold psb_live4, psb_dash in Hbb. lia. }
apply (mle_weaken MT S S' _ _ MTL (mle_station MT S Sc S' _ _ MTL Hmo HMLE')). lia.
Qed.

(* --- the slot record() returns ------------------------------------------------------------------------------ *)
Lemma psb_slot_range : (exists i, 0 <= i < REC_CALLS_MAX /\ rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/
rec_slot R = A_REC_SPILL.
Proof.
unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [H | H]; [left | right; reflexivity].
exists (Z.of_nat (length (r_calls R))). split; [unfold REC_CALLS_MAX; lia | reflexivity].
Qed.

(* the slot's bytes lie in g_rec's call table or in record.spill *)
Lemma psb_slot_PG : forall a, rec_slot R <= a < rec_slot R + CALL_SIZE ->
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) /\ Exists (in_zr a) recb_PG.
Proof.
intros a Ha. destruct psb_slot_range as [(i & Hi & E) | E]; rewrite E in Ha.
- assert (Hg : A_G_REC <= a < A_G_REC + REC_SIZE) by (unfold REC_CALLS_MAX, A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia).
  split; [left; exact Hg | exact (recb_grec_in a Hg)].
- assert (Hs : A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) by (unfold CALL_SIZE, SC_SIZE in *; lia).
  split; [right; exact Hs | exact (recb_spill_in a Hs)].
Qed.

Lemma psb_FP_PG : forall a, Exists (in_zr a) recb_PG -> (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
inFP FPps a.
Proof.
intros a _ [Ha | Ha]; unfold psb_FP; apply inFP_cons; [left; exact Ha | right; apply inFP_cons; left; exact Ha].
Qed.

Lemma psb_stk_v : PINS_SET_STK = 16608.
Proof. vm_compute. reflexivity. Qed.

(* --- the call of arg_s (0x8c974, 0x8c980, 0x8c98c, 0x8c9a4), through its contract (arg_s_c.v targ_s_spec) ---- *)
Definition psb_argfp (A : list (list byte)) : list (Z * Z) :=
if Z.of_nat (length A) <? REC_ARGS_MAX
then [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
      (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A), rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8)]
else [].

Lemma psb_argfp_PG : forall A a, (length A < 6)%nat -> inFP (psb_argfp A) a ->
rec_slot R <= a < rec_slot R + CALL_SIZE.
Proof.
intros A a HA Hf. unfold psb_argfp in Hf.
replace (Z.of_nat (length A) <? REC_ARGS_MAX) with true in Hf by (symmetry; apply Z.ltb_lt; unfold REC_ARGS_MAX; lia).
apply inFP_cons in Hf as [Hf | Hf]; [unfold CALL_OFF_NARGS, CALL_SIZE in *; lia|].
apply inFP_cons in Hf as [Hf | Hf]; [unfold CALL_OFF_ARGS, CALL_SIZE in *; lia|].
destruct Hf as (r & Hr & _). destruct Hr.
Qed.

Lemma psb_call_arg_s : forall lyc Sc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc k s v A O2 retk,
JJ lyc Sc Wc memc mdc k ->
spZ regsc = spZ regs - 48 -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
getr regsc 10 = w64 (rec_slot R) -> getr regsc 11 = w64 s -> s0Z regsc < alloc_ceiling ->
(length A < 6)%nat ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_PINS_SET A) O2 ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] s v ->
(forall x, v = Some x -> atail_vis SEGS Wc memc (s + Z.of_nat (length x))) ->
st_nev Sc + EV_ARG_S <= EV_MAX -> blocks_bytes Sc + LIVE_ARG_S v <= LIVE_MAX -> mo_ok MT Sc (XM_ARG_S MT v) ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_arg_s)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 p,
 c2 = mkCfg (mkst regs2 (getr regsc 1) mem2 (seg_rom SEGS)) md2 /\
 JJ ly2 S2 W2 mem2 md2 (k + EV_ARG_S) /\
 ajournal SEGS B ARG_S_STK (spZ regs + -48) (psb_argfp A) lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 EV_ARG_S /\
 aregs_preserved regsc regs2 /\
 blocks_bytes S2 <= blocks_bytes Sc + LIVE_ARG_S v /\ mo_le MT Sc S2 (XM_ARG_S MT v) /\
 4096 <= p < 2 ^ 64 /\
 Permutation (ablocks B ly2 S2) ((p, Z.of_nat (length (sarg v)) + 1) :: ablocks B lyc Sc) /\
 Forall (fun qk => iv_apart p (Z.of_nat (length (sarg v)) + 1) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
 rec_repA B ly2 S2 (rdW W2 mem2) (rec_record R REC_PINS_SET (A ++ [sarg v])) ((p, Z.of_nat (length (sarg v)) + 1) :: O2)).
Proof.
intros lyc Sc Wc regsc memc mdc k s v A O2 retk HJ Hsp G3 G4 Gra Hrk Hrk2 G10 G11 Hs0 HlenA HREP2 HSTR HTAIL HEV2 HLIVE2 HMOK2.
pose proof (psb_sp0 B ly S W regs mem md ch HPRE) as (Hal & Hsp0 & Htop0 & HS0).
pose proof asan_consts as (C1 & _). pose proof pa_B_ok as HBASE.
destruct (psb_ro_at B HB cmd_img_facts_tfib ly S W regs mem md ch R O
  HPRE HROD HREP lyc Sc Wc memc mdc k HJ) as [HRODc HROOKc].
eapply SRr_mono.
{ eapply (cl_callS_wide B LAWS Wc regsc memc _ PINS_SET_STK (spZ regs) FPps ly S W mem md []
    lyc Sc mdc k ARG_S_STK (psb_argfp A) EV_ARG_S (-48) (getr regsc 1) []).
  - exact HJ.
  - lia.
  - reflexivity.
  - lia.
  - unfold ARG_S_STK, XMALLOC_STK, ASTACK, ESTACK. lia.
  - rewrite psb_stk_v. unfold ARG_S_STK, XMALLOC_STK, ASTACK, ESTACK. lia.
  - exact G3.
  - exact G4.
  - reflexivity.
  - rewrite Gra. apply ret_ok_codeptr_v; [exact Hrk | exact Hrk2].
  - rewrite Gra, unsigned_lit_small by lia. pose proof pa_base_lo. lia.
  - apply achain_low. exact Hs0.
  - intros HPREx.
    exact (TARG_S lyc Sc Wc regsc memc mdc [] (rec_slot R) s REC_PINS_SET A v R O2 HPREx HRODc HROOKc G10 G11
      eq_refl HREP2 (or_introl HSTR) HTAIL HEV2 HLIVE2 HMOK2).
  - intros a Hf. pose proof (psb_argfp_PG A a HlenA Hf) as Ha.
    destruct (psb_slot_PG a Ha) as [Hr HPG].
    exact (recb_prog_awr_m B HB cmd_prog_img _ _ _ _ _ _ _ _ a (psb_FP_PG a HPG Hr) HPG).
  - intros ly2 S2 W2 regs3 mem2 md2 _ a Hf Hw _. exfalso.
    pose proof (psb_argfp_PG A a HlenA Hf) as Ha. destruct (psb_slot_PG a Ha) as [Hr _].
    rewrite psb_stk_v in Hw. unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hr. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & HK).
cbv zeta in HK.
destruct HK as (Hbb & Hmle & [(Hlen6 & _) | (_ & p & H4096 & Hperm & Hap & HREP3)]);
  [exfalso; unfold REC_ARGS_MAX in Hlen6; lia|].
exists ly2, S2, regs2, mem2, md2, p.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HJc|]. split; [exact HP2|].
split; [exact Hbb|]. split; [exact Hmle|]. split; [exact H4096|]. split; [exact Hperm|]. split; [exact Hap | exact HREP3].
Qed.

(* --- the call of record (0x8c968), through its contract (record_c.v trecord_spec) ---------------------------- *)
Definition psb_recfp : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
(if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O).

Lemma psb_call_record : forall (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc k retk ch1,
JJ ly S Wc memc mdc k ->
spZ regsc = spZ regs - 48 -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
getr regsc 10 = w64 REC_PINS_SET ->
achain ly (rdW Wc memc) (spZ regs + -48) (s0Z regsc) ch1 ->
rec_repA B ly S (rdW Wc memc) R O ->
st_nev S + EV_RECORD R <= EV_MAX -> mo_ok MT S (XM_RECORD MT R) ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_record)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 F O1,
 c2 = mkCfg (mkst regs2 (getr regsc 1) mem2 (seg_rom SEGS)) md2 /\
 JJ ly2 S2 W2 mem2 md2 (k + EV_RECORD R) /\
 ajournal SEGS B RECORD_STK (spZ regs + -48) psb_recfp ly S Wc memc mdc [] ly2 S2 W2 mem2 md2 (EV_RECORD R) /\
 aregs_preserved regsc regs2 /\
 getr regs2 10 = w64 (rec_slot R) /\
 Permutation (ablocks B ly S) (ablocks B ly2 S2 ++ F) /\
 Z.of_nat (length F) = rec_spill_frees R /\
 (forall pn, In pn F -> In pn O) /\
 rec_repA B ly2 S2 (rdW W2 mem2) (rec_record R REC_PINS_SET []) O1 /\
 (forall pn, In pn O1 <-> In pn O /\ ~ In pn F) /\
 blocks_bytes S2 <= blocks_bytes S /\
 mo_le MT S S2 (XM_RECORD MT R)).
Proof.
intros Wc regsc memc mdc k retk ch1 HJ Hsp G3 G4 Gra Hrk Hrk2 G10 Hch1 HREP2 HEV2 HMOK2.
pose proof (psb_sp0 B ly S W regs mem md ch HPRE) as (Hal & Hsp0 & Htop0 & HS0).
pose proof asan_consts as (C1 & _). pose proof pa_B_ok as HBASE.
destruct (psb_ro_at B HB cmd_img_facts_tfib ly S W regs mem md ch R O
  HPRE HROD HREP ly S Wc memc mdc k HJ) as [HRODc _].
pose proof (proj1 HJ) as HARc.
eapply SRr_mono.
{ eapply (cl_callS_wide B LAWS Wc regsc memc _ PINS_SET_STK (spZ regs) FPps ly S W mem md []
    ly S mdc k RECORD_STK psb_recfp (EV_RECORD R) (-48) (getr regsc 1) ch1).
  - exact HJ.
  - lia.
  - reflexivity.
  - lia.
  - unfold RECORD_STK, REC_CALLS_FREE_STK, ASTACK. lia.
  - rewrite psb_stk_v. unfold RECORD_STK, REC_CALLS_FREE_STK, ASTACK. lia.
  - exact G3.
  - exact G4.
  - reflexivity.
  - rewrite Gra. apply ret_ok_codeptr_v; [exact Hrk | exact Hrk2].
  - rewrite Gra, unsigned_lit_small by lia. pose proof pa_base_lo. lia.
  - exact Hch1.
  - intros HPREx.
    exact (TRECORD ly S Wc regsc memc mdc ch1 REC_PINS_SET R O HPREx HRODc G10
      ltac:(unfold REC_PINS_SET, REC_FN_COUNT; lia) HREP2 HEV2 HMOK2).
  - intros a Hf. unfold psb_recfp in Hf. apply inFP_cons in Hf as [Ha | Hf].
    + assert (Hg : A_G_REC <= a < A_G_REC + REC_SIZE) by (unfold OFF_NCALLS, REC_SIZE in *; lia).
      exact (recb_prog_awr_m B HB cmd_prog_img _ _ _ _ _ _ _ _ a (psb_FP_PG a (recb_grec_in a Hg) (or_introl Hg)) (recb_grec_in a Hg)).
    + apply inFP_cons in Hf as [Ha | Hf].
      * destruct (psb_slot_PG a ltac:(unfold CALL_SIZE; lia)) as [Hr HPG].
        exact (recb_prog_awr_m B HB cmd_prog_img _ _ _ _ _ _ _ _ a (psb_FP_PG a HPG Hr) HPG).
      * destruct (Nat.ltb (length (r_calls R)) 16); [destruct Hf as (r & Hr & _); destruct Hr|].
        apply inFP_ablocks_fp_inv in Hf as (p & n & Hpn & Hpa).
        right; left. split.
        -- replace a with (p + (a - p)) by lia. unfold psb_FP. apply inFP_cons; right. apply inFP_cons; right.
           exact (inFP_ablocks_fp O p n (a - p) Hpn ltac:(lia)).
        -- exists p, n. split; [exact (psb_O_live B ly S W mem R O HREP (p, n) Hpn) | lia].
  - intros ly2 S2 W2 regs3 mem2 md2 _ a Hf Hw _. exfalso.
    assert (Hlo : a < alloc_ceiling).
    { unfold psb_recfp in Hf. apply inFP_cons in Hf as [Ha | Hf]; [unfold A_G_REC, OFF_NCALLS in Ha; lia|].
      apply inFP_cons in Hf as [Ha | Hf].
      - destruct (psb_slot_PG a ltac:(unfold CALL_SIZE; lia)) as [Hr _]. unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hr. lia.
      - destruct (Nat.ltb (length (r_calls R)) 16); [destruct Hf as (r & Hr & _); destruct Hr|].
        apply inFP_ablocks_fp_inv in Hf as (p & n & Hpn & Hpa).
        destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc (psb_O_live B ly S W mem R O HREP (p, n) Hpn)) as (_ & _ & Hce & _). lia. }
    rewrite psb_stk_v in Hw, Hsp0. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & HK).
destruct HK as (F & O1 & H10 & Hperm & HlenF & HFO & HREP3 & HO1 & Hbb & Hmle).
exists ly2, S2, regs2, mem2, md2, F, O1.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HJc|]. split; [exact HP2|]. split; [exact H10|].
split; [exact Hperm|]. split; [exact HlenF|]. split; [exact HFO|]. split; [exact HREP3|]. split; [exact HO1|].
split; [exact Hbb | exact Hmle].
Qed.

(* --- the call of mix_call (0x8c9c8), through its contract (mix_call_c.v tmix_call_spec) ---------------------- *)
Lemma psb_call_mix : forall lyc Sc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc k A O2 retk,
JJ lyc Sc Wc memc mdc k ->
spZ regsc = spZ regs - 48 -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
getr regsc 10 = w64 (r_state R) -> getr regsc 11 = w64 (rec_slot R) ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_PINS_SET A) O2 ->
st_nev Sc + EV_MIX_CALL <= EV_MAX ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_mix_call)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 (getr regsc 1) mem2 (seg_rom SEGS)) md2 /\
 JJ ly2 S2 W2 mem2 md2 (k + EV_MIX_CALL) /\
 ajournal SEGS B MIX_CALL_STK (spZ regs + -48) [] lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 EV_MIX_CALL /\
 aregs_preserved regsc regs2 /\
 getr regs2 10 = w64 (mixcall (r_state R) REC_PINS_SET A) /\ ly2 = lyc /\ S2 = Sc).
Proof.
intros lyc Sc Wc regsc memc mdc k A O2 retk HJ Hsp G3 G4 Gra Hrk Hrk2 G10 G11 HREP2 HEV2.
pose proof (psb_sp0 B ly S W regs mem md ch HPRE) as (Hal & Hsp0 & Htop0 & HS0).
pose proof asan_consts as (C1 & _). pose proof pa_B_ok as HBASE.
destruct (psb_ro_at B HB cmd_img_facts_tfib ly S W regs mem md ch R O
  HPRE HROD HREP lyc Sc Wc memc mdc k HJ) as [HRODc HROOKc].
destruct (rec_bridge_slot B lyc Sc _ R REC_PINS_SET A O2 HREP2) as (HSLOT & _ & _ & P & HCALL & _).
destruct (psb_scalars B lyc Sc _ _ O2 HREP2) as (_ & _ & _ & _ & _ & Hst64).
destruct (psb_rec_record_scalars R REC_PINS_SET A) as (_ & _ & Est & _). rewrite Est in Hst64.
eapply SRr_mono.
{ eapply (cl_callS_na B LAWS Wc regsc memc _ PINS_SET_STK (spZ regs) FPps ly S W mem md []
    lyc Sc mdc k MIX_CALL_STK [] EV_MIX_CALL (-48) (getr regsc 1)).
  - exact HJ.
  - lia.
  - reflexivity.
  - lia.
  - unfold MIX_CALL_STK, ESTACK. lia.
  - rewrite psb_stk_v. unfold MIX_CALL_STK, ESTACK. lia.
  - exact G3.
  - exact G4.
  - reflexivity.
  - rewrite Gra. apply ret_ok_codeptr_v; [exact Hrk | exact Hrk2].
  - rewrite Gra, unsigned_lit_small by lia. pose proof pa_base_lo. lia.
  - intros HPREx.
    exact (TMIX_CALL lyc Sc Wc regsc memc mdc (r_state R) (rec_slot R) (REC_PINS_SET, A) P HPREx HRODc G10 Hst64 G11
      HSLOT HCALL HROOKc HEV2).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & HK).
destruct HK as (H10 & _ & Hly & HS).
exists ly2, S2, regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HJc|]. split; [exact HP2|]. split; [exact H10|].
split; [exact Hly | exact HS].
Qed.

End entry.
End e.
End f.
End d.

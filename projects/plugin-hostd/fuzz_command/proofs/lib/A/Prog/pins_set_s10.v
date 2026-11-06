(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the close of pins_set's recorded call and its tail jump into answer_code,
   after proofs/cgif/cgif_file_fuzzer/lib/A/ACh*.v at c8557374ad2e (the last segments of the
   cgif_close walk: the call closed into the model, and the tail call composed with the call rule) over
   fuzz_command's recorder. *)

(* `ps_close`: after the fourth argument is stored, the slot holds the whole call (fn = 20, nargs = 4, the four
   copies), so the recorder's representation is the one of `rec_record R 20 A`.
   `ps_tail`: the body ends `ld ra..s8; addi sp,sp,80; j answer_code`, so answer_code runs at pins_set's entry
   stack pointer and returns to pins_set's caller; its post is pins_set's post. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c mix_call_c answer_code_c pins_set_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
RecBLemmas pins_set_s2 pins_set_s1 pins_set_s3 pins_set_s6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
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
(* the callee of the tail jump *)
Hypothesis TANSWER_CODE : tanswer_code_spec B MT.

(* two live blocks with the same start are the same block *)
Lemma pt_same_start : forall ly S (W : world SEGS) mem md p n m,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (p, m) (ablocks B ly S) -> n = m.
Proof.
intros ly S W mem md p n m HAR H1 H2.
destruct (Z.eq_dec n m) as [->|Hne]; [reflexivity|]. exfalso.
pose proof (sep_blocks SEGS B LAWS ly S W mem md p n p m HAR H1 H2
  ltac:(intros E; injection E as E'; exact (Hne E'))) as D.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR H1) as (_ & _ & _ & _ & _ & _ & Hn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR H2) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos n ltac:(lia)) as [Qn _]. pose proof (req_size_pos m ltac:(lia)) as [Qm _].
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

Section entry.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (pu pf pl pv : Z) (uri files layout verdict : option (list byte)) (R : rstate)
  (O : list (Z * Z)).
Hypothesis HPRE : afn_pre SEGS B PINS_SET_STK ly S W regs mem md ch.
(* rounding mode 0 at the entry (the statement's pre since pass 4); the calls before the tail jump keep the FP state *)
Hypothesis HRM : Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis HSU : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pu uri.
Hypothesis HSF : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pf files.
Hypothesis HSL : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pl layout.
Hypothesis HSV : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pv verdict.
Hypothesis HREPA : rec_repA B ly S (rdW W mem) R O.
Hypothesis HEV : st_nev S + EV_PINS_SET R <= EV_MAX.
Hypothesis HLIVE : blocks_bytes S + LIVE_PINS_SET R uri files layout verdict <= LIVE_MAX.
Hypothesis HMOK : mo_ok MT S (XM_PINS_SET MT R uri files layout verdict).
(* room for answer_code's side-stack frame (the statement's premise, pins_set_c.v:113) *)
Hypothesis HFRM : Z.of_nat (length (frames S)) <= 8.

#[local] Notation sp0 := (ps_sp0 regs).
#[local] Notation FPps := (ps_FP O).
#[local] Notation A := (ps_A uri files layout verdict).
#[local] Notation PTRS := (ps_ptrs pu pf pl pv uri files layout verdict).
#[local] Notation CORE := (ps_core B MT ly S W regs mem md uri files layout verdict R O).
#[local] Notation KEEP := (ps_keep B regs pf pl pv R).
#[local] Notation POST := (ps_post B MT ly S W regs mem md uri files layout verdict R O).

(* --- the recorded call closes ---------------------------------------------------------------------------- *)

(* each argument string has at most LMAX bytes: the caller's string by its astr_argA, the defaults by
   computation *)
Lemma pt_sarg_lmax : forall p v, astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p v ->
Z.of_nat (length (sarg v)) <= LMAX.
Proof.
intros p [x|] Hv; cbn [sarg].
- destruct Hv as (_ & _ & Hn & _). lia.
- change (Z.of_nat (length (bstr "(null)"%string))) with 6. unfold LMAX. lia.
Qed.

Lemma pt_darg_lmax : forall p v, astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p v ->
Z.of_nat (length (darg v (bstr "-"%string))) <= LMAX.
Proof.
intros p [x|] Hv; cbn [darg].
- destruct Hv as (_ & _ & Hn & _). lia.
- change (Z.of_nat (length (bstr "-"%string))) with 1. unfold LMAX. lia.
Qed.

Lemma pt_A_lmax : Forall (fun s => Z.of_nat (length s) <= LMAX) A.
Proof.
unfold ps_A.
constructor; [exact (pt_sarg_lmax _ _ HSU)|].
constructor; [exact (pt_sarg_lmax _ _ HSF)|].
constructor; [exact (pt_sarg_lmax _ _ HSL)|].
constructor; [exact (pt_darg_lmax _ _ HSV)|].
constructor.
Qed.

Lemma ps_close : ps_close_stmt B MT ly S W regs mem md uri files layout verdict R O.
Proof.
unfold ps_close_stmt.
intros P lyc Sc Wc memc mdc k HlenP HC.
destruct HC as [HJ Hk Hlen Hmo Hbb Hfr Hlive Hrec].
destruct Hrec as (Rb & Qb & rdb & blb & HA & HlenR & Hrr & Hsp0 & Hprot & HQb & Hcov & HNC & HFN & HNA & HND & HARGS & HNEWB).
rewrite app_nil_r in Hcov, HND, HNEWB.
assert (Hn : ps_n R = Z.of_nat (length (r_calls Rb))) by (unfold ps_n; rewrite HlenR; reflexivity).
(* the slot holds the call: fn = 20, nargs = 4, and the four copies *)
assert (HSLOT : acall_at (ablocks B lyc Sc) (rdW Wc memc) (ps_c R) (REC_PINS_SET, A) P).
{ unfold acall_at. cbn [fst snd].
  split; [unfold REC_PINS_SET, REC_FN_COUNT; lia|].
  split; [unfold ps_A; cbn [length]; lia|].
  split; [rewrite HlenP; reflexivity|].
  split; [unfold CALL_OFF_FN; rewrite Z.add_0_r; exact HFN|].
  split; [unfold CALL_OFF_NARGS; rewrite HlenP in HNA; exact HNA|].
  split; [exact HND|].
  intros i s pn Hs Hpn.
  destruct (HNEWB i pn Hpn) as (N1 & N2 & N3 & N4 & _).
  assert (Es : nth i A [] = s) by (apply nth_error_nth; exact Hs).
  rewrite Es in N2, N3.
  pose proof (proj1 (Forall_forall _ _) pt_A_lmax s (nth_error_In _ _ Hs)) as HL. cbv beta in HL.
  split; [unfold CALL_OFF_ARGS; exact (HARGS i pn Hpn)|].
  split; [exact N1|]. split; [exact N4|]. split; [lia | exact N3]. }
assert (HAPT : forall pn, In pn P ->
  iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE).
{ intros pn Hpn. destruct (In_nth_error P pn Hpn) as (i & Hi).
  destruct (HNEWB i pn Hi) as (_ & _ & _ & _ & N5 & N6 & _). split; [exact N5 | exact N6]. }
assert (HFRS : forall pn, In pn P -> ~ In (fst pn) (map fst (lay_blocks Qb))).
{ intros pn Hpn. destruct (In_nth_error P pn Hpn) as (i & Hi).
  destruct (HNEWB i pn Hi) as (_ & _ & _ & _ & _ & _ & N7 & _). exact N7. }
pose proof (arep_put blb (ablocks B lyc Sc) rdb (rdW Wc memc) Rb Qb REC_PINS_SET A P (ps_n R) HA Hn Hprot
  (fun pn H => proj1 (HQb pn H)) Hsp0 HNC HSLOT pt_A_lmax HAPT HFRS) as HPUT.
rewrite Hrr in HPUT.
set (Q2 := qput (length (r_calls Rb)) Qb P) in *.
(* the blocks of the new layout: the base layout's and the four copies *)
assert (HQ2 : forall pn, In pn (lay_blocks Q2) <-> In pn (lay_blocks Qb) \/ In pn P).
{ intros pn. unfold Q2. destruct (Nat.ltb_spec (length (r_calls Rb)) 16) as [H16 | H16].
  - rewrite <- in_app_iff. split; intros H.
    + exact (Permutation_in _ (lay_blocks_qput_slot _ Qb P H16) H).
    + exact (Permutation_in _ (Permutation_sym (lay_blocks_qput_slot _ Qb P H16)) H).
  - rewrite (lay_blocks_qput_spill _ Qb P H16). unfold lay_blocks.
    rewrite (Hsp0 ltac:(lia)). cbn [app]. rewrite !in_app_iff. tauto. }
exists (lay_blocks Q2).
split; [exists Q2; split; [exact HPUT | intros pn; apply iff_refl]|].
split.
{ intros pn Hpn. destruct (Hcov pn Hpn) as [H | [H | H]];
    [left; exact H | right; apply HQ2; left; exact H | right; apply HQ2; right; exact H]. }
split.
{ intros pn Hpn. apply HQ2 in Hpn as [H | H].
  - left. exact (proj1 (proj2 (HQb pn H))).
  - destruct (In_nth_error P pn H) as (i & Hi).
    destruct (HNEWB i pn Hi) as (_ & _ & _ & _ & _ & _ & _ & N8).
    destruct N8 as [N8 | N8]; [right; exact N8 | left; exact N8]. }
exact HSLOT.
Qed.

(* --- the tail jump into answer_code ---------------------------------------------------------------------- *)

(* the recorder's footprint holds no read-only byte *)
Lemma pt_FP_ro : forall a, in_roP SEGS RLO RHI a -> ~ inFP FPps a.
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

(* every byte of the recorder's footprint is below the stack *)
Lemma pt_FP_low : forall a, inFP FPps a -> a < alloc_ceiling.
Proof.
intros a Hf. pose proof asan_consts as (C1 & _).
unfold ps_FP in Hf. apply inFP_cons in Hf as [Hf | Hf]; [unfold A_G_REC, REC_SIZE in Hf; lia|].
apply inFP_cons in Hf as [Hf | Hf]; [unfold A_REC_SPILL, SC_SIZE in Hf; lia|].
destruct (inFP_ablocks_fp_inv O a Hf) as (q & n & Hq & Hr).
destruct (ps_O_facts B ly S _ R O HREPA (q, n) Hq) as [_ HqS].
destruct HPRE as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q n HAR HqS) as (_ & _ & Hc & _). lia.
Qed.

Lemma ps_tail : ps_tail_stmt B MT ly S W regs mem md uri files layout verdict R O.
Proof.
unfold ps_tail_stmt.
intros lyc Sc Wc memc mdc k regs2 R2 O2 code HJ Hsp2 R1 HP2 H10 Hcode HREP2 MID1 MID2 MID3 HMODEL Hk Hbb Hmo.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & Hnev & Hk0 & KEEPhi & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (Esp0 : ps_sp0 regs = spZ regs) by reflexivity.
assert (Ecode : snd (pins_set_m R uri files layout verdict) = code) by (rewrite HMODEL; reflexivity).
(* the recorder's blocks at the jump are live *)
assert (HO2L : forall pn, In pn O2 -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (proj2 (ps_O_facts B lyc Sc _ R2 O2 HREP2 pn Hpn))).
(* the answer the recorder holds at the jump: 0, or the start of one of its blocks *)
assert (HOLD : exists old, aval_mem (rdW Wc memc) (A_G_REC + OFF_ANSWER) 8 old /\
  (old = 0 \/ exists pa, In pa O2 /\ fst pa = old)).
{ pose proof HREP2 as (Q2 & HA2 & HO2).
  destruct HA2 as (_ & _ & _ & _ & HAns & _). unfold aanswer_at in HAns.
  destruct (r_answer R2) as [x|], (l_answer Q2) as [pa|] eqn:Eq; try contradiction.
  - exists (fst pa). split; [exact (proj1 HAns)|]. right. exists pa.
    split; [apply HO2; exact (ps_lay_ans_in Q2 pa Eq) | reflexivity].
  - exists 0. split; [exact HAns | left; reflexivity]. }
destruct HOLD as (old & HOLDV & HOLDC).
(* a live block that starts where the answer does is the recorder's answer block *)
assert (HOLDNO : forall pn, In pn (ablocks B lyc Sc) -> fst pn = old -> In pn O2).
{ intros [p n] Hpn Hf. cbn [fst] in Hf.
  destruct HOLDC as [E0 | ([pp pm] & Hpa & Hpf)].
  - exfalso. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hpn) as (_ & H4096 & _). lia.
  - cbn [fst] in Hpf. subst pp. subst p.
    pose proof (pt_same_start lyc Sc Wc memc mdc old n pm HARc Hpn (HO2L _ Hpa)) as En.
    subst pm. exact Hpa. }
(* the answer is a 64-bit word: 0, or the start of a live block, below alloc_ceiling *)
assert (HOLDB : 0 <= old < 2 ^ 64).
{ destruct HOLDC as [-> | ([p n] & Hpa & Hpf)]; [lia|]. cbn [fst] in Hpf. subst p.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ old n HARc (HO2L _ Hpa)) as (_ & H4096 & Hce & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [Qn _]. lia. }
(* the frame chain of the entry, carried to the jump: its words lie at or above the entry stack pointer,
   which no byte of the footprint reaches *)
assert (HCH : achain lyc (rdW Wc memc) (ps_sp0 regs + 0) (s0Z regs2) ch).
{ rewrite Z.add_0_r, Esp0.
  assert (Es0 : s0Z regs2 = s0Z regs).
  { unfold s0Z.
    rewrite (pt_pres regs regs2 8 8%bv HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
    reflexivity. }
  rewrite Es0. apply (achain_ly_top ly lyc); [exact Etop|].
  apply (achain_kept ly (rdW W mem) (rdW Wc memc) (spZ regs) (s0Z regs) ch (spZ regs));
    [exact Hch | lia | lia |].
  intros a Ha. apply KEEPhi; [lia | lia |]. intros Hfp. pose proof (pt_FP_low a Hfp). lia. }
(* gp and tp at the jump are the caller's *)
assert (R3 : getr regs2 3 = w64 (as_gp B)).
{ rewrite (pt_pres regs regs2 3 3%bv HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  exact Hgp. }
assert (R4 : getr regs2 4 = w64 (as_tp B)).
{ rewrite (pt_pres regs regs2 4 4%bv HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  exact Htp. }
(* what answer_code needs of the state it starts in *)
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW Wc memc))
  by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ pt_FP_ro HROD).
pose proof (cmd_ro_ok_of_aro lyc Sc Wc memc mdc HARc HRODc) as HROOKc.
(* the stack from the entry stack pointer up: no byte of the footprint is on the stack *)
assert (Hstk80 : 80 <= PINS_SET_STK) by (vm_compute; congruence).
assert (HFRc : Z.of_nat (length (frames Sc)) <= 8) by (rewrite Hfrs; exact HFRM).
assert (HEVc : st_nev Sc + EV_ANSWER_CODE <= EV_MAX) by lia.
assert (HLIVEc : blocks_bytes Sc + LIVE_ANSWER_CODE code <= LIVE_MAX).
{ pose proof HLIVE as HL. unfold LIVE_PINS_SET in HL. rewrite Ecode in HL.
  unfold ps_live, ps_A in Hbb. cbn [firstn map fold_right] in Hbb. lia. }
assert (XACN : 0 <= XM_ANSWER_CODE MT code).
{ unfold XM_ANSWER_CODE, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (resp code)) + 1) ltac:(lia)). lia. }
assert (XMEQ : rec_spill_frees R * mo_free MT + ps_xm MT uri files layout verdict 4 + XM_ANSWER_CODE MT code =
  XM_PINS_SET MT R uri files layout verdict).
{ unfold XM_PINS_SET. rewrite Ecode. unfold ps_xm, ps_A. cbn [firstn map fold_right]. lia. }
assert (HMOKc : mo_ok MT Sc (XM_ANSWER_CODE MT code)).
{ apply (mok_station MT S Sc (XM_PINS_SET MT R uri files layout verdict) _ _ MTL HMOK Hmo XACN). lia. }
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS Wc regs2 memc _ PINS_SET_STK (ps_sp0 regs) (ps_FP O) ly S W mem md []
    lyc Sc mdc k ANSWER_CODE_STK
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O2))
    EV_ANSWER_CODE 0 (getr regs2 1) ch).
  - exact HJ.
  - rewrite Hsp2. lia.
  - reflexivity.
  - lia.
  - unfold ANSWER_CODE_STK, HAND_BACK_STK, ASTACK, ESTACK. lia.
  - unfold PINS_SET_STK. lia.
  - exact R3.
  - exact R4.
  - reflexivity.
  - rewrite R1. exact Hra.
  - rewrite R1. exact Hra4.
  - exact HCH.
  - intros HPREa.
    exact (TANSWER_CODE lyc Sc Wc regs2 memc mdc ch code old R2 O2 HPREa HRM HRODc HROOKc H10 Hcode
      HREP2 HOLDV HOLDB HFRc HEVc HLIVEc HMOKc).
  - (* every byte answer_code writes is one this call may write *)
    intros a Hfp. apply inFP_cons in Hfp as [Ha | Hfp].
    + assert (Hg : A_G_REC <= a < A_G_REC + REC_SIZE) by (unfold OFF_ANSWER in Ha; unfold REC_SIZE; lia).
      right; right; right; right; left.
      split; [unfold ps_FP; apply inFP_cons; left; exact Hg|].
      split; [rewrite (ts_prog B HB), ps_PG_tfib; exact (recb_grec_in a Hg)|].
      exact (cmd_prog_img a (recb_grec_in a Hg)).
    + apply inFP_ablocks_fp_inv in Hfp as (p & n & Hin & Hr).
      apply pt_in_filter in Hin as [Hin _].
      pose proof (HO2L (p, n) Hin) as HinC.
      destruct (MID3 (p, n) Hin) as [HinO | HnS].
      * right; left. split.
        -- replace a with (p + (a - p)) by lia. unfold ps_FP. apply inFP_cons; right. apply inFP_cons; right.
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
cbv beta. intros W' c' _ (fx1 & ly' & S' & regs' & mem' & md' & Hfx & -> & HJ' & _ & HPR & HK).
destruct HK as (p1 & O' & Hret & Hfresh & Hblocks & HREP' & HO' & HBB' & HMLE').
unfold ps_post. rewrite R1.
apply (apost_baseF_intro (fx := fx) SEGS fx1 _ _ _ _ _ _ _ _ _ _ _ _ ly' S');
  [exact Hfx | exact (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' Hk)
  | exact (aregs_preserved_trans _ _ _ HP2 HPR) |].
cbv beta.
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
{ unfold LIVE_PINS_SET. rewrite Ecode. unfold ps_live, ps_A in Hbb. cbn [firstn map fold_right] in Hbb. lia. }
apply (mle_weaken MT S S' _ _ MTL (mle_station MT S Sc S' _ _ MTL Hmo HMLE')). lia.
Qed.

End entry.
End e.
End f.
End d.

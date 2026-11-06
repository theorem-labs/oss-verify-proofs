(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of check_reply_answer's ASan walk (plugin-hostd/fuzz_command), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the walk's kit: regions, facts, register files, seed lemma cl_seed) over fuzz_command's listing (lib/A/Prog/CmdList.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_answer_k.v, with its module paths and module names changed; 175 of its 203 lines of code are new or changed and 401 lines of the source are left out. *)
(* sup_remove's walk on the ASan build of plugin-hostd/fuzz_command, the tail piece (sr_tail_stmt,
   lib/A/Prog/sup_remove_s1.v): at the tail jump `j answer` (0x8ac1c) sp and ra are the entry's, so answer's return
   is sup_remove's. answer's statement (tanswer_spec, lib/A/Prog/answer_c.v) is composed into sup_remove's journal by
   PaFx.v's cl_callS_wideF (PaNoChain.v's cl_callS_wide for a callee whose post is apost_baseF) at offset 0 with the
   entry frame chain; answer's footprint holds g_rec's answer and state words (program statics in sr_FP) and the old
   answer's block (one of O, live at the tail as a recorder block). The shape is the read-only literal "resp 0" at
   0x21ce0 (CmdRo.v RO_lit_21ce0).

   Statement passes 4 and 5 (FP lifts, and frame chains at a call): TANSWER holds at every FP state
   and is used at the piece's own fx, with the piece's rounding-mode-0 premise; apost_baseF_intro closes the
   piece's apost_baseF at the fx1 answer returns. answer's afn_pre chain is the entry's (s0 at the tail jump is the
   entry s0, class A), kept by the journal (achain_kept); astack_pres is gone. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaSB PaCallRun PaCall PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdAddr CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c arg_i_c answer_c sup_remove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_remove_s1 sup_remove_r.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* a literal address outside every range of a list *)
Lemma srt_nzr : forall a (l : list (Z * Z)),
existsb (fun r : Z * Z => (fst r <=? a) && (a <? fst r + snd r))%bool l = false -> ~ Exists (in_zr a) l.
Proof.
intros a l H HE. apply Exists_exists in HE as (r & Hr & [H1 H2]).
assert (E : existsb (fun r : Z * Z => (fst r <=? a) && (a <? fst r + snd r))%bool l = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite H in E. discriminate E.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a.
Hypothesis RPG : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a.
Hypothesis RRO : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a.
Hypothesis cmd_ro_in_img : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.

Lemma sr_tail : sr_tail_stmt B MT.
Proof.
(* intros straight on the statement: `unfold` would zeta-reduce the statement's lets t and R1 *)
intros ly S W regs mem md ch id R O lyt St Wt regst memt mdt kt Ot c old acc t R1
  HPRE HFRM Hfr HARO HO HJ Hsp Hra1 HP H10 H11 H12 HREP HOLD Hold64 HOLDO HCALL Hkt Hkev HEV HLIVE HMO HACC Hacc.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HARt & Hly & _ & _ & _ & Hfrt & Hnev & _ & G1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the callee-saved registers the tail state keeps *)
assert (P3 : getr regst 3 = getr regs 3) by (apply (HP 3); right; left; reflexivity).
assert (P4 : getr regst 4 = getr regs 4) by (apply (HP 4); right; right; left; reflexivity).
assert (P8 : getr regst 8 = getr regs 8) by (apply (HP 8); right; right; right; left; reflexivity).
assert (P3' : getr regst 3 = w64 (as_gp B)) by (rewrite P3; exact Hgp).
assert (P4' : getr regst 4 = w64 (as_tp B)) by (rewrite P4; exact Htp).
assert (HraT : YK0s.ret_ok (getr regst 1)) by (rewrite Hra1; exact Hra).
assert (Hra4T : 4096 <= bv_unsigned (getr regst 1)) by (rewrite Hra1; exact Hra4).
(* answer's entry *)
assert (HSIG : SIGMA CS_answer = BASE + AF_answer).
{ rewrite (SIGP CS_answer) by (cbn [In cmd_prog_syms]; repeat (first [left; reflexivity | right])). reflexivity. }
rewrite HSIG.
assert (Hsp0 : spZ regst = spZ regs + 0) by lia.
assert (HSTK0 : 0 <= ANSWER_STK) by (vm_compute; discriminate).
assert (HSTK : ANSWER_STK - 0 <= SUP_REMOVE_STK) by (unfold SUP_REMOVE_STK; lia).
(* the entry chain, kept above the entry sp *)
assert (HchT : achain lyt (rdW Wt memt) (spZ regs + 0) (s0Z regst) ch).
{ unfold s0Z at 1. rewrite P8. change (bv_unsigned (getr regs 8)) with (s0Z regs). rewrite Z.add_0_r.
  apply (achain_ly_top ly lyt). { destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET. }
  apply (achain_kept ly (rdW W mem) (rdW Wt memt) (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
  intros a Ha. apply G1; [lia | lia |].
  intros Hf. destruct (sr_FP_cases O a Hf) as [Hpg | Hb].
  - destruct Hpg as (r & Hr & Hra'). unfold cmd_PG in Hr. cbn [In] in Hr.
    unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in *.
    destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hra'; lia.
  - destruct (inFP_ablocks_fp_inv O a Hb) as (p & n & Hin & Hpa).
    destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (proj1 (Forall_forall _ _) HO _ Hin)) as (_ & _ & Hpc & _).
    lia. }
(* answer's footprint *)
set (FP1 := (A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
  ablocks_fp (filter (fun pn : Z * Z => fst pn =? old) Ot)).
assert (HOLDB : forall a, inFP (ablocks_fp (filter (fun pn : Z * Z => fst pn =? old) Ot)) a ->
  exists p n, In (p, n) Ot /\ In (p, n) O /\ p <= a < p + req_size n).
{ intros a Hb. destruct (inFP_ablocks_fp_inv _ a Hb) as (p & n & Hin & Hpa).
  apply list_elem_of_In, list_basics.list.list_elem_of_filter in Hin as [Hpo Hin]. apply list_elem_of_In in Hin.
  assert (Hpo' : p = old).
  { revert Hpo. cbn. destruct (Z.eqb_spec p old) as [E|E]; [intros _; exact E | intros []]. }
  clear Hpo. rename Hpo' into Hpo.
  exists p, n. split; [exact Hin|]. split; [exact (HOLDO (p, n) Hin Hpo) | exact Hpa]. }
assert (HFPlow : forall a, inFP FP1 a -> a < alloc_ceiling).
{ intros a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]].
  - cbn [fst snd] in Ha. unfold A_G_REC, OFF_ANSWER in Ha. lia.
  - cbn [fst snd] in Ha. unfold A_G_REC, OFF_STATE in Ha. lia.
  - destruct (HOLDB a (ex_intro _ r (conj Hr Ha))) as (p & n & _ & HinO & Hpa).
    destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (proj1 (Forall_forall _ _) HO _ HinO)) as (_ & _ & Hpc & _).
    lia. }
assert (HFP : forall a, inFP FP1 a ->
  awr_byte SEGS B SUP_REMOVE_STK (spZ regs) (sr_FP O) (ablocks B ly S) (ablocks B lyt St) (frames S) lyt [] a).
{ intros a Ha. unfold awr_byte, awr_prog_or_caller.
  destruct Ha as (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]].
  - cbn [fst snd] in Ha.
    assert (Hpg : inFP cmd_PG a) by (apply sr_inPG; unfold OFF_ANSWER, A_G_REC in *; lia).
    right. right. right. right. left.
    split; [|split; [exact (HPROG B HB a Hpg) | exact (cif_prog_img a Hpg)]].
    exists (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8).
    split; [unfold sr_FP; right; left; reflexivity | cbn [fst snd]; unfold OFF_CALLS, OFF_ANSWER in *; lia].
  - cbn [fst snd] in Ha.
    assert (Hpg : inFP cmd_PG a) by (apply sr_inPG; unfold OFF_STATE, A_G_REC in *; lia).
    right. right. right. right. left.
    split; [|split; [exact (HPROG B HB a Hpg) | exact (cif_prog_img a Hpg)]].
    exists (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8).
    split; [unfold sr_FP; right; right; left; reflexivity | cbn [fst snd]; lia].
  - destruct (HOLDB a (ex_intro _ r (conj Hr Ha))) as (p & n & HinT & HinO & Hpa).
    right. left. split.
    + exists (p, p + req_size n). split; [|cbn [fst snd]; lia].
      unfold sr_FP. right. right. right. right. unfold ablocks_fp.
      exact (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) O (p, n) HinO).
    + exists p, n. split; [|exact Hpa].
      destruct HREP as (Q & HQ & HOQ).
      exact (proj1 (proj2 (sr_lay_live _ _ _ _ _ _ HQ) (p, n) (proj1 (HOQ (p, n)) HinT))). }
(* the facts answer's statement asks at the tail state *)
assert (HAROt : arodata_okP SEGS RLO RHI B (rdW Wt memt))
  by exact (sr_aro_journal B LAWS RPG RRO SUP_REMOVE_STK (spZ regs) O
    ly S W mem md [] lyt St Wt memt mdt kt HAR HO HJ HARO).
assert (HROK : cmd_ro_ok (rdW Wt memt)) by exact (cmd_ro_ok_of_aro lyt St Wt memt mdt HARt HAROt).
assert (HLIT : abytes_atR (rdW Wt memt) 0x21ce0 RO_lit_21ce0).
{ clear - HROK. destruct HROK as [HRO _]. unfold cmd_ro_bytes in HRO.
  repeat match type of HRO with
  | abytes_atR _ 0x21ce0 _ /\ _ => exact (proj1 HRO)
  | _ /\ _ => apply proj2 in HRO
  end. }
assert (HRI : forall i, 0 <= i < 7 -> in_roP SEGS RLO RHI (0x21ce0 + i)).
{ pose proof cmd_ro_in_img as HROIN. clear - HROIN. unfold cmd_ro_in in HROIN.
  repeat match type of HROIN with
  | (forall i : Z, _ -> _ (0x21ce0 + i)) /\ _ => exact (proj1 HROIN)
  | _ /\ _ => apply proj2 in HROIN
  end. }
assert (HSTR : astr_atR (rdW Wt memt) 0x21ce0 REC_MOD_HOST_SHAPE).
{ split.
  - replace (REC_MOD_HOST_SHAPE ++ [Z_to_bv 8 0]) with RO_lit_21ce0 by (vm_compute; reflexivity). exact HLIT.
  - apply (no0_nz REC_MOD_HOST_SHAPE). vm_compute. reflexivity. }
(* the literal's end 0x21ce6 is one of CmdRo's literal ends *)
assert (HEND : In (0x21ce0 + Z.of_nat 6) cmd_ro_ends).
{ assert (E : existsb (Z.eqb (0x21ce0 + Z.of_nat 6)) cmd_ro_ends = true) by (vm_compute; reflexivity).
  apply existsb_exists in E as (e & He & Ee). apply Z.eqb_eq in Ee. rewrite Ee. exact He. }
assert (HADB : cmd_addr_b 0x21ce0 7 = true) by (vm_compute; reflexivity).
assert (HHUB : cmd_hull_b 0x21ce0 7 = true) by (vm_compute; reflexivity).
assert (HSHAPE : astr_argA B lyt St (rdW Wt memt) (in_roP SEGS RLO RHI) Ot 0x21ce0 (Some REC_MOD_HOST_SHAPE)).
{ unfold astr_argA. cbv zeta.
  assert (LX : length REC_MOD_HOST_SHAPE = 6%nat) by (vm_compute; reflexivity). rewrite LX.
  change (Z.of_nat 6 + 1) with 7.
  split; [lia|]. split; [exact HSTR|]. split; [unfold LMAX; lia|]. right.
  split; [|exact (conj HADB (conj HHUB HEND))].
  intros i Hi. split; [exact (HRI i Hi)|]. split.
  - rewrite (ts_owned B HB).
    assert (Ci : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
    repeat (destruct Ci as [Ci|Ci]; [subst i; apply srt_nzr; vm_compute; reflexivity|]).
    subst i. apply srt_nzr. vm_compute. reflexivity.
  - rewrite (ts_errno B HB). unfold TFIB_ERRNO. lia. }
assert (HFITS : fits REC_MOD_HOST_SHAPE) by (apply fits_shape_set; left; reflexivity).
assert (HXM0 : 0 <= XM_ANSWER MT t).
{ unfold XM_ANSWER, hand_back_c.XM_HAND_BACK, xstrdup_c.XM_XSTRDUP.
  pose proof (mo_free_nonneg MT MTL) as F0.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length t) + 1) ltac:(lia)) as M0. lia. }
(* c is a slot of g_rec's call table (at most 16 calls) or record.spill *)
assert (Hc64 : 0 <= c < 2 ^ 64).
{ destruct HREP as (Q & HQ & _). destruct (sr_ncalls _ _ _ _ _ _ HQ) as (_ & HN).
  destruct HCALL as [(k & Hk & ->) | (-> & _)].
  - assert (Hk' : (k < length (r_calls R1))%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
    unfold A_G_REC, OFF_CALLS, CALL_SIZE. lia.
  - unfold A_REC_SPILL. lia. }
(* the tail call: answer's statement composed into sup_remove's journal *)
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS Wt regst memt (Z_to_bv 64 (BASE + AF_answer)) SUP_REMOVE_STK (spZ regs) (sr_FP O)
    ly S W mem md [] lyt St mdt kt ANSWER_STK FP1 EV_ANSWER 0 (getr regst 1) ch _
    HJ Hsp0 eq_refl ltac:(lia) HSTK0 HSTK P3' P4' eq_refl HraT Hra4T HchT).
  - intros HPREa.
    exact (TANSWER fx lyt St Wt regst memt mdt ch c 0x21ce0 old (REC_REMOVE, [dec id]) REC_MOD_HOST_SHAPE true R1 Ot
      HPREa HFRM ltac:(rewrite Hfrt; exact Hfr) HAROt HROK H10 Hc64 H11 ltac:(lia)
      ltac:(rewrite H12; vm_compute; reflexivity) HREP HOLD Hold64 (fun _ => conj HSHAPE HFITS) (fun _ _ => HCALL)
      ltac:(lia) HLIVE (mok_station MT S St _ acc _ MTL HMO HACC HXM0 Hacc)).
  - exact HFP.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (HFPlow a Ha). lia. }
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJ1 & HP2 & HK).
rewrite Hra1.
apply (apost_baseF_intro (fx := fx) SEGS fx1 _ _ _ _ _ _ _ _ _ _ _ _ ly2 S2);
  [exact Hfx | eapply (ajournal_mono_k SEGS B); [exact HJ2 | lia] | exact (aregs_preserved_trans _ _ _ HP HP2) |].
destruct HK as (p1 & p2 & O' & K10 & K4096 & Kne & Kfr & Kbl & Krep & KO' & Kstr & Kbb & Kmle).
exists p1, p2, O'.
exact (conj K10 (conj K4096 (conj Kne (conj Kfr (conj Kbl (conj Krep (conj KO' (conj Kstr (conj Kbb
  (mle_weaken MT S S2 _ _ MTL (mle_station MT S St S2 acc _ MTL HACC Kmle) Hacc)))))))))).
Qed.
End c.
End b.
End a.

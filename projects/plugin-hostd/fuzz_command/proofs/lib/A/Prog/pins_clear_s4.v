(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the join segment and the tail jump of pins_clear's ASan walk on
   plugin-hostd/fuzz_command, after proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v and ACh2.v (the segments of the
   cgif_close walk that end in a call) over fuzz_command's listing. *)

(* From 0x8cd2c, where record()'s two arms meet, pins_clear writes the call into the slot (fn = 21, no
   arguments), picks the argument (the caller's string, or the image's "(null)" when it is NULL), copies it with
   xstrdup and stores the copy in the slot; then it reads g_rec.refuse and either answers the input's code or
   folds the call into g_rec.state with mix_call and answers SUCCESS. Either way it releases the frame and
   tail-jumps into answer_code, which `pcl_tail` composes with the rest of the call. *)

(* pins_clear (recorder.c:524-533) records the call with the inlined record(), copies its one argument with
   xstrdup, and then either answers the input's refusal code or folds the call into g_rec.state and answers
   SUCCESS; either way it releases its frame and tail-jumps into answer_code.

   The walk runs the listing in two segments (lib/A/Prog/pins_clear_s2.v): the entry segment to the test of
   g_rec.ncalls, and the join segment from the point where record()'s two arms meet to the tail jump. The steps
   the recorder's representation takes are lib/A/Prog/pins_clear_s1.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YG0q YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaNoChain PaDenot PaSB PaLibH PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas pins_clear_s1 pins_clear_s2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c mix_call_c hand_back_c answer_code_c pins_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's own hypotheses (lib/A/Prog/pins_clear_c.v), at every FP state *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis TANSWER_CODE : forall fx0 : YK11.FPState, @tanswer_code_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's per-binary hypotheses, with the statements' names, shared by every recorder walk *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
(* the record's facts about the read-only range and the heap that the statement does not carry yet, with
   the statements' names and forms, shared by every recorder walk; they become CmdRecFacts lemmas in pass 3 *)
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* the footprint of the call: g_rec, record.spill and the recorder's own blocks *)
Definition pcl_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma pcl_inFP_grec : forall O a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP (pcl_FP O) a.
Proof. intros O a Ha. exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha]. Qed.

Lemma pcl_inFP_spill : forall O a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP (pcl_FP O) a.
Proof.
intros O a Ha. exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE).
split; [right; left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

Lemma pcl_inFP_blk : forall O p n i, In (p, n) O -> 0 <= i < req_size n -> inFP (pcl_FP O) (p + i).
Proof.
intros O p n i Hin Hi. destruct (inFP_ablocks_fp O p n i Hin Hi) as (r & Hr & Hb).
exists r. split; [right; right; exact Hr | exact Hb].
Qed.

(* the blocks answer_code frees: the ones that start where the recorder's answer does *)
Lemma pcl_in_filter : forall (l : list (Z * Z)) (x : Z * Z) (old : Z),
In x (filter (fun pn => fst pn =? old) l) -> In x l /\ fst x = old.
Proof.
intros l x old. induction l as [|y l IH]; intros H; [destruct H|].
cbn in H. destruct (fst y =? old) eqn:E; cbn in H.
- destruct H as [-> | H].
  + split; [left; reflexivity | apply Z.eqb_eq; exact E].
  + destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

(* a byte of g_rec or record.spill in the footprint is a byte the walk may write *)
Lemma pcl_awr_prog : forall STK sp0 O bl0 blc fr0 lyc own a,
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
awr_byte SEGS B STK sp0 (pcl_FP O) bl0 blc fr0 lyc own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyc own a Ha.
assert (HP : Exists (in_zr a) recb_PG)
  by (destruct Ha as [Ha | Ha]; [apply recb_grec_in; exact Ha | apply recb_spill_in; exact Ha]).
right; right; right; right; left.
split; [destruct Ha as [Ha | Ha]; [apply pcl_inFP_grec; exact Ha | apply pcl_inFP_spill; exact Ha]|].
split; [rewrite (recb_ts_prog_m B HB); exact HP | exact (cmd_prog_img a HP)].
Qed.

(* two live blocks with the same start are the same block *)
Lemma pcl_same_start : forall ly S (W : world SEGS) mem md p n m,
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

(* no live block starts at 0 *)
Lemma pcl_no_zero_block : forall ly S (W : world SEGS) mem md n,
AR SEGS B ly S W mem md -> ~ In (0, n) (ablocks B ly S).
Proof.
intros ly S W mem md n HAR Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ 0 n HAR Hin) as (_ & H4096 & _). lia.
Qed.

(* what the walk knows about the blocks when it reaches a point in the body: the recorder owns O2, every other
   block of the entry is still live, and a block that is live now either was live at the entry and is none of
   the recorder's, or is one the recorder owns now *)
Definition pcl_blocks_mid (ly S lyc Sc : _) (O O2 : list (Z * Z)) : Prop :=
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O2) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
(forall pn, In pn O2 -> In pn O \/ ~ In pn (ablocks B ly S)).

(* the post of the statement (lib/A/Prog/pins_clear_c.v:99-110), over the model's argument uri *)
Definition pcl_Q (ly S : _) (O : list (Z * Z)) (R : rstate) (uri : option (list byte))
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (r : Z) (O' : list (Z * Z)),
pins_clear_m R uri = (R', r) /\
getr regs' 10 = w64 r /\ -2 ^ 31 <= r < 2 ^ 31 /\
rec_repA B ly' S' (rdW W' mem') R' O' /\
(forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
(forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
blocks_bytes S' <= blocks_bytes S + LIVE_PINS_CLEAR R uri /\
mo_le MT S S' (XM_PINS_CLEAR MT R uri).

(* --- the tail jump into answer_code ---------------------------------------------------------------------- *)

(* The body ends by restoring its frame and jumping into answer_code with the code in a0, so answer_code runs at
   this call's entry stack pointer and returns to this call's caller: the composition is cl_callS_wideF at offset
   0 with the entry ra; answer_code's FP state is the function's (apost_baseF_intro). *)
Lemma pcl_tail : forall ly S (W : world SEGS) regs mem md R O uri ch lyc Sc (Wc : world SEGS) memc mdc k
  (regs2 : bvmap 5 word) R2 O2 old code,
ajournal SEGS B PINS_CLEAR_STK (spZ regs) (pcl_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
afn_pre SEGS B PINS_CLEAR_STK ly S W regs mem md ch ->
(* rounding mode 0 at the entry (the statement's pre, which answer_code's printf asks) *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* the registers at the jump: the frame is gone, ra and the callee-saved registers are the caller's *)
spZ regs2 = spZ regs -> getr regs2 1 = getr regs 1 -> aregs_preserved regs regs2 ->
getr regs2 10 = w64 code -> -2 ^ 31 <= code < 2 ^ 31 ->
(* the recorder's state at the jump, and the answer it still holds *)
rec_repA B lyc Sc (rdW Wc memc) R2 O2 ->
aval_mem (rdW Wc memc) (A_G_REC + OFF_ANSWER) 8 old -> 0 <= old < 2 ^ 64 ->
pcl_blocks_mid ly S lyc Sc O O2 ->
(* the recorder's own block the answer lives in, if it has one: it is one of the entry's and still live *)
(forall pn, In pn O2 -> fst pn = old -> In pn O /\ In pn (ablocks B lyc Sc)) ->
(forall pn, In pn O2 -> In pn (ablocks B lyc Sc)) ->
(* a live block that starts where the answer does is one of the recorder's *)
(forall pn, In pn (ablocks B lyc Sc) -> fst pn = old -> In pn O2) ->
(* every byte of this call's footprint is below the stack *)
(forall a, inFP (pcl_FP O) a -> a < alloc_ceiling) ->
(* the model: answering the code is the step the member's model function takes *)
pins_clear_m R uri = (fst (rec_answer_code R2 code), snd (rec_answer_code R2 code)) ->
(* what answer_code needs of the state it starts in *)
arodata_okP SEGS RLO RHI B (rdW Wc memc) -> cmd_ro_ok (rdW Wc memc) ->
Z.of_nat (length (frames Sc)) <= 8 ->
st_nev Sc + EV_ANSWER_CODE <= EV_MAX -> blocks_bytes Sc + LIVE_ANSWER_CODE code <= LIVE_MAX ->
mo_ok MT Sc (XM_ANSWER_CODE MT code) ->
(* the budgets of the whole call *)
k + EV_ANSWER_CODE <= EV_PINS_CLEAR R ->
blocks_bytes Sc + LIVE_ANSWER_CODE code <= blocks_bytes S + LIVE_PINS_CLEAR R uri ->
mo_le MT S Sc (XM_PINS_CLEAR MT R uri - XM_ANSWER_CODE MT code) ->
SRr SEGS Wc (cfg_at SEGS (BASE + AF_answer_code) regs2 memc mdc)
  (apost_baseF SEGS B PINS_CLEAR_STK (pcl_FP O) regs ly S W mem md (EV_PINS_CLEAR R) (pcl_Q ly S O R uri)).
Proof.
intros ly S W regs mem md R O uri ch lyc Sc Wc memc mdc k regs2 R2 O2 old code
  HJ PRE HFRM Hsp2 R1 HP2 H10 Hcode HREP2 HOLD Hold64 HMID HANS HO2L HOLDNO HFPlo HMODEL HROD HROOK HFR HEV
  HLIVE HMOK Hk HBB HMLE.
pose proof PRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & Hk0 & KEEPhi & _ & _ & _ & _ & Hpresc & Hstkc & _ & HQTc).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HMID as (MID1 & MID2 & MID3).
(* the frame chain of the entry, carried to the jump: its words lie above the stack pointer, which no byte of
   the footprint reaches *)
assert (HCH : achain lyc (rdW Wc memc) (spZ regs + 0) (s0Z regs2) ch).
{ rewrite Z.add_0_r.
  assert (Es0 : s0Z regs2 = s0Z regs)
    by (unfold s0Z; f_equal; exact (HP2 8 ltac:(unfold acallee_saved; lia))).
  rewrite Es0. apply (achain_ly_top ly lyc); [exact Etop|].
  apply (achain_kept ly (rdW W mem) (rdW Wc memc) (spZ regs) (s0Z regs) ch (spZ regs));
    [exact Hch | lia | lia |].
  intros a Ha. apply KEEPhi; [lia | lia |]. intros Hfp. pose proof (HFPlo a Hfp). lia. }
(* the stack pointer and the saved registers at the jump *)
assert (R3 : getr regs2 3 = w64 (as_gp B))
  by (etransitivity; [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact Hgp]).
assert (R4 : getr regs2 4 = w64 (as_tp B))
  by (etransitivity; [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact Htp]).
(* ra is the caller's: the epilogue restored it from the frame *)
pose proof HREP2 as (Q2 & HA2 & HO2).
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS Wc regs2 memc _ PINS_CLEAR_STK (spZ regs) (pcl_FP O) ly S W mem md []
    lyc Sc mdc k ANSWER_CODE_STK
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O2))
    EV_ANSWER_CODE 0 (getr regs2 1) ch).
  - exact HJ.
  - rewrite Hsp2. lia.
  - reflexivity.
  - lia.
  - unfold ANSWER_CODE_STK, HAND_BACK_STK, ASTACK, ESTACK. lia.
  - unfold PINS_CLEAR_STK, ANSWER_CODE_STK. lia.
  - exact R3.
  - exact R4.
  - reflexivity.
  - rewrite R1. exact Hra.
  - rewrite R1. exact Hra4.
  - exact HCH.
  - intros HPREa. unfold cfg_at in *.
    exact (TANSWER_CODE fx lyc Sc Wc regs2 memc mdc ch code old R2 O2 HPREa HFRM HROD HROOK H10 Hcode
      HREP2 HOLD Hold64 HFR HEV HLIVE HMOK).
  - (* every byte answer_code writes is one this call may write *)
    intros a Hfp. apply inFP_cons in Hfp as [Ha | Hfp].
    + apply pcl_awr_prog. left. unfold OFF_ANSWER, REC_SIZE in *. lia.
    + apply inFP_ablocks_fp_inv in Hfp as (p & n & Hin & Hr).
      apply pcl_in_filter in Hin as [Hin Heq]. cbn [fst] in Heq.
      destruct (HANS (p, n) Hin ltac:(cbn [fst]; exact Heq)) as [HinO Hlive].
      right; left.
      split; [replace a with (p + (a - p)) by lia; exact (pcl_inFP_blk O p n (a - p) HinO ltac:(lia))|].
      exists p, n. split; [exact Hlive | lia].
  - (* no byte of answer_code's footprint is in this call's stack window *)
    intros ly2 S2 W2 regs3 mem2 md2 HK a Hfp Hw Hn. exfalso.
    apply inFP_cons in Hfp as [Ha | Hfp].
    + unfold A_G_REC, OFF_ANSWER, PINS_CLEAR_STK, ANSWER_CODE_STK in *. lia.
    + apply inFP_ablocks_fp_inv in Hfp as (p & n & Hin & Hr).
      apply pcl_in_filter in Hin as [Hin _].
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc (HO2L (p, n) Hin)) as (_ & _ & Hceil2 & _).
      cbn [fst snd] in Hceil2. unfold PINS_CLEAR_STK in *. lia. }
(* answer_code's post, at the FP state fx1 it returns, is this call's post *)
cbv beta. intros W' c' _ (fx1 & ly' & S' & regs' & mem' & md' & Hfx & -> & HJ' & _ & HPR & HK).
destruct HK as (p1 & O' & Hret & Hfresh & Hblocks & HREP' & HO' & HBB' & HMLE').
rewrite R1.
apply (apost_baseF_intro (fx := fx) SEGS fx1 _ _ _ _ _ _ _ _ _ _ _ _ ly' S');
  [exact Hfx | exact (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' Hk)
  | exact (aregs_preserved_trans _ _ _ HP2 HPR) |].
(* the model's step and the three block statements *)
set (nres := Z.of_nat (length (resp code)) + 1) in *.
exists (fst (rec_answer_code R2 code)), (snd (rec_answer_code R2 code)), O'.
split; [exact HMODEL|].
split; [exact Hret|].
split; [unfold rec_answer_code; cbn [snd]; exact Hcode|].
split; [exact HREP'|].
split.
{ intros pn Hpn. apply HO' in Hpn as [[Hpn _] | ->].
  - exact (MID3 pn Hpn).
  - destruct (in_dec recb_pair_dec (p1, nres) (ablocks B ly S)) as [Hin | Hnin]; [|right; exact Hnin].
    left. destruct (in_dec recb_pair_dec (p1, nres) O) as [HinO | HninO]; [exact HinO|].
    exfalso. pose proof (MID2 (p1, nres) Hin HninO) as Hlc.
    destruct (Z.eq_dec p1 old) as [Eo | Ne].
    + destruct (MID3 (p1, nres) (HOLDNO (p1, nres) Hlc ltac:(cbn [fst]; exact Eo))) as [H | H];
        [exact (HninO H) | exact (H Hin)].
    + exact (Hfresh (p1, nres) Hlc ltac:(cbn [fst]; exact Ne) eq_refl). }
split.
{ intros pn Hpn HnO. apply Hblocks. left. split; [exact (MID2 pn Hpn HnO)|].
  intros Hfst.
  (* a block of the entry that the recorder does not own cannot start where the answer does *)
  destruct (MID3 pn (HOLDNO pn (MID2 pn Hpn HnO) Hfst)) as [HinO | Hnin];
    [exact (HnO HinO) | exact (Hnin Hpn)]. }
split.
{ intros pn Hpn. apply Hblocks in Hpn as [[Hpn Hne] | ->].
  - destruct (MID1 pn Hpn) as [H | H]; [left; exact H|].
    right. apply HO'. left. split; [exact H | exact Hne].
  - right. apply HO'. right. reflexivity. }
split; [lia|].
replace (XM_PINS_CLEAR MT R uri)
  with ((XM_PINS_CLEAR MT R uri - XM_ANSWER_CODE MT code) + XM_ANSWER_CODE MT code) by lia.
exact (mo_le_trans MT MTL S Sc S' _ _ HMLE HMLE').
Qed.

(* --- the join segment's glue ------------------------------------------------------------------------------ *)

Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the bytes the segment's runs may write: the frame, the slot and g_rec.state *)
Definition pcj_Z (sp0 c x : Z) : Prop :=
(sp0 - 64 <= x < sp0) \/ (c <= x < c + CALL_SIZE) \/ (A_G_REC + OFF_STATE <= x < A_G_REC + OFF_STATE + 8).

(* the bytes the segment keeps: g_rec, record.spill and the bytes of the blocks bl, outside the slot and the state *)
Definition pcj_prot (bl : list (Z * Z)) (c a : Z) : Prop :=
((A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
 (exists q m, In (q, m) bl /\ q <= a < q + m)) /\
~ (c <= a < c + CALL_SIZE) /\ ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8).

Lemma pcj_prot_mono : forall bl bl' c a, (forall pn, In pn bl -> In pn bl') -> pcj_prot bl c a -> pcj_prot bl' c a.
Proof.
intros bl bl' c a Hbl ([Hpg | (q & m & Hin & Ha)] & Hns & Hnt).
- split; [left; exact Hpg | split; assumption].
- split; [right; exists q, m; split; [exact (Hbl _ Hin) | exact Ha] | split; assumption].
Qed.

(* a kept byte is outside every window of the segment's runs *)
Lemma pcj_prot_out : forall ly S (W : world SEGS) mem md sp0 c a,
AR SEGS B ly S W mem md -> alloc_ceiling + 64 <= sp0 ->
pcj_prot (ablocks B ly S) c a -> 0 <= a < 2 ^ 64 /\ ~ pcj_Z sp0 c a.
Proof.
intros ly S W mem md sp0 c a HAR Hsp ([Hpg | (q & m & Hin & Ha)] & Hns & Hnt);
  pose proof asan_consts as (C1 & _).
- assert (HP : Exists (in_zr a) recb_PG)
    by (destruct Hpg as [H | H]; [apply recb_grec_in | apply recb_spill_in]; exact H).
  pose proof (pa_img_range a (cmd_prog_img a HP)) as Hr.
  split; [lia|]. unfold pcj_Z. intros [H | [H | H]]; [lia | exact (Hns H) | exact (Hnt H)].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hq].
  split; [lia|]. unfold pcj_Z. intros [H | [H | H]]; [lia | exact (Hns H) | exact (Hnt H)].
Qed.

(* a byte of a live block is a kept byte: the slot and the state are image bytes, a block's are not *)
Lemma pcj_prot_heap : forall ly S (W : world SEGS) mem md c q m a,
AR SEGS B ly S W mem md -> pcl_slot_ok c -> In (q, m) (ablocks B ly S) -> q <= a < q + m ->
pcj_prot (ablocks B ly S) c a.
Proof.
intros ly S W mem md c q m a HAR Hc Hin Ha.
destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hin) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hq].
pose proof (blk_img SEGS B LAWS ly S W mem md q m a HAR Hin ltac:(lia)) as Hni.
split; [right; exists q, m; split; [exact Hin | exact Ha]|]. split.
- intros Hs. apply Hni. apply cmd_prog_img. exact (pcl_in_PG_slot c a Hc Hs).
- intros Hs. apply Hni. apply cmd_prog_img. apply recb_grec_in. unfold OFF_STATE, REC_SIZE in *. lia.
Qed.

(* a callee with an empty footprint keeps the program's statics *)
Lemma pcj_call_keeps_PG : forall STK1 sp1 lyc Sc (W1 : world SEGS) mem1 md1 own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 [] lyc Sc W1 mem1 md1 own ly2 S2 W2 mem2 md2 k1 ->
Exists (in_zr a) recb_PG -> rdW W2 mem2 a = rdW W1 mem1 a.
Proof.
intros STK1 sp1 lyc Sc W1 mem1 md1 own ly2 S2 W2 mem2 md2 k1 a HJ HP.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIMG & _).
destruct (recb_prog_unowned_m B HB cmd_prog_img a HP) as (Himg & Hown & Herr).
apply HIMG; [exact Himg | exact Hown | exact Herr |].
apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | apply inFP_nil].
Qed.

(* ... and every kept byte of a block that stays live *)
Lemma pcj_prot_call : forall STK1 sp1 lyc Sc (W1 : world SEGS) mem1 md1 own ly2 S2 (W2 : world SEGS) mem2 md2 k1 bl c a,
ajournal SEGS B STK1 sp1 [] lyc Sc W1 mem1 md1 own ly2 S2 W2 mem2 md2 k1 ->
(forall pn, In pn bl -> In pn (ablocks B lyc Sc) /\ In pn (ablocks B ly2 S2)) ->
pcj_prot bl c a -> rdW W2 mem2 a = rdW W1 mem1 a.
Proof.
intros STK1 sp1 lyc Sc W1 mem1 md1 own ly2 S2 W2 mem2 md2 k1 bl c a HJ Hbl ([Hpg | (q & m & Hin & Ha)] & _ & _).
- apply (pcj_call_keeps_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ).
  destruct Hpg as [H | H]; [apply recb_grec_in | apply recb_spill_in]; exact H.
- pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBLK & _).
  destruct (Hbl (q, m) Hin) as [H1 H2].
  pose proof (req_size_pos m ltac:(lia)) as [_ Hq].
  replace a with (q + (a - q)) by lia.
  exact (HBLK q m (a - q) H1 H2 ltac:(lia) (inFP_nil _)).
Qed.

Lemma pcj_region_kept : forall E (W W2 : world SEGS) m m2 nn b lo hi wlo whi cs,
bv_unsigned (ew E nn) = b ->
(forall a, b + lo <= a < b + hi -> rdW W2 m2 a = rdW W m a) ->
(forall a, b + wlo <= a < b + whi -> writable_at SEGS (mrestrict (w_H W2) m2) a) ->
region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W2) m2) (YP09.mkRegion (Some nn) lo hi wlo whi cs).
Proof.
intros E W W2 m m2 nn b lo hi wlo whi cs U Hv Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U.
- intros a Ha. apply (mbyte_of_aview SEGS). exact (Hv a Ha).
- intros a Ha _. exact (Hw a Ha).
Qed.

Lemma pcj_aval_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk (a + Z.of_nat k)) by lia. exact (H k Hkn). Qed.

Lemma pcj_aval_mod : forall rd a v, aval_mem rd a 4 v -> aval_mem rd a 4 (v mod 2 ^ 32).
Proof.
intros rd a v H k Hk. rewrite (H k Hk). f_equal. unfold YG0f.le_byte. change (8 * Z.of_nat 4) with 32.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma pcj_denot_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma pcj_soff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* a 32-bit word of g_rec, loaded with sign extension *)
Lemma pcj_sext32 : forall E n v, ew E n = Z_to_bv 64 (v mod 2 ^ 32) -> -2 ^ 31 <= v < 2 ^ 31 ->
U E (SExt true 32 (SOff n 0)) = v mod 2 ^ 64.
Proof.
intros E n v Hn Hv. rewrite U_SExt. cbv beta iota.
pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)) as Hm.
rewrite (U_atom E n (v mod 2 ^ 32) Hn ltac:(lia)).
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite Z.mod_mod by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite Zplus_mod_idemp_l. rewrite (Z.mod_small (v + 2 ^ 31)) by lia.
replace (v + 2 ^ 31 - 2 ^ 31) with v by lia.
rewrite zcanon_wrap. unfold bv_wrap. reflexivity.
Qed.

Lemma pcj_sext32_denot : forall E n v, ew E n = Z_to_bv 64 (v mod 2 ^ 32) -> -2 ^ 31 <= v < 2 ^ 31 ->
sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv. apply bv_eq. rewrite Z_to_bv_unsigned.
change (bv_unsigned (sv_denot E (SExt true 32 (SOff n 0)))) with (U E (SExt true 32 (SOff n 0))).
rewrite (pcj_sext32 E n v Hn Hv). unfold bv_wrap. reflexivity.
Qed.

Lemma pcj_mod0 : forall v, -2 ^ 63 <= v < 2 ^ 63 -> v mod 2 ^ 64 = 0 -> v = 0.
Proof.
intros v Hv H. destruct (Z_lt_le_dec v 0) as [Hn | Hn].
- rewrite <- (Z.mod_add v 1 (2 ^ 64)) in H by lia. rewrite Z.mod_small in H by lia. lia.
- rewrite Z.mod_small in H by lia. exact H.
Qed.

Lemma pcj_nodup_fst : forall (l : list (Z * Z)) x y, List.NoDup (map fst l) -> In x l -> In y l -> fst x = fst y -> x = y.
Proof.
induction l as [|z l IH]; intros x y Hnd Hx Hy E; [destruct Hx|].
cbn [map] in Hnd. inversion Hnd as [|z' l' Hni Hnd' Heq]; subst.
destruct Hx as [<- | Hx], Hy as [<- | Hy].
- reflexivity.
- exfalso. apply Hni. rewrite E. apply in_map. exact Hy.
- exfalso. apply Hni. rewrite <- E. apply in_map. exact Hx.
- exact (IH x y Hnd' Hx Hy E).
Qed.

(* a live block lies apart from a range of image bytes *)
Lemma pcj_heap_apart : forall ly S (W : world SEGS) mem md p n lo len,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < len ->
(forall a, lo <= a < lo + len -> in_img SEGS a) -> iv_apart p n lo len.
Proof.
intros ly S W mem md p n lo len HAR Hin Hlen Himg. unfold iv_apart.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
destruct (Z_le_gt_dec (p + n) lo) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (lo + len) p) as [H'|H']; [right; exact H'|]. exfalso.
pose proof (req_size_pos n ltac:(lia)) as Hq.
apply (blk_img SEGS B LAWS ly S W mem md p n (Z.max p lo) HAR Hin); [lia | apply Himg; lia].
Qed.

(* the fresh block's start is no start of a block that was live before it *)
Lemma pcj_fresh : forall lyF SF (WF : world SEGS) memF mdF blc L p n,
AR SEGS B lyF SF WF memF mdF -> In (p, n) (ablocks B lyF SF) -> 0 < n ->
Forall (fun qk => iv_apart p n (fst qk) (snd qk)) blc ->
(forall pn, In pn L -> In pn blc /\ In pn (ablocks B lyF SF)) -> ~ In p (map fst L).
Proof.
intros lyF SF WF memF mdF blc L p n HARF Hin Hn Hap HL Hm.
apply in_map_iff in Hm as ([q m] & Hq & HqL). cbn [fst] in Hq. subst q.
destruct (HL _ HqL) as [Hc HF].
rewrite (pcl_same_start lyF SF WF memF mdF p m n HARF HF Hin) in Hc.
rewrite Forall_forall in Hap. pose proof (Hap _ Hc) as H. unfold iv_apart in H. cbn [fst snd] in H. lia.
Qed.

(* the footprint: g_rec, record.spill and the recorder's blocks *)
Lemma pcj_fp_inv : forall O a, inFP (pcl_FP O) a ->
Exists (in_zr a) recb_PG \/ exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof.
intros O a Ha. unfold pcl_FP in Ha. apply inFP_cons in Ha as [Ha | Ha]; [left; apply recb_grec_in; exact Ha|].
apply inFP_cons in Ha as [Ha | Ha]; [left; apply recb_spill_in; exact Ha|].
right. exact (inFP_ablocks_fp_inv O a Ha).
Qed.

Lemma pcj_fp_ro : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> forall a, in_roP SEGS RLO RHI a -> ~ inFP (pcl_FP O) a.
Proof.
intros ly S W mem md O HAR HO a Hro Hfp. destruct (cmd_ro_prog_apart a Hro) as [Himg HnPG].
destruct (pcj_fp_inv O a Hfp) as [HP | (p & n & Hin & Ha)]; [exact (HnPG HP)|].
exact (blk_img SEGS B LAWS ly S W mem md p n a HAR (HO _ Hin) Ha Himg).
Qed.

Lemma pcj_fp_low : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> forall a, inFP (pcl_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O HAR HO a Hfp. pose proof asan_consts as (C1 & _).
destruct (pcj_fp_inv O a Hfp) as [HP | (p & n & Hin & Ha)].
- pose proof (pa_img_range a (cmd_prog_img a HP)). lia.
- destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hin)) as (_ & _ & Hc & _). lia.
Qed.

(* --- the recorder's model and representation at the jump ------------------------------------------------ *)

Lemma pcj_rr_fields : forall R fn A,
r_refuse (rec_record R fn A) = r_refuse R /\ r_code (rec_record R fn A) = r_code R /\
r_state (rec_record R fn A) = r_state R.
Proof.
intros R fn A. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); destruct R; cbn; repeat split.
Qed.

Lemma pcj_rr_set_state : forall R h fn A, rec_record (set_state R h) fn A = set_state (rec_record R fn A) h.
Proof.
intros R h fn A. unfold rec_record. change (r_calls (set_state R h)) with (r_calls R).
destruct (Nat.ltb (length (r_calls R)) 16); destruct R; reflexivity.
Qed.

Lemma pcj_set_state_id : forall R, set_state R (r_state R) = R.
Proof. intros R. destruct R. reflexivity. Qed.

(* the table arm's representation at the jump, with g_rec.state holding h *)
Lemma pcj_rep_table : forall bl bl' rd rd' R Q c p s h,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(length (r_calls R) < 16)%nat ->
c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE ->
   ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (c <= a < c + CALL_SIZE) ->
   ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rd' a = rd a) ->
rd_agree rd rd' A_REC_SPILL SC_SIZE ->
(forall pn, In pn (lay_blocks Q) -> In pn bl' /\ rd_agree rd rd' (fst pn) (snd pn)) ->
aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
aval_mem rd' (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
pcl_new_call bl' rd' c p s ->
iv_apart p (Z.of_nat (length s) + 1) A_G_REC REC_SIZE ->
iv_apart p (Z.of_nat (length s) + 1) A_REC_SPILL SC_SIZE ->
~ In p (map fst (lay_blocks Q)) ->
arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record (set_state R h) REC_PINS_CLEAR [s])
  (RLay (l_calls Q ++ [[(p, Z.of_nat (length s) + 1)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
Proof.
intros bl bl' rd rd' R Q c p s h HA Hlt Hc HKEEP HSP HBL HNC HST Hh HNEW Hap1 Hap2 Hnew.
pose proof HA as (_ & _ & _ & _ & _ & _ & _ & HOWN).
set (rdm := fun a => if (A_G_REC + OFF_STATE <=? a) && (a <? A_G_REC + OFF_STATE + 8) then rd' a else rd a).
assert (Erdm : forall a, ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rdm a = rd a).
{ intros a Ha. unfold rdm. destruct ((A_G_REC + OFF_STATE <=? a) && (a <? A_G_REC + OFF_STATE + 8)) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia. }
assert (Erdm' : forall a, A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8 -> rdm a = rd' a).
{ intros a Ha. unfold rdm. replace ((A_G_REC + OFF_STATE <=? a) && (a <? A_G_REC + OFF_STATE + 8)) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
assert (HAm : arep_at bl rdm A_G_REC A_REC_SPILL (set_state R h) Q).
{ apply (pcl_arep_state bl rd rdm R Q h HA Erdm); [|exact Hh].
  intros k Hk. rewrite Erdm' by (cbn [Z.of_nat] in *; lia). exact (HST k Hk). }
apply (pcl_arep_slot bl bl' rdm rd' (set_state R h) Q c p s HAm).
- exact Hlt.
- exact Hc.
- intros a Ha Hn Hs.
  destruct (Z_lt_le_dec a (A_G_REC + OFF_STATE)) as [H1 | H1];
    [rewrite Erdm by lia; apply HKEEP; [exact Ha | exact Hn | exact Hs | lia]|].
  destruct (Z_lt_le_dec a (A_G_REC + OFF_STATE + 8)) as [H2 | H2];
    [rewrite Erdm' by lia; reflexivity | rewrite Erdm by lia; apply HKEEP; [exact Ha | exact Hn | exact Hs | lia]].
- intros i Hi. rewrite (Erdm (A_REC_SPILL + i)) by (unfold A_REC_SPILL, A_G_REC, OFF_STATE, SC_SIZE in *; lia).
  exact (HSP i Hi).
- intros pn Hpn. destruct (HBL pn Hpn) as [Hin Hag]. split; [exact Hin|].
  destruct (proj2 HOWN pn Hpn) as [Hiv _]. unfold iv_apart in Hiv.
  intros i Hi. rewrite Erdm by (unfold OFF_STATE, REC_SIZE in *; lia). exact (Hag i Hi).
- exact HNC.
- exact HNEW.
- exact Hap1.
- exact Hap2.
- exact Hnew.
Qed.

(* the spill arm's representation at the jump, with g_rec.state holding h *)
Lemma pcj_rep_spill : forall bl bl' rd rd' R Q p s h,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
length (r_calls R) = 16%nat ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE ->
   ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rd' a = rd a) ->
(forall pn, In pn (lay_nospill Q) -> In pn bl' /\ rd_agree rd rd' (fst pn) (snd pn)) ->
aval_mem rd' (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
pcl_new_call bl' rd' A_REC_SPILL p s ->
iv_apart p (Z.of_nat (length s) + 1) A_G_REC REC_SIZE ->
iv_apart p (Z.of_nat (length s) + 1) A_REC_SPILL SC_SIZE ->
~ In p (map fst (lay_nospill Q)) ->
arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record (set_state R h) REC_PINS_CLEAR [s])
  (RLay (l_calls Q) [(p, Z.of_nat (length s) + 1)] (l_answer Q) (l_reply Q)).
Proof.
intros bl bl' rd rd' R Q p s h HA H16 HKEEP HBL HST Hh HNEW Hap1 Hap2 Hnew.
pose proof HA as (_ & _ & _ & _ & _ & _ & _ & HOWN).
set (rdm := fun a => if (A_G_REC + OFF_STATE <=? a) && (a <? A_G_REC + OFF_STATE + 8) then rd' a else rd a).
assert (Erdm : forall a, ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rdm a = rd a).
{ intros a Ha. unfold rdm. destruct ((A_G_REC + OFF_STATE <=? a) && (a <? A_G_REC + OFF_STATE + 8)) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia. }
assert (Erdm' : forall a, A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8 -> rdm a = rd' a).
{ intros a Ha. unfold rdm. replace ((A_G_REC + OFF_STATE <=? a) && (a <? A_G_REC + OFF_STATE + 8)) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
assert (HAm : arep_at bl rdm A_G_REC A_REC_SPILL (set_state R h) Q).
{ apply (pcl_arep_state bl rd rdm R Q h HA Erdm); [|exact Hh].
  intros k Hk. rewrite Erdm' by (cbn [Z.of_nat] in *; lia). exact (HST k Hk). }
apply (pcl_arep_spill bl bl' rdm rd' (set_state R h) Q p s HAm).
- exact H16.
- intros a Ha.
  destruct (Z_lt_le_dec a (A_G_REC + OFF_STATE)) as [H1 | H1];
    [rewrite Erdm by lia; apply HKEEP; [exact Ha | lia]|].
  destruct (Z_lt_le_dec a (A_G_REC + OFF_STATE + 8)) as [H2 | H2];
    [rewrite Erdm' by lia; reflexivity | rewrite Erdm by lia; apply HKEEP; [exact Ha | lia]].
- intros pn Hpn. destruct (HBL pn Hpn) as [Hin Hag]. split; [exact Hin|].
  destruct (proj2 HOWN pn (In_lay_nospill Q pn Hpn)) as [Hiv _]. unfold iv_apart in Hiv.
  intros i Hi. rewrite Erdm by (unfold OFF_STATE, REC_SIZE in *; lia). exact (Hag i Hi).
- exact HNEW.
- exact Hap1.
- exact Hap2.
- exact Hnew.
Qed.

Lemma pcj_nospill_live : forall bl blc rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
Permutation bl (blc ++ l_spill Q) -> forall pn, In pn (lay_nospill Q) -> In pn blc.
Proof.
intros bl blc rd R Q HA HP pn Hpn.
pose proof (lay_blocks_in _ _ _ _ _ _ HA pn (In_lay_nospill Q pn Hpn)) as Hin.
apply (Permutation_in _ HP) in Hin. apply in_app_or in Hin as [H | H]; [exact H|]. exfalso.
pose proof HA as (_ & _ & _ & _ & _ & _ & _ & HND & _).
pose proof (nodup_fst_perm _ _ (lay_blocks_perm_nospill Q) HND) as H2.
rewrite map_app in H2. apply NoDup_ListNoDup in H2.
exact (list_nodup_app_disj _ _ (fst pn) H2 (in_map fst _ _ H) (in_map fst _ _ Hpn)).
Qed.

Lemma pcj_answer_ptr : forall bl rd t q, aanswer_at bl rd A_G_REC t q ->
aval_mem rd (A_G_REC + OFF_ANSWER) 8 (oaddr q) /\ (forall pn, q = Some pn -> In pn bl).
Proof.
intros bl rd t q H. unfold aanswer_at in H. destruct t, q; try contradiction.
- destruct H as (V & _ & Hin & _). split; [exact V|]. intros pn' Hq. injection Hq as <-. exact Hin.
- split; [exact H | intros pn' Hq; discriminate].
Qed.

(* the recorder's blocks at the jump, and the answer block among them *)
Lemma pcj_O2_facts : forall lyF SF (WF : world SEGS) memF mdF rdF R2 Q2 O Q,
AR SEGS B lyF SF WF memF mdF ->
arep_at (ablocks B lyF SF) rdF A_G_REC A_REC_SPILL R2 Q2 ->
l_answer Q2 = l_answer Q -> (forall pn, In pn (lay_blocks Q) -> In pn O) ->
(forall pn, In pn (lay_blocks Q2) -> fst pn = oaddr (l_answer Q) -> In pn O /\ In pn (ablocks B lyF SF)) /\
(forall pn, In pn (lay_blocks Q2) -> In pn (ablocks B lyF SF)) /\
(forall pn, In pn (ablocks B lyF SF) -> fst pn = oaddr (l_answer Q) -> In pn (lay_blocks Q2)).
Proof.
intros lyF SF WF memF mdF rdF R2 Q2 O Q HARF HA2 EA HQO.
pose proof (lay_blocks_in _ _ _ _ _ _ HA2) as HIN.
pose proof HA2 as (_ & _ & _ & _ & _ & _ & _ & HND & _).
apply NoDup_ListNoDup in HND.
assert (Hlive : forall pn, In pn (ablocks B lyF SF) -> 4096 <= fst pn).
{ intros [q m] Hin. destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARF Hin) as (_ & H4096 & _). exact H4096. }
destruct (l_answer Q) as [pa|] eqn:EQ; cbn [oaddr].
- assert (Hpa2 : In pa (lay_blocks Q2)) by exact (In_lay_answer Q2 pa EA).
  assert (HpaO : In pa O) by exact (HQO pa (In_lay_answer Q pa EQ)).
  split; [|split; [exact HIN|]].
  + intros pn Hpn Hf. assert (E : pn = pa) by exact (pcj_nodup_fst _ pn pa HND Hpn Hpa2 Hf). subst pn.
    split; [exact HpaO | exact (HIN pa Hpa2)].
  + intros [q m] Hin Hf. destruct pa as [pq pm]. cbn [fst] in Hf. subst q.
    rewrite (pcl_same_start lyF SF WF memF mdF pq m pm HARF Hin (HIN _ Hpa2)). exact Hpa2.
- split; [|split; [exact HIN|]].
  + intros pn Hpn Hf. pose proof (Hlive pn (HIN pn Hpn)). lia.
  + intros pn Hin Hf. pose proof (Hlive pn Hin). lia.
Qed.

Lemma pcj_mid_table : forall ly S lyF SF O Q p n,
(forall pn, In pn O <-> In pn (lay_blocks Q)) ->
Permutation (ablocks B lyF SF) ((p, n) :: ablocks B ly S) ->
Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B ly S) -> 0 < n ->
pcl_blocks_mid ly S lyF SF O (lay_blocks (RLay (l_calls Q ++ [[(p, n)]]) (l_spill Q) (l_answer Q) (l_reply Q))).
Proof.
intros ly S lyF SF O Q p n HOQ HP Hap Hn.
pose proof (pcl_lay_perm (l_calls Q) (l_spill Q) (l_answer Q) (l_reply Q) (p, n)) as PERM.
assert (EQ : RLay (l_calls Q) (l_spill Q) (l_answer Q) (l_reply Q) = Q) by (destruct Q; reflexivity).
rewrite EQ in PERM.
assert (HO2 : forall pn, In pn (lay_blocks (RLay (l_calls Q ++ [[(p, n)]]) (l_spill Q) (l_answer Q) (l_reply Q))) <->
  In pn O \/ pn = (p, n)).
{ intros pn. split.
  - intros H. apply (Permutation_in _ PERM) in H. apply in_app_or in H as [H | [H | []]];
    [left; apply HOQ; exact H | right; symmetry; exact H].
  - intros [H | ->]; apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app;
    [left; apply HOQ; exact H | right; left; reflexivity]. }
assert (Hfresh : ~ In (p, n) (ablocks B ly S)).
{ intros Hin. rewrite Forall_forall in Hap. pose proof (Hap _ Hin) as H. unfold iv_apart in H. cbn [fst snd] in H. lia. }
split; [|split].
- intros pn Hpn. apply (Permutation_in _ HP) in Hpn. destruct Hpn as [<- | Hpn].
  + right. apply HO2. right. reflexivity.
  + destruct (in_dec recb_pair_dec pn O) as [HinO | HnO].
    * right. apply HO2. left. exact HinO.
    * left. split; assumption.
- intros pn Hpn _. apply (Permutation_in _ (Permutation_sym HP)). right. exact Hpn.
- intros pn Hpn. apply HO2 in Hpn as [H | ->]; [left; exact H | right; exact Hfresh].
Qed.

Lemma pcj_mid_spill : forall ly S lyc Sc lyF SF O Q p n,
(forall pn, In pn O <-> In pn (lay_blocks Q)) ->
List.NoDup (ablocks B ly S) ->
Permutation (ablocks B ly S) (ablocks B lyc Sc ++ l_spill Q) ->
Permutation (ablocks B lyF SF) ((p, n) :: ablocks B lyc Sc) ->
Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B lyc Sc) -> 0 < n ->
pcl_blocks_mid ly S lyF SF O (lay_blocks (RLay (l_calls Q) [(p, n)] (l_answer Q) (l_reply Q))).
Proof.
intros ly S lyc Sc lyF SF O Q p n HOQ HND HPS HP Hap Hn.
pose proof (pcl_lay_perm_spill (l_calls Q) (l_answer Q) (l_reply Q) (p, n)) as PERM.
assert (ENS : lay_nospill (RLay (l_calls Q) [(p, n)] (l_answer Q) (l_reply Q)) = lay_nospill Q) by reflexivity.
rewrite ENS in PERM.
pose proof (lay_blocks_perm_nospill Q) as PQ.
assert (HO2 : forall pn, In pn (lay_blocks (RLay (l_calls Q) [(p, n)] (l_answer Q) (l_reply Q))) <->
  In pn (lay_nospill Q) \/ pn = (p, n)).
{ intros pn. split.
  - intros H. apply (Permutation_in _ PERM) in H. destruct H as [<- | H]; [right; reflexivity | left; exact H].
  - intros [H | ->]; apply (Permutation_in _ (Permutation_sym PERM)); [right; exact H | left; reflexivity]. }
assert (HOsp : forall pn, In pn O -> In pn (l_spill Q) \/ In pn (lay_nospill Q)).
{ intros pn H. apply HOQ in H. apply (Permutation_in _ PQ) in H. apply in_app_or in H. exact H. }
assert (HspO : forall pn, In pn (l_spill Q) -> In pn O) by (intros pn H; apply HOQ; exact (In_lay_spill Q pn H)).
assert (HnsO : forall pn, In pn (lay_nospill Q) -> In pn O) by (intros pn H; apply HOQ; exact (In_lay_nospill Q pn H)).
assert (Hfresh : ~ In (p, n) (ablocks B lyc Sc)).
{ intros Hin. rewrite Forall_forall in Hap. pose proof (Hap _ Hin) as H. unfold iv_apart in H. cbn [fst snd] in H. lia. }
pose proof (Permutation_NoDup HPS HND) as HND'.
split; [|split].
- intros pn Hpn. apply (Permutation_in _ HP) in Hpn. destruct Hpn as [<- | Hpn].
  + right. apply HO2. right. reflexivity.
  + assert (HpS : In pn (ablocks B ly S))
      by (apply (Permutation_in _ (Permutation_sym HPS)); apply in_or_app; left; exact Hpn).
    destruct (in_dec recb_pair_dec pn O) as [HinO | HnO].
    * destruct (HOsp pn HinO) as [Hsp | Hns].
      -- exfalso. exact (list_nodup_app_disj _ _ pn HND' Hpn Hsp).
      -- right. apply HO2. left. exact Hns.
    * left. split; assumption.
- intros pn Hpn HnO. apply (Permutation_in _ (Permutation_sym HP)). right.
  apply (Permutation_in _ HPS) in Hpn. apply in_app_or in Hpn as [H | H]; [exact H | exfalso; exact (HnO (HspO pn H))].
- intros pn Hpn. apply HO2 in Hpn as [H | ->]; [left; exact (HnsO pn H)|].
  destruct (in_dec recb_pair_dec (p, n) (ablocks B ly S)) as [Hin | Hnin]; [|right; exact Hnin].
  left. apply (Permutation_in _ HPS) in Hin.
  apply in_app_or in Hin as [H | H]; [exfalso; exact (Hfresh H) | exact (HspO _ H)].
Qed.

(* the windows of the segment's runs are the frame, the slot and the state *)
Ltac pcj_win Usp UC UGR :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in let Hq := fresh "Hq" in
  intros b wlo whi x Hin Hx; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp, ?UC, ?UGR in Hx;
     unfold pcj_Z, CALL_SIZE, OFF_STATE;
     first [left; lia | right; left; lia | right; right; lia] |]);
  destruct Hin.

(* every byte the segment's runs write is a byte the call may write *)
Ltac pcj_awr Usp UC UGR HSLOT :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
  eapply awr_ok_cons_stack_off; [reflexivity | exact Usp | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |];
  eapply awr_ok_cons_gen;
  [ reflexivity | exact UC
  | let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply pcl_awr_prog; apply HSLOT; unfold CALL_SIZE; lia |];
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  eapply awr_ok_cons_gen;
  [ reflexivity | exact UGR
  | let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply pcl_awr_prog; left; unfold OFF_STATE, REC_SIZE; lia
  | apply awr_ok_nil ].

(* a register of a symbolic state, as the state's own value *)
Ltac pcj_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

(* a region of a symbolic state *)
Ltac pcj_region HS i HR :=
lazymatch type of HS with
| st_ok _ ?E ?ssx (restrict ?H ?msx) =>
  let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth (segs := SEGS) E ssx (restrict H msx) i r HS
    ltac:(vm_compute; reflexivity)) as HR;
  cbn [ms_mem restrict mkst] in HR
end.

(* the registers at the jump: the epilogue restored ra and s0 .. s5 from the frame and released it; gp, tp and
   s6 .. s11 were never written *)
Lemma pcj_regs_end : forall (regs regsF : bvmap 5 word),
getr regsF 1 = Z_to_bv 64 (bv_unsigned (getr regs 1)) ->
getr regsF 2 = Z_to_bv 64 (spZ regs) ->
getr regsF 3 = getr regs 3 -> getr regsF 4 = getr regs 4 ->
getr regsF 8 = Z_to_bv 64 (bv_unsigned (getr regs 8)) ->
getr regsF 9 = Z_to_bv 64 (bv_unsigned (getr regs 9)) ->
getr regsF 18 = Z_to_bv 64 (bv_unsigned (getr regs 18)) ->
getr regsF 19 = Z_to_bv 64 (bv_unsigned (getr regs 19)) ->
getr regsF 20 = Z_to_bv 64 (bv_unsigned (getr regs 20)) ->
getr regsF 21 = Z_to_bv 64 (bv_unsigned (getr regs 21)) ->
(forall r, 22 <= r <= 27 -> getr regsF (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
spZ regsF = spZ regs /\ getr regsF 1 = getr regs 1 /\ aregs_preserved regs regsF.
Proof.
intros regs regsF F1 F2 F3 F4 F8 F9 F18 F19 F20 F21 F22.
rewrite Z_to_bv_bv_unsigned in F1, F8, F9, F18, F19, F20, F21.
assert (F2' : getr regsF 2 = getr regs 2) by (rewrite F2; unfold spZ; apply Z_to_bv_bv_unsigned).
assert (L : forall (b : bv 5), getr regsF b = getr regs b ->
  getr regsF (Z_to_bv 5 (bv_unsigned b)) = getr regs (Z_to_bv 5 (bv_unsigned b)))
  by (intros b H; rewrite Z_to_bv_bv_unsigned; exact H).
split; [unfold spZ; rewrite F2'; reflexivity|]. split; [exact F1|].
intros r Hr. unfold acallee_saved in Hr.
destruct (Z_le_gt_dec 22 r) as [H22 | H22]; [apply F22; lia|].
assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21) by lia.
destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
- exact (L (2%bv : bv 5) F2').
- exact (L (3%bv : bv 5) F3).
- exact (L (4%bv : bv 5) F4).
- exact (L (8%bv : bv 5) F8).
- exact (L (9%bv : bv 5) F9).
- exact (L (18%bv : bv 5) F18).
- exact (L (19%bv : bv 5) F19).
- exact (L (20%bv : bv 5) F20).
- exact (L (21%bv : bv 5) F21).
Qed.

(* The tail jump, from what the two arms leave at it: the recorder's representation at the jump (the table or
   the spill slot holds the new call, g_rec.state holds h), the blocks, the model's step, and the budgets. *)
Lemma pcj_finish : forall ly S (W : world SEGS) regs mem md ch R O Q u lyc Sc (Wc : world SEGS) memc mdc c
  lyF SF (WF : world SEGS) memF mdF (regsF : bvmap 5 word) kF p h code,
afn_pre SEGS B PINS_CLEAR_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn O <-> In pn (lay_blocks Q)) ->
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_PINS_CLEAR R <= EV_MAX -> blocks_bytes S + LIVE_PINS_CLEAR R (Some u) <= LIVE_MAX ->
mo_ok MT S (XM_PINS_CLEAR MT R (Some u)) ->
Z.of_nat (length u) + 1 <= LMAX + 1 ->
(* the join *)
AR SEGS B lyc Sc Wc memc mdc ->
pcl_at_join B ly S W mem R (l_spill Q) lyc Sc Wc memc c (rec_spill_frees R) ->
pcl_slot_ok c ->
mo_le MT S Sc (rec_spill_frees R * mo_free MT) -> blocks_bytes Sc <= blocks_bytes S ->
(* the jump *)
ajournal SEGS B PINS_CLEAR_STK (spZ regs) (pcl_FP O) ly S W mem md [] lyF SF WF memF mdF kF ->
kF = rec_spill_frees R + EV_XSTRDUP ->
(forall a, pcj_prot (ablocks B lyc Sc) c a -> rdW WF memF a = rdW Wc memc a) ->
Permutation (ablocks B lyF SF) ((p, Z.of_nat (length u) + 1) :: ablocks B lyc Sc) ->
Forall (fun qk => iv_apart p (Z.of_nat (length u) + 1) (fst qk) (snd qk)) (ablocks B lyc Sc) ->
4096 <= p ->
aval_mem (rdW WF memF) (c + CALL_OFF_FN) 4 REC_PINS_CLEAR ->
aval_mem (rdW WF memF) (c + CALL_OFF_NARGS) 4 1 ->
aval_mem (rdW WF memF) (c + CALL_OFF_ARGS) 8 p ->
astr_atR (rdW WF memF) p u ->
aval_mem (rdW WF memF) (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
mo_le MT Sc SF (XM_XSTRDUP MT u) -> blocks_bytes SF <= blocks_bytes Sc + LIVE_XSTRDUP u ->
spZ regsF = spZ regs -> getr regsF 1 = getr regs 1 -> aregs_preserved regs regsF -> getr regsF 10 = w64 code ->
(r_refuse R = 0 /\ h = mixcall (r_state R) REC_PINS_CLEAR [u] /\ code = 0) \/
(r_refuse R <> 0 /\ h = r_state R /\ code = r_code R) ->
SRr SEGS WF (cfg_at SEGS (BASE + AF_answer_code) regsF memF mdF)
  (apost_baseF SEGS B PINS_CLEAR_STK (pcl_FP O) regs ly S W mem md (EV_PINS_CLEAR R) (pcl_Q ly S O R (Some u))).
Proof.
intros ly S W regs mem md ch R O Q u lyc Sc Wc memc mdc c lyF SF WF memF mdF regsF kF p h code
  PRE HFRM HROD HA HOQ HFRS HEV HLIVE HMOK HLEN HARc HAJ Hcs HMLE HBB
  HJF HkF KEEPF HPm HFap Hp4096 HFN HNA HARG Hpx HST Hh MLEF HBBF Hsp2 R1 HP2 H10 HMOD.
pose proof PRE as (HAR & _).
pose proof asan_consts as (C1 & _).
pose proof (proj1 HJF) as HARF.
pose proof HJF as (_ & _ & _ & _ & _ & HFRF & HnevF & _).
pose proof HA as (_ & _ & _ & _ & _ & _ & HSCAL & _).
pose proof HSCAL as (_ & _ & _ & _ & _ & Rrf & Rcd & _ & Rst & _).
assert (HOlive : forall pn, In pn O -> In pn (ablocks B ly S))
  by (intros pn H; apply (lay_blocks_in _ _ _ _ _ _ HA); apply HOQ; exact H).
pose proof (pcj_fp_ro ly S W mem md O HAR HOlive) as HFPRO.
pose proof (pcj_fp_low ly S W mem md O HAR HOlive) as HFPLO.
assert (HRODF : arodata_okP SEGS RLO RHI B (rdW WF memF))
  by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ ly S W mem md [] lyF SF WF memF mdF _
    HJF HFPRO HROD).
assert (HpF : In (p, Z.of_nat (length u) + 1) (ablocks B lyF SF))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPm | left; reflexivity]).
assert (HcF : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B lyF SF))
  by (intros pn H; eapply Permutation_in; [apply Permutation_sym; exact HPm | right; exact H]).
assert (HL0 : 0 < Z.of_nat (length u) + 1) by lia.
assert (HNEW : pcl_new_call (ablocks B lyF SF) (rdW WF memF) c p u).
{ split; [exact HFN|]. split; [exact HNA|]. split; [exact HARG|]. split; [exact Hpx|].
  split; [lia|]. split; [exact HpF|]. unfold LMAX in *. lia. }
assert (Hap1 : iv_apart p (Z.of_nat (length u) + 1) A_G_REC REC_SIZE).
{ apply (pcj_heap_apart lyF SF WF memF mdF p _ A_G_REC REC_SIZE HARF HpF); [unfold REC_SIZE; lia|].
  intros a Ha. apply cmd_prog_img. apply recb_grec_in. exact Ha. }
assert (Hap2 : iv_apart p (Z.of_nat (length u) + 1) A_REC_SPILL SC_SIZE).
{ apply (pcj_heap_apart lyF SF WF memF mdF p _ A_REC_SPILL SC_SIZE HARF HpF); [unfold SC_SIZE; lia|].
  intros a Ha. apply cmd_prog_img. apply recb_spill_in. exact Ha. }
(* the model's step *)
destruct (pcj_rr_fields R REC_PINS_CLEAR [u]) as (Fr & Fc & Fs).
set (R2 := rec_record (set_state R h) REC_PINS_CLEAR [u]).
assert (HMODEL : pins_clear_m R (Some u) = (fst (rec_answer_code R2 code), snd (rec_answer_code R2 code))).
{ rewrite <- surjective_pairing. unfold pins_clear_m, rec_stub_code. cbn [sarg]. rewrite Fr. unfold R2.
  destruct HMOD as [(HR0 & -> & ->) | (HR0 & -> & ->)].
  - rewrite HR0. cbn [Z.eqb]. rewrite pcj_rr_set_state. unfold rec_mix. cbn [fst snd]. rewrite Fs. reflexivity.
  - replace (r_refuse R =? 0) with false by (symmetry; apply Z.eqb_neq; exact HR0).
    rewrite pcj_set_state_id, Fc. reflexivity. }
assert (Hsnd : snd (pins_clear_m R (Some u)) = code) by (rewrite HMODEL; reflexivity).
assert (Hcode : -2 ^ 31 <= code < 2 ^ 31) by (destruct HMOD as [(_ & _ & ->) | (_ & _ & ->)]; lia).
(* the representation at the jump and the blocks *)
assert (HJA : exists Q2, arep_at (ablocks B lyF SF) (rdW WF memF) A_G_REC A_REC_SPILL R2 Q2 /\
  l_answer Q2 = l_answer Q /\ pcl_blocks_mid ly S lyF SF O (lay_blocks Q2)).
{ destruct HAJ as [(Hlt & Ec & _ & EB & HNC & KG & KS & KH) | (H16 & Ec & _ & PB & _ & KG & KS & KH)].
  - exists (RLay (l_calls Q ++ [[(p, Z.of_nat (length u) + 1)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
    split; [|split; [reflexivity|]].
    + apply (pcj_rep_table (ablocks B ly S) (ablocks B lyF SF) (rdW W mem) (rdW WF memF) R Q c p u h HA Hlt Ec).
      * intros a Ha Hn Hs Ht. rewrite (KEEPF a (conj (or_introl (or_introl Ha)) (conj Hs Ht))). exact (KG a Ha Hn).
      * intros i Hi.
        assert (Hsp : A_REC_SPILL <= A_REC_SPILL + i < A_REC_SPILL + SC_SIZE) by lia.
        assert (Hns : ~ (c <= A_REC_SPILL + i < c + CALL_SIZE))
          by (rewrite Ec; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, SC_SIZE in *; lia).
        assert (Hnt : ~ (A_G_REC + OFF_STATE <= A_REC_SPILL + i < A_G_REC + OFF_STATE + 8))
          by (unfold A_G_REC, A_REC_SPILL, OFF_STATE in *; lia).
        rewrite (KEEPF (A_REC_SPILL + i) (conj (or_introl (or_intror Hsp)) (conj Hns Hnt))).
        exact (KS (A_REC_SPILL + i) Hsp).
      * intros pn Hpn. pose proof (lay_blocks_in _ _ _ _ _ _ HA pn Hpn) as HinS. rewrite <- EB in HinS.
        split; [exact (HcF _ HinS)|]. destruct pn as [q m]. cbn [fst snd]. intros i Hi.
        rewrite (KEEPF (q + i) (pcj_prot_heap lyc Sc Wc memc mdc c q m (q + i) HARc Hcs HinS ltac:(lia))).
        exact (KH q m i HinS Hi).
      * apply (pcj_aval_kept (rdW Wc memc)); [exact HNC|]. intros x Hx. cbn [Z.of_nat] in Hx. apply KEEPF.
        split; [left; left; unfold OFF_NCALLS, REC_SIZE in *; lia|].
        split; [rewrite Ec; unfold OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia | unfold OFF_NCALLS, OFF_STATE in *; lia].
      * exact HST.
      * exact Hh.
      * exact HNEW.
      * exact Hap1.
      * exact Hap2.
      * apply (pcj_fresh lyF SF WF memF mdF (ablocks B lyc Sc) (lay_blocks Q) p _ HARF HpF HL0 HFap).
        intros pn Hpn. pose proof (lay_blocks_in _ _ _ _ _ _ HA pn Hpn) as HinS. rewrite <- EB in HinS.
        split; [exact HinS | exact (HcF _ HinS)].
    + apply (pcj_mid_table ly S lyF SF O Q p _ HOQ); [rewrite <- EB; exact HPm | rewrite <- EB; exact HFap | exact HL0].
  - exists (RLay (l_calls Q) [(p, Z.of_nat (length u) + 1)] (l_answer Q) (l_reply Q)).
    split; [|split; [reflexivity|]].
    + rewrite Ec in HNEW.
      apply (pcj_rep_spill (ablocks B ly S) (ablocks B lyF SF) (rdW W mem) (rdW WF memF) R Q p u h HA H16).
      * intros a Ha Ht.
        assert (Hns : ~ (c <= a < c + CALL_SIZE)) by (rewrite Ec; unfold A_G_REC, A_REC_SPILL, REC_SIZE in *; lia).
        rewrite (KEEPF a (conj (or_introl (or_introl Ha)) (conj Hns Ht))). exact (KG a Ha).
      * intros pn Hpn. pose proof (pcj_nospill_live _ _ _ _ _ HA PB pn Hpn) as Hinc.
        split; [exact (HcF _ Hinc)|]. destruct pn as [q m]. cbn [fst snd]. intros i Hi.
        rewrite (KEEPF (q + i) (pcj_prot_heap lyc Sc Wc memc mdc c q m (q + i) HARc Hcs Hinc ltac:(lia))).
        exact (KH q m i Hinc Hi).
      * exact HST.
      * exact Hh.
      * exact HNEW.
      * exact Hap1.
      * exact Hap2.
      * apply (pcj_fresh lyF SF WF memF mdF (ablocks B lyc Sc) (lay_nospill Q) p _ HARF HpF HL0 HFap).
        intros pn Hpn. pose proof (pcj_nospill_live _ _ _ _ _ HA PB pn Hpn) as Hinc.
        split; [exact Hinc | exact (HcF _ Hinc)].
    + exact (pcj_mid_spill ly S lyc Sc lyF SF O Q p _ HOQ (recb_ablocks_nodup_m B ly S W mem md HAR) PB HPm HFap HL0). }
destruct HJA as (Q2 & HA2 & EA2 & HMID).
pose proof (pcj_O2_facts lyF SF WF memF mdF (rdW WF memF) R2 Q2 O Q HARF HA2 EA2 (fun pn H => proj2 (HOQ pn) H))
  as (HANS & HO2L & HOLDNO).
pose proof HA2 as (_ & _ & _ & _ & HANS2 & _).
destruct (pcj_answer_ptr _ _ _ _ HANS2) as [HOLD HOLDin]. rewrite EA2 in HOLD, HOLDin.
assert (Hold64 : 0 <= oaddr (l_answer Q) < 2 ^ 64).
{ destruct (l_answer Q) as [[pa na]|] eqn:EQa; cbn [oaddr fst]; [|lia].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ pa na HARF (HOLDin _ eq_refl)) as (_ & H4096 & Hc & _ & _ & _ & Hn).
  pose proof (req_size_pos na ltac:(lia)). lia. }
(* the budgets *)
assert (HEV' : st_nev S + (rec_spill_frees R + EV_XSTRDUP + EV_ANSWER_CODE) <= EV_MAX) by exact HEV.
assert (EVa : EV_ANSWER_CODE = 4) by reflexivity. assert (EVx : EV_XSTRDUP = 1) by reflexivity.
assert (HLx : blocks_bytes S + (LIVE_XSTRDUP u + LIVE_ANSWER_CODE (snd (pins_clear_m R (Some u)))) <= LIVE_MAX)
  by exact HLIVE.
rewrite Hsnd in HLx.
assert (HMLEF : mo_le MT S SF (XM_PINS_CLEAR MT R (Some u) - XM_ANSWER_CODE MT code)).
{ apply (mo_le_mono MT MTL S SF _ _ (mo_le_trans MT MTL S Sc SF _ _ HMLE MLEF)).
  unfold XM_PINS_CLEAR. cbn [sarg]. rewrite Hsnd. lia. }
apply (pcl_tail ly S W regs mem md R O (Some u) ch lyF SF WF memF mdF kF regsF R2 (lay_blocks Q2)
  (oaddr (l_answer Q)) code HJF PRE HFRM Hsp2 R1 HP2 H10 Hcode (ex_intro _ Q2 (conj HA2 (fun pn => iff_refl _)))
  HOLD Hold64 HMID HANS HO2L HOLDNO HFPLO HMODEL HRODF (cmd_ro_ok_of_aro lyF SF WF memF mdF HARF HRODF)).
- rewrite HFRF. exact HFRS.
- lia.
- unfold LIVE_XSTRDUP in *. lia.
- apply (mo_ok_step MT MTL S SF (XM_PINS_CLEAR MT R (Some u) - XM_ANSWER_CODE MT code)); [|exact HMLEF].
  replace (XM_PINS_CLEAR MT R (Some u) - XM_ANSWER_CODE MT code + XM_ANSWER_CODE MT code)
    with (XM_PINS_CLEAR MT R (Some u)) by lia.
  exact HMOK.
- rewrite HkF. unfold EV_PINS_CLEAR. lia.
- unfold LIVE_PINS_CLEAR. cbn [sarg]. rewrite Hsnd. unfold LIVE_XSTRDUP in *. lia.
- exact HMLEF.
Qed.
(* --- the join segment: 0x8cd2c to the tail jump ----------------------------------------------------------- *)

Lemma pcl_join_seg : forall ly S (W : world SEGS) regs mem md ch R O Q pu u
  lyc Sc (Wc : world SEGS) memc mdc k c (regsJ : bvmap 5 word),
(* the call's entry (lib/A/Prog/pins_clear_c.v:77-94) *)
afn_pre SEGS B PINS_CLEAR_STK ly S W regs mem md ch ->
(* rounding mode 0 (lib/A/Prog/pins_clear_c.v); answer_code's printf asks it at the tail jump *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 pu -> 0 <= pu < 2 ^ 64 ->
in_blockA (ablocks B ly S) pu (Z.of_nat (length u) + 1) ->
Forall (fun qk => iv_apart pu (Z.of_nat (length u) + 1) (fst qk) (snd qk)) O ->
astr_atR (rdW W mem) pu u -> Z.of_nat (length u) + 1 <= LMAX + 1 ->
arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn O <-> In pn (lay_blocks Q)) ->
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_PINS_CLEAR R <= EV_MAX -> blocks_bytes S + LIVE_PINS_CLEAR R (Some u) <= LIVE_MAX ->
mo_ok MT S (XM_PINS_CLEAR MT R (Some u)) ->
(* the state where record()'s arms meet *)
ajournal SEGS B PINS_CLEAR_STK (spZ regs) (pcl_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
pcl_at_join B ly S W mem R (l_spill Q) lyc Sc Wc memc c k ->
pcl_slot_ok c ->
spZ regsJ = spZ regs - PCL_FRAME ->
getr regsJ 8 = w64 c -> getr regsJ 9 = w64 pu ->
getr regsJ 19 = w64 A_G_REC -> getr regsJ 20 = w64 SB ->
getr regsJ 3 = w64 (as_gp B) -> getr regsJ 4 = w64 (as_tp B) ->
(forall r, 22 <= r <= 27 -> getr regsJ (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
pcl_frame_at (rdW Wc memc) (spZ regsJ) (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8))
  (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19))
  (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21)) ->
mo_le MT S Sc (rec_spill_frees R * mo_free MT) ->
blocks_bytes Sc <= blocks_bytes S ->
SRr SEGS Wc (cfg_at SEGS (BASE + PCL_JOIN) regsJ memc mdc)
  (apost_baseF SEGS B PINS_CLEAR_STK (pcl_FP O) regs ly S W mem md (EV_PINS_CLEAR R) (pcl_Q ly S O R (Some u))).
Proof.
intros ly S W regs mem md ch R O Q pu u lyc Sc Wc memc mdc k c regsJ
  PRE HFRM HROD HROOK H10 Hpu64 HBLK HAPO HSTR HLEN HA HOQ HFRS HEV HLIVE HMOK
  HJ HAJ Hcs Hsp R8 R9 R19 R20 R3 R4 R22 HFRAME HMLE HBB.
pose proof PRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof pa_base_lo as HBLO.
assert (WS : PINS_CLEAR_STK = 16560) by (vm_compute; reflexivity).
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & _ & _ & _ & _ & HFRc & Hnevc & Hk0 & _ & _ & _ & _ & _ & Hpresc & _).
destruct (pcl_slot_bounds c Hcs) as (Hcb & Hc8 & Hcf).
assert (HSLOT : forall a, c <= a < c + CALL_SIZE ->
  A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).
{ intros a Ha. destruct Hcf as [Hcf | ->]; [left | right];
  unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, CALL_SIZE, OFF_CALLS, OFF_ANSWER in *; lia. }
assert (Hspc : alloc_ceiling + 64 <= spZ regs) by lia.
(* the entry's representation *)
pose proof HA as (Hg8 & Hs8 & Hap & HG1 & HANS & HRPL & HSCAL & HOWN).
pose proof HSCAL as (Vrf & Vcd & _ & Vst & _ & Rrf & Rcd & _ & Rst & _).
assert (HOlive : forall pn, In pn O -> In pn (ablocks B ly S))
  by (intros pn H; apply (lay_blocks_in _ _ _ _ _ _ HA); apply HOQ; exact H).
(* what both arms of record() leave at the join *)
assert (JF : (forall a, A_G_REC <= a < A_G_REC + REC_SIZE ->
    ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW Wc memc a = rdW W mem a) /\
  (forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> ~ (c <= a < c + CALL_SIZE) -> rdW Wc memc a = rdW W mem a) /\
  (forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < n -> rdW Wc memc (p + i) = rdW W mem (p + i)) /\
  (exists F, Permutation (ablocks B ly S) (ablocks B lyc Sc ++ F) /\ (forall pn, In pn F -> In pn O)) /\
  k = rec_spill_frees R).
{ destruct HAJ as [(Hlt & -> & -> & EB & _ & KG & KS & KH) | (H16 & -> & -> & PB & _ & KG & KS & KH)].
  - split; [exact KG|]. split; [intros a Ha _; exact (KS a Ha)|]. split; [exact KH|].
    split; [exists []; split; [rewrite app_nil_r, EB; apply Permutation_refl | intros pn []]|].
    unfold rec_spill_frees. apply Nat.ltb_lt in Hlt. rewrite Hlt. reflexivity.
  - split; [intros a Ha _; exact (KG a Ha)|].
    split; [intros a Ha Hn; exfalso; apply Hn; unfold CALL_SIZE, SC_SIZE in *; lia|]. split; [exact KH|].
    split; [exists (l_spill Q); split; [exact PB | intros pn H; apply HOQ; exact (In_lay_spill Q pn H)]|].
    pose proof HG1 as (_ & _ & _ & _ & (_ & _ & HLP & _) & _).
    unfold rec_spill_frees. rewrite H16. cbn [Nat.ltb Nat.leb]. rewrite HLP. reflexivity. }
destruct JF as (JG & JS & JH & (F & JB & JFO) & HkR). subst k.
(* refuse, code and state at the join *)
assert (Vrf' : aval_mem (rdW Wc memc) (A_G_REC + OFF_REFUSE) 4 (r_refuse R mod 2 ^ 32)).
{ apply (pcj_aval_kept (rdW W mem)); [exact (pcj_aval_mod _ _ _ Vrf)|].
  intros x Hx. cbn [Z.of_nat] in Hx. apply JG; unfold OFF_REFUSE, OFF_NCALLS, REC_SIZE in *; lia. }
assert (Vcd' : aval_mem (rdW Wc memc) (A_G_REC + OFF_CODE) 4 (r_code R mod 2 ^ 32)).
{ apply (pcj_aval_kept (rdW W mem)); [exact (pcj_aval_mod _ _ _ Vcd)|].
  intros x Hx. cbn [Z.of_nat] in Hx. apply JG; unfold OFF_CODE, OFF_NCALLS, REC_SIZE in *; lia. }
assert (Vst' : aval_mem (rdW Wc memc) (A_G_REC + OFF_STATE) 8 (r_state R)).
{ apply (pcj_aval_kept (rdW W mem)); [exact Vst|].
  intros x Hx. cbn [Z.of_nat] in Hx. apply JG; unfold OFF_STATE, OFF_NCALLS, REC_SIZE in *; lia. }
(* the symbolic state at the join *)
assert (HspJ : 2 ^ 46 - PCL_FRAME <= spZ regsJ <= 2 ^ 47) by (rewrite Hsp; unfold PCL_FRAME; lia).
assert (HspJ16 : spZ regsJ mod 16 = 0).
{ rewrite Hsp. unfold PCL_FRAME. replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hsp16. }
assert (HpresJ : forall a, spZ regsJ <= a < spZ regsJ + PCL_FRAME -> apresent (w_H Wc) memc a).
{ intros a Ha. apply Hpresc. rewrite Hsp in Ha. unfold PCL_FRAME in Ha. lia. }
destruct (pcl_seed_join B HB VOBJS cmd_prog_writable lyc Sc Wc memc mdc regsJ c
  (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
  (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))
  (bv_unsigned (getr regs 21)) (r_refuse R mod 2 ^ 32) (r_code R mod 2 ^ 32) (r_state R)
  HARc Hcs HspJ HspJ16 R8 R19 R20 HpresJ HFRAME Vrf' (Z.mod_pos_bound (r_refuse R) (2 ^ 32) ltac:(lia)) Vcd'
  (Z.mod_pos_bound (r_code R) (2 ^ 32) ltac:(lia)) Vst' Rst) as [HS SHOK].
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E0 := Ex) in HS, SHOK end.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E0 m = getr regsJ rr).
{ intros m rr Hm. unfold E0. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E32 : ew E0 32 = Z_to_bv 64 SB)
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E34 : ew E0 34 = Z_to_bv 64 c)
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E35 : ew E0 35 = Z_to_bv 64 (bv_unsigned (getr regs 1)))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E36 : ew E0 36 = Z_to_bv 64 (bv_unsigned (getr regs 8)))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E37 : ew E0 37 = Z_to_bv 64 (bv_unsigned (getr regs 9)))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); change 37%nat with (32 + 5)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E38 : ew E0 38 = Z_to_bv 64 (bv_unsigned (getr regs 18)))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); change 38%nat with (32 + 6)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E39 : ew E0 39 = Z_to_bv 64 (bv_unsigned (getr regs 19)))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); change 39%nat with (32 + 7)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E40 : ew E0 40 = Z_to_bv 64 (bv_unsigned (getr regs 20)))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); change 40%nat with (32 + 8)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E41 : ew E0 41 = Z_to_bv 64 (bv_unsigned (getr regs 21)))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); change 41%nat with (32 + 9)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E42 : ew E0 42 = Z_to_bv 64 (r_refuse R mod 2 ^ 32))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); change 42%nat with (32 + 10)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E43 : ew E0 43 = Z_to_bv 64 (r_code R mod 2 ^ 32))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); change 43%nat with (32 + 11)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E44 : ew E0 44 = Z_to_bv 64 (r_state R))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); change 44%nat with (32 + 12)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (EGR : ew E0 285 = Z_to_bv 64 A_G_REC).
{ rewrite (img_env_atomP E0 285%nat HEI ltac:(unfold A_TEXT, A_LIM; lia)).
  change 285%nat with PCL_GR. rewrite (pcl_grec_val VOBJS). reflexivity. }
clearbody E0.
assert (UGR : bv_unsigned (ew E0 285) = A_G_REC) by (rewrite EGR; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (UC : bv_unsigned (ew E0 34) = c)
  by (rewrite E34; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs + -64).
{ rewrite (EE 2%nat 2%bv eq_refl). change (bv_unsigned (getr regsJ 2)) with (spZ regsJ). rewrite Hsp. unfold PCL_FRAME. lia. }
assert (E9 : ew E0 9 = Z_to_bv 64 pu) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
(* the argument's block: live at the entry, none of the recorder's, so live at the join *)
destruct HBLK as (q & m & Hqm & Hq1 & Hq2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hqm) as (_ & Hq4096 & _ & _ & _ & _ & Hm0).
assert (HqO : ~ In (q, m) O).
{ intros HqO. rewrite Forall_forall in HAPO. pose proof (HAPO _ HqO) as H. unfold iv_apart in H. cbn [fst snd] in H. lia. }
assert (Hqc : In (q, m) (ablocks B lyc Sc)).
{ apply (Permutation_in _ JB) in Hqm. apply in_app_or in Hqm as [H | H]; [exact H | exfalso; exact (HqO (JFO _ H))]. }
unfold cfg_at, w64.
(* 0x8cd2c .. 0x8cd5c: the slot's fn and nargs, up to the NULL test of the argument *)
paj_run_to_tok RUNTO HS HJ SHOK PCL_SPAN PCL_ARGBR.
{ pcj_awr Usp UC UGR HSLOT. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv1 := mdx) in *; clearbody mdv1 end.
psrr_branch_tok RUN BR HS SHOK PCL_SPAN.
2: { exfalso. rewrite branch_ne_U in Hc.
     rewrite (U_atom E0 9 pu E9 Hpu64), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
     apply negb_false_iff, Z.eqb_eq in Hc. lia. }
clear Hc.
(* 0x8cd5c .. 0x8cd6c: the argument is the caller's string; the call of xstrdup *)
paj_run_tok RUN HS HJ SHOK PCL_SPAN.
{ pcj_awr Usp UC UGR HSLOT. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv2 := mdx) in *; clearbody mdv2 end.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ pcj_Z (spZ regs) c a -> rdW Wc (ms_mem ms0) a = rdW Wc memc a).
{ intros a Ha Hn.
  rewrite (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) (ms_mem ms) (ms_mem ms0) (pcj_Z (spZ regs) c) HFr0);
    [ | pcj_win Usp UC UGR | exact Ha | exact Hn].
  apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) memc (ms_mem ms) (pcj_Z (spZ regs) c) HFr);
    [pcj_win Usp UC UGR | exact Ha | exact Hn]. }
assert (PROT1 : forall a, pcj_prot (ablocks B lyc Sc) c a -> rdW Wc (ms_mem ms0) a = rdW Wc memc a).
{ intros a Ha. destruct (pcj_prot_out lyc Sc Wc memc mdc (spZ regs) c a HARc Hspc Ha) as [Hr Hn].
  exact (KEEP1 a Hr Hn). }
(* the call of xstrdup at 0x8cd6c *)
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
assert (SIGX : SIG CS_xstrdup = BASE + AF_xstrdup).
{ rewrite (SIGP CS_xstrdup ltac:(cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]))).
  f_equal; vm_compute; reflexivity. }
rewrite SIGX.
assert (Esp1 : spZ (ms_regs ms0) = spZ regs + -64) by (unfold spZ at 1; rewrite P2; exact Usp).
pose proof (proj1 HJ) as HAR1.
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev1 & _).
assert (HFPRO : forall a, in_roP SEGS RLO RHI a -> ~ inFP (pcl_FP O) a) by exact (pcj_fp_ro ly S W mem md O HAR HOlive).
assert (HFPLO : forall a, inFP (pcl_FP O) a -> a < alloc_ceiling) by exact (pcj_fp_low ly S W mem md O HAR HOlive).
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms0)))
  by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ ly S W mem md [] lyc Sc Wc (ms_mem ms0)
    mdv2 _ HJ HFPRO HROD).
assert (HSTR1 : astr_atR (rdW Wc (ms_mem ms0)) pu u).
{ apply (astr_atR_agree_in (rdW W mem) _ q m); [exact HSTR | | lia | lia].
  intros i Hi. rewrite (PROT1 (q + i) (pcj_prot_heap lyc Sc Wc memc mdc c q m (q + i) HARc Hcs Hqc ltac:(lia))).
  exact (JH q m i Hqc Hi). }
assert (HTAIL1 : atail_vis SEGS Wc (ms_mem ms0) (pu + Z.of_nat (length u)))
  by exact (cmd_heap_tail_vis lyc Sc Wc (ms_mem ms0) mdv2 q m (pu + Z.of_nat (length u)) HAR1 Hqc ltac:(lia)).
assert (XMa : 0 <= XM_ANSWER_CODE MT (snd (pins_clear_m R (Some u)))).
{ unfold XM_ANSWER_CODE, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (resp (snd (pins_clear_m R (Some u))))) + 1) ltac:(lia)).
  lia. }
assert (LAa : 0 <= LIVE_ANSWER_CODE (snd (pins_clear_m R (Some u))))
  by (unfold LIVE_ANSWER_CODE, LIVE_HAND_BACK, LIVE_XSTRDUP; lia).
assert (HLx : blocks_bytes S + (LIVE_XSTRDUP u + LIVE_ANSWER_CODE (snd (pins_clear_m R (Some u)))) <= LIVE_MAX)
  by exact HLIVE.
assert (HEVx : st_nev S + (rec_spill_frees R + EV_XSTRDUP + EV_ANSWER_CODE) <= EV_MAX) by exact HEV.
assert (EVa : EV_ANSWER_CODE = 4) by reflexivity.
assert (EVx : EV_XSTRDUP = 1) by reflexivity.
set (Kx := fun ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 (md2 : Model) => exists p : Z,
  getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
  Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP u) :: ablocks B lyc Sc) /\
  Forall (fun qk => iv_apart p (LIVE_XSTRDUP u) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
  in_blockA (ablocks B ly2 S2) p (LIVE_XSTRDUP u) /\
  astr_atR (rdW W2 mem2) p u /\ astr_atR (rdW W2 mem2) pu u /\
  blocks_bytes S2 <= blocks_bytes Sc + LIVE_XSTRDUP u /\
  mo_le MT Sc S2 (XM_XSTRDUP MT u)).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS Wc (ms_regs ms0) (ms_mem ms0) _ PINS_CLEAR_STK (spZ regs) (pcl_FP O) ly S W mem md []
    lyc Sc _ (rec_spill_frees R) XSTRDUP_STK [] EV_XSTRDUP (-64) (getr (ms_regs ms0) 1) [] Kx HJ).
  - exact Esp1.
  - reflexivity.
  - lia.
  - vm_compute. discriminate.
  - rewrite WS. vm_compute. discriminate.
  - rewrite P3, (EE 3%nat 3%bv eq_refl). exact R3.
  - rewrite P4, (EE 4%nat 4%bv eq_refl). exact R4.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite P1, unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite P8, UC. unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb. lia.
  - intros HPRE1. eapply SRr_mono.
    { apply (TXSTRDUP fx lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdv2 [] pu u HPRE1 HROD1).
      - rewrite P10. exact E9.
      - left. cbv beta iota zeta delta [astr_argA].
        split; [lia|]. split; [exact HSTR1|]. split; [exact HLEN|].
        left. split; [exists q, m; split; [exact Hqc | lia] | constructor].
      - exact HTAIL1.
      - lia.
      - lia.
      - apply (mo_ok_step MT MTL S Sc (rec_spill_frees R * mo_free MT) (XM_XSTRDUP MT u)); [|exact HMLE].
        apply (mo_ok_le MT MTL S _ (XM_PINS_CLEAR MT R (Some u)) HMOK).
        unfold XM_PINS_CLEAR. cbn [sarg]. lia. }
    intros W2 c2 _ H. exact H.
  - intros a Ha. destruct (inFP_nil a Ha).
  - intros ? ? ? ? ? ? _ a Ha. destruct (inFP_nil a Ha). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
destruct HK2 as (p & Hp10 & [Hp4096 Hp64] & HPm & HFap & HinB & Hpx & Hsx & HBB2 & MLE2).
pose proof (proj1 HJ2) as HAR2.
assert (HpF2 : In (p, LIVE_XSTRDUP u) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPm | left; reflexivity]).
assert (Hbl12 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
  by (intros pn H; eapply Permutation_in; [apply Permutation_sym; exact HPm | right; exact H]).
(* back at 0x8cd70: the frame, the slot and g_rec's words are kept *)
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & HHI2 & _).
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  repeat apply Forall_cons; [| | | | apply Forall_nil].
  - apply (pcj_region_kept E0 Wc W2 (ms_mem ms0) mem2 2 (spZ regs + -64)); [exact Usp | |].
    + intros a Ha. apply HHI2; [lia | unfold XSTRDUP_STK, ASTACK in *; lia | apply inFP_nil].
    + intros a Ha. apply (apresent_writable SEGS). apply Hpres2. lia.
  - apply (pcj_region_kept E0 Wc W2 (ms_mem ms0) mem2 34 c); [exact UC | |].
    + intros a Ha. apply (pcj_call_keeps_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc2).
      apply (pcl_in_PG_slot c a Hcs). unfold CALL_SIZE; lia.
    + intros a Ha. apply (cmd_prog_writable _ _ _ _ _ a HAR2). apply (pcl_in_PG_slot c a Hcs). unfold CALL_SIZE; lia.
  - apply (pcj_region_kept E0 Wc W2 (ms_mem ms0) mem2 285 A_G_REC); [exact UGR | | intros a Ha; lia].
    intros a Ha. apply (pcj_call_keeps_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc2).
    apply recb_grec_in. unfold REC_SIZE; lia.
  - apply (pcj_region_kept E0 Wc W2 (ms_mem ms0) mem2 285 A_G_REC); [exact UGR | |].
    + intros a Ha. apply (pcj_call_keeps_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc2).
      apply recb_grec_in. unfold OFF_STATE, REC_SIZE in *. lia.
    + intros a Ha. apply (cmd_prog_writable _ _ _ _ _ a HAR2). apply recb_grec_in. unfold OFF_STATE, REC_SIZE in *. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E2 := havoc E0 48 (map (getr regs2) CLOB)) in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 48)%nat -> ew E2 n = ew E0 n) by (intros n Hn; apply YN3v.ew_havoc_old; exact Hn).
assert (A52 : ew E2 52 = getr regs2 10) by reflexivity.
clearbody E2.
assert (UGR2 : bv_unsigned (ew E2 285) = A_G_REC).
{ rewrite (img_env_atomP E2 285%nat HEI2 ltac:(unfold A_TEXT, A_LIM; lia)). change 285%nat with PCL_GR.
  rewrite (pcl_grec_val VOBJS). apply unsigned_lit_small. unfold A_G_REC; lia. }
assert (UC2 : bv_unsigned (ew E2 34) = c) by (rewrite OLD2 by lia; exact UC).
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs + -64) by (rewrite OLD2 by lia; exact Usp).
assert (SHOK2 : sh_ok SEGS Bxp PCL_SH E2 (mrestrict (w_H W2) mem2)).
{ apply (pcl_sh_ok B HB ly2 S2 W2 mem2 md2 E2 c HAR2 Hcs); unfold PCL_SB, PCL_C.
  - rewrite (OLD2 32%nat ltac:(lia)). exact E32.
  - rewrite (OLD2 34%nat ltac:(lia)). exact E34. }
clear SHOK.
(* 0x8cd70 .. 0x8cda8: nargs := 1, args[0] := the copy, g_rec.refuse into a2 *)
rewrite P1.
paj_run_to_tok RUNTO HS HJ2 SHOK2 PCL_SPAN PCL_REFBR.
{ pcj_awr Usp2 UC2 UGR2 HSLOT. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv3 := mdx) in *; clearbody mdv3 end.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ pcj_Z (spZ regs) c a -> rdW W2 (ms_mem ms1) a = rdW W2 mem2 a).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) E2 _ (w_H W2) mem2 (ms_mem ms1) (pcj_Z (spZ regs) c) HFr1);
    [pcj_win Usp2 UC2 UGR2 | exact Ha | exact Hn]. }
assert (PROT2 : forall a, pcj_prot (ablocks B lyc Sc) c a -> rdW W2 (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha.
  destruct (pcj_prot_out ly2 S2 W2 mem2 md2 (spZ regs) c a HAR2 Hspc (pcj_prot_mono _ _ c a Hbl12 Ha)) as [Hr Hn].
  rewrite (KEEP2 a Hr Hn).
  rewrite (pcj_prot_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ablocks B lyc Sc) c a HJc2
    ltac:(intros pn Hpn; split; [exact Hpn | exact (Hbl12 pn Hpn)]) Ha).
  exact (PROT1 a Ha). }
assert (HPX2 : forall i, 0 <= i < Z.of_nat (length u) + 1 -> rdW W2 (ms_mem ms1) (p + i) = rdW W2 mem2 (p + i)).
{ intros i Hi.
  destruct (pcj_prot_out ly2 S2 W2 mem2 md2 (spZ regs) c (p + i) HAR2 Hspc
    (pcj_prot_heap ly2 S2 W2 mem2 md2 c p _ (p + i) HAR2 Hcs HpF2 ltac:(unfold LIVE_XSTRDUP; lia))) as [Hr Hn].
  exact (KEEP2 _ Hr Hn). }
assert (UR : U E2 (SExt true 32 (SOff 42 0)) = r_refuse R mod 2 ^ 64).
{ apply pcj_sext32; [rewrite (OLD2 42%nat ltac:(lia)); exact E42 | exact Rrf]. }
assert (SIGA : SIG CS_answer_code = BASE + AF_answer_code).
{ rewrite (SIGP CS_answer_code ltac:(cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]))).
  f_equal; vm_compute; reflexivity. }
(* 0x8cda8: beqz a2, the test of g_rec.refuse *)
psrr_branch_tok RUN BR HS SHOK2 PCL_SPAN.
- (* g_rec.refuse is 0: 0x8cdb4 .. 0x8cdbc, the call of mix_call(g_rec.state, c) *)
  assert (HR0 : r_refuse R = 0).
  { rewrite branch_eq_U, UR, U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
    apply Z.eqb_eq in Hc. apply pcj_mod0; [lia | exact Hc]. }
  paj_run_tok RUN HS HJ2 SHOK2 PCL_SPAN.
  { pcj_awr Usp2 UC2 UGR2 HSLOT. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv4 := mdx) in *; clearbody mdv4 end.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ pcj_Z (spZ regs) c a ->
    rdW W2 (ms_mem ms2) a = rdW W2 (ms_mem ms1) a).
  { intros a Ha Hn.
    apply (kept_of_frame (segs := SEGS) E2 _ (w_H W2) (ms_mem ms1) (ms_mem ms2) (pcj_Z (spZ regs) c) HFr2);
      [pcj_win Usp2 UC2 UGR2 | exact Ha | exact Hn]. }
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  pcj_region HS 1%nat HRs3.
  assert (SIGM : SIG CS_mix_call = BASE + AF_mix_call).
  { rewrite (SIGP CS_mix_call ltac:(cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]))).
    f_equal; vm_compute; reflexivity. }
  rewrite SIGM.
  (* the recorded call, as mix_call reads it *)
  assert (HPX3 : astr_atR (rdW W2 (ms_mem ms2)) p u).
  { apply (astr_atR_agree_in (rdW W2 mem2) _ p (Z.of_nat (length u) + 1)); [exact Hpx | | lia | lia].
    intros i Hi. rewrite <- (HPX2 i Hi).
    destruct (pcj_prot_out ly2 S2 W2 mem2 md2 (spZ regs) c (p + i) HAR2 Hspc
      (pcj_prot_heap ly2 S2 W2 mem2 md2 c p _ (p + i) HAR2 Hcs HpF2 ltac:(unfold LIVE_XSTRDUP; lia))) as [Hr Hn].
    exact (KEEP3 _ Hr Hn). }
  assert (HNEW3 : pcl_new_call (ablocks B ly2 S2) (rdW W2 (ms_mem ms2)) c p u).
  { split; [| split; [| split]].
    - apply (aval_mem_view SEGS). change 4%nat with (N.to_nat 4). unfold CALL_OFF_FN.
      apply (field_of_region E2 _ 34%nat c _ _ _ _ _ 0 4 (SLit 21) REC_PINS_CLEAR HRs3 UC2 ltac:(cbn [In]; tauto));
        [reflexivity | unfold REC_PINS_CLEAR; cbn; lia | cbn; lia].
    - apply (aval_mem_view SEGS). change 4%nat with (N.to_nat 4). unfold CALL_OFF_NARGS.
      apply (field_of_region E2 _ 34%nat c _ _ _ _ _ 4 4 (SLit 1) 1 HRs3 UC2 ltac:(cbn [In]; tauto));
        [reflexivity | cbn; lia | cbn; lia].
    - apply (aval_mem_view SEGS). change 8%nat with (N.to_nat 8). unfold CALL_OFF_ARGS.
      apply (field_of_region E2 _ 34%nat c _ _ _ _ _ 8 8 (SOff 52 0) p HRs3 UC2 ltac:(cbn [In]; tauto));
        [rewrite pcj_soff0, A52; exact Hp10 | rewrite pcl_pow8; lia | cbn; lia].
    - split; [exact HPX3|]. split; [lia|]. split; [exact HpF2|]. unfold LMAX in *. lia. }
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
  assert (HROD3 : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem ms2)))
    by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ ly S W mem md [] ly2 S2 W2 (ms_mem ms2)
      mdv4 _ HJ2 HFPRO HROD).
  set (Km := fun ly3 S3 (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) =>
    getr regs3 10 = w64 (mixcall (r_state R) (fst (REC_PINS_CLEAR, [u])) (snd (REC_PINS_CLEAR, [u]))) /\
    Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) /\ ly3 = ly2 /\ S3 = S2).
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS W2 (ms_regs ms2) (ms_mem ms2) _ PINS_CLEAR_STK (spZ regs) (pcl_FP O) ly S W mem md []
      ly2 S2 _ (rec_spill_frees R + EV_XSTRDUP) MIX_CALL_STK [] EV_MIX_CALL (-64) (getr (ms_regs ms2) 1) [] Km HJ2).
    - unfold spZ at 1. rewrite Q2. exact Usp2.
    - reflexivity.
    - lia.
    - vm_compute. discriminate.
    - rewrite WS. vm_compute. discriminate.
    - rewrite Q3, OLD2, (EE 3%nat 3%bv eq_refl) by lia. exact R3.
    - rewrite Q4, OLD2, (EE 4%nat 4%bv eq_refl) by lia. exact R4.
    - reflexivity.
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Q1, unsigned_lit_small by lia. lia.
    - apply achain_low. unfold s0Z. rewrite Q8, UC2. unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb. lia.
    - intros HPRE3. eapply SRr_mono.
      { apply (TMIX_CALL fx ly2 S2 W2 (ms_regs ms2) (ms_mem ms2) mdv4 (r_state R) c (REC_PINS_CLEAR, [u])
          [(p, LIVE_XSTRDUP u)] (afn_pre_na_of SEGS B _ _ _ _ _ _ _ _ HPRE3) HROD3).
        - rewrite Q10, OLD2 by lia. exact E44.
        - exact Rst.
        - rewrite Q11, OLD2 by lia. exact E34.
        - exact Hcs.
        - exact (pcl_acall_new _ _ c p u HNEW3).
        - exact (cmd_ro_ok_of_aro ly2 S2 W2 (ms_mem ms2) mdv4 (proj1 HJ2) HROD3).
        - unfold EV_MIX_CALL. lia. }
      intros W3 c3 _ H. exact H.
    - intros a Ha. destruct (inFP_nil a Ha).
    - intros ? ? ? ? ? ? _ a Ha. destruct (inFP_nil a Ha). }
  cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HK3).
  destruct HK3 as (Hm10 & HPm3 & -> & ->).
  (* back at 0x8cdc0 *)
  jafter_call_keep_pi HS 64%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2; 3]%nat HS3.
  match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & HHI3 & _).
    pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
    pose proof (proj1 HJ3) as HAR3.
    repeat apply Forall_cons; [| | | | apply Forall_nil].
    - apply (pcj_region_kept E2 W2 W3 (ms_mem ms2) mem3 2 (spZ regs + -64)); [exact Usp2 | |].
      + intros a Ha. apply HHI3; [lia | unfold MIX_CALL_STK, ESTACK in *; lia | apply inFP_nil].
      + intros a Ha. apply (apresent_writable SEGS). apply Hpres3. lia.
    - apply (pcj_region_kept E2 W2 W3 (ms_mem ms2) mem3 34 c); [exact UC2 | |].
      + intros a Ha. apply (pcj_call_keeps_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3).
        apply (pcl_in_PG_slot c a Hcs). unfold CALL_SIZE; lia.
      + intros a Ha. apply (cmd_prog_writable _ _ _ _ _ a HAR3). apply (pcl_in_PG_slot c a Hcs). unfold CALL_SIZE; lia.
    - apply (pcj_region_kept E2 W2 W3 (ms_mem ms2) mem3 285 A_G_REC); [exact UGR2 | | intros a Ha; lia].
      intros a Ha. apply (pcj_call_keeps_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3).
      apply recb_grec_in. unfold REC_SIZE; lia.
    - apply (pcj_region_kept E2 W2 W3 (ms_mem ms2) mem3 285 A_G_REC); [exact UGR2 | |].
      + intros a Ha. apply (pcj_call_keeps_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3).
        apply recb_grec_in. unfold OFF_STATE, REC_SIZE in *. lia.
      + intros a Ha. apply (cmd_prog_writable _ _ _ _ _ a HAR3). apply recb_grec_in. unfold OFF_STATE, REC_SIZE in *. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  set (E3 := havoc E2 64 (map (getr regs3) CLOB)) in HS.
  assert (HEIE3 : img_env VAL A_LIM E3) by (apply img_env_havoc; [exact HEI2 | cbv; lia]).
  assert (OLD3 : forall n, (n < 64)%nat -> ew E3 n = ew E2 n) by (intros n Hn; apply YN3v.ew_havoc_old; exact Hn).
  assert (A68 : ew E3 68 = getr regs3 10) by reflexivity.
  clearbody E3.
  assert (UGR3 : bv_unsigned (ew E3 285) = A_G_REC).
  { rewrite (img_env_atomP E3 285%nat HEIE3 ltac:(unfold A_TEXT, A_LIM; lia)). change 285%nat with PCL_GR.
    rewrite (pcl_grec_val VOBJS). apply unsigned_lit_small. unfold A_G_REC; lia. }
  assert (UC3 : bv_unsigned (ew E3 34) = c) by (rewrite OLD3 by lia; exact UC2).
  assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs + -64) by (rewrite OLD3 by lia; exact Usp2).
  assert (SHOK3 : sh_ok SEGS Bxp PCL_SH E3 (mrestrict (w_H W3) mem3)).
  { apply (pcl_sh_ok B HB ly2 S2 W3 mem3 md3 E3 c (proj1 HJ3) Hcs); unfold PCL_SB, PCL_C.
    - rewrite (OLD3 32%nat ltac:(lia)), (OLD2 32%nat ltac:(lia)). exact E32.
    - rewrite (OLD3 34%nat ltac:(lia)), (OLD2 34%nat ltac:(lia)). exact E34. }
  clear SHOK2.
  (* 0x8cdc0 .. 0x8cdec: g_rec.state := the digest, a0 := 0, the epilogue and the tail jump *)
  rewrite Q1.
  paj_run_tok RUN HS HJ3 SHOK3 PCL_SPAN.
  { pcj_awr Usp3 UC3 UGR3 HSLOT. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv5 := mdx) in *; clearbody mdv5 end.
  assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> ~ pcj_Z (spZ regs) c a -> rdW W3 (ms_mem ms3) a = rdW W3 mem3 a).
  { intros a Ha Hn. apply (kept_of_frame (segs := SEGS) E3 _ (w_H W3) mem3 (ms_mem ms3) (pcj_Z (spZ regs) c) HFr3);
      [pcj_win Usp3 UC3 UGR3 | exact Ha | exact Hn]. }
  pmkst HS. rewrite SIGA.
  prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
  prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
  prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21.
  prreg HS (Z_to_bv 5 22) F22. prreg HS (Z_to_bv 5 23) F23. prreg HS (Z_to_bv 5 24) F24.
  prreg HS (Z_to_bv 5 25) F25. prreg HS (Z_to_bv 5 26) F26. prreg HS (Z_to_bv 5 27) F27.
  pcj_reg HS (10%bv : bv 5) F10.
  pcj_region HS 1%nat HRsF. pcj_region HS 3%nat HRtF.
  assert (KEEPF : forall a, pcj_prot (ablocks B lyc Sc) c a -> rdW W3 (ms_mem ms3) a = rdW Wc memc a).
  { intros a Ha. pose proof (pcj_prot_mono _ _ c a Hbl12 Ha) as Ha2.
    destruct (pcj_prot_out ly2 S2 W2 mem2 md2 (spZ regs) c a HAR2 Hspc Ha2) as [Hr Hn].
    rewrite (KEEP4 a Hr Hn).
    rewrite (pcj_prot_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ablocks B ly2 S2) c a HJc3
      ltac:(intros pn Hpn; split; exact Hpn) Ha2).
    rewrite (KEEP3 a Hr Hn). exact (PROT2 a Ha). }
  assert (HPXF : astr_atR (rdW W3 (ms_mem ms3)) p u).
  { apply (astr_atR_agree_in (rdW W2 (ms_mem ms2)) _ p (Z.of_nat (length u) + 1)); [exact HPX3 | | lia | lia].
    intros i Hi.
    assert (HPi : pcj_prot (ablocks B ly2 S2) c (p + i))
      by exact (pcj_prot_heap ly2 S2 W2 mem2 md2 c p _ (p + i) HAR2 Hcs HpF2 ltac:(unfold LIVE_XSTRDUP; lia)).
    destruct (pcj_prot_out ly2 S2 W2 mem2 md2 (spZ regs) c (p + i) HAR2 Hspc HPi) as [Hr Hn].
    rewrite (KEEP4 _ Hr Hn).
    exact (pcj_prot_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ablocks B ly2 S2) c (p + i) HJc3
      ltac:(intros pn Hpn; split; exact Hpn) HPi). }
  assert (Hh : 0 <= mixcall (r_state R) REC_PINS_CLEAR [u] < 2 ^ 64) by exact (mixcall_range _ _ _ Rst).
  destruct (pcj_regs_end regs (ms_regs ms3)) as (Hsp2F & R1F & HP2F).
  { rewrite F1, OLD3, OLD2 by lia. exact E35. }
  { rewrite F2, Usp3. f_equal. lia. }
  { rewrite F3, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) by lia. rewrite R3. symmetry. exact Hgp. }
  { rewrite F4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) by lia. rewrite R4. symmetry. exact Htp. }
  { rewrite F8, OLD3, OLD2 by lia. exact E36. }
  { rewrite F9, OLD3, OLD2 by lia. exact E37. }
  { rewrite F18, OLD3, OLD2 by lia. exact E38. }
  { rewrite F19, OLD3, OLD2 by lia. exact E39. }
  { rewrite F20, OLD3, OLD2 by lia. exact E40. }
  { rewrite F21, OLD3, OLD2 by lia. exact E41. }
  { intros r Hr. assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    - rewrite F22, OLD3, OLD2, (EE 22%nat (Z_to_bv 5 22) eq_refl) by lia. apply R22; lia.
    - rewrite F23, OLD3, OLD2, (EE 23%nat (Z_to_bv 5 23) eq_refl) by lia. apply R22; lia.
    - rewrite F24, OLD3, OLD2, (EE 24%nat (Z_to_bv 5 24) eq_refl) by lia. apply R22; lia.
    - rewrite F25, OLD3, OLD2, (EE 25%nat (Z_to_bv 5 25) eq_refl) by lia. apply R22; lia.
    - rewrite F26, OLD3, OLD2, (EE 26%nat (Z_to_bv 5 26) eq_refl) by lia. apply R22; lia.
    - rewrite F27, OLD3, OLD2, (EE 27%nat (Z_to_bv 5 27) eq_refl) by lia. apply R22; lia. }
  apply (pcj_finish ly S W regs mem md ch R O Q u lyc Sc Wc memc mdc c ly2 S2 W3 (ms_mem ms3) mdv5 (ms_regs ms3)
    (rec_spill_frees R + EV_XSTRDUP + EV_MIX_CALL) p (mixcall (r_state R) REC_PINS_CLEAR [u]) 0
    PRE HFRM HROD HA HOQ HFRS HEV HLIVE HMOK HLEN HARc HAJ Hcs HMLE HBB HJ3).
  + unfold EV_MIX_CALL. lia.
  + exact KEEPF.
  + exact HPm.
  + exact HFap.
  + exact Hp4096.
  + apply (aval_mem_view SEGS). change 4%nat with (N.to_nat 4). unfold CALL_OFF_FN.
    apply (field_of_region E3 _ 34%nat c _ _ _ _ _ 0 4 (SLit 21) REC_PINS_CLEAR HRsF UC3 ltac:(cbn [In]; tauto));
      [reflexivity | unfold REC_PINS_CLEAR; cbn; lia | cbn; lia].
  + apply (aval_mem_view SEGS). change 4%nat with (N.to_nat 4). unfold CALL_OFF_NARGS.
    apply (field_of_region E3 _ 34%nat c _ _ _ _ _ 4 4 (SLit 1) 1 HRsF UC3 ltac:(cbn [In]; tauto));
      [reflexivity | cbn; lia | cbn; lia].
  + apply (aval_mem_view SEGS). change 8%nat with (N.to_nat 8). unfold CALL_OFF_ARGS.
    apply (field_of_region E3 _ 34%nat c _ _ _ _ _ 8 8 (SOff 52 0) p HRsF UC3 ltac:(cbn [In]; tauto));
      [rewrite pcj_soff0, OLD3, A52 by lia; exact Hp10 | rewrite pcl_pow8; lia | cbn; lia].
  + exact HPXF.
  + apply (aval_mem_view SEGS). change 8%nat with (N.to_nat 8). unfold OFF_STATE.
    apply (field_of_region E3 _ 285%nat A_G_REC _ _ _ _ _ 944 8 (SOff 68 0) _ HRtF UGR3 ltac:(cbn [In]; tauto));
      [rewrite pcj_soff0, A68; exact Hm10 | rewrite pcl_pow8; exact Hh | cbn; lia].
  + exact Hh.
  + exact MLE2.
  + exact HBB2.
  + exact Hsp2F.
  + exact R1F.
  + exact HP2F.
  + exact F10.
  + left. split; [exact HR0 | split; reflexivity].
- (* g_rec.refuse is not 0: 0x8cdac .. 0x8cdec, a0 := g_rec.code, the epilogue and the tail jump *)
  assert (HRn : r_refuse R <> 0).
  { intros HR0. rewrite branch_eq_U, UR, U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
    rewrite HR0 in Hc. vm_compute in Hc. discriminate Hc. }
  paj_run_tok RUN HS HJ2 SHOK2 PCL_SPAN.
  { pcj_awr Usp2 UC2 UGR2 HSLOT. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv4 := mdx) in *; clearbody mdv4 end.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ pcj_Z (spZ regs) c a ->
    rdW W2 (ms_mem ms2) a = rdW W2 (ms_mem ms1) a).
  { intros a Ha Hn.
    apply (kept_of_frame (segs := SEGS) E2 _ (w_H W2) (ms_mem ms1) (ms_mem ms2) (pcj_Z (spZ regs) c) HFr2);
      [pcj_win Usp2 UC2 UGR2 | exact Ha | exact Hn]. }
  pmkst HS. rewrite SIGA.
  prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
  prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
  prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21.
  prreg HS (Z_to_bv 5 22) F22. prreg HS (Z_to_bv 5 23) F23. prreg HS (Z_to_bv 5 24) F24.
  prreg HS (Z_to_bv 5 25) F25. prreg HS (Z_to_bv 5 26) F26. prreg HS (Z_to_bv 5 27) F27.
  pcj_reg HS (10%bv : bv 5) F10.
  pcj_region HS 1%nat HRsF. pcj_region HS 3%nat HRtF.
  assert (KEEPF : forall a, pcj_prot (ablocks B lyc Sc) c a -> rdW W2 (ms_mem ms2) a = rdW Wc memc a).
  { intros a Ha. pose proof (pcj_prot_mono _ _ c a Hbl12 Ha) as Ha2.
    destruct (pcj_prot_out ly2 S2 W2 mem2 md2 (spZ regs) c a HAR2 Hspc Ha2) as [Hr Hn].
    rewrite (KEEP3 a Hr Hn). exact (PROT2 a Ha). }
  assert (HPXF : astr_atR (rdW W2 (ms_mem ms2)) p u).
  { apply (astr_atR_agree_in (rdW W2 mem2) _ p (Z.of_nat (length u) + 1)); [exact Hpx | | lia | lia].
    intros i Hi. rewrite <- (HPX2 i Hi).
    destruct (pcj_prot_out ly2 S2 W2 mem2 md2 (spZ regs) c (p + i) HAR2 Hspc
      (pcj_prot_heap ly2 S2 W2 mem2 md2 c p _ (p + i) HAR2 Hcs HpF2 ltac:(unfold LIVE_XSTRDUP; lia))) as [Hr Hn].
    exact (KEEP3 _ Hr Hn). }
  destruct (pcj_regs_end regs (ms_regs ms2)) as (Hsp2F & R1F & HP2F).
  { rewrite F1, OLD2 by lia. exact E35. }
  { rewrite F2, Usp2. f_equal. lia. }
  { rewrite F3, OLD2, (EE 3%nat 3%bv eq_refl) by lia. rewrite R3. symmetry. exact Hgp. }
  { rewrite F4, OLD2, (EE 4%nat 4%bv eq_refl) by lia. rewrite R4. symmetry. exact Htp. }
  { rewrite F8, OLD2 by lia. exact E36. }
  { rewrite F9, OLD2 by lia. exact E37. }
  { rewrite F18, OLD2 by lia. exact E38. }
  { rewrite F19, OLD2 by lia. exact E39. }
  { rewrite F20, OLD2 by lia. exact E40. }
  { rewrite F21, OLD2 by lia. exact E41. }
  { intros r Hr. assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    - rewrite F22, OLD2, (EE 22%nat (Z_to_bv 5 22) eq_refl) by lia. apply R22; lia.
    - rewrite F23, OLD2, (EE 23%nat (Z_to_bv 5 23) eq_refl) by lia. apply R22; lia.
    - rewrite F24, OLD2, (EE 24%nat (Z_to_bv 5 24) eq_refl) by lia. apply R22; lia.
    - rewrite F25, OLD2, (EE 25%nat (Z_to_bv 5 25) eq_refl) by lia. apply R22; lia.
    - rewrite F26, OLD2, (EE 26%nat (Z_to_bv 5 26) eq_refl) by lia. apply R22; lia.
    - rewrite F27, OLD2, (EE 27%nat (Z_to_bv 5 27) eq_refl) by lia. apply R22; lia. }
  apply (pcj_finish ly S W regs mem md ch R O Q u lyc Sc Wc memc mdc c ly2 S2 W2 (ms_mem ms2) mdv4 (ms_regs ms2)
    (rec_spill_frees R + EV_XSTRDUP) p (r_state R) (r_code R)
    PRE HFRM HROD HA HOQ HFRS HEV HLIVE HMOK HLEN HARc HAJ Hcs HMLE HBB HJ2).
  + reflexivity.
  + exact KEEPF.
  + exact HPm.
  + exact HFap.
  + exact Hp4096.
  + apply (aval_mem_view SEGS). change 4%nat with (N.to_nat 4). unfold CALL_OFF_FN.
    apply (field_of_region E2 _ 34%nat c _ _ _ _ _ 0 4 (SLit 21) REC_PINS_CLEAR HRsF UC2 ltac:(cbn [In]; tauto));
      [reflexivity | unfold REC_PINS_CLEAR; cbn; lia | cbn; lia].
  + apply (aval_mem_view SEGS). change 4%nat with (N.to_nat 4). unfold CALL_OFF_NARGS.
    apply (field_of_region E2 _ 34%nat c _ _ _ _ _ 4 4 (SLit 1) 1 HRsF UC2 ltac:(cbn [In]; tauto));
      [reflexivity | cbn; lia | cbn; lia].
  + apply (aval_mem_view SEGS). change 8%nat with (N.to_nat 8). unfold CALL_OFF_ARGS.
    apply (field_of_region E2 _ 34%nat c _ _ _ _ _ 8 8 (SOff 52 0) p HRsF UC2 ltac:(cbn [In]; tauto));
      [rewrite pcj_soff0, A52; exact Hp10 | rewrite pcl_pow8; lia | cbn; lia].
  + exact HPXF.
  + apply (aval_mem_view SEGS). change 8%nat with (N.to_nat 8). unfold OFF_STATE.
    apply (field_of_region E2 _ 285%nat A_G_REC _ _ _ _ _ 944 8 (SOff 44 0) _ HRtF UGR2 ltac:(cbn [In]; tauto));
      [rewrite pcj_soff0, OLD2 by lia; exact E44 | rewrite pcl_pow8; exact Rst | cbn; lia].
  + exact Rst.
  + exact MLE2.
  + exact HBB2.
  + exact Hsp2F.
  + exact R1F.
  + exact HP2F.
  + rewrite F10. exact (pcj_sext32_denot E2 43 (r_code R) ltac:(rewrite (OLD2 43%nat ltac:(lia)); exact E43) Rcd).
  + right. split; [exact HRn | split; reflexivity].
Qed.
End e.
End f.

End d.

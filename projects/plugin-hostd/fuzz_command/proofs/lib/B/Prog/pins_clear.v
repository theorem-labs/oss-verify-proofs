(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of pins_clear (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_pins_clear = 0x8cbe8), proving a Theorem Labs lane's tpins_clear_spec
   (lib/B/Prog/pins_clear_c.v) over the callees' statements record_c, arg_s_c, mix_call_c and answer_code_c. The
   tail jump into answer_code (pcb_tail) and the join of the two arms (pcb_finish) are the A walk's pcl_tail and
   pcj_finish (lib/A/Prog/pins_clear_s4.v on a working branch 3cc8391594b), re-derived for B, where record()
   and arg_s() are functions with their own statements instead of inlined code. The runs and calls follow the B
   walk of socket_send (lib/B/Prog/socket_send.v on a working branch a470f91dbfb).

   The walk (B code: lib/B/Prog/pins_clear_aux.v's header):
   - entry: the 32-byte frame; the environment's atoms 32, 33, 34 are g_rec.refuse and g_rec.code as unsigned
     32-bit words and g_rec.state at the entry;
   - 0x8cc00 record(21) (cl_callS_wide, trecord_spec); 0x8cc0c arg_s(slot, uri) (cl_callS_wide, targ_s_spec);
   - after arg_s the region of g_rec (pins_clear_aux.v's pcb_grec) joins the symbolic state, and the run stops at
     the refusal test 0x8cc1c (paj_branch);
   - not refused: 0x8cc30 mix_call(state, slot) (cl_callS_na, tmix_call_spec), the store of g_rec.state, the
     epilogue and the tail jump; refused: the load of g_rec.code, the epilogue and the tail jump;
   - the tail jump at the entry sp: answer_code (PaFx.v's callS_wideF at offset 0, tanswer_code_spec at the
     current fx).
   No report and no UBSan trap in the function (27 instructions, no `jal __asan_report_*`, no unimp / ebreak; the
   only conditional branch, 0x8cc1c, is the refusal test): there is no report or trap edge to refute here.

   Section hypotheses beyond the statement's (TRECORD, TARG_S, TMIX_CALL, TANSWER_CODE, VOBJS), with the names a Theorem Labs lane
   gives them (statements from a Theorem Labs lane 713692f1e0c): HB (a Theorem Labs lane's allocator record), MTL (the meter's laws),
   cmd_sig_prog_PB (the call targets, CmdObj.v), cmd_img_facts_tfib (the pinned image facts, CmdRecImg.v) and PRW
   (CmdRecCells.v's premise, the core's prog_rw). The record facts the walk uses (cmd_prog_img, cmd_ro_prog_apart,
   ROB, RELRO_IMG, cmd_ro_ok_of_aro, cmd_heap_tail_vis, PROG_WRITABLE) are a Theorem Labs lane's lemmas over them, by exact. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdSyms CmdList CmdAddr CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c hand_back_c record_c arg_s_c mix_call_c answer_code_c pins_clear_c pins_clear_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas CmdRecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRo CmdRecCells CmdRecRest.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* --- facts with no machine state ---------------------------------------------------------------------------- *)
Lemma pcb_in_filter : forall (l : list (Z * Z)) (x : Z * Z) (old : Z),
In x (filter (fun pn => fst pn =? old) l) -> In x l /\ fst x = old.
Proof.
intros l x old. induction l as [|y l IH]; intros H; [destruct H|].
cbn in H. destruct (fst y =? old) eqn:E; cbn in H.
- destruct H as [-> | H].
  + split; [left; reflexivity | apply Z.eqb_eq; exact E].
  + destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

(* the slot record() returns: a call of g_rec's table or record.spill (record_c.v rec_slot) *)
Lemma pcb_slot_cases : forall R, (length (r_calls R) <= 16)%nat ->
((length (r_calls R) < 16)%nat /\ rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))) \/
((length (r_calls R) = 16)%nat /\ rec_slot R = A_REC_SPILL).
Proof.
intros R Hl. unfold rec_slot. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
- left. apply Nat.ltb_lt in E. split; [exact E | reflexivity].
- right. apply Nat.ltb_ge in E. split; [lia | reflexivity].
Qed.
Lemma pcb_slot_in : forall R, (length (r_calls R) <= 16)%nat ->
(A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + OFF_ANSWER) \/ rec_slot R = A_REC_SPILL.
Proof.
intros R Hl. destruct (pcb_slot_cases R Hl) as [(H1 & ->) | (_ & ->)]; [left | right; reflexivity].
unfold OFF_CALLS, CALL_SIZE, OFF_ANSWER. lia.
Qed.

(* the call record(fn) put in the slot, as the representation states it *)
Lemma pcb_rep_acall : forall (B : asyms) ly S rd R fn A O,
rec_repA B ly S rd (rec_record R fn A) O -> exists P, acall_at (ablocks B ly S) rd (rec_slot R) (fn, A) P /\
  (forall pn, In pn P -> In pn (ablocks B ly S)).
Proof.
intros B ly S rd R fn A O (Q & HA & _).
pose proof HA as (_ & _ & _ & HC & _).
destruct HC as (Hl16 & HlQ & _ & HCi & HSp & _).
unfold rec_slot. unfold rec_record in *. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
- cbn [set_calls r_calls] in *. rewrite length_app in HlQ. cbn [length] in HlQ.
  destruct (nth_error (l_calls Q) (length (r_calls R))) as [P|] eqn:EP;
    [|apply nth_error_None in EP; lia].
  exists P.
  assert (Ec : nth_error (r_calls R ++ [(fn, A)]) (length (r_calls R)) = Some (fn, A)).
  { rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
  split; [exact (proj1 (HCi _ _ _ Ec EP))|].
  intros pn Hpn. exact (proj1 (pcb_arep_lay_in _ _ _ _ _ Q pn HA (pcb_lay_calls_in Q _ P pn EP Hpn))).
- cbn [set_spill r_spill] in *. exists (l_spill Q). split; [exact HSp|].
  intros pn Hpn. exact (proj1 (pcb_arep_lay_in _ _ _ _ _ Q pn HA (pcb_lay_spill_in Q pn Hpn))).
Qed.

(* the representation, with the recorder's bytes and its blocks' bytes kept *)
Lemma pcb_rep_kept : forall (B : asyms) ly S ly' S' (rd rd' : reader) R O,
rec_repA B ly S rd R O ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) -> rd' a = rd a) ->
(forall pn i, In pn O -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
rec_repA B ly' S' rd' R O.
Proof.
intros B ly S ly' S' rd rd' R O (Q & HA & HOQ) HK HKB Hbl. exists Q. split; [|exact HOQ].
apply (pcb_arep_kept (ablocks B ly S) (ablocks B ly' S') rd rd' R Q HA HK).
- intros pn i Hin Hi. apply HKB; [apply (proj2 (HOQ pn)); exact Hin | exact Hi].
- intros pn Hin. apply Hbl. apply (proj2 (HOQ pn)). exact Hin.
Qed.

(* the recorder's answer pointer word, and its block *)
Lemma pcb_answer_ptr : forall bl rd gr t q, aanswer_at bl rd gr t q ->
aval_mem rd (gr + OFF_ANSWER) 8 (oaddr q) /\ (forall pn, q = Some pn -> In pn bl).
Proof.
intros bl rd gr t q H. destruct t as [x|], q as [pn|]; cbn in H |- *.
- destruct H as (A1 & _ & A3 & _). split; [exact A1|]. intros pn' E. injection E as <-. exact A3.
- destruct H.
- destruct H.
- split; [exact H | intros pn E; discriminate E].
Qed.
Lemma pcb_rep_answer : forall (B : asyms) ly S rd R O, rec_repA B ly S rd R O ->
exists q, aval_mem rd (A_G_REC + OFF_ANSWER) 8 (oaddr q) /\
  (forall pn, q = Some pn -> In pn O /\ In pn (ablocks B ly S) /\ 1 <= snd pn).
Proof.
intros B ly S rd R O (Q & HA & HOQ). exists (l_answer Q).
pose proof HA as (_ & _ & _ & _ & HAN & _).
destruct (pcb_answer_ptr _ _ _ _ _ HAN) as [H1 H2]. split; [exact H1|].
intros pn Hq. assert (HL : In pn (lay_blocks Q)) by exact (pcb_lay_answer_in Q pn Hq).
destruct (pcb_arep_lay_in _ _ _ _ R Q pn HA HL) as [Hin Hs].
split; [apply HOQ; exact HL | split; [exact Hin | exact Hs]].
Qed.

(* the run of the executor keeps every byte its symbolic regions do not write: the frame below the entry sp and
   (from the call of arg_s on) g_rec.state *)
Lemma pcb_keep_run {fx : YK11.FPState} {segs : list Segment} : forall E rs (H : word -> bool) (m m' : word -> option byte) sp0 a,
frame_of E rs (mrestrict H m) (mrestrict H m') ->
Forall (fun r => (YP09.r_base r = Some 2%nat /\ -32 <= YP09.r_wlo r /\ YP09.r_whi r <= 0) \/
  (YP09.r_base r = Some (A_OBJ 44) /\ 944 <= YP09.r_wlo r /\ YP09.r_whi r <= 952)) rs ->
bv_unsigned (ew E 2) = sp0 -> bv_unsigned (ew E (A_OBJ 44)) = A_G_REC ->
0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> ~ (A_G_REC + 944 <= a < A_G_REC + 952) ->
aview segs H m' a = aview segs H m a.
Proof.
intros E rs H m m' sp0 a Hfr Hrs Usp UG Ha H1 H2. apply (aview_eq_of segs). apply Hfr.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
intros (r & Hr & Hw). rewrite Forall_forall in Hrs. destruct (Hrs r Hr) as [(Hb & Hl & Hh) | (Hb & Hl & Hh)];
rewrite Hb in Hw; cbn [base_val] in Hw; [rewrite Usp in Hw | rewrite UG in Hw]; lia.
Qed.
Ltac pcb_rs_ok :=
repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.r_base YP09.r_wlo YP09.r_whi];
first [left; split; [reflexivity | lia] | right; split; [reflexivity | lia]].
Lemma pcb_keep_stack {fx : YK11.FPState} {segs : list Segment} : forall E rs (H : word -> bool) (m m' : word -> option byte) sp0 a,
frame_of E rs (mrestrict H m) (mrestrict H m') ->
Forall (fun r => YP09.r_base r = Some 2%nat /\ -32 <= YP09.r_wlo r /\ YP09.r_whi r <= 0) rs ->
bv_unsigned (ew E 2) = sp0 -> 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) ->
aview segs H m' a = aview segs H m a.
Proof.
intros E rs H m m' sp0 a Hfr Hrs Usp Ha H1. apply (aview_eq_of segs). apply Hfr.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
intros (r & Hr & Hw). rewrite Forall_forall in Hrs. destruct (Hrs r Hr) as (Hb & Hl & Hh).
rewrite Hb in Hw; cbn [base_val] in Hw. rewrite Usp in Hw. lia.
Qed.
Ltac pcb_rs_stack :=
repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; split; [reflexivity | lia].
Ltac pcb_rs_norm HFr :=
lazymatch type of HFr with frame_of _ ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr end.

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
(* the statement's hypotheses (lib/B/Prog/pins_clear_c.v:76-80, a Theorem Labs lane 713692f1e0c) *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis TANSWER_CODE : forall fx0 : YK11.FPState, @tanswer_code_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's hypotheses: the allocator record (a Theorem Labs lane's lib/B/YF0m.v) and the meter's laws, as the A walk carries
   them (lib/A/Prog/pins_clear.v:70-75); the facts a Theorem Labs lane states only at PI := PB_cmd, under the lemma's name, so a
   closing file discharges them by exact: the call targets (CmdObj.v cmd_sig_prog_PB) and the pinned image facts
   (CmdRecImg.v cmd_img_facts_tfib); and CmdRecCells.v's own premise PRW (the core's prog_rw, YCbq.v:1145), the
   writability of g_rec for the store at 0x8cc3c *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @CmdRecBase.cmd_img_facts SK SEGS B0.
Hypothesis PRW : prog_rw SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @CmdRecBase.cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
(* a Theorem Labs lane's record facts over any image (lib/B/Prog/CmdRec{Rest,Ro,Img,Cells}.v, a Theorem Labs lane 713692f1e0c), by exact *)
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart SEGS B LAWS HB IMG.
Let ROB : ro_below_ofl SEGS RLO RHI := CmdRecRo.ROB SEGS B LAWS HB IMG.
Let RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a := CmdRecRo.RELRO_IMG SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md -> arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let PROG_WRITABLE : forall (m : word -> option byte) a, inFP cmd_PG a -> writable_at SEGS m a :=
  CmdRecCells.PROG_WRITABLE SEGS B LAWS HB PRW.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).
Let AWRPG := pcb_awr_PG B HB cmd_prog_img.
Let KH := pcb_kept_heap B cmd_prog_img.
Let ARO := pcb_aro_kept B ROB RELRO_IMG cmd_ro_prog_apart.
Let CKP := pcb_callee_keeps_PG B HB cmd_prog_img.
(* a byte of a live block: below alloc_ceiling and apart from g_rec.state (an image byte, which no heap block holds) *)
Lemma pcb_blk_ok : forall ly S (W : world SEGS) mem md b k i, AR SEGS B ly S W mem md -> In (b, k) (ablocks B ly S) ->
0 <= i < req_size k -> 4096 <= b + i < alloc_ceiling /\ ~ (A_G_REC + 944 <= b + i < A_G_REC + 952).
Proof.
intros ly S W mem md b k i HAR Hin Hi.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b k HAR Hin) as (_ & Hb4 & Hbc & _).
split; [lia|]. intros Hs.
apply (recb_heap_noimg_m B ly S W mem md b k (b + i) HAR Hin ltac:(lia)).
apply cmd_prog_img. apply pcb_in_PG_grec. unfold REC_SIZE. lia.
Qed.

(* --- the footprint and the callees' footprints ---------------------------------------------------------------- *)
Lemma pcb_awr_prog : forall STK sp0 O bl0 blc fr0 lyc own a,
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
awr_byte SEGS B STK sp0 (pcb_FP O) bl0 blc fr0 lyc own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyc own a [Ha | Ha].
- apply AWRPG; [apply pcb_inFP_grec | apply pcb_in_PG_grec]; exact Ha.
- apply AWRPG; [apply pcb_inFP_spill | apply pcb_in_PG_spill]; exact Ha.
Qed.
Lemma pcb_inFP_blk : forall O p n i, In (p, n) O -> 0 <= i < req_size n -> inFP (pcb_FP O) (p + i).
Proof.
intros O p n i Hin Hi. destruct (inFP_ablocks_fp O p n i Hin Hi) as (r & Hr & Hb).
exists r. split; [right; right; exact Hr | exact Hb].
Qed.

(* record()'s footprint (record_c.v:102-103): CmdRecAns' rca_recFP *)
Lemma pcb_rec_awr : forall STK sp0 R O bl0 blc fr0 ly own a, (length (r_calls R) <= 16)%nat ->
(forall pn, In pn O -> In pn blc) ->
inFP (rca_recFP R O) a -> awr_byte SEGS B STK sp0 (pcb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 R O bl0 blc fr0 ly own a Hl HO Ha. unfold rca_recFP in Ha.
apply inFP_cons in Ha as [Ha | Ha].
- apply pcb_awr_prog. left. unfold OFF_NCALLS, REC_SIZE in *. lia.
- apply inFP_cons in Ha as [Ha | Ha].
  + apply pcb_awr_prog. destruct (pcb_slot_in R Hl) as [Hs | Hs].
    * left. unfold OFF_CALLS, CALL_SIZE, OFF_ANSWER, REC_SIZE in *. lia.
    * right. rewrite Hs in Ha. unfold SC_SIZE. lia.
  + destruct (Nat.ltb (length (r_calls R)) 16); [destruct (inFP_nil a Ha)|].
    apply inFP_ablocks_fp_inv in Ha as (p & n & Hin & Hr). right; left. split.
    * replace a with (p + (a - p)) by lia. exact (pcb_inFP_blk O p n (a - p) Hin ltac:(lia)).
    * exists p, n. split; [exact (HO _ Hin) | lia].
Qed.
Lemma pcb_rec_FP_low : forall ly S (W : world SEGS) mem md R O a, AR SEGS B ly S W mem md ->
(length (r_calls R) <= 16)%nat -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
inFP (rca_recFP R O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md R O a HAR Hl HO Ha. pose proof asan_consts as (C1 & _). unfold rca_recFP in Ha.
apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_NCALLS in Ha; lia|].
apply inFP_cons in Ha as [Ha | Ha].
- destruct (pcb_slot_in R Hl) as [Hs | Hs]; [|rewrite Hs in Ha];
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, OFF_ANSWER in *; lia.
- destruct (Nat.ltb (length (r_calls R)) 16); [destruct (inFP_nil a Ha)|].
  apply inFP_ablocks_fp_inv in Ha as (p & n & Hin & Hr).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hin)) as (_ & _ & Hc & _). lia.
Qed.

(* arg_s's footprint (arg_s_c.v:113-116) at the slot c, with no argument yet *)
Definition pcb_arg_FP (c : Z) : list (Z * Z) :=
[(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * Z.of_nat 0, c + CALL_OFF_ARGS + 8 * Z.of_nat 0 + 8)].
Lemma pcb_arg_in : forall R a, (length (r_calls R) <= 16)%nat -> inFP (pcb_arg_FP (rec_slot R)) a ->
(A_G_REC + OFF_CALLS <= a < A_G_REC + OFF_ANSWER) \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.
Proof.
intros R a Hl Ha. unfold pcb_arg_FP, CALL_OFF_NARGS, CALL_OFF_ARGS in Ha. cbn [Z.of_nat] in Ha.
apply inFP_cons in Ha as [Ha | Ha]; [|apply inFP_cons in Ha as [Ha | Ha]; [|destruct (inFP_nil a Ha)]];
destruct (pcb_slot_in R Hl) as [Hs | Hs]; [left | right; rewrite Hs in Ha | left | right; rewrite Hs in Ha];
unfold OFF_CALLS, CALL_SIZE, OFF_ANSWER, SC_SIZE in *; lia.
Qed.
Lemma pcb_arg_awr : forall STK sp0 R O bl0 blc fr0 ly own a, (length (r_calls R) <= 16)%nat ->
inFP (pcb_arg_FP (rec_slot R)) a -> awr_byte SEGS B STK sp0 (pcb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 R O bl0 blc fr0 ly own a Hl Ha. apply pcb_awr_prog.
destruct (pcb_arg_in R a Hl Ha) as [H | H]; [left; unfold OFF_CALLS, OFF_ANSWER, REC_SIZE in *; lia | right; exact H].
Qed.
Lemma pcb_arg_sink : forall R, (length (r_calls R) <= 16)%nat -> ~ YI16.sink_open_fp (pcb_arg_FP (rec_slot R)).
Proof.
intros R Hl. apply sink_closed_pos. unfold pcb_arg_FP.
destruct (pcb_slot_in R Hl) as [Hs | Hs]; [|rewrite Hs];
repeat constructor; cbn [fst]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
Qed.

(* --- the tail jump into answer_code (the A walk's pcl_tail) ------------------------------------------------- *)
Definition pcb_blocks_mid (ly : alayout) (S : astate) (lyc : alayout) (Sc : astate) (O O2 : list (Z * Z)) : Prop :=
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O2) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
(forall pn, In pn O2 -> In pn O \/ ~ In pn (ablocks B ly S)).

(* the post of the statement (pins_clear_c.v:104-117), over the model's argument uri *)
Definition pcb_Q (ly : alayout) (S : astate) (O : list (Z * Z)) (R : rstate) (uri : option (list byte))
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

Lemma pcb_tail : forall ly S (W : world SEGS) regs mem md R O uri ch lyc Sc (Wc : world SEGS) memc mdc k
  (regs2 : bvmap 5 word) R2 O2 old code,
ajournal SEGS B PINS_CLEAR_STK (spZ regs) (pcb_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
afn_pre SEGS B PINS_CLEAR_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
spZ regs2 = spZ regs -> getr regs2 1 = getr regs 1 -> aregs_preserved regs regs2 ->
getr regs2 10 = w64 code -> -2 ^ 31 <= code < 2 ^ 31 ->
rec_repA B lyc Sc (rdW Wc memc) R2 O2 ->
aval_mem (rdW Wc memc) (A_G_REC + OFF_ANSWER) 8 old -> 0 <= old < 2 ^ 64 ->
pcb_blocks_mid ly S lyc Sc O O2 ->
(forall pn, In pn O2 -> fst pn = old -> In pn O /\ In pn (ablocks B lyc Sc)) ->
(forall pn, In pn O2 -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn (ablocks B lyc Sc) -> fst pn = old -> In pn O2) ->
(forall a, inFP (pcb_FP O) a -> a < alloc_ceiling) ->
pins_clear_m R uri = (fst (rec_answer_code R2 code), snd (rec_answer_code R2 code)) ->
arodata_okP SEGS RLO RHI B (rdW Wc memc) -> cmd_ro_ok (rdW Wc memc) ->
Z.of_nat (length (frames Sc)) <= 8 ->
st_nev Sc + EV_ANSWER_CODE <= EV_MAX -> blocks_bytes Sc + LIVE_ANSWER_CODE code <= LIVE_MAX ->
mo_ok MT Sc (XM_ANSWER_CODE MT code) ->
k + EV_ANSWER_CODE <= EV_PINS_CLEAR R ->
blocks_bytes Sc + LIVE_ANSWER_CODE code <= blocks_bytes S + LIVE_PINS_CLEAR R uri ->
mo_le MT S Sc (XM_PINS_CLEAR MT R uri - XM_ANSWER_CODE MT code) ->
SRr SEGS Wc (cfg_at SEGS (BASE + AF_answer_code) regs2 memc mdc)
  (apost_baseF SEGS B PINS_CLEAR_STK (pcb_FP O) regs ly S W mem md (EV_PINS_CLEAR R) (pcb_Q ly S O R uri)).
Proof.
intros ly S W regs mem md R O uri ch lyc Sc Wc memc mdc k regs2 R2 O2 old code
  HJ PRE HFRM Hsp2 R1 HP2 H10 Hcode HREP2 HOLD Hold64 HMID HANS HO2L HOLDNO HFPlo HMODEL HROD HROOK HFR HEV
  HLIVE HMOK Hk HBB HMLE.
assert (WS : PINS_CLEAR_STK = 16592) by (vm_compute; reflexivity).
assert (WA : ANSWER_CODE_STK = 16560) by (vm_compute; reflexivity).
pose proof PRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
rewrite WS in Hslo, Hbot.
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
  intros a Ha. apply KEEPhi; [lia | rewrite WS; lia |]. intros Hfp. pose proof (HFPlo a Hfp). lia. }
assert (R3 : getr regs2 3 = w64 (as_gp B))
  by (etransitivity; [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact Hgp]).
assert (R4 : getr regs2 4 = w64 (as_tp B))
  by (etransitivity; [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact Htp]).
pose proof HREP2 as (Q2 & HA2 & HO2).
(* answer_code runs at the entry sp (offset 0) with the entry ra: PaFx.v's callS_wideF (cl_callS_wide for a callee
   with the FP-existential post apost_baseF) *)
eapply SRr_mono.
{ unfold cfg_at in *.
  eapply (callS_wideF B LAWS Wc regs2 memc _ PINS_CLEAR_STK (spZ regs) (pcb_FP O) ly S W mem md [] lyc Sc mdc k
    ANSWER_CODE_STK
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O2))
    EV_ANSWER_CODE 0 (getr regs2 1) ch _ HJ).
  - rewrite Hsp2. lia.
  - reflexivity.
  - lia.
  - rewrite WA. lia.
  - rewrite WA, WS. lia.
  - exact R3.
  - exact R4.
  - reflexivity.
  - rewrite R1. exact Hra.
  - rewrite R1. exact Hra4.
  - exact HCH.
  - intros HPREa.
    exact (TANSWER_CODE fx lyc Sc Wc regs2 memc mdc ch code old R2 O2 HPREa HFRM HROD HROOK H10 Hcode
      HREP2 HOLD Hold64 HFR HEV HLIVE HMOK).
  - intros a Hfp. apply inFP_cons in Hfp as [Ha | Hfp].
    + apply pcb_awr_prog. left. unfold OFF_ANSWER, REC_SIZE in *. lia.
    + apply inFP_ablocks_fp_inv in Hfp as (p & n & Hin & Hr).
      apply pcb_in_filter in Hin as [Hin Heq]. cbn [fst] in Heq.
      destruct (HANS (p, n) Hin ltac:(cbn [fst]; exact Heq)) as [HinO Hlive].
      right; left.
      split; [replace a with (p + (a - p)) by lia; exact (pcb_inFP_blk O p n (a - p) HinO ltac:(lia))|].
      exists p, n. split; [exact Hlive | lia].
  - intros ly2 S2 W2 regs3 mem2 md2 HK a Hfp Hw Hn. exfalso.
    apply inFP_cons in Hfp as [Ha | Hfp].
    + unfold A_G_REC, OFF_ANSWER in *. lia.
    + apply inFP_ablocks_fp_inv in Hfp as (p & n & Hin & Hr).
      apply pcb_in_filter in Hin as [Hin _].
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc (HO2L (p, n) Hin)) as (_ & _ & Hceil2 & _).
      cbn [fst snd] in Hceil2. lia. }
(* answer_code's post is this call's post *)
cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & HFX' & HCSR' & HJ' & HJ1 & HPR & HK).
destruct HK as (p1 & O' & Hret & Hfresh & Hblocks & HREP' & HO' & HBB' & HMLE').
exists fx', ly', S', regs', mem', md'.
split; [rewrite R1; reflexivity|].
split; [exact HFX'|].
split; [exact HCSR'|].
split; [exact (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' Hk)|].
split; [exact (aregs_preserved_trans _ _ _ HP2 HPR)|].
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
(* --- the meter's costs are nonnegative ----------------------------------------------------------------------- *)
Lemma pcb_xm_xmalloc : forall n, 0 <= XM_XMALLOC MT n.
Proof. intros n. unfold XM_XMALLOC, LIVE_XMALLOC. apply (mo_malloc_nonneg MT MTL). lia. Qed.
Lemma pcb_xm_answer_code : forall c, 0 <= XM_ANSWER_CODE MT c.
Proof.
intros c. unfold XM_ANSWER_CODE, XM_HAND_BACK.
pose proof (pcb_xm_xmalloc (Z.of_nat (length (resp c)) + 1)). pose proof (mo_free_nonneg MT MTL). lia.
Qed.

(* --- the join of the two arms at the tail jump (the A walk's pcj_finish) ------------------------------------ *)
(* From what record(), arg_s() and the arm leave at the jump: the recorder's representation (the new call recorded,
   g_rec.state holding h), its blocks, the answer it still holds (whose pointer word nothing since record() wrote),
   the model's step and the budgets, the tail jump into answer_code gives the statement's post. *)
Lemma pcb_finish : forall ly S (W : world SEGS) regs mem md ch R O u
  ly1 S1 (W1 : world SEGS) mem1 F O1 p lyF SF (WF : world SEGS) memF mdF (regsF : bvmap 5 word) kF h code,
afn_pre SEGS B PINS_CLEAR_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
rec_repA B ly S (rdW W mem) R O ->
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_PINS_CLEAR R <= EV_MAX -> blocks_bytes S + LIVE_PINS_CLEAR R (Some u) <= LIVE_MAX ->
mo_ok MT S (XM_PINS_CLEAR MT R (Some u)) ->
(* record() *)
Permutation (ablocks B ly S) (ablocks B ly1 S1 ++ F) ->
(forall pn, In pn F -> In pn O) ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) ->
rec_repA B ly1 S1 (rdW W1 mem1) (rec_record R REC_PINS_CLEAR []) O1 ->
blocks_bytes S1 <= blocks_bytes S -> mo_le MT S S1 (XM_RECORD MT R) ->
(* arg_s() *)
4096 <= p -> Permutation (ablocks B lyF SF) ((p, Z.of_nat (length u) + 1) :: ablocks B ly1 S1) ->
Forall (fun qk => iv_apart p (Z.of_nat (length u) + 1) (fst qk) (snd qk)) (ablocks B ly1 S1) ->
blocks_bytes SF <= blocks_bytes S1 + LIVE_ARG_S (Some u) -> mo_le MT S1 SF (XM_ARG_S MT (Some u)) ->
(* the jump *)
ajournal SEGS B PINS_CLEAR_STK (spZ regs) (pcb_FP O) ly S W mem md [] lyF SF WF memF mdF kF ->
kF <= EV_RECORD R + EV_ARG_S ->
(forall i, 0 <= i < 8 -> rdW WF memF (A_G_REC + OFF_ANSWER + i) = rdW W1 mem1 (A_G_REC + OFF_ANSWER + i)) ->
rec_repA B lyF SF (rdW WF memF) (set_state (rec_record R REC_PINS_CLEAR [u]) h)
  ((p, Z.of_nat (length u) + 1) :: O1) ->
spZ regsF = spZ regs -> getr regsF 1 = getr regs 1 -> aregs_preserved regs regsF -> getr regsF 10 = w64 code ->
(r_refuse R = 0 /\ h = mixcall (r_state R) REC_PINS_CLEAR [u] /\ code = 0) \/
(r_refuse R <> 0 /\ h = r_state R /\ code = r_code R) ->
SRr SEGS WF (cfg_at SEGS (BASE + AF_answer_code) regsF memF mdF)
  (apost_baseF SEGS B PINS_CLEAR_STK (pcb_FP O) regs ly S W mem md (EV_PINS_CLEAR R) (pcb_Q ly S O R (Some u))).
Proof.
intros ly S W regs mem md ch R O u ly1 S1 W1 mem1 F O1 p lyF SF WF memF mdF regsF kF h code
  PRE HFRM HROD HREP HFRS HEV HLIVE HMOK HPF HFO HO1 HREP1 HBB1 MLE1 Hp4096 HPF2 HFap HBB2 MLE2 HJF HkF HKANS
  HREPF Hsp2 R1 HP2 H10 HMOD.
pose proof PRE as (HAR & _).
pose proof asan_consts as (C1 & _).
pose proof (proj1 HJF) as HARF.
pose proof HJF as (_ & _ & _ & _ & _ & HFRF & HnevF & _).
set (n := Z.of_nat (length u) + 1) in *.
assert (Hn1 : 1 <= n) by (subst n; lia).
pose proof (pcb_rep_O_in B ly S _ R O HREP) as HOlive.
pose proof (pcb_rep_O_in B ly1 S1 _ _ O1 HREP1) as HO1live.
pose proof (recb_ablocks_nodup_m B ly S W mem md HAR) as ND0.
assert (ND1F : List.NoDup (ablocks B ly1 S1 ++ F)) by exact (Permutation_NoDup HPF ND0).
assert (HF1 : forall pn, In pn (ablocks B ly1 S1) -> ~ In pn F)
  by (intros pn H1 H2; exact (list_nodup_app_disj _ _ pn ND1F H1 H2)).
assert (HL1 : forall pn, In pn (ablocks B ly1 S1) -> In pn (ablocks B ly S))
  by (intros pn H; apply (Permutation_in _ (Permutation_sym HPF)); apply in_or_app; left; exact H).
assert (HL0 : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly1 S1) \/ In pn F)
  by (intros pn H; apply in_app_or; exact (Permutation_in _ HPF H)).
assert (HLF : forall pn, In pn (ablocks B lyF SF) <-> pn = (p, n) \/ In pn (ablocks B ly1 S1)).
{ intros pn. split; intros H.
  - apply (Permutation_in _ HPF2) in H. destruct H as [<- | H]; [left; reflexivity | right; exact H].
  - apply (Permutation_in _ (Permutation_sym HPF2)). destruct H as [-> | H]; [left; reflexivity | right; exact H]. }
assert (Hpn : forall pn, In pn (ablocks B ly1 S1) -> pn <> (p, n)).
{ intros pn Hin ->. rewrite Forall_forall in HFap. pose proof (HFap _ Hin) as Hd.
  unfold iv_apart in Hd. cbn [fst snd] in Hd. lia. }
(* the blocks *)
assert (HMID : pcb_blocks_mid ly S lyF SF O ((p, n) :: O1)).
{ split; [|split].
  - intros pn H. apply HLF in H as [-> | H]; [right; left; reflexivity|].
    destruct (in_dec recb_pair_dec pn O) as [HinO | HnO].
    + right. right. apply HO1. split; [exact HinO | exact (HF1 pn H)].
    + left. split; [exact (HL1 pn H) | exact HnO].
  - intros pn H HnO. apply HLF. right. destruct (HL0 pn H) as [H1 | H1]; [exact H1|].
    exfalso. exact (HnO (HFO pn H1)).
  - intros pn [<- | H].
    + destruct (in_dec recb_pair_dec (p, n) O) as [HinO | HnO]; [left; exact HinO|].
      right. intros Hin0. destruct (HL0 _ Hin0) as [H1 | H1]; [exact (Hpn _ H1 eq_refl) | exact (HnO (HFO _ H1))].
    + left. exact (proj1 (proj1 (HO1 pn) H)). }
(* the answer the recorder holds after record(): its pointer word, kept to the jump *)
destruct (pcb_rep_answer B ly1 S1 _ _ O1 HREP1) as (q1 & Vq1 & Hq1).
set (old := oaddr q1).
assert (HOLD : aval_mem (rdW WF memF) (A_G_REC + OFF_ANSWER) 8 old).
{ apply (pcb_aval_mem_kept (rdW W1 mem1)); [exact Vq1|]. intros k Hk. apply HKANS. lia. }
assert (Hold64 : 0 <= old < 2 ^ 64).
{ subst old. destruct q1 as [[a na]|]; cbn [oaddr fst]; [|lia].
  destruct (Hq1 (a, na) eq_refl) as (_ & Hin & _).
  assert (HinF : In (a, na) (ablocks B lyF SF)) by (apply HLF; right; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ a na HARF HinF) as (_ & H4096 & Hc & _ & _ & _ & Hn).
  pose proof (req_size_pos na ltac:(lia)) as [Qn _]. lia. }
assert (Hold_p : old <> p).
{ subst old. destruct q1 as [[a na]|]; cbn [oaddr fst]; [|lia].
  destruct (Hq1 (a, na) eq_refl) as (_ & Hin & Hna). cbn [snd] in Hna.
  intros ->. rewrite Forall_forall in HFap. pose proof (HFap _ Hin) as Hd. unfold iv_apart in Hd.
  cbn [fst snd] in Hd. lia. }
assert (HO2L : forall pn, In pn ((p, n) :: O1) -> In pn (ablocks B lyF SF)).
{ intros pn [<- | H]; apply HLF; [left; reflexivity | right; exact (HO1live pn H)]. }
assert (HANS : forall pn, In pn ((p, n) :: O1) -> fst pn = old -> In pn O /\ In pn (ablocks B lyF SF)).
{ intros pn [<- | H] Hf; [cbn [fst] in Hf; exfalso; exact (Hold_p (eq_sym Hf))|].
  split; [exact (proj1 (proj1 (HO1 pn) H)) | apply HLF; right; exact (HO1live pn H)]. }
assert (HOLDNO : forall pn, In pn (ablocks B lyF SF) -> fst pn = old -> In pn ((p, n) :: O1)).
{ intros pn H Hf. apply HLF in H as [-> | H]; [left; reflexivity|]. right.
  assert (H1 : In pn (ablocks B lyF SF)) by (apply HLF; right; exact H).
  subst old. destruct q1 as [pa|]; cbn [oaddr] in Hf.
  - destruct (Hq1 pa eq_refl) as (HinO1 & Hin & _).
    destruct pn as [a m], pa as [a' m']. cbn [fst] in Hf. subst a'.
    destruct (recb_pair_dec (a, m) (a, m')) as [E | Ne]; [rewrite E; exact HinO1|]. exfalso.
    assert (H2 : In (a, m') (ablocks B lyF SF)) by (apply HLF; right; exact Hin).
    pose proof (sep_blocks SEGS B LAWS lyF SF WF memF mdF a m a m' HARF H1 H2 Ne) as D.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ a m HARF H1) as (_ & _ & _ & _ & _ & _ & Hm).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ a m' HARF H2) as (_ & _ & _ & _ & _ & _ & Hm').
    pose proof (req_size_pos m ltac:(lia)) as [Qm _]. pose proof (req_size_pos m' ltac:(lia)) as [Qm' _].
    unfold zdisjoint in D. cbn [fst snd] in D. lia.
  - exfalso. destruct pn as [a m]. cbn [fst] in Hf. subst a.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ 0 m HARF H1) as (_ & H4096 & _). lia. }
assert (HFPlo : forall a, inFP (pcb_FP O) a -> a < alloc_ceiling).
{ intros a Ha. destruct (pcb_inFP_inv O a Ha) as [HPG | ([q m] & Hin & Hqa)].
  - pose proof (pa_img_range a (cmd_prog_img a HPG)). lia.
  - cbn [fst snd] in Hqa. destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR (HOlive _ Hin)) as (_ & _ & Hc & _). lia. }
(* the model's step *)
assert (HMODEL : pins_clear_m R (Some u) =
  (fst (rec_answer_code (rec_record (set_state R h) REC_PINS_CLEAR [u]) code),
   snd (rec_answer_code (rec_record (set_state R h) REC_PINS_CLEAR [u]) code))).
{ rewrite <- surjective_pairing. exact (pcb_model R u h code HMOD). }
assert (Hsnd : snd (pins_clear_m R (Some u)) = code) by (rewrite HMODEL; reflexivity).
assert (Hcode : -2 ^ 31 <= code < 2 ^ 31).
{ pose proof HREP as (Q0 & HA0 & _). pose proof HA0 as (_ & _ & _ & _ & _ & _ & HSC0 & _).
  pose proof HSC0 as (_ & _ & _ & _ & _ & Rrf & Rcd & _). destruct HMOD as [(_ & _ & ->) | (_ & _ & ->)]; lia. }
rewrite <- pcb_rr_set_state in HREPF.
pose proof (ARO _ _ O ly S W mem md [] lyF SF WF memF mdF kF HJF HAR HOlive HROD) as HRODF.
assert (WEA : EV_ANSWER_CODE = 4) by reflexivity. assert (WEX : EV_ARG_S = 1) by reflexivity.
assert (XMS : XM_PINS_CLEAR MT R (Some u) = XM_RECORD MT R + XM_ARG_S MT (Some u) + XM_ANSWER_CODE MT code)
  by (unfold XM_PINS_CLEAR; rewrite Hsnd; reflexivity).
assert (LVS : LIVE_PINS_CLEAR R (Some u) = LIVE_ARG_S (Some u) + LIVE_ANSWER_CODE code)
  by (unfold LIVE_PINS_CLEAR; rewrite Hsnd; reflexivity).
assert (MLE12 : mo_le MT S SF (XM_RECORD MT R + XM_ARG_S MT (Some u))) by exact (mo_le_trans MT MTL S S1 SF _ _ MLE1 MLE2).
apply (pcb_tail ly S W regs mem md R O (Some u) ch lyF SF WF memF mdF kF regsF
  (rec_record (set_state R h) REC_PINS_CLEAR [u]) ((p, n) :: O1) old code HJF PRE HFRM Hsp2 R1 HP2 H10 Hcode
  HREPF HOLD Hold64 HMID HANS HO2L HOLDNO HFPlo HMODEL HRODF (cmd_ro_ok_of_aro lyF SF WF memF mdF HARF HRODF)).
- rewrite HFRF. exact HFRS.
- unfold EV_PINS_CLEAR in HEV. rewrite WEA, WEX in *. lia.
- rewrite LVS in HLIVE. lia.
- apply (mo_ok_step MT MTL S SF (XM_RECORD MT R + XM_ARG_S MT (Some u)) (XM_ANSWER_CODE MT code)); [|exact MLE12].
  rewrite XMS in HMOK. exact HMOK.
- unfold EV_PINS_CLEAR. rewrite WEA, WEX in *. lia.
- rewrite LVS. lia.
- rewrite XMS. replace (XM_RECORD MT R + XM_ARG_S MT (Some u) + XM_ANSWER_CODE MT code - XM_ANSWER_CODE MT code)
    with (XM_RECORD MT R + XM_ARG_S MT (Some u)) by lia. exact MLE12.
Qed.

(* --- the walk ------------------------------------------------------------------------------------------------ *)
Theorem tpins_clear_holds : tpins_clear_spec B MT.
Proof.
unfold tpins_clear_spec.
intros ly S W regs mem md ch pu u R O PRE HFRM HROD HROOK H10 Hpu HBLK HAP HSTR HLEN HREP HFR HEV HLIVE HMOK.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof PRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : PINS_CLEAR_STK = 16592) by (vm_compute; reflexivity).
assert (WR : RECORD_STK = 16560) by (vm_compute; reflexivity).
assert (WAS : ARG_S_STK = 16464) by (vm_compute; reflexivity).
assert (WM : MIX_CALL_STK = 4192) by (vm_compute; reflexivity).
assert (WEA : EV_ANSWER_CODE = 4) by reflexivity. assert (WEX : EV_ARG_S = 1) by reflexivity.
rewrite WS in Hslo, Hbot.
pose proof (pcb_rep_O_in B ly S _ R O HREP) as HOlive.
pose proof HREP as (Q0 & HA0 & HOQ0).
pose proof HA0 as (_ & _ & _ & HC0 & _ & _ & HSC0 & _).
pose proof HC0 as (Hl16 & _).
pose proof HSC0 as (_ & _ & _ & _ & _ & Rrf & Rcd & _ & Rst & _).
set (rf32 := r_refuse R mod 2 ^ 32). set (cd32 := r_code R mod 2 ^ 32). set (h0 := r_state R).
assert (Rrf32 : 0 <= rf32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
assert (Rcd32 : 0 <= cd32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
(* the argument's block: live, and none of the recorder's *)
destruct HBLK as (q & m & Hqm & Hq1 & Hq2).
assert (HqO : ~ In (q, m) O).
{ intros Hin. rewrite Forall_forall in HAP. pose proof (HAP _ Hin) as Hd. unfold iv_apart in Hd.
  cbn [fst snd] in Hd. lia. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hqm) as (_ & Hq4096 & Hqc & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hqr].
assert (Hmeta : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  0 <= a < alloc_ceiling).
{ intros a Ha. unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha. lia. }
(* ---- the entry: the 32-byte frame, then the call of record(21) at 0x8cc00 ---- *)
pose proof (ajournal_init SEGS B PINS_CLEAR_STK (pcb_FP O) ly S W regs mem md ch PRE) as HJ.
pose proof (pcb_entry W mem regs (map (Z_to_bv 64) [rf32; cd32; h0]) Hal16 ltac:(lia)
  ltac:(intros a Ha; apply Hpres; rewrite WS; lia)) as HS.
unfold cfg_at. change (w64 (BASE + AF_pins_clear)) with (Z_to_bv 64 (BASE + AF_pins_clear)).
remember (Eimg (Ereg regs (map (Z_to_bv 64) [rf32; cd32; h0]))) as E0 eqn:HE0.
assert (HEI0 : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (HAE0 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [rf32; cd32; h0])) E0)
  by (rewrite HE0; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs r).
{ intros n r Hn. rewrite HE0. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E0 32 = Z_to_bv 64 rf32)
  by (rewrite HE0, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 cd32)
  by (rewrite HE0, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 h0)
  by (rewrite HE0, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
clear HE0.
assert (UGR0 : bv_unsigned (ew E0 (A_OBJ 44)) = A_G_REC)
  by (rewrite (HEI0 (A_OBJ 44)) by (unfold A_OBJ, A_TEXT, A_LIM; lia); exact (pcb_grec_val VOBJS)).
assert (Usp0 : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp0 | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia |
    apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr1. rename ms into msA. pcb_rs_norm HFr1.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> rdW W (ms_mem msA) a = rdW W mem a)
  by (intros a Ha Hn; exact (pcb_keep_stack E0 _ (w_H W) mem (ms_mem msA) (spZ regs) a HFr1 ltac:(pcb_rs_stack) Usp0 Ha Hn)).
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10.
assert (EspA : spZ (ms_regs msA) = spZ regs + -32)
  by (unfold spZ at 1; rewrite R2, Usp0; apply unsigned_lit_small; lia).
assert (HREPA : rec_repA B ly S (rdW W (ms_mem msA)) R O).
{ apply (pcb_rep_kept B ly S ly S (rdW W mem) _ R O HREP); [| |exact HOlive].
  - intros a Ha. pose proof (Hmeta a Ha). apply KA; lia.
  - intros [b k] i Hin Hi. cbn [fst snd] in *.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b k HAR (HOlive _ Hin)) as (_ & Hb4 & Hbc & _ & _ & _ & Hk).
    pose proof (req_size_pos k ltac:(lia)) as [_ Hkr]. apply KA; lia. }
pmkst HS. rewrite (rca_sig_record cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs msA) (ms_mem msA) _ PINS_CLEAR_STK (spZ regs) (pcb_FP O) ly S W mem md []
    ly S _ 0 RECORD_STK _ (EV_RECORD R) (-32) (getr (ms_regs msA) 1) ch _ HJ).
  - exact EspA.
  - reflexivity.
  - lia.
  - rewrite WR. lia.
  - rewrite WR, WS. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite R1, unsigned_lit_small by lia. lia.
  - apply (achain_lower ly _ (spZ regs)); [|lia].
    assert (Es0 : s0Z (ms_regs msA) = s0Z regs) by (unfold s0Z; rewrite R8, (EE 8%nat 8%bv eq_refl); reflexivity).
    rewrite Es0. apply (achain_kept ly (rdW W mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
    intros a Ha. apply KA; lia.
  - intros HPREc.
    exact (TRECORD fx ly S W (ms_regs msA) (ms_mem msA) _ ch REC_PINS_CLEAR R O HPREc
      (ARO _ _ O ly S W mem md [] ly S W (ms_mem msA) _ 0 HJ HAR HOlive HROD)
      R10 ltac:(unfold REC_PINS_CLEAR, REC_FN_COUNT; lia) HREPA
      ltac:(unfold EV_PINS_CLEAR in HEV; rewrite WEA, WEX in HEV; lia)
      ltac:(apply (mo_ok_le MT MTL S _ _ HMOK); unfold XM_PINS_CLEAR;
            pose proof (pcb_xm_xmalloc (Z.of_nat (length (sarg (Some u))) + 1));
            pose proof (pcb_xm_answer_code (snd (pins_clear_m R (Some u)))); unfold XM_ARG_S; lia)).
  - intros a Ha. exact (pcb_rec_awr _ _ R O _ _ _ _ _ a Hl16 HOlive Ha).
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw Hn. exfalso.
    pose proof (pcb_rec_FP_low ly S W mem md R O a HAR Hl16 HOlive Ha). lia. }
cbv beta. intros W1 c1 Hwle1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & HJc1 & HP1 & HK1).
destruct HK1 as (F & O1 & R10r & HPF & HlenF & HFO & HREP1 & HO1 & HBB1 & MLE1).
(* back at 0x8cc04: the frame is kept (record's footprint is g_rec, record.spill and the spill's old blocks) *)
jafter_call_keep_pi HS 35%nat regs1 (mrestrict (w_H W1) mem1) HP1 [0]%nat HS1.
match type of HS1 with ?t -> _ => assert (HRK : t); [|specialize (HS1 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; [|apply Forall_nil].
  pose proof HJc1 as (_ & _ & _ & _ & _ & _ & _ & _ & HHI1 & _).
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
  apply (pcb_region_kept_PG E0 W W1 (ms_mem msA) mem1 2 (spZ regs)); [exact Usp0 | |].
  + intros a Ha. apply HHI1; [lia | rewrite WR; lia |].
    intros Hfp. pose proof (pcb_rec_FP_low ly S W mem md R O a HAR Hl16 HOlive Hfp). lia.
  + intros a Ha. apply (apresent_writable SEGS). apply Hpres1. rewrite WS. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS1. rename HS1 into HS. rewrite R1. clear R1 R2 R3 R4 R8 R10.
remember (havoc E0 35 (map (getr regs1) CLOB)) as E1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI0 | cbv; lia]).
assert (OLD1 : forall n, (n < 35)%nat -> ew E1 n = ew E0 n) by (intros n Hn; rewrite HE1; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE1 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [rf32; cd32; h0])) E1)
  by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE0]).
assert (E39 : ew E1 39 = getr regs1 10) by (rewrite HE1; reflexivity).
clear HE1.
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite OLD1 by lia; exact Usp0).
pose proof (proj1 HJ1) as HAR1.
pose proof HREP1 as (Q1 & HA1 & HOQ1).
assert (Hslot : rec_slot R < alloc_ceiling /\ 0 <= rec_slot R)
  by (destruct (pcb_slot_in R Hl16) as [Hs | Hs]; [|rewrite Hs]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, OFF_ANSWER in *; lia).
(* the argument's block outlives record() (it is none of the recorder's, record() frees only the recorder's) *)
assert (Hqm1 : In (q, m) (ablocks B ly1 S1)).
{ destruct (in_app_or _ _ _ (Permutation_in _ HPF Hqm)) as [H | H]; [exact H|]. exfalso. exact (HqO (HFO _ H)). }
(* ---- 0x8cc04 .. 0x8cc0c, then the call of arg_s(slot, uri) ---- *)
paj_run_shc RUNP RUNC HS HJ1.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp1 | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia |
    apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr2. rename ms into msB. rename HJ1 into HJ1r. pcb_rs_norm HFr2.
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> rdW W1 (ms_mem msB) a = rdW W1 mem1 a)
  by (intros a Ha Hn; exact (pcb_keep_stack E1 _ (w_H W1) mem1 (ms_mem msB) (spZ regs) a HFr2 ltac:(pcb_rs_stack) Usp1 Ha Hn)).
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
assert (EspB : spZ (ms_regs msB) = spZ regs + -32)
  by (unfold spZ at 1; rewrite R2, Usp1; apply unsigned_lit_small; lia).
pose proof HJ1r as (_ & _ & _ & _ & _ & HFR1 & Hnev1 & _).
assert (HREPB : rec_repA B ly1 S1 (rdW W1 (ms_mem msB)) (rec_record R REC_PINS_CLEAR []) O1).
{ apply (pcb_rep_kept B ly1 S1 ly1 S1 (rdW W1 mem1) _ _ O1 HREP1); [| |exact (pcb_rep_O_in B ly1 S1 _ _ O1 HREP1)].
  - intros a Ha. pose proof (Hmeta a Ha). apply KB; lia.
  - intros [b k] i Hin Hi. cbn [fst snd] in *.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b k HAR1 (pcb_rep_O_in B ly1 S1 _ _ O1 HREP1 _ Hin))
      as (_ & Hb4 & Hbc & _ & _ & _ & Hk).
    pose proof (req_size_pos k ltac:(lia)) as [_ Hkr]. apply KB; lia. }
pose proof (ARO _ _ O ly S W mem md [] ly1 S1 W1 (ms_mem msB) _ _ HJ1r HAR HOlive HROD) as HRODB.
pmkst HS. rewrite (pcb_sig_arg_s cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W1 (ms_regs msB) (ms_mem msB) _ PINS_CLEAR_STK (spZ regs) (pcb_FP O) ly S W mem md []
    ly1 S1 _ _ ARG_S_STK _ EV_ARG_S (-32) (getr (ms_regs msB) 1) [] _ HJ1r).
  - exact EspB.
  - reflexivity.
  - lia.
  - rewrite WAS. lia.
  - rewrite WAS, WS. lia.
  - rewrite R3, OLD1, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite R4, OLD1, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite R1, unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite R8, E39, R10r. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - intros HPREc.
    exact (TARG_S fx ly1 S1 W1 (ms_regs msB) (ms_mem msB) _ [] (rec_slot R) pu REC_PINS_CLEAR [] (Some u) R O1 HPREc
      HRODB (cmd_ro_ok_of_aro ly1 S1 W1 (ms_mem msB) _ (proj1 HJ1r) HRODB)
      ltac:(rewrite R10, E39; exact R10r)
      ltac:(rewrite R11, OLD1, (EE 10%nat 10%bv eq_refl) by lia; exact H10)
      eq_refl HREPB
      ltac:(left; cbn [astr_argA]; split; [lia|]; split;
            [apply (pcb_rastr_kept (rdW W mem)); [exact HSTR|]; intros i Hi;
             replace (pu + i) with (q + (pu - q + i)) by lia;
             exact (KH _ _ O ly S W mem md [] ly1 S1 W1 (ms_mem msB) _ _ q m (pu - q + i) HJ1r HAR HOlive Hqm HqO Hqm1
               ltac:(lia))
            | split; [lia | left; split; [exists q, m; split; [exact Hqm1 | lia] | constructor]]])
      ltac:(intros x Ex; injection Ex as <-;
            exact (cmd_heap_tail_vis ly1 S1 W1 (ms_mem msB) _ q m (pu + Z.of_nat (length u)) (proj1 HJ1r) Hqm1 ltac:(lia)))
      ltac:(unfold EV_PINS_CLEAR, EV_RECORD in *; rewrite WEA, WEX in *; lia)
      ltac:(unfold LIVE_PINS_CLEAR, LIVE_ANSWER_CODE, LIVE_HAND_BACK, LIVE_ARG_S, LIVE_XMALLOC in *; lia)
      ltac:(apply (mo_ok_step MT MTL S S1 (XM_RECORD MT R) (XM_ARG_S MT (Some u))); [|exact MLE1];
            apply (mo_ok_le MT MTL S _ _ HMOK); unfold XM_PINS_CLEAR;
            pose proof (pcb_xm_answer_code (snd (pins_clear_m R (Some u)))); lia)).
  - intros a Ha. exact (pcb_arg_awr _ _ R O _ _ _ _ _ a Hl16 Ha).
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw Hn. exfalso.
    destruct (pcb_arg_in R a Hl16 Ha) as [H | H]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, OFF_ANSWER, SC_SIZE in H; lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
destruct HK2 as (HBB2 & MLE2 & HK2). destruct HK2 as [(Hsix & _) | (_ & HK2)];
  [unfold REC_ARGS_MAX in Hsix; cbn in Hsix; discriminate Hsix|].
destruct HK2 as (p & HK2). cbv zeta in HK2. cbn [sarg app] in HK2, HBB2, MLE2.
destruct HK2 as (Hp & HPF2 & HFap & HREP2).
(* back at 0x8cc10: the frame is kept (arg_s's footprint is the slot's nargs and args[0]) *)
jafter_call_keep_pi HS 51%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; [|apply Forall_nil].
  pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & HHI2 & _).
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  apply (pcb_region_kept_PG E1 W1 W2 (ms_mem msB) mem2 2 (spZ regs)); [exact Usp1 | |].
  + intros a Ha. apply HHI2; [lia | rewrite WAS; lia |].
    intros Hfp. destruct (pcb_arg_in R a Hl16 Hfp) as [H | H]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, OFF_ANSWER, SC_SIZE in H; lia.
  + intros a Ha. apply (apresent_writable SEGS). apply Hpres2. rewrite WS. lia. }
rewrite R1. clear R1 R2 R3 R4 R8 R10 R11.
remember (havoc E1 51 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS2.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
assert (OLD2 : forall n, (n < 51)%nat -> ew E2 n = ew E1 n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [rf32; cd32; h0])) E2)
  by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
clear HE2.
assert (UGR2 : bv_unsigned (ew E2 (A_OBJ 44)) = A_G_REC)
  by (rewrite (HEI2 (A_OBJ 44)) by (unfold A_OBJ, A_TEXT, A_LIM; lia); exact (pcb_grec_val VOBJS)).
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2, OLD1 by lia; exact Usp0).
pose proof (proj1 HJ2) as HAR2.
(* g_rec's refuse, code and state after arg_s: the entry's (record() and arg_s() write none of them) *)
pose proof HREP2 as (Q2 & HA2 & HOQ2).
pose proof HA2 as (_ & _ & _ & _ & _ & _ & HSC2 & _).
pose proof HSC2 as (Vrf2 & Vcd2 & _ & Vst2 & _).
destruct (pcb_rr_fields R REC_PINS_CLEAR [u]) as (Frf & Fcd & Fst).
rewrite Frf in Vrf2. rewrite Fcd in Vcd2. rewrite Fst in Vst2.
clear HS. pose proof (st_ok_pi_add_region E2 _ _ pcb_grec HS2 eq_refl) as HS.
match type of HS with ?t -> _ => assert (HRK : t); [|specialize (HS HRK); clear HRK] end.
{ unfold region_ok, pcb_grec.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem mkst].
  rewrite UGR2. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|].
  split; [intros o Ho; apply PROG_WRITABLE; exists (A_G_REC, A_G_REC + 960);
    split; [left; reflexivity | cbn [fst snd]; lia]|].
  constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (chunk_ok_val SEGS E2 _ A_G_REC 0 4 (SOff 32 0) rf32);
      [cbn [sv_denot]; rewrite OLD2, OLD1, E32, Z.add_0_r, Z_to_bv_bv_unsigned by lia; reflexivity
      | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia |].
    change (A_G_REC + 0) with (A_G_REC + OFF_REFUSE). change (N.to_nat 4) with 4%nat.
    exact (val_mem_view SEGS (w_H W2) mem2 _ _ _ (pcb_aval_mod _ _ _ Vrf2)).
  - apply (chunk_ok_val SEGS E2 _ A_G_REC 4 4 (SOff 33 0) cd32);
      [cbn [sv_denot]; rewrite OLD2, OLD1, E33, Z.add_0_r, Z_to_bv_bv_unsigned by lia; reflexivity
      | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia |].
    change (A_G_REC + 4) with (A_G_REC + OFF_CODE). change (N.to_nat 4) with 4%nat.
    exact (val_mem_view SEGS (w_H W2) mem2 _ _ _ (pcb_aval_mod _ _ _ Vcd2)).
  - apply (chunk_ok_val SEGS E2 _ A_G_REC 944 8 (SOff 34 0) h0);
      [cbn [sv_denot]; rewrite OLD2, OLD1, E34, Z.add_0_r, Z_to_bv_bv_unsigned by lia; reflexivity
      | change (8 * Z.of_N 8) with 64; lia | change (Z.of_N 8) with 8; lia |].
    change (A_G_REC + 944) with (A_G_REC + OFF_STATE). change (N.to_nat 8) with 8%nat.
    exact (val_mem_view SEGS (w_H W2) mem2 _ _ _ Vst2). }
match type of HS with ?t -> _ => assert (HRK : t); [|specialize (HS HRK); clear HRK] end.
{ cbn [all_disjoint ss_mem]. split; [|exact I]. unfold extent_disjoint, pcb_grec.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UGR2, Usp2. unfold A_G_REC in *. lia. }
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS end.
clear HS2. rewrite <- restrict_mkst_fx in HS.
(* ---- 0x8cc10 .. 0x8cc18: s1 := g_rec, a0 := g_rec.refuse; the refusal test at 0x8cc1c ---- *)
paj_run_shc RUNP RUNC HS HJ2.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply (pcb_awr_cons_grec VOBJS B HB cmd_prog_img); [reflexivity | exact HEI2 | cbn; lia | cbn; unfold REC_SIZE; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact Usp2 | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia |
    apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr3. rename ms into msC. rename HJ2 into HJ2r. pcb_rs_norm HFr3.
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> ~ (A_G_REC + 944 <= a < A_G_REC + 952) ->
  rdW W2 (ms_mem msC) a = rdW W2 mem2 a)
  by (intros a Ha Hn1 Hn2; exact (pcb_keep_run E2 _ (w_H W2) mem2 (ms_mem msC) (spZ regs) a HFr3 ltac:(pcb_rs_ok)
        Usp2 UGR2 Ha Hn1 Hn2)).
assert (H32 : ew E2 32 = Z_to_bv 64 (r_refuse R mod 2 ^ 32)) by (rewrite OLD2, OLD1 by lia; exact E32).
assert (H33 : ew E2 33 = Z_to_bv 64 (r_code R mod 2 ^ 32)) by (rewrite OLD2, OLD1 by lia; exact E33).
assert (H34 : ew E2 34 = Z_to_bv 64 h0) by (rewrite OLD2, OLD1 by lia; exact E34).
assert (H39 : ew E2 39 = w64 (rec_slot R)) by (rewrite OLD2, E39 by lia; exact R10r).
assert (Hstk_lo : alloc_ceiling + 16592 <= spZ regs) by lia.
pose proof (pcb_rep_O_in B ly2 S2 _ _ _ HREP2) as HO2live.
(* the answer pointer word, kept from record()'s return to here: arg_s writes only the slot's nargs and args[0] *)
assert (KAC : forall i, 0 <= i < 8 ->
  rdW W2 (ms_mem msC) (A_G_REC + OFF_ANSWER + i) = rdW W1 mem1 (A_G_REC + OFF_ANSWER + i)).
{ intros i Hi.
  rewrite KC by (unfold A_G_REC, OFF_ANSWER in *; lia).
  rewrite (CKP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A_G_REC + OFF_ANSWER + i) HJc2 (pcb_arg_sink R Hl16)
    ltac:(intros Hfp; destruct (pcb_arg_in R _ Hl16 Hfp) as [H | H];
          unfold A_G_REC, A_REC_SPILL, OFF_ANSWER, OFF_CALLS, SC_SIZE in H; lia)
    ltac:(apply pcb_in_PG_grec; unfold OFF_ANSWER, REC_SIZE; lia)).
  apply KB; unfold A_G_REC, OFF_ANSWER in *; lia. }
psrr_branch_pi RUNP BR HS.
- (* g_rec.refuse = 0, the branch to 0x8cc28 taken: mix_call(state, slot), the store of g_rec.state, the tail jump *)
  pose proof (pcb_br_zero E2 32 (r_refuse R) H32 Rrf Hc) as Hrf0. clear Hc.
  paj_run_shc RUNP RUNC HS HJ2r.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply (pcb_awr_cons_grec VOBJS B HB cmd_prog_img); [reflexivity | exact HEI2 | cbn; lia | cbn; unfold REC_SIZE; lia |].
    eapply awr_ok_cons_stack; [reflexivity | exact Usp2 | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia |
      apply awr_ok_nil]. }
  clear HF HG. rename HFr into HFr4. rename ms into msD. pcb_rs_norm HFr4.
  assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> ~ (A_G_REC + 944 <= a < A_G_REC + 952) ->
    rdW W2 (ms_mem msD) a = rdW W2 mem2 a).
  { intros a Ha Hn1 Hn2. rewrite <- (KC a Ha Hn1 Hn2).
    exact (pcb_keep_run E2 _ (w_H W2) (ms_mem msC) (ms_mem msD) (spZ regs) a HFr4 ltac:(pcb_rs_ok) Usp2 UGR2 Ha Hn1 Hn2). }
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
  assert (EspD : spZ (ms_regs msD) = spZ regs + -32)
    by (unfold spZ at 1; rewrite R2, Usp2; apply unsigned_lit_small; lia).
  pose proof HJ2r as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
  pose proof (ARO _ _ O ly S W mem md [] ly2 S2 W2 (ms_mem msD) _ _ HJ2r HAR HOlive HROD) as HRODD.
  (* the call record() made and arg_s() completed: (21, [u]) in the slot *)
  destruct (pcb_rep_acall B ly2 S2 _ R REC_PINS_CLEAR [u] _ HREP2) as (P & HacP & HPin).
  assert (HacD : acall_at (ablocks B ly2 S2) (rdW W2 (ms_mem msD)) (rec_slot R) (REC_PINS_CLEAR, [u]) P).
  { apply (pcb_acall_at_kept (ablocks B ly2 S2) (ablocks B ly2 S2) (rdW W2 mem2)); [exact HacP | exact HPin | |].
    - intros j Hj. cbn [snd length Z.of_nat] in Hj. unfold CALL_OFF_ARGS in Hj.
      destruct (pcb_slot_in R Hl16) as [Hs | Hs]; [|rewrite Hs];
      apply KD; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, OFF_ANSWER in *; lia.
    - intros [b k] j Hpn Hj. cbn [fst snd] in *.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ b k HAR2 (HPin _ Hpn)) as (_ & _ & _ & _ & _ & _ & Hk).
      pose proof (req_size_pos k ltac:(lia)) as [_ Hkr].
      destruct (pcb_blk_ok ly2 S2 W2 mem2 md2 b k j HAR2 (HPin _ Hpn) ltac:(lia)) as [Hb1 Hb2].
      apply KD; [lia | lia | exact Hb2]. }
  assert (Hslot_cases : (exists i, 0 <= i < REC_CALLS_MAX /\ rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/
    rec_slot R = A_REC_SPILL).
  { destruct (pcb_slot_cases R Hl16) as [(Hlt & ->) | (_ & ->)]; [left | right; reflexivity].
    exists (Z.of_nat (length (r_calls R))). split; [unfold REC_CALLS_MAX; lia | reflexivity]. }
  (* ---- the call of mix_call(state, slot) at 0x8cc30 ---- *)
  pmkst HS. rewrite (pcb_sig_mix_call cmd_sig_prog_PB).
  eapply SRr_bind.
  { eapply (cl_callS_na B LAWS W2 (ms_regs msD) (ms_mem msD) _ PINS_CLEAR_STK (spZ regs) (pcb_FP O) ly S W mem md []
      ly2 S2 _ _ MIX_CALL_STK [] EV_MIX_CALL (-32) (getr (ms_regs msD) 1) _ HJ2r).
    - exact EspD.
    - reflexivity.
    - lia.
    - rewrite WM. lia.
    - rewrite WM, WS. lia.
    - rewrite R3, OLD2, OLD1, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
    - rewrite R4, OLD2, OLD1, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
    - reflexivity.
    - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite R1, unsigned_lit_small by lia. lia.
    - intros HPREc.
      exact (TMIX_CALL fx ly2 S2 W2 (ms_regs msD) (ms_mem msD) _ h0 (rec_slot R) (REC_PINS_CLEAR, [u]) P HPREc HRODD
        ltac:(rewrite R10, H34; reflexivity) Rst ltac:(rewrite R11; exact H39) Hslot_cases HacD
        (cmd_ro_ok_of_aro ly2 S2 W2 (ms_mem msD) _ (proj1 HJ2r) HRODD)
        ltac:(unfold EV_PINS_CLEAR, EV_MIX_CALL in *; lia)).
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & (Hmix10 & Hperm3 & Ely3 & ES3)).
  subst ly3 S3. cbn [fst snd] in Hmix10.
  pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & HHI3 & HBLK3 & _).
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
  pose proof (proj1 HJ3) as HAR3.
  assert (KM : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> rdW W3 mem3 a = rdW W2 (ms_mem msD) a)
    by (intros a Ha; exact (CKP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3 ltac:(apply sink_closed_pos; constructor)
          (inFP_nil a) Ha)).
  (* back at 0x8cc34: g_rec's region and the frame are kept (mix_call writes nothing outside its own frame) *)
  jafter_call_keep_pi HS 67%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1]%nat HS3.
  match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
  { cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
    - apply (pcb_region_kept_PG E2 W2 W3 (ms_mem msD) mem3 285%nat A_G_REC); [exact UGR2 | |].
      + intros a Ha. apply KM. apply pcb_in_PG_grec. unfold REC_SIZE. lia.
      + intros a Ha. apply PROG_WRITABLE. exists (A_G_REC, A_G_REC + 960).
        split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Ha; lia].
    - apply (pcb_region_kept_PG E2 W2 W3 (ms_mem msD) mem3 2 (spZ regs)); [exact Usp2 | |].
      + intros a Ha. apply HHI3; [lia | rewrite WM; lia |]. intros Hfp. exact (inFP_nil a Hfp).
      + intros a Ha. apply (apresent_writable SEGS). apply Hpres3. rewrite WS. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS. rewrite R1. clear R1 R2 R3 R4 R10 R11.
  remember (havoc E2 67 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
  assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
  assert (OLD3 : forall n, (n < 67)%nat -> ew E3 n = ew E2 n)
    by (intros n Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
  assert (HAE3 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [rf32; cd32; h0])) E3)
    by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
  assert (E71 : ew E3 71 = getr regs3 10) by (rewrite HE3; reflexivity).
  clear HE3.
  assert (UGR3 : bv_unsigned (ew E3 (A_OBJ 44)) = A_G_REC)
    by (rewrite (HEI3 (A_OBJ 44)) by (unfold A_OBJ, A_TEXT, A_LIM; lia); exact (pcb_grec_val VOBJS)).
  assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp2).
  (* ---- 0x8cc34 .. 0x8cc50: g_rec.state := the digest, a0 := 0, the epilogue, j answer_code ---- *)
  paj_run_shc RUNP RUNC HS HJ3.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply (pcb_awr_cons_grec VOBJS B HB cmd_prog_img); [reflexivity | exact HEI3 | cbn; lia | cbn; unfold REC_SIZE; lia |].
    eapply awr_ok_cons_stack; [reflexivity | exact Usp3 | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia |
      apply awr_ok_nil]. }
  clear HF HG. rename HFr into HFr5. rename ms into msE. pcb_rs_norm HFr5.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> ~ (A_G_REC + 944 <= a < A_G_REC + 952) ->
    rdW W3 (ms_mem msE) a = rdW W3 mem3 a)
    by (intros a Ha Hn1 Hn2; exact (pcb_keep_run E3 _ (w_H W3) mem3 (ms_mem msE) (spZ regs) a HFr5 ltac:(pcb_rs_ok)
          Usp3 UGR3 Ha Hn1 Hn2)).
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (mdE := m) in *; clearbody mdE end.
  prreg HS (1%bv : bv 5) Rf1. prreg HS (2%bv : bv 5) Rf2. prreg HS (10%bv : bv 5) Rf10.
  (* g_rec.state at the jump: the digest mix_call returned *)
  pose proof (st_ok_region_nth E3 _ _ 0 _ HS eq_refl) as HRf. cbn [ms_mem restrict] in HRf.
  pose proof (field_of_region_any E3 _ 285%nat A_G_REC _ _ _ _ _ 944 8 (SOff 71 0) HRf UGR3
    ltac:(cbn; tauto) ltac:(cbn; lia)) as F944.
  pose proof (mixcall_range h0 REC_PINS_CLEAR [u] Rst) as Hmr.
  assert (D944 : bv_unsigned (sv_denot E3 (SOff 71 0)) mod 2 ^ (8 * Z.of_N 8) = mixcall h0 REC_PINS_CLEAR [u]).
  { cbn [sv_denot]. rewrite E71, Hmix10, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned, Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
    rewrite (Z.mod_small (mixcall h0 REC_PINS_CLEAR [u])) by lia. apply Z.mod_small. lia. }
  rewrite D944 in F944. change (A_G_REC + 944) with (A_G_REC + OFF_STATE) in F944. change (N.to_nat 8) with 8%nat in F944.
  (* the recorder's bytes but g_rec.state, and its blocks' bytes, from arg_s's return to the jump *)
  assert (KREC : forall a, 0 <= a < alloc_ceiling -> ~ (A_G_REC + 944 <= a < A_G_REC + 952) ->
    Exists (in_zr a) TFIB_PROG_STATIC -> rdW W3 (ms_mem msE) a = rdW W2 mem2 a).
  { intros a Ha Hs HP. rewrite KE by lia. rewrite (KM a HP). apply KD; lia. }
  assert (KBLK : forall pn i, In pn ((p, Z.of_nat (length u) + 1) :: O1) -> 0 <= i < snd pn ->
    rdW W3 (ms_mem msE) (fst pn + i) = rdW W2 mem2 (fst pn + i)).
  { intros [b k] i Hpn Hi. cbn [fst snd] in *.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b k HAR2 (HO2live _ Hpn)) as (_ & _ & _ & _ & _ & _ & Hk).
    pose proof (req_size_pos k ltac:(lia)) as [_ Hkr].
    destruct (pcb_blk_ok ly2 S2 W2 mem2 md2 b k i HAR2 (HO2live _ Hpn) ltac:(lia)) as [Hb1 Hb2].
    rewrite KE by lia. rewrite (HBLK3 b k i (HO2live _ Hpn) (HO2live _ Hpn) ltac:(lia) (inFP_nil _)).
    apply KD; lia. }
  assert (HREPF : rec_repA B ly2 S2 (rdW W3 (ms_mem msE))
    (set_state (rec_record R REC_PINS_CLEAR [u]) (mixcall (r_state R) REC_PINS_CLEAR [u]))
    ((p, Z.of_nat (length u) + 1) :: O1)).
  { apply (pcb_rep_state B ly2 S2 ly2 S2 (rdW W2 mem2) _ _ _ _ HREP2 (aval_mem_view SEGS _ _ _ _ _ F944) Hmr).
    - intros a Ha Hs. apply KREC; [pose proof (Hmeta a Ha); lia | unfold OFF_STATE in Hs; lia |].
      destruct Ha as [Ha | Ha]; [apply pcb_in_PG_grec | apply pcb_in_PG_spill]; exact Ha.
    - exact KBLK.
    - exact HO2live. }
  assert (HKANS : forall i, 0 <= i < 8 ->
    rdW W3 (ms_mem msE) (A_G_REC + OFF_ANSWER + i) = rdW W1 mem1 (A_G_REC + OFF_ANSWER + i)).
  { intros i Hi. rewrite <- (KAC i Hi). rewrite KE by (unfold A_G_REC, OFF_ANSWER in *; lia).
    rewrite (KM (A_G_REC + OFF_ANSWER + i) ltac:(apply pcb_in_PG_grec; unfold OFF_ANSWER, REC_SIZE; lia)).
    rewrite KD by (unfold A_G_REC, OFF_ANSWER in *; lia).
    symmetry. apply KC; unfold A_G_REC, OFF_ANSWER in *; lia. }
  rewrite (pcb_sig_answer_code cmd_sig_prog_PB).
  apply (pcb_finish ly S W regs mem md ch R O u ly1 S1 W1 mem1 F O1 p ly2 S2 W3 (ms_mem msE) mdE (ms_regs msE)
    (0 + EV_RECORD R + EV_ARG_S + EV_MIX_CALL) (mixcall (r_state R) REC_PINS_CLEAR [u]) 0
    PRE HFRM HROD HREP HFR HEV HLIVE HMOK HPF HFO HO1 HREP1 HBB1 MLE1 ltac:(lia) HPF2 HFap HBB2 MLE2 HJ3
    ltac:(unfold EV_MIX_CALL; lia) HKANS HREPF).
  + unfold spZ at 1. rewrite Rf2, OLD3, OLD2, OLD1 by lia. rewrite (EE 2%nat 2%bv eq_refl). reflexivity.
  + rewrite Rf1, OLD3, OLD2, OLD1 by lia. exact (EE 1%nat 1%bv eq_refl).
  + exact (aregs_preserved_of_st_ok SEGS (w_H W3) E3 _ msE regs (map (Z_to_bv 64) [rf32; cd32; h0]) HS HAE3
      ltac:(vm_compute; reflexivity)).
  + rewrite Rf10. reflexivity.
  + left. split; [exact Hrf0 | split; reflexivity].
- (* g_rec.refuse <> 0, the branch not taken: a0 := g_rec.code, the epilogue, the tail jump *)
  pose proof (pcb_br_refused E2 32 (r_refuse R) H32 Rrf Hc) as Hrf1. clear Hc.
  paj_run_shc RUNP RUNC HS HJ2r.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply (pcb_awr_cons_grec VOBJS B HB cmd_prog_img); [reflexivity | exact HEI2 | cbn; lia | cbn; unfold REC_SIZE; lia |].
    eapply awr_ok_cons_stack; [reflexivity | exact Usp2 | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia |
      apply awr_ok_nil]. }
  clear HF HG. rename HFr into HFr4. rename ms into msD. pcb_rs_norm HFr4.
  assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> ~ (A_G_REC + 944 <= a < A_G_REC + 952) ->
    rdW W2 (ms_mem msD) a = rdW W2 mem2 a).
  { intros a Ha Hn1 Hn2. rewrite <- (KC a Ha Hn1 Hn2).
    exact (pcb_keep_run E2 _ (w_H W2) (ms_mem msC) (ms_mem msD) (spZ regs) a HFr4 ltac:(pcb_rs_ok) Usp2 UGR2 Ha Hn1 Hn2). }
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (mdD := m) in *; clearbody mdD end.
  prreg HS (1%bv : bv 5) Rf1. prreg HS (2%bv : bv 5) Rf2.
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms (10%bv : bv 5) HS) as Rf10;
    let e := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in change (sr_get (ss_regs ss) (10%bv : bv 5)) with e in Rf10;
    cbn [ms_regs restrict mkst] in Rf10 end.
  (* g_rec.state at the jump: the entry's, unchanged *)
  pose proof (st_ok_region_nth E2 _ _ 0 _ HS eq_refl) as HRf. cbn [ms_mem restrict] in HRf.
  pose proof (field_of_region_any E2 _ 285%nat A_G_REC _ _ _ _ _ 944 8 (SOff 34 0) HRf UGR2
    ltac:(cbn; tauto) ltac:(cbn; lia)) as F944.
  assert (D944 : bv_unsigned (sv_denot E2 (SOff 34 0)) mod 2 ^ (8 * Z.of_N 8) = r_state R).
  { cbn [sv_denot]. rewrite H34, Z.add_0_r. rewrite Z_to_bv_bv_unsigned, Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
    unfold h0. rewrite (Z.mod_small (r_state R)) by lia. apply Z.mod_small. lia. }
  rewrite D944 in F944. change (A_G_REC + 944) with (A_G_REC + OFF_STATE) in F944. change (N.to_nat 8) with 8%nat in F944.
  assert (HREPF : rec_repA B ly2 S2 (rdW W2 (ms_mem msD)) (set_state (rec_record R REC_PINS_CLEAR [u]) (r_state R))
    ((p, Z.of_nat (length u) + 1) :: O1)).
  { apply (pcb_rep_state B ly2 S2 ly2 S2 (rdW W2 mem2) _ _ _ _ HREP2 (aval_mem_view SEGS _ _ _ _ _ F944) Rst).
    - intros a Ha Hs. pose proof (Hmeta a Ha). apply KD; [lia | lia | unfold OFF_STATE in Hs; lia].
    - intros [b k] i Hpn Hi. cbn [fst snd] in *.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ b k HAR2 (HO2live _ Hpn)) as (_ & _ & _ & _ & _ & _ & Hk).
      pose proof (req_size_pos k ltac:(lia)) as [_ Hkr].
      destruct (pcb_blk_ok ly2 S2 W2 mem2 md2 b k i HAR2 (HO2live _ Hpn) ltac:(lia)) as [Hb1 Hb2].
      apply KD; lia.
    - exact HO2live. }
  assert (HKANS : forall i, 0 <= i < 8 ->
    rdW W2 (ms_mem msD) (A_G_REC + OFF_ANSWER + i) = rdW W1 mem1 (A_G_REC + OFF_ANSWER + i)).
  { intros i Hi. rewrite <- (KAC i Hi).
    rewrite KD by (unfold A_G_REC, OFF_ANSWER in *; lia).
    symmetry. apply KC; unfold A_G_REC, OFF_ANSWER in *; lia. }
  rewrite (pcb_sig_answer_code cmd_sig_prog_PB).
  apply (pcb_finish ly S W regs mem md ch R O u ly1 S1 W1 mem1 F O1 p ly2 S2 W2 (ms_mem msD) mdD (ms_regs msD)
    (0 + EV_RECORD R + EV_ARG_S) (r_state R) (r_code R)
    PRE HFRM HROD HREP HFR HEV HLIVE HMOK HPF HFO HO1 HREP1 HBB1 MLE1 ltac:(lia) HPF2 HFap HBB2 MLE2 HJ2r
    ltac:(lia) HKANS HREPF).
  + unfold spZ at 1. rewrite Rf2, OLD2, OLD1 by lia. rewrite (EE 2%nat 2%bv eq_refl). reflexivity.
  + rewrite Rf1, OLD2, OLD1 by lia. exact (EE 1%nat 1%bv eq_refl).
  + exact (aregs_preserved_of_st_ok SEGS (w_H W2) E2 _ msD regs (map (Z_to_bv 64) [rf32; cd32; h0]) HS HAE2
      ltac:(vm_compute; reflexivity)).
  + rewrite Rf10. exact (pcb_sext32_denot E2 33 (r_code R) H33 Rcd).
  + right. split; [exact Hrf1 | split; reflexivity].
Qed.
Print Assumptions tpins_clear_holds.
End e.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_lv2_worker_set (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_sup_lv2_worker_set = 0x8c0cc, 28 instructions, 112 bytes): it proves
   a Theorem Labs lane's `tsup_lv2_worker_set_spec` (lib/B/Prog/sup_lv2_worker_set_c.v; statement from a Theorem Labs lane f490061c104, over
   a Theorem Labs lane c022a2f6a88) in the form of cgif_file_fuzzer's per-function walks: afn_pre at the entry, the symbolic
   executor over the position-abstract listing up to each call (the plain runs of lib/B/Prog/PaCallRun.v, no shadow
   access in the function), the callee contracts of record, arg_s and rec_shape_of (taken at the entry's FP state,
   which these apost_base callees keep) through cl_callS_wide / cl_callS_na (lib/B/Prog/PaNoChain.v), and answer's
   FP-existential post (apost_baseF) through PaFx.callS_wideF at the tail jump, which is this function's
   apost_baseF. The frame chains (pass 5, no astack_pres): s0 = worker (a heap pointer) at the four program calls,
   achain_low; at the tail jump s0 and sp are the entry's, afn_pre's chain moved by achain_kept / achain_ly_top.
   It is the B re-walk of the A walk
   lib/A/Prog/sup_lv2_worker_set.v + _s0 .. _s3 (a working branch 5c647899d9f), whose rec_shape_of call,
   tail call of answer and post assembly (sup_lv2_worker_set_s2.v slw_D2 / slw_D3) it follows; B calls record and
   arg_s where A inlines them, so A's segments A, B and s3 become one contract step each. The Generation-N B walk
   lib/B/Prog/sup_lv2_worker_set.v on a working branch 543f2c3645b (template only, not ported) cuts the same
   code at the same return addresses.

   B code (MEASURED from the pinned fuzz_command.asan-ubsan with pyelftools and capstone, symbol-keyed; a Theorem Labs lane's
   gen/dis/sup_lv2_worker_set.s): a 32-byte frame (ra, s0, s1, s2), `mv s0,a1` (worker), `mv s1,a0` (uri);
   record(15) at 0x8c0ec (ret 0x8c0f0), `mv s2,a0` (the slot); arg_s(slot, uri) at 0x8c0f8; arg_s(slot, worker) at
   0x8c104; rec_shape_of(.str.13 = 0x21ee0, 14) at 0x8c114 (the listing's `PHi 10 176; PAddHi 10 10 176 (A_OBJ 75) 0`
   at 0x8c108: a0 = the literal's address, nothing is loaded or stored through the auipc base); the epilogue and the
   tail jump `j answer` (0x8c138) with a0 = slot, a1 = the shape, a2 = 1, at the entry sp.
   Report / trap edges: none. The function has no branch, no `unimp`/`ebreak`, no call to any of the 24
   __asan_report_* entries and 0 UBSan trap sites (a Theorem Labs lane's gen/traps.B.summary); its checks are its callees'
   (record 4, arg_s 5, answer 5 trap sites, rec_shape_of 2 inline checks), refuted in their own walks, whose
   contracts this walk uses. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_lv2_worker_set.v, with its module names and numbers changed; 801 of its 959 lines of code are new or changed and 946 lines of the source are left out. *)
(* The ASan+UBSan walk of sup_pin_accept (plugin-hostd/fuzz_command, image fuzz_command.asan-ubsan, entry
   BASE + AF_sup_pin_accept = 0x8be78): it proves a Theorem Labs lane's `tsup_pin_accept_spec` (lib/B/Prog/sup_pin_accept_c.v,
   statement from a Theorem Labs lane 713692f1e0c) in the form of cgif_file_fuzzer's per-function walks: afn_pre at the entry, the
   symbolic executor over the position-abstract listing up to each call, the callee contracts record_c, arg_s_c and
   rec_shape_of_c at the three calls (cl_callS_wide, cl_callS_na; each callee contract taken at the entry's FP state,
   which those apost_base callees keep), answer_c at the tail jump (PaFx.v's callS_wideF at this function's entry
   sp, answer's post being FP-existential), and apost_baseF at the end. Pass 5: no presence of the stack up to
   ly_top is assumed; the callees' frame chains are achain's empty case at record and arg_s (s0 = uri, a heap
   address below alloc_ceiling) and afn_pre's own chain at the tail jump (s0 restored).

   It is the B re-walk of the A walk lib/A/Prog/sup_pin_accept.v (a working branch 6293aadbb38, with
   its halves sup_pin_accept_s4.v / _s2.v and the recorder lemmas of sup_pin_accept_r.v), at B's code
   (lib/B/Prog/sup_pin_accept_aux.v; 22 instructions, 0x8be78 .. 0x8bed0, listing CmdList.v:5793-5814):
   - prologue (32-byte frame, ra s0 s1 saved); `mv s0,a0`; `li a0,13`; `jal record` (0x8be90);
   - `mv s1,a0`; `mv a1,s0`; `jal arg_s` (0x8be9c);
   - the verb "pin_accept" by auipc/addi (listing object 72, 0x21ea0); `li a1,10`; `jal rec_shape_of` (0x8beac);
   - `li a2,1`; `mv a1,a0`; `mv a0,s1`; the frame restored; `j answer` (0x8becc).
   A inlines record() (with its spill arm through rec_calls_free and two ASan checks) and xstrdup (with two more
   checks); B calls record and arg_s, which carry those checks. B's code has no conditional branch, no
   `jal __asan_report_*` and no `unimp`: there is no report or UBSan trap edge in this function (measured with
   capstone on the pinned image, sha256 658cefbe...df401; the statement's header agrees: gen/funcs.tsv 0 reports,
   gen/traps.B.summary 0 trap sites). The Generation-N walk of the same B code (a working branch 543f2c3645b
   lib/B/Prog/sup_pin_accept.v) is a template only, not ported.

   The recorder lemmas of the A walk's sup_pin_accept_r.v / _s2.v are restated here for B (module paths, B's
   addresses, prefix spb_). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdChk CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_calls_free_c mix_call_c hand_back_c record_c arg_s_c rec_shape_of_c answer_c sup_pin_accept_c sup_pin_accept_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecRo CmdRecRest CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas CmdRecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the recorder's representation read through a later state (A walk sup_pin_accept_r.v, for B) ---- *)

(* the footprint of sup_pin_accept's contract (sup_pin_accept_c.v, apost_base's list) *)
Definition spb_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

(* the bytes the representation reads besides the recorder's blocks: g_rec and record.spill *)
Definition spb_in_rec (a : Z) : Prop := A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.

(* every block of O is still live in bl' and keeps its bytes *)
Definition spb_keepsO (rd rd' : reader) (bl' : list (Z * Z)) (O : list (Z * Z)) : Prop :=
  forall pn, In pn O -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i).

Lemma spb_aval_mem_keep : forall rd rd' a n v,
  aval_mem rd a n v -> (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma spb_abytes_keep : forall rd rd' a l,
  abytes_atR rd a l -> (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

Lemma spb_astr_keep : forall rd rd' p s,
  astr_atR rd p s -> (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H Hn] K. split; [|exact Hn].
  apply (spb_abytes_keep rd); [exact H|]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply K. lia.
Qed.

Lemma spb_blk_keep_at : forall (rd rd' : reader) p n x,
  (forall i, 0 <= i < n -> rd' (p + i) = rd (p + i)) -> p <= x < p + n -> rd' x = rd x.
Proof. intros rd rd' p n x K Hx. replace x with (p + (x - p)) by lia. apply K. lia. Qed.

Lemma spb_acall_keep : forall bl bl' rd rd' a c P,
  acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hk) K KP.
  unfold acall_at. unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  split; [exact Hfn|]. split; [exact Hn|]. split; [exact Hl|].
  split; [apply (spb_aval_mem_keep rd); [exact Hb0 | intros x Hx; apply K; lia]|].
  split; [apply (spb_aval_mem_keep rd); [exact Hb1 | intros x Hx; apply K; lia]|].
  split; [exact Hnd|].
  intros k s pn Es Ep. destruct (Hk k s pn Es Ep) as (Hs & Hp0 & Hin & Hsz & Hstr).
  assert (Hkl : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  destruct (KP pn (nth_error_In P k Ep)) as [Hin' Kp].
  split; [apply (spb_aval_mem_keep rd); [exact Hs | intros x Hx; apply K; lia]|].
  split; [exact Hp0|]. split; [exact Hin'|]. split; [exact Hsz|].
  apply (spb_astr_keep rd); [exact Hstr|]. intros x Hx.
  apply (spb_blk_keep_at rd rd' (fst pn) (snd pn)); [exact Kp | lia].
Qed.

Lemma spb_aanswer_keep : forall bl bl' rd rd' gr t q,
  aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  aanswer_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q HA K KQ. revert HA KQ. unfold aanswer_at.
  destruct t as [s|]; destruct q as [pn|]; intros HA KQ; try contradiction.
  - destruct HA as (N1 & N2 & N3 & N4 & N5 & N6).
    destruct (KQ pn (or_introl eq_refl)) as [Kin Kp].
    split; [apply (spb_aval_mem_keep rd); [exact N1 | intros y Hy; apply K; lia]|].
    split; [exact N2|]. split; [exact Kin|]. split; [exact N4|]. split; [|exact N6].
    apply (spb_astr_keep rd); [exact N5|]. intros y Hy.
    apply (spb_blk_keep_at rd rd' (fst pn) (snd pn)); [exact Kp | lia].
  - apply (spb_aval_mem_keep rd); [exact HA | intros y Hy; apply K; lia].
Qed.

Lemma spb_areply_keep : forall bl bl' rd rd' gr t q,
  areply_at bl rd gr t q ->
  (forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY_SIZE + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  areply_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q HP K KQ. revert HP KQ. unfold areply_at. unfold OFF_REPLY, OFF_REPLY_SIZE in *.
  destruct t as [s|]; destruct q as [pn|]; intros HP KQ; try contradiction.
  - destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    destruct (KQ pn (or_introl eq_refl)) as [Kin Kp].
    split; [apply (spb_aval_mem_keep rd); [exact P1 | intros y Hy; apply K; lia]|].
    split; [apply (spb_aval_mem_keep rd); [exact P2 | intros y Hy; apply K; lia]|].
    split; [exact P3|]. split; [exact P4|]. split; [exact Kin|]. split; [exact P6|]. split; [|exact P8].
    apply (spb_abytes_keep rd); [exact P7|]. intros y Hy.
    apply (spb_blk_keep_at rd rd' (fst pn) (snd pn)); [exact Kp | lia].
  - destruct HP as [P1 P2].
    split; [apply (spb_aval_mem_keep rd); [exact P1 | intros y Hy; apply K; lia]|].
    apply (spb_aval_mem_keep rd); [exact P2 | intros y Hy; apply K; lia].
Qed.

Lemma spb_ag1_scalars_keep : forall rd rd' gr R,
  ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960 -> rd' x = rd x) ->
  ag1_scalars rd' gr R.
Proof.
  intros rd rd' gr R HX K. unfold ag1_scalars in *. unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  destruct HX as (X1 & X2 & X3 & X4 & X5 & X6).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  - apply (spb_aval_mem_keep rd); [exact X1 | intros x Hx; apply K; lia].
  - apply (spb_aval_mem_keep rd); [exact X2 | intros x Hx; apply K; lia].
  - apply (spb_aval_mem_keep rd); [exact X3 | intros x Hx; apply K; lia].
  - apply (spb_aval_mem_keep rd); [exact X4 | intros x Hx; apply K; lia].
  - apply (spb_aval_mem_keep rd); [exact X5 | intros x Hx; apply K; lia].
Qed.

Lemma spb_acall_in : forall bl rd a c P pn, acall_at bl rd a c P -> In pn P -> In pn bl /\ fst pn <> 0.
Proof.
  intros bl rd a c P pn (_ & _ & Hl & _ & _ & _ & Hk) Hin.
  destruct (In_nth_error P pn Hin) as [k Ek].
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- Hl; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (Hk k s pn Es Ek) as (_ & H0 & H1 & _). split; assumption.
Qed.

Lemma spb_arep_in : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> In pn bl /\ fst pn <> 0.
Proof.
  intros bl rd gr sc R Q pn (_ & _ & _ & HC & HA & HP & _ & _) Hin.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP0 & Hpn).
    destruct (In_nth_error _ _ HP0) as [i Ei].
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    exact (spb_acall_in _ _ _ _ _ _ (proj1 (C4 i c P Ec Ei)) Hpn).
  - apply in_app_or in Hin as [Hin|Hin]; [exact (spb_acall_in _ _ _ _ _ _ C5 Hin)|].
    apply in_app_or in Hin as [Hin|Hin].
    + revert HA Hin. unfold aanswer_at.
      destruct (r_answer R); destruct (l_answer Q) as [pn'|]; intros HA Hin; cbn [oblk In] in Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HA as (_ & H0 & H1 & _). split; assumption.
    + revert HP Hin. unfold areply_at.
      destruct (r_reply R); destruct (l_reply Q) as [pn'|]; intros HP Hin; cbn [oblk In] in Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HP as (_ & _ & H0 & _ & H1 & _). split; assumption.
Qed.

Lemma spb_arep_keep : forall bl bl' rd rd' R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (forall a, spb_in_rec a -> rd' a = rd a) ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
  intros bl bl' rd rd' R Q (H1 & H2 & H3 & HC & HA & HP & HX & HW) K KQ.
  unfold arep_at. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split.
  { destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
    refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    - apply (spb_aval_mem_keep rd); [exact C3 | intros x Hx; apply K; unfold spb_in_rec, OFF_NCALLS, REC_SIZE in *; lia].
    - intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (spb_acall_keep bl bl' rd rd' _ c P Hc).
      + intros x Hx. apply K. unfold spb_in_rec, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
      + intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
        exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    - apply (spb_acall_keep bl bl' rd rd' _ _ _ C5).
      + intros x Hx. apply K. unfold spb_in_rec, CALL_SIZE, SC_SIZE in *. lia.
      + intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
  split.
  { apply (spb_aanswer_keep bl bl' rd rd' A_G_REC _ _ HA).
    - intros x Hx. apply K. unfold spb_in_rec, OFF_ANSWER, REC_SIZE in *. lia.
    - intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
  split.
  { apply (spb_areply_keep bl bl' rd rd' A_G_REC _ _ HP).
    - intros x Hx. apply K. unfold spb_in_rec, OFF_REPLY, OFF_REPLY_SIZE, REC_SIZE in *. lia.
    - intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
  split; [|exact HW].
  apply (spb_ag1_scalars_keep rd rd' A_G_REC R HX). intros x Hx. apply K. unfold spb_in_rec, REC_SIZE. lia.
Qed.

(* a member of a filtered list is a member of the list (the filter answer_c.v's footprint uses) *)
Lemma spb_filter_in : forall (old : Z) (l : list (Z * Z)) x, In x (filter (fun pn => fst pn =? old) l) -> In x l.
Proof.
intros old l x. induction l as [|a l IH]; intros H; cbn in H; [exact H|].
repeat match type of H with context [match ?d with left _ => _ | right _ => _ end] => destruct d end;
repeat match type of H with context [if ?b then _ else _] => destruct b end;
first [ destruct H as [<- | H]; [left; reflexivity | right; exact (IH H)] | right; exact (IH H) ].
Qed.

(* the block bookkeeping of the post, over the block lists of the entry (bl0), after record (blc), answer's entry
   (bl3, after arg_s's fresh block pnew) and the end (bl5), from answer's post (its fresh blocks p1, p2 are none of
   answer's entry blocks other than the freed old answer's) *)
Lemma spb_post_lists : forall (bl0 blc bl3 bl5 O O1 O' : list (Z * Z)) pnew p1 p2 (old : Z),
(forall pn, In pn bl0 -> ~ In pn O -> In pn blc) ->
(forall pn, In pn blc -> In pn bl0) ->
(forall pn, In pn O1 -> In pn O) ->
(forall pn, In pn O -> In pn blc -> In pn O1) ->
(forall pn, In pn O1 -> In pn blc) ->
~ In pnew blc ->
(forall pn, In pn bl3 <-> pn = pnew \/ In pn blc) ->
(forall pn, In pn bl3 -> fst pn <> old -> pn <> p1 /\ pn <> p2) -> p1 <> p2 ->
(forall pn, In pn bl5 <-> (In pn bl3 /\ fst pn <> old) \/ pn = p1 \/ pn = p2) ->
(forall pn, In pn O' <-> (In pn (pnew :: O1) /\ fst pn <> old) \/ pn = p1) ->
(forall pn, In pn bl3 -> fst pn = old -> In pn (pnew :: O1)) ->
(forall pn, In pn O' -> In pn bl0 -> In pn O) /\
In p2 bl5 /\
(In p2 bl0 -> In p2 O) /\
(forall pn, In pn bl0 -> ~ In pn O -> pn <> p2) /\
~ In p2 O' /\ (forall pn, In pn O' -> In pn bl5) /\
(forall pn, In pn bl0 -> ~ In pn O -> In pn bl5) /\
(forall pn, In pn bl5 -> (In pn bl0 /\ ~ In pn O) \/ In pn O' \/ pn = p2).
Proof.
intros bl0 blc bl3 bl5 O O1 O' pnew p1 p2 old HB2 HB1 HO1 HO2 HO1c Hnew H3 Hfold H12 H5 HO' Hold.
assert (Hdec : forall pn (l : list (Z * Z)), In pn l \/ ~ In pn l)
  by (intros pn l; destruct (in_dec (fun x y : Z * Z => decide (x = y)) pn l); tauto).
assert (K : forall pn, In pn bl0 -> ~ In pn O -> fst pn <> old).
{ intros pn H0 HnO Eo. assert (H3' : In pn bl3) by (apply H3; right; exact (HB2 _ H0 HnO)).
  pose proof (Hold _ H3' Eo) as Hin. destruct Hin as [E | Hin].
  - subst pn. exact (Hnew (HB2 _ H0 HnO)).
  - exact (HnO (HO1 _ Hin)). }
assert (HO2in : forall pn, In pn (pnew :: O1) -> In pn bl3).
{ intros pn [<- | Hin]; apply H3; [left; reflexivity | right; exact (HO1c _ Hin)]. }
assert (L3 : forall pn, In pn bl0 -> ~ In pn O -> pn <> p2).
{ intros pn H0 HnO. assert (H3' : In pn bl3) by (apply H3; right; exact (HB2 _ H0 HnO)).
  exact (proj2 (Hfold _ H3' (K _ H0 HnO))). }
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- intros pn Hpn H0. destruct (Hdec pn O) as [HO|HnO]; [exact HO|]. exfalso.
  apply HO' in Hpn as [(Hin & Hne) | ->].
  + destruct Hin as [<- | Hin]; [exact (Hnew (HB2 _ H0 HnO)) | exact (HnO (HO1 _ Hin))].
  + assert (H3' : In p1 bl3) by (apply H3; right; exact (HB2 _ H0 HnO)).
    exact (proj1 (Hfold _ H3' (K _ H0 HnO)) eq_refl).
- apply H5. right; right. reflexivity.
- intros H0. destruct (Hdec p2 O) as [HO|HnO]; [exact HO|]. exfalso. exact (L3 _ H0 HnO eq_refl).
- exact L3.
- intros Hin. apply HO' in Hin as [(Hin & Hne) | E]; [|exact (H12 (eq_sym E))].
  exact (proj2 (Hfold _ (HO2in _ Hin) Hne) eq_refl).
- intros pn Hpn. apply HO' in Hpn as [(Hin & Hne) | ->]; apply H5;
  [left; split; [exact (HO2in _ Hin) | exact Hne] | right; left; reflexivity].
- intros pn H0 HnO. apply H5. left. split; [apply H3; right; exact (HB2 _ H0 HnO) | exact (K _ H0 HnO)].
- intros pn Hpn. apply H5 in Hpn as [(Hin3 & Hne) | [-> | ->]].
  + apply H3 in Hin3 as [-> | Hc].
    * right; left. apply HO'. left. split; [left; reflexivity | exact Hne].
    * destruct (Hdec pn O) as [HinO | HnO].
      -- right; left. apply HO'. left. split; [right; exact (HO2 _ HinO Hc) | exact Hne].
      -- left. split; [exact (HB1 _ Hc) | exact HnO].
  + right; left. apply HO'. right. reflexivity.
  + right; right. reflexivity.
Qed.

(* the slot record() returns lies in g_rec's call table or is record.spill *)
Lemma spb_slot_in_rec : forall R a, (length (r_calls R) <= 16)%nat ->
  rec_slot R <= a < rec_slot R + CALL_SIZE -> spb_in_rec a.
Proof.
intros R a HL Ha. unfold rec_slot in Ha. unfold spb_in_rec.
destruct (Nat.ltb (length (r_calls R)) 16) eqn:Elt.
- apply Nat.ltb_lt in Elt. left. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
- right. unfold CALL_SIZE, SC_SIZE in *. lia.
Qed.

Lemma spb_slot_range : forall R, (length (r_calls R) <= 16)%nat -> 0x5e32c0 <= rec_slot R <= 0x5e3760.
Proof.
intros R HL. unfold rec_slot. destruct (Nat.ltb (length (r_calls R)) 16) eqn:Elt.
- apply Nat.ltb_lt in Elt. unfold A_G_REC, OFF_CALLS, CALL_SIZE. lia.
- unfold A_REC_SPILL. lia.
Qed.

Lemma spb_in_recPG : forall a, spb_in_rec a -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a [Ha | Ha]; apply Exists_exists.
- exists (A_G_REC, REC_SIZE). split; [left; reflexivity | unfold in_zr; cbn [fst snd]; exact Ha].
- exists (A_REC_SPILL, SC_SIZE). split; [right; left; reflexivity | unfold in_zr; cbn [fst snd]; exact Ha].
Qed.

(* the symbolic state at the entry: the 32-byte frame the prologue writes; atom 2 is the entry sp *)
Definition spb_facts0 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition spb_entry : sstate := mkSS AF_sup_pin_accept sr_atoms [stack_region 32] None spb_facts0.

(* cgif's region_kept over aview for a region whose window bytes stay present (the socket_send walk's
   ss_region_kept_hi2): the call's world may grow *)
Lemma spb_region_kept_hi2 {fx : YK11.FPState} : forall (segs : list Segment) E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview segs H2 m2 a = aview segs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept segs E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros segs E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav. exact Ha.
- intros _. apply (apresent_writable segs). apply Hp. exact Ha.
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

Section r. Variable B : asyms.
(* the representation survives any change outside g_rec, record.spill and the recorder's blocks *)
Lemma spb_rep_keep : forall ly S rd ly' S' rd' R O,
  rec_repA B ly S rd R O -> (forall a, spb_in_rec a -> rd' a = rd a) -> spb_keepsO rd rd' (ablocks B ly' S') O ->
  rec_repA B ly' S' rd' R O.
Proof.
  intros ly S rd ly' S' rd' R O (Q & HR & HO) K KO. unfold spb_keepsO in KO.
  exists Q. split; [|exact HO].
  apply (spb_arep_keep _ _ rd rd' R Q HR K). intros pn Hpn. apply KO. apply HO. exact Hpn.
Qed.

Lemma spb_rep_blocks : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O ->
  In pn (ablocks B ly S) /\ fst pn <> 0 /\ iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE.
Proof.
  intros ly S rd R O (Q & HR & HO) pn Hpn. apply HO in Hpn.
  destruct (spb_arep_in _ _ _ _ _ _ pn HR Hpn) as [H1 H2].
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & (_ & HAP)).
  destruct (HAP pn Hpn) as [H3 H4]. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma spb_rep_answer : forall ly S rd R O, rec_repA B ly S rd R O ->
  exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\ (old = 0 \/ exists pn, In pn O /\ fst pn = old).
Proof.
  intros ly S rd R O (Q & HR & HO).
  pose proof HR as (_ & _ & _ & _ & HA & _).
  revert HA. unfold aanswer_at.
  destruct (r_answer R) as [t|]; destruct (l_answer Q) as [pn|] eqn:EA; intros HA; try contradiction.
  - destruct HA as (N1 & _). exists (fst pn). split; [exact N1|]. right. exists pn. split; [|reflexivity].
    apply HO. unfold lay_blocks. rewrite EA. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    left. reflexivity.
  - exists 0. split; [exact HA | left; reflexivity].
Qed.

Lemma spb_rep_ncalls : forall ly S rd R O, rec_repA B ly S rd R O -> (length (r_calls R) <= 16)%nat.
Proof. intros ly S rd R O (Q & (_ & _ & _ & (HL & _) & _) & _). exact HL. Qed.
End r.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's callee contracts (sup_pin_accept_c.v, Section e; pass 4b: each holds at every FP state) *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses: HB, the allocator record (lib/B/YF0m.v, Record CmdBSyms); MTL, the meter's laws;
   cmd_sig_prog_PB, the call target of every program function (lib/B/Prog/CmdObj.v cmd_sig_prog), which a Theorem Labs lane proves
   only at PI := PB_cmd (CmdRecRest.v cmd_sig_prog_PB), so it is a Section hypothesis under that lemma's name.
   LAWS is not a hypothesis: AR_laws_ok (lib/Reusable/YG0q.v) proves it. *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
(* the per-binary record facts: a Theorem Labs lane's B CmdRecFacts groups (a working branch 713692f1e0c). Their lemmas are
   stated for any segments and allocator record, from AR's laws (LAWS), HB and the image facts
   IMG : cmd_img_facts segs B, so the walk uses them by exact: CmdRecRest.cmd_prog_img (:65),
   CmdRecRest.cmd_ro_prog_apart (:56), CmdRecRo.ROB (:73), CmdRecRo.RELRO_IMG (:64), CmdRecRo.cmd_ro_ok_of_aro
   (:88), CmdRecRo.CMD_RO_IN (:56), and CmdRecImg.cmd_heap_tail_vis (:34, from LAWS and HB alone). The image facts
   are proved at the concrete image (CmdRecImg.v:68 cmd_img_facts_tfib, over tfibsegs and YE2k.tfib_sink_head);
   this walk is over an abstract PAImg and sink head, so it takes that lemma as a named hypothesis with its name
   and form (SEGS and SK in place of tfibsegs and tfib_sink_head), which a closing file discharges by exact. *)
Hypothesis cmd_img_facts_tfib : forall B, CmdBSyms B -> CmdRecBase.cmd_img_facts SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : CmdRecBase.cmd_img_facts SEGS B := cmd_img_facts_tfib B HB.
Let cmd_prog_img := CmdRecRest.cmd_prog_img SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart := CmdRecRest.cmd_ro_prog_apart SEGS B LAWS HB IMG.
Let ROB := CmdRecRo.ROB SEGS B LAWS HB IMG.
Let RELRO_IMG := CmdRecRo.RELRO_IMG SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro := CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG.
Let CMD_RO_IN := CmdRecRo.CMD_RO_IN SEGS B LAWS HB IMG.
Let cmd_heap_tail_vis := CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.

(* g_rec's and record.spill's bytes are none of the runtime's statics and not the errno cell (the record's
   prog_static_sep) *)
Lemma spb_rec_unowned : forall a, spb_in_rec a ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. pose proof (spb_in_recPG a Ha) as HP.
assert (HP' : Exists (in_zr a) (as_prog_static B)) by (rewrite (ts_prog B HB); exact HP).
destruct (prog_static_sep B a (ts_ok B HB) HP') as (H1 & H2 & _). split; assumption.
Qed.

(* a g_rec / record.spill byte in the footprint is one the walk may write: awr_byte's program-static disjunct *)
Lemma spb_awr_rec : forall STK sp0 O bl0 blc fr0 ly own a, spb_in_rec a ->
awr_byte SEGS B STK sp0 (spb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 O bl0 blc fr0 ly own a Ha.
pose proof (spb_in_recPG a Ha) as HP.
right; right; right; right; left.
split; [|split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)]].
destruct Ha as [Ha | Ha].
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

(* a callee whose footprint misses a byte of g_rec / record.spill leaves it as it was (the journal's image clause) *)
Lemma spb_rec_kept : forall STK sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly' S' W' mem' md' k a,
ajournal SEGS B STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP1 -> spb_in_rec a -> ~ inFP FP1 a -> rdW W' mem' a = rdW Wc memc a.
Proof.
intros STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k a HJ Hsk Ha Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (spb_rec_unowned a Ha) as [Ho He].
apply F3; [| exact Ho | exact He | exact (fp_spares_closed FP1 a Hsk Hn)].
apply cmd_prog_img. apply spb_in_recPG. exact Ha.
Qed.

(* no read-only byte is in the contract's footprint (arodata_ok_journalP's premise) *)
Lemma spb_ro_off : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
forall a, in_roP SEGS RLO RHI a -> ~ inFP (spb_FP O) a.
Proof.
intros ly S W mem md O HAR HOS a Hro (r & Hr & Ha).
destruct (cmd_ro_prog_apart a Hro) as [Himg Hnp].
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- apply Hnp. apply spb_in_recPG. left. exact Ha.
- apply Hnp. apply spb_in_recPG. right. exact Ha.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  exact (blk_img SEGS B LAWS ly S W mem md p n a HAR (HOS _ Hin) Ha Himg).
Qed.

(* two live blocks with the same start are the same block (the allocator record keeps them disjoint) *)
Lemma spb_same_start : forall ly S (W : world SEGS) mem md a b, AR SEGS B ly S W mem md ->
In a (ablocks B ly S) -> In b (ablocks B ly S) -> fst a = fst b -> a = b.
Proof.
intros ly S W mem md [pa na] [pb nb] HAR Ha Hb E. cbn [fst] in E. subst pb.
destruct (decide ((pa, na) = (pa, nb))) as [Heq | Hne]; [exact Heq|]. exfalso.
pose proof (sep_blocks SEGS B LAWS ly S W mem md pa na pa nb HAR Ha Hb Hne) as Hd.
destruct (al_blocks _ _ LAWS ly S W mem md pa na HAR Ha) as (_ & _ & _ & _ & _ & _ & Hna).
destruct (al_blocks _ _ LAWS ly S W mem md pa nb HAR Hb) as (_ & _ & _ & _ & _ & _ & Hnb).
pose proof (req_size_pos na ltac:(lia)) as [Ra _]. pose proof (req_size_pos nb ltac:(lia)) as [Rb _].
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the representation and a string argument depend on the reader only below alloc_ceiling: g_rec, record.spill and
   the read-only image are image bytes, the recorder's blocks heap bytes *)
Lemma spb_rep_low : forall ly S (W : world SEGS) mem md rd' R O, AR SEGS B ly S W mem md ->
rec_repA B ly S (rdW W mem) R O -> (forall a, 0 <= a < alloc_ceiling -> rd' a = rdW W mem a) ->
rec_repA B ly S rd' R O.
Proof.
intros ly S W mem md rd' R O HAR HREP K. pose proof asan_consts as (C1 & _).
apply (spb_rep_keep B ly S (rdW W mem) ly S rd' R O HREP).
- intros a Ha. apply K. unfold spb_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
- unfold spb_keepsO. intros [p n] Hpn. pose proof (proj1 (spb_rep_blocks B ly S _ _ _ HREP _ Hpn)) as Hin.
  split; [exact Hin|]. intros i Hi. cbn [fst snd] in Hi |- *.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hp4 & Hpc & _ & _ & _ & Hn0).
  pose proof (req_size_pos n ltac:(lia)) as [_ Rn]. apply K. lia.
Qed.

Lemma spb_argA_low : forall ly S (W : world SEGS) mem md rd' O p v, AR SEGS B ly S W mem md ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p v ->
(forall a, 0 <= a < alloc_ceiling -> rd' a = rdW W mem a) ->
astr_argA B ly S rd' (in_roP SEGS RLO RHI) O p v.
Proof.
intros ly S W mem md rd' O p [x|] HAR HA K; [|exact HA]. pose proof asan_consts as (C1 & _).
unfold astr_argA in HA |- *. cbv beta iota zeta in HA |- *. destruct HA as (Hp0 & Hstr & Hn & Harm).
split; [exact Hp0|]. split; [|split; [exact Hn | exact Harm]].
apply (spb_astr_keep (rdW W mem)); [exact Hstr|]. intros y Hy. apply K.
destruct Harm as [((pb & kb & Hpk & Hpb1 & Hpb2) & _) | (Hro & _)].
- destruct (al_blocks _ _ LAWS ly S W mem md pb kb HAR Hpk) as (_ & Hp4 & Hpc & _ & _ & _ & Hk0).
  pose proof (req_size_pos kb ltac:(lia)) as [_ Rk]. lia.
- destruct (Hro (y - p) ltac:(lia)) as [Hr _]. replace (p + (y - p)) with y in Hr by lia.
  destruct (cmd_ro_prog_apart y Hr) as [Himg _]. pose proof (pa_img_range y Himg). lia.
Qed.

(* the verb literal's 11 bytes are owned by no runtime entry and are not the errno cell (the record's lists) *)
Lemma spb_verb_unowned : forall i, 0 <= i < 11 ->
~ Exists (in_zr (0x21ea0 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x21ea0 + i < as_errno B + 4).
Proof.
intros i Hi. rewrite (ts_owned B HB), (ts_errno B HB). split.
- intros HE. apply Exists_exists in HE as ([lo n] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
  assert (Hb : forallb (fun r => (0x21eab <=? fst r) || (fst r + snd r <=? 0x21ea0)) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Hq. cbn beta in Hq. cbn [fst snd] in Hq.
  apply Bool.orb_true_iff in Hq as [Hq | Hq]; apply Z.leb_le in Hq; lia.
- unfold TFIB_ERRNO. lia.
Qed.

Lemma spb_entry_ok : forall ly S W regs mem md ch,
afn_pre SEGS B SUP_PIN_ACCEPT_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) spb_entry
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_pin_accept)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SUP_PIN_ACCEPT_STK = 16592) by (vm_compute; reflexivity).
rewrite WS in Hslo, Hpres, Hbot, Hstk0.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [])).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- apply pairwise_disjoint_of_extents. unfold stack_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I | exact I]]. cbn [spb_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
Qed.

(* the contract of lib/B/Prog/sup_pin_accept_c.v *)
Theorem tsup_pin_accept_holds : tsup_pin_accept_spec B MT.
Proof.
unfold tsup_pin_accept_spec.
intros ly S W regs mem md ch pu uri R O HPRE Hfrm HROD HROOK H10 Hpu HSTR HREP HFR8 Hev Hlive HMOK.
destruct HSTR as (x & -> & (pb & kb & Hpbk & Hpb1 & Hpb2) & HSTRX & HLEN & HAPO).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SUP_PIN_ACCEPT_STK = 16592) by (vm_compute; reflexivity).
assert (WR : RECORD_STK = 16560) by (vm_compute; reflexivity).
assert (WA : ARG_S_STK = 16464) by (vm_compute; reflexivity).
assert (WQ : REC_SHAPE_OF_STK = 8288) by (vm_compute; reflexivity).
assert (WN : ANSWER_STK = 16592) by (vm_compute; reflexivity).
rewrite WS in Hslo, Hbot.
(* the uri's block, which is none of the recorder's *)
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb kb HAR Hpbk) as (_ & Hpb4096 & Hpbc & _ & _ & _ & Hkb).
pose proof (req_size_pos kb ltac:(lia)) as [Rkb1 Rkb2].
assert (Hpbn : ~ In (pb, kb) O).
{ intros HinO. pose proof (proj1 (Forall_forall _ _) HAPO _ HinO) as Hd. unfold iv_apart in Hd. cbn [fst snd] in Hd. lia. }
assert (HOS : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hpn; exact (proj1 (spb_rep_blocks B ly S _ _ _ HREP _ Hpn))).
pose proof (spb_rep_ncalls B ly S _ _ _ HREP) as HL16.
pose proof (spb_slot_range R HL16) as Hslot.
assert (HFPlo : forall a, inFP (spb_FP O) a -> a < alloc_ceiling).
{ intros a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
  - unfold A_G_REC, REC_SIZE in Ha. lia.
  - unfold A_REC_SPILL, SC_SIZE in Ha. lia.
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([pb' nb'] & <- & Hin). cbn [fst snd] in Ha.
    destruct (al_blocks _ _ LAWS ly S W mem md pb' nb' HAR (HOS _ Hin)) as (_ & _ & Hbc & _). lia. }
assert (HROFF : forall a, in_roP SEGS RLO RHI a -> ~ inFP (spb_FP O) a) by exact (spb_ro_off ly S W mem md O HAR HOS).
(* the meter and the counters, split over the four calls *)
set (t0 := snd (sup_pin_accept_m R (Some x))) in *.
assert (HXA : 0 <= XM_ARG_S MT (Some x)) by (unfold XM_ARG_S, XM_XMALLOC; apply (mo_malloc_nonneg MT MTL); unfold LIVE_XMALLOC; lia).
assert (HXN : 0 <= XM_ANSWER MT t0).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length t0) + 1)) ltac:(unfold LIVE_XMALLOC; lia)). lia. }
assert (HMOKR : mo_ok MT S (XM_RECORD MT R)) by (apply (mo_ok_le MT MTL S _ _ HMOK); unfold XM_SUP_PIN_ACCEPT; fold t0; lia).
assert (HEVR : st_nev S + EV_RECORD R <= EV_MAX) by (unfold EV_SUP_PIN_ACCEPT, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in Hev; lia).
(* the journal from the entry, and the symbolic state at the entry *)
pose proof (ajournal_init SEGS B SUP_PIN_ACCEPT_STK (spb_FP O) ly S W regs mem md ch HPRE) as HJ.
pose proof (spb_entry_ok ly S W regs mem md ch HPRE) as HS.
unfold cfg_at. change (w64 (BASE + AF_sup_pin_accept)) with (Z_to_bv 64 (BASE + AF_sup_pin_accept)).
remember (Eimg (Ereg regs [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. rewrite HE. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
(* ---- 0x8be78 .. 0x8be90: the prologue, s0 := uri, a0 := 13, the call of record ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr1. rename ms into msA.
prreg HS (10%bv : bv 5) R10. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (1%bv : bv 5) R1. prreg HS (8%bv : bv 5) R8.
assert (Esp1 : spZ (ms_regs msA) = spZ regs + -32)
  by (unfold spZ at 1; rewrite R2, Usp; apply unsigned_lit_small; lia).
assert (K1 : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem msA) a = rdW W mem a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) HFr1);
  [| lia | cbv beta; lia].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; cbv beta; lia|]).
  destruct Hin. }
pose proof (proj1 HJ) as HAR1.
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem msA)))
  by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := ROB) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROFF HROD).
assert (HREP1 : rec_repA B ly S (rdW W (ms_mem msA)) R O) by exact (spb_rep_low ly S W mem md _ R O HAR HREP K1).
pose (FP1R := (A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
  (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)).
assert (HFP1R : forall a, inFP FP1R a -> spb_in_rec a \/ exists b n, In (b, n) O /\ b <= a < b + req_size n).
{ intros a Ha. unfold FP1R in Ha. apply inFP_cons in Ha as [Ha | Ha].
  { left. left. unfold A_G_REC, OFF_NCALLS, REC_SIZE in *. lia. }
  apply inFP_cons in Ha as [Ha | Ha].
  { left. exact (spb_slot_in_rec R a HL16 ltac:(unfold CALL_SIZE; lia)). }
  right. revert Ha. destruct (Nat.ltb (length (r_calls R)) 16); intros Ha; [exfalso; exact (inFP_nil a Ha)|].
  destruct Ha as (r & Hr & Hrr). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hin). cbn [fst snd] in Hrr.
  exists b, n. split; [exact Hin | exact Hrr]. }
assert (HFP1Rlo : forall a, inFP FP1R a -> a < alloc_ceiling).
{ intros a Ha. destruct (HFP1R a Ha) as [Hr | (b & n & Hin & Hb)].
  - unfold spb_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hr. lia.
  - destruct (al_blocks _ _ LAWS ly S W mem md b n HAR (HOS _ Hin)) as (_ & _ & Hbc & _). lia. }
pmkst HS. rewrite (CmdRecAns.rca_sig_record (PI := PI) cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs msA) (ms_mem msA) _ SUP_PIN_ACCEPT_STK (spZ regs) (spb_FP O) ly S W mem md [] ly S _ 0
    RECORD_STK FP1R (EV_RECORD R) (-32) (getr (ms_regs msA) 1) [] _ HJ Esp1).
  - reflexivity.
  - lia.
  - rewrite WR. lia.
  - rewrite WR, WS. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite R1, unsigned_lit_small by lia. lia.
  - unfold s0Z. rewrite R8, (EE 10%nat 10%bv eq_refl), H10. unfold w64. rewrite unsigned_lit_small by lia.
    apply achain_low. lia.
  - intros HPX. exact (TRECORD fx ly S W (ms_regs msA) (ms_mem msA) _ [] REC_PIN_ACCEPT R O HPX HROD1
      ltac:(rewrite R10; reflexivity) ltac:(unfold REC_PIN_ACCEPT, REC_FN_COUNT; lia) HREP1 HEVR HMOKR).
  - intros a Ha. destruct (HFP1R a Ha) as [Hr | (b & n & Hin & Hb)]; [apply spb_awr_rec; exact Hr|].
    right; left. split.
    + exists (b, b + req_size n). split; [right; right; apply in_map_iff; exists (b, n); split; [reflexivity | exact Hin] | cbn [fst snd]; exact Hb].
    + exists b, n. split; [exact (HOS _ Hin) | exact Hb].
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso. pose proof (HFP1Rlo a Ha). rewrite WS in Hw. lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJR & HP2 & HK2).
destruct HK2 as (F & O1 & Hr10 & HPermR & HFlen & HFO & HREP2 & HO1iff & Hbb2 & HMLE2).
pose proof (proj1 HJ2) as HAR2.
assert (Hpbk2 : In (pb, kb) (ablocks B ly2 S2)).
{ pose proof (Permutation_in _ HPermR Hpbk) as H. apply in_app_or in H as [H | H]; [exact H|].
  exfalso. exact (Hpbn (HFO _ H)). }
(* the uri's bytes: record's footprint misses its block *)
pose proof HJR as (_ & _ & _ & _ & _ & _ & _ & _ & FR1 & FR2 & _).
assert (KR : forall i, 0 <= i < kb -> rdW W2 mem2 (pb + i) = rdW W (ms_mem msA) (pb + i)).
{ intros i Hi. apply (FR2 pb kb i Hpbk Hpbk2 ltac:(lia)).
  intros Hf. destruct (HFP1R _ Hf) as [Hr | (b & n & Hin & Hb)].
  - apply (blk_img SEGS B LAWS ly S W _ _ pb kb (pb + i) HAR1 Hpbk ltac:(lia)). apply cmd_prog_img. apply spb_in_recPG. exact Hr.
  - assert (Hne : (pb, kb) <> (b, n)) by (intros E'; rewrite E' in Hpbn; exact (Hpbn Hin)).
    pose proof (sep_blocks SEGS B LAWS ly S W _ _ pb kb b n HAR1 Hpbk (HOS _ Hin) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
rewrite R1.
jafter_call_keep_pi HS 32%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (spb_region_kept_hi2 SEGS E (w_H W) (w_H W2) (ms_mem msA) mem2 2 (spZ regs)); [exact Usp | |].
  + intros a Ha. apply FR1; [lia | try rewrite Esp1; rewrite WR; lia |].
    intros Hf. pose proof (HFP1Rlo a Hf). lia.
  + intros a Ha. apply HJ2pres. rewrite WS. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 32 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 32)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs []) E2) by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
assert (E36 : ew E2 36 = getr regs2 10) by (rewrite HE2; reflexivity).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
(* ---- 0x8be94 .. 0x8be9c: s1 := the slot, a1 := uri, the call of arg_s ---- *)
paj_run_shc RUNP RUNC HS HJ2.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp2 | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr2. rename ms into msB.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (1%bv : bv 5) Q1. prreg HS (8%bv : bv 5) Q8.
assert (Esp2 : spZ (ms_regs msB) = spZ regs + -32)
  by (unfold spZ at 1; rewrite Q2, Usp2; apply unsigned_lit_small; lia).
assert (K2 : forall a, 0 <= a < alloc_ceiling -> rdW W2 (ms_mem msB) a = rdW W2 mem2 a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) HFr2);
  [| lia | cbv beta; lia].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2 in Hrr; cbv beta; lia|]).
  destruct Hin. }
pose proof (proj1 HJ2) as HAR2'.
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem msB)))
  by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := ROB) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROFF HROD).
pose proof (cmd_ro_ok_of_aro _ _ _ _ _ HAR2' HROD2) as HRO2.
assert (HREP2' : rec_repA B ly2 S2 (rdW W2 (ms_mem msB)) (rec_record R REC_PIN_ACCEPT []) O1)
  by exact (spb_rep_low ly2 S2 W2 mem2 md2 _ _ O1 HAR2 HREP2 K2).
assert (HSTR2 : astr_atR (rdW W2 (ms_mem msB)) pu x).
{ apply (spb_astr_keep (rdW W mem)); [exact HSTRX|]. intros y Hy.
  transitivity (rdW W2 mem2 y); [apply K2; lia|].
  transitivity (rdW W (ms_mem msA) y).
  { pose proof (KR (y - pb) ltac:(lia)) as Hk. replace (pb + (y - pb)) with y in Hk by lia. exact Hk. }
  apply K1. lia. }
assert (HTL : forall x', Some x = Some x' -> atail_vis SEGS W2 (ms_mem msB) (pu + Z.of_nat (length x'))).
{ intros x' Hx'. injection Hx' as <-. apply (cmd_heap_tail_vis ly2 S2 W2 (ms_mem msB) _ pb kb _ HAR2' Hpbk2). lia. }
assert (HARGA : astr_argA B ly2 S2 (rdW W2 (ms_mem msB)) (in_roP SEGS RLO RHI) [] pu (Some x)).
{ unfold astr_argA. cbv zeta. split; [lia|]. split; [exact HSTR2|]. split; [exact HLEN|].
  left. split; [exists pb, kb; split; [exact Hpbk2 | lia] | apply Forall_nil]. }
pose proof HJ2 as (_ & _ & _ & _ & _ & Hfr2 & Hnev2 & _).
assert (HEVA : st_nev S2 + EV_ARG_S <= EV_MAX)
  by (unfold EV_SUP_PIN_ACCEPT, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *; lia).
assert (HLA : blocks_bytes S2 + LIVE_ARG_S (Some x) <= LIVE_MAX).
{ unfold LIVE_SUP_PIN_ACCEPT, LIVE_ANSWER, LIVE_HAND_BACK in Hlive. fold t0 in Hlive. unfold LIVE_ARG_S, LIVE_XMALLOC in *. lia. }
assert (HMOKA : mo_ok MT S2 (XM_ARG_S MT (Some x))).
{ apply (mo_ok_le MT MTL S2 _ (XM_ARG_S MT (Some x) + XM_ANSWER MT t0)); [|lia].
  apply (mo_ok_step MT MTL S S2 (XM_RECORD MT R)); [|exact HMLE2].
  unfold XM_SUP_PIN_ACCEPT in HMOK. fold t0 in HMOK. rewrite <- Z.add_assoc in HMOK. exact HMOK. }
assert (EA0 : (Z.of_nat (length (@nil (list byte))) <? REC_ARGS_MAX) = true) by reflexivity.
pose (FP1A := (if Z.of_nat (length (@nil (list byte))) <? REC_ARGS_MAX
  then [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
        (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))),
         rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))) + 8)]
  else [])).
assert (HFP1A : forall a, inFP FP1A a -> spb_in_rec a).
{ intros a Ha. unfold FP1A in Ha. rewrite EA0 in Ha. cbn [length Z.of_nat] in Ha.
  apply spb_slot_in_rec with (R := R); [exact HL16|].
  apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS, CALL_SIZE in *; lia|].
  apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS, CALL_SIZE in *; lia|].
  exfalso. exact (inFP_nil a Ha). }
pmkst HS. rewrite (spb_sig_arg_s cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W2 (ms_regs msB) (ms_mem msB) _ SUP_PIN_ACCEPT_STK (spZ regs) (spb_FP O) ly S W mem md [] ly2 S2 _
    (0 + EV_RECORD R) ARG_S_STK FP1A EV_ARG_S (-32) (getr (ms_regs msB) 1) [] _ HJ2 Esp2).
  - reflexivity.
  - lia.
  - rewrite WA. lia.
  - rewrite WA, WS. lia.
  - rewrite Q3, OLD2, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite Q4, OLD2, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1, unsigned_lit_small by lia. lia.
  - unfold s0Z. rewrite Q8, OLD2, (EE 10%nat 10%bv eq_refl), H10 by lia. unfold w64. rewrite unsigned_lit_small by lia.
    apply achain_low. lia.
  - intros HPX. exact (TARG_S fx ly2 S2 W2 (ms_regs msB) (ms_mem msB) _ [] (rec_slot R) pu REC_PIN_ACCEPT [] (Some x) R O1
      HPX HROD2 HRO2 ltac:(rewrite Q10, E36; exact Hr10)
      ltac:(rewrite Q11, OLD2, (EE 10%nat 10%bv eq_refl) by lia; exact H10)
      eq_refl HREP2' (or_introl HARGA) HTL HEVA HLA HMOKA).
  - intros a Ha. apply spb_awr_rec. exact (HFP1A a Ha).
  - intros ly3' S3' W3' regs3' mem3' md3' _ a Ha Hw _. exfalso. pose proof (HFP1A a Ha) as Hr.
    unfold spb_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hr. rewrite WS in Hw. lia. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJA & HP3 & HK3).
destruct HK3 as (Hbb3 & HMLE3 & [(Hsix & _) | (_ & p & Hp)]).
{ exfalso. cbn [length Z.of_nat] in Hsix. unfold REC_ARGS_MAX in Hsix. lia. }
cbv zeta in Hp. cbn [sarg app] in Hp, Hbb3, HMLE3.
destruct Hp as (Hp4096 & HPerm3 & HAp3 & HREP3).
pose proof (proj1 HJ3) as HAR3.
(* ---- after arg_s: the symbolic state, then 0x8bea0 .. 0x8beac: a0 := "pin_accept", a1 := 10, the call of
   rec_shape_of ---- *)
pose proof HJA as (_ & _ & _ & _ & _ & _ & _ & _ & FA1 & _).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ3pres & _).
rewrite Q1.
jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (spb_region_kept_hi2 SEGS E2 (w_H W2) (w_H W3) (ms_mem msB) mem3 2 (spZ regs)); [exact Usp2 | |].
  + intros a Ha. apply FA1; [lia | try rewrite Esp2; rewrite WA; lia |].
    intros Hf. pose proof (HFP1A a Hf) as Hr. unfold spb_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hr.
    lia.
  + intros a Ha. apply HJ3pres. rewrite WS. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E2 48 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n, (n < 48)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE3 : env_agree 32 (Ereg regs []) E3) by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp2).
paj_run_shc RUNP RUNC HS HJ3.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp3 | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr3. rename ms into msC.
prreg HS (10%bv : bv 5) V10. prreg HS (11%bv : bv 5) V11. prreg HS (2%bv : bv 5) V2. prreg HS (3%bv : bv 5) V3.
prreg HS (4%bv : bv 5) V4. prreg HS (1%bv : bv 5) V1.
assert (Esp3 : spZ (ms_regs msC) = spZ regs + -32)
  by (unfold spZ at 1; rewrite V2, Usp3; apply unsigned_lit_small; lia).
assert (K3 : forall a, 0 <= a < alloc_ceiling -> rdW W3 (ms_mem msC) a = rdW W3 mem3 a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) HFr3);
  [| lia | cbv beta; lia].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; cbv beta; lia|]).
  destruct Hin. }
assert (V10' : getr (ms_regs msC) 10 = w64 0x21ea0).
{ rewrite V10, (img_env_atomP E3 313 HEI3 ltac:(unfold A_TEXT, A_LIM; lia)).
  change (VAL 313%nat) with (VAL (A_OBJ 72)). rewrite (spb_verb_val VOBJS). reflexivity. }
assert (HLV : Z.of_nat (length spb_verb) = 10) by (vm_compute; reflexivity).
assert (V11' : getr (ms_regs msC) 11 = w64 (Z.of_nat (length spb_verb))) by (rewrite V11, HLV; reflexivity).
pose proof (proj1 HJ3) as HAR3'.
assert (HROD3 : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem msC)))
  by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := ROB) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HROFF HROD).
pose proof (cmd_ro_ok_of_aro _ _ _ _ _ HAR3' HROD3) as HRO3.
assert (HLIT : abytes_atR (rdW W3 (ms_mem msC)) 0x21ea0 RO_lit_21ea0).
{ clear - HRO3. destruct HRO3 as [HRB _]. unfold cmd_ro_bytes in HRB.
  repeat (first [exact (proj1 HRB) | apply proj2 in HRB]). }
assert (HVB : abytes_atR (rdW W3 (ms_mem msC)) 0x21ea0 spb_verb).
{ intros i Hi. rewrite (HLIT i) by (rewrite <- spb_verb_lit, length_app; cbn [length]; lia).
  rewrite <- spb_verb_lit. rewrite app_nth1 by exact Hi. reflexivity. }
assert (HVRO : forall i, 0 <= i < 11 -> in_roP SEGS RLO RHI (0x21ea0 + i)).
{ clear - CMD_RO_IN. unfold cmd_ro_in in CMD_RO_IN. repeat (first [exact (proj1 CMD_RO_IN) | apply proj2 in CMD_RO_IN]). }
assert (HVA : astr_argA B ly3 S3 (rdW W3 (ms_mem msC)) (in_roP SEGS RLO RHI) [] 0x21ea0 (Some spb_verb)).
{ unfold astr_argA. cbv zeta. rewrite HLV. split; [lia|]. split.
  { split; [rewrite spb_verb_lit; exact HLIT | exact spb_verb_no0]. }
  split; [unfold LMAX; lia|]. right. split; [intros i Hi; exact (conj (HVRO i Hi) (spb_verb_unowned i Hi))|].
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  assert (Hb : existsb (Z.eqb 0x21eaa) cmd_ro_ends = true) by (vm_compute; reflexivity).
  apply existsb_exists in Hb as (y & Hy & Hey). apply Z.eqb_eq in Hey. rewrite <- Hey in Hy. exact Hy. }
pose proof HJ3 as (_ & _ & _ & _ & _ & Hfr3 & Hnev3 & _).
assert (HEVS : st_nev S3 + EV_REC_SHAPE_OF <= EV_MAX)
  by (unfold EV_SUP_PIN_ACCEPT, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC, EV_REC_SHAPE_OF in *; lia).
pmkst HS. rewrite (spb_sig_rso cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W3 (ms_regs msC) (ms_mem msC) _ SUP_PIN_ACCEPT_STK (spZ regs) (spb_FP O) ly S W mem md [] ly3 S3 _
    (0 + EV_RECORD R + EV_ARG_S) REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-32) (getr (ms_regs msC) 1) _ HJ3 Esp3).
  - reflexivity.
  - lia.
  - rewrite WQ. lia.
  - rewrite WQ, WS. lia.
  - rewrite V3, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite V4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
  - reflexivity.
  - rewrite V1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite V1, unsigned_lit_small by lia. lia.
  - intros HPS. exact (TREC_SHAPE_OF fx ly3 S3 W3 (ms_regs msC) (ms_mem msC) _ 0x21ea0 spb_verb HPS HROD3 V10' ltac:(lia) V11'
      ltac:(rewrite HLV; lia) HRO3 VOBJS (fun _ => conj HVB (or_intror HVA)) HEVS).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJS & HP4 & ((q & Hq10 & Hq64 & HqA) & Hperm4 & -> & ->)).
pose proof (proj1 HJ4) as HAR4.
(* ---- after rec_shape_of: the symbolic state, then 0x8beb0 .. 0x8becc: a2 := 1, a1 := the shape, a0 := the slot,
   the frame restored, the tail jump into answer ---- *)
pose proof HJS as (_ & _ & _ & _ & _ & _ & _ & _ & FS1 & FS2 & _).
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ4pres & _).
rewrite V1.
jafter_call_keep_pi HS 64%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (spb_region_kept_hi2 SEGS E3 (w_H W3) (w_H W4) (ms_mem msC) mem4 2 (spZ regs)); [exact Usp3 | |].
  + intros a Ha. apply FS1; [lia | try rewrite Esp3; rewrite WQ; lia | exact (inFP_nil a)].
  + intros a Ha. apply HJ4pres. rewrite WS. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E3 64 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (OLD4 : forall n, (n < 64)%nat -> ew E4 n = ew E3 n) by (intros n Hn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE4 : env_agree 32 (Ereg regs []) E4) by (rewrite HE4; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
assert (E68 : ew E4 68 = getr regs4 10) by (rewrite HE4; reflexivity).
clear HE4.
assert (Usp4 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by lia; exact Usp3).
paj_run_shc RUNP RUNC HS HJ4.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp4 | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr4. rename ms into msD.
assert (K4 : forall a, 0 <= a < alloc_ceiling -> rdW W4 (ms_mem msD) a = rdW W4 mem4 a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) HFr4);
  [| lia | cbv beta; lia].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp4 in Hrr; cbv beta; lia|]).
  destruct Hin. }
pose proof (aregs_preserved_of_st_ok SEGS (w_H W4) E4 _ msD regs [] HS HAE4 ltac:(vm_compute; reflexivity)) as HPT.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  set (rgT := rg) in *; set (mT := mm) in *; set (mdT := mdq) in *
end.
clearbody mdT.
assert (TR1' : getr rgT 1 = getr regs 1) by (rewrite T1, OLD4, OLD3, OLD2 by lia; exact (EE 1%nat 1%bv eq_refl)).
assert (TRsp : spZ rgT = spZ regs) by (unfold spZ at 1; rewrite T2; exact Usp4).
assert (TR3 : getr rgT 3 = getr regs 3) by (rewrite T3, OLD4, OLD3, OLD2 by lia; exact (EE 3%nat 3%bv eq_refl)).
assert (TR4 : getr rgT 4 = getr regs 4) by (rewrite T4, OLD4, OLD3, OLD2 by lia; exact (EE 4%nat 4%bv eq_refl)).
assert (TR8 : getr rgT 8 = getr regs 8) by (rewrite T8, OLD4, OLD3, OLD2 by lia; exact (EE 8%nat 8%bv eq_refl)).
assert (TR10 : getr rgT 10 = w64 (rec_slot R)) by (rewrite T10, OLD4, OLD3, E36 by lia; exact Hr10).
assert (TR11 : getr rgT 11 = w64 q) by (rewrite T11, E68; exact Hq10).
(* the recorder after arg_s, at answer's entry: kept over the run, rec_shape_of (empty footprint) and the
   epilogue *)
clear R10 R2 R3 R4 R1 R8.
set (n := Z.of_nat (length x) + 1) in *.
assert (Hn1 : 1 <= n) by (subst n; lia).
set (R2 := rec_record R REC_PIN_ACCEPT [x]) in *.
set (O2 := (p, n) :: O1) in *.
assert (HREP3C : rec_repA B ly3 S3 (rdW W3 (ms_mem msC)) R2 O2) by exact (spb_rep_low ly3 S3 W3 mem3 md3 _ _ O2 HAR3 HREP3 K3).
assert (HREP4 : rec_repA B ly3 S3 (rdW W4 mem4) R2 O2).
{ apply (spb_rep_keep B ly3 S3 (rdW W3 (ms_mem msC)) ly3 S3 (rdW W4 mem4) R2 O2 HREP3C).
  - intros a Ha. exact (spb_rec_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJS (sink_closed_pos [] (Forall_nil _)) Ha (inFP_nil a)).
  - unfold spb_keepsO. intros [a k'] Hpn. pose proof (proj1 (spb_rep_blocks B ly3 S3 _ _ _ HREP3C _ Hpn)) as Hin.
    split; [exact Hin|]. intros i Hi. cbn [fst snd] in Hi |- *.
    destruct (al_blocks _ _ LAWS ly3 S3 W3 _ _ a k' HAR3' Hin) as (_ & _ & _ & _ & _ & _ & Hk0).
    pose proof (req_size_pos k' ltac:(lia)) as [_ Rk].
    exact (FS2 a k' i Hin Hin ltac:(lia) (inFP_nil _)). }
assert (HREPT : rec_repA B ly3 S3 (rdW W4 mT) R2 O2) by exact (spb_rep_low ly3 S3 W4 mem4 md4 _ _ O2 HAR4 HREP4 K4).
(* answer's premises at the tail state *)
pose proof HJ4 as (HART & HlyT & _ & _ & _ & HfrT & HnevT & _ & F1T & _).
pose proof HlyT as (_ & _ & _ & _ & _ & _ & _ & _ & EtopT & _).
assert (HRODT : arodata_okP SEGS RLO RHI B (rdW W4 mT))
  by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := ROB) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4 HROFF HROD).
pose proof (cmd_ro_ok_of_aro _ _ _ _ _ HART HRODT) as HROT.
assert (HFRT : Z.of_nat (length (frames S3)) <= 8) by (rewrite HfrT; exact HFR8).
set (xs := shape_of spb_verb) in *.
set (e := (REC_PIN_ACCEPT, [x])).
set (t := snd (rec_answer R2 e xs true)).
assert (Ht : t0 = t) by reflexivity.
destruct (spb_rep_answer B ly3 S3 _ _ _ HREPT) as (old & Hold & Holdc).
assert (HSH : r_refuse R2 = 0 ->
  astr_argA B ly3 S3 (rdW W4 mT) (in_roP SEGS RLO RHI) O2 q (Some xs) /\ fits xs).
{ intros _. split; [|unfold fits; vm_compute; discriminate].
  exact (spb_argA_low ly3 S3 W4 mem4 md4 _ O2 q (Some xs) HAR4 (HqA O2) K4). }
assert (Hold64 : 0 <= old < 2 ^ 64).
{ destruct Holdc as [-> | ([pb' kb'] & Hpn & Eo)]; [lia|]. cbn [fst] in Eo. subst old.
  pose proof (proj1 (spb_rep_blocks B ly3 S3 _ _ _ HREPT _ Hpn)) as Hin.
  destruct (al_blocks _ _ LAWS ly3 S3 W4 mT mdT pb' kb' HART Hin) as (_ & Hp4 & Hpc & _ & _ & _ & Hk0).
  pose proof (req_size_pos kb' ltac:(lia)) as [Rk1 Rk2]. lia. }
assert (HSLOT : r_refuse R2 = 0 -> true = true ->
  (exists k0, nth_error (r_calls R2) k0 = Some e /\ rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k0) \/
  (rec_slot R = A_REC_SPILL /\ e = r_spill R2)).
{ intros _ _. unfold R2, rec_record, rec_slot. destruct (Nat.ltb (length (r_calls R)) 16) eqn:Elt.
  - left. exists (length (r_calls R)). cbn [r_calls set_calls].
    split; [rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity | reflexivity].
  - right. cbn [r_spill set_spill]. split; reflexivity. }
assert (Hchg : true = negb (bv_unsigned (getr rgT 12) =? 0)) by (rewrite T12; reflexivity).
assert (HEVT : st_nev S3 + EV_ANSWER <= EV_MAX)
  by (unfold EV_SUP_PIN_ACCEPT, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC, EV_REC_SHAPE_OF in *; lia).
assert (Hbb3' : blocks_bytes S3 <= blocks_bytes S + n).
{ unfold LIVE_ARG_S, LIVE_XMALLOC in Hbb3. cbn [sarg] in Hbb3. fold n in Hbb3. lia. }
assert (HLIVET : blocks_bytes S3 + LIVE_ANSWER t <= LIVE_MAX).
{ rewrite <- Ht. unfold LIVE_SUP_PIN_ACCEPT, LIVE_ARG_S, LIVE_XMALLOC in Hlive. cbn [sarg] in Hlive. fold t0 n in Hlive.
  unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC in *. lia. }
assert (HMOKT : mo_ok MT S3 (XM_ANSWER MT t)).
{ rewrite <- Ht. apply (mo_ok_step MT MTL S2 S3 (XM_ARG_S MT (Some x))); [|exact HMLE3].
  apply (mo_ok_step MT MTL S S2 (XM_RECORD MT R)); [|exact HMLE2].
  unfold XM_SUP_PIN_ACCEPT in HMOK. fold t0 in HMOK. rewrite <- Z.add_assoc in HMOK. exact HMOK. }
(* the tail jump: answer runs at this function's entry sp and returns to its caller *)
rewrite (spb_sig_answer cmd_sig_prog_PB).
eapply SRr_mono.
{ eapply (callS_wideF (L := cmd_listing) (PI := PI) B LAWS W4 rgT mT _ SUP_PIN_ACCEPT_STK (spZ regs) (spb_FP O) ly S W mem md [] ly3 S3 mdT
    (0 + EV_RECORD R + EV_ARG_S + EV_REC_SHAPE_OF) ANSWER_STK
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
     ablocks_fp (filter (fun pn => fst pn =? old) O2))
    EV_ANSWER 0 (getr rgT 1) ch _ HJ4).
  - rewrite TRsp. lia.
  - reflexivity.
  - lia.
  - rewrite WN. lia.
  - rewrite WN, WS. lia.
  - rewrite TR3. exact Hgp.
  - rewrite TR4. exact Htp.
  - reflexivity.
  - rewrite TR1'. exact Hra.
  - rewrite TR1'. exact Hra4.
  - rewrite Z.add_0_r. unfold s0Z. rewrite TR8. fold (s0Z regs).
    apply (achain_ly_top ly ly3 _ _ _ _ EtopT).
    apply (achain_kept ly (rdW W mem) (rdW W4 mT) (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
    intros a Ha. apply F1T; [lia | lia |]. intros Hf. pose proof (HFPlo a Hf). lia.
  - intros HPRE3. eapply SRr_mono.
    + exact (TANSWER fx ly3 S3 W4 rgT mT mdT ch (rec_slot R) q old e xs true R2 O2
        HPRE3 Hfrm HFRT HRODT HROT TR10 ltac:(lia) TR11 Hq64 Hchg HREPT Hold Hold64 HSH HSLOT HEVT HLIVET HMOKT).
    + cbv beta. intros W6 c6 _ (fx6 & ly6 & S6 & regs6 & mem6 & md6 & -> & HF6a & HF6b & HJ6 & HP6 & HK6).
      exists fx6, ly6, S6, regs6, mem6, md6. split; [reflexivity|]. split; [exact HF6a|]. split; [exact HF6b|].
      split; [exact HJ6|]. split; [exact HP6 | exact HK6].
  - intros a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
    + apply spb_awr_rec. left. unfold A_G_REC, OFF_ANSWER, REC_SIZE in *. lia.
    + apply spb_awr_rec. left. unfold A_G_REC, OFF_STATE, REC_SIZE in *. lia.
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([pb' nb'] & <- & Hin). cbn [fst snd] in Ha.
      apply spb_filter_in in Hin.
      assert (HinT : In (pb', nb') (ablocks B ly3 S3)) by exact (proj1 (spb_rep_blocks B ly3 S3 _ _ _ HREPT _ Hin)).
      destruct (in_dec (fun u v : Z * Z => decide (u = v)) (pb', nb') O) as [HO | HnO].
      * right; left. split.
        { exists (pb', pb' + req_size nb'). split; [right; right; apply in_map_iff; exists (pb', nb'); split; [reflexivity | exact HO]|].
          cbn [fst snd]. exact Ha. }
        exists pb', nb'. split; [exact HinT | exact Ha].
      * right; right; left. exists pb', nb'. split; [exact HinT|]. split; [|exact Ha].
        intros H0. unfold O2 in Hin. destruct Hin as [E' | Hin].
        -- injection E' as <- <-.
           assert (HnewSc : ~ In (p, n) (ablocks B ly2 S2)).
           { intros Hin2. pose proof (proj1 (Forall_forall _ _) HAp3 _ Hin2) as Hap. cbn [fst snd] in Hap.
             unfold iv_apart in Hap. lia. }
           apply HnewSc. pose proof (Permutation_in _ HPermR H0) as H1. apply in_app_or in H1 as [H1 | H1]; [exact H1|].
           exfalso. exact (HnO (HFO _ H1)).
        -- exact (HnO (proj1 (proj1 (HO1iff _) Hin))).
  - intros ly6 S6 W6 regs6 mem6 md6 _ a _ Hw Hn. exfalso. rewrite WN in Hn. rewrite WS in Hw. lia. }
cbv beta. intros W5 c5 _ (fx5 & ly5 & S5 & regs5 & mem5 & md5 & -> & HF5a & HF5b & HJ5 & HJc5 & HP5 & HK5).
destruct HK5 as (p1 & p2 & O' & HK5). cbv zeta in HK5.
change (snd (rec_answer R2 e xs true)) with t in HK5.
destruct HK5 as (Hp2r & Hp24096 & H12 & Hfold & Hbl5 & HREP5 & HO'iff & Hstr5 & HBB5 & HMLE5).
set (nt := Z.of_nat (length t) + 1) in *.
pose proof (proj1 HJ5) as HAR5.
unfold apost_baseF. exists fx5, ly5, S5, regs5, mem5, md5.
split; [rewrite TR1'; reflexivity|].
split; [exact HF5a|]. split; [exact HF5b|].
split.
{ eapply (ajournal_mono_k SEGS B); [exact HJ5|].
  unfold EV_SUP_PIN_ACCEPT, EV_REC_SHAPE_OF, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC. lia. }
split; [exact (aregs_preserved_trans _ _ _ HPT HP5)|].
(* the block bookkeeping *)
pose proof (RecBLemmas.recb_ablocks_nodup_m B ly S W mem md HAR) as ND0.
pose proof (Permutation_NoDup HPermR ND0) as ND1.
assert (HB2 : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly2 S2)).
{ intros pn H0 HnO. pose proof (Permutation_in _ HPermR H0) as H1. apply in_app_or in H1 as [H1 | H1]; [exact H1|].
  exfalso. exact (HnO (HFO _ H1)). }
assert (HB1 : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B ly S))
  by (intros pn H1; exact (Permutation_in _ (Permutation_sym HPermR) (in_or_app _ _ _ (or_introl H1)))).
assert (HO1 : forall pn, In pn O1 -> In pn O) by (intros pn H1; exact (proj1 (proj1 (HO1iff pn) H1))).
assert (HO2 : forall pn, In pn O -> In pn (ablocks B ly2 S2) -> In pn O1).
{ intros pn HO H1. apply HO1iff. split; [exact HO|]. intros HF. exact (RecBLemmas.list_nodup_app_disj _ _ pn ND1 H1 HF). }
assert (HO1c : forall pn, In pn O1 -> In pn (ablocks B ly2 S2))
  by (intros pn H1; exact (proj1 (spb_rep_blocks B ly2 S2 _ _ _ HREP2 pn H1))).
assert (HnewSc : ~ In (p, n) (ablocks B ly2 S2)).
{ intros Hin2. pose proof (proj1 (Forall_forall _ _) HAp3 _ Hin2) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart in Hap. lia. }
assert (H3iff : forall pn, In pn (ablocks B ly3 S3) <-> pn = (p, n) \/ In pn (ablocks B ly2 S2)).
{ intros pn. split; intros Hpn.
  - apply (Permutation_in _ HPerm3) in Hpn. destruct Hpn as [<- | Hpn]; [left; reflexivity | right; exact Hpn].
  - apply (Permutation_in _ (Permutation_sym HPerm3)). destruct Hpn as [-> | Hpn]; [left; reflexivity | right; exact Hpn]. }
assert (Hold3 : forall pn, In pn (ablocks B ly3 S3) -> fst pn = old -> In pn O2).
{ intros pn Hpn Eo. destruct Holdc as [Eold | (pn' & Hpn' & Eo')].
  - destruct pn as [a k']. destruct (al_blocks _ _ LAWS ly3 S3 W4 mT mdT a k' HART Hpn) as (_ & H4096 & _).
    cbn [fst] in Eo. lia.
  - assert (Hpn'3 : In pn' (ablocks B ly3 S3)) by exact (proj1 (spb_rep_blocks B ly3 S3 _ _ _ HREPT _ Hpn')).
    rewrite (spb_same_start ly3 S3 W4 mT mdT pn pn' HART Hpn Hpn'3 ltac:(congruence)). exact Hpn'. }
destruct (spb_post_lists (ablocks B ly S) (ablocks B ly2 S2) (ablocks B ly3 S3) (ablocks B ly5 S5) O O1 O'
  (p, n) (p1, nt) (p2, nt) old HB2 HB1 HO1 HO2 HO1c HnewSc H3iff Hfold
  ltac:(intros E'; injection E' as E'; exact (H12 E')) Hbl5 HO'iff Hold3) as (L1 & L2 & L2' & L3 & L4 & L4' & L5 & L6).
exists (fst (rec_answer R2 e xs true)), t, p2, O'.
split; [exact (surjective_pairing (rec_answer R2 e xs true))|].
split; [exact Hp2r|]. split; [exact Hp24096|]. split; [exact HREP5|].
assert (L1' : forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)).
{ intros pn Hpn. destruct (in_dec (fun u v : Z * Z => decide (u = v)) pn (ablocks B ly S)) as [H0 | H0];
  [left; exact (L1 pn Hpn H0) | right; exact H0]. }
split; [exact L1'|]. split; [exact L2|]. split; [exact L3|].
split.
{ intros Hq'. apply in_map_iff in Hq' as (pn & Ep & Hpn).
  apply L4. rewrite <- (spb_same_start ly5 S5 W5 mem5 md5 pn (p2, nt) HAR5 (L4' _ Hpn) L2 Ep). exact Hpn. }
split; [exact Hstr5|].
split.
{ intros pn H0 HnO. pose proof (L5 pn H0 HnO) as H5'. split; [exact H5'|].
  pose proof (L3 pn H0 HnO) as Hne.
  destruct pn as [a k'].
  pose proof (sep_blocks SEGS B LAWS ly5 S5 W5 mem5 md5 a k' p2 nt HAR5 H5' L2 Hne) as Hd.
  destruct (al_blocks _ _ LAWS ly5 S5 W5 mem5 md5 a k' HAR5 H5') as (_ & _ & _ & _ & _ & _ & Hkk).
  destruct (al_blocks _ _ LAWS ly5 S5 W5 mem5 md5 p2 nt HAR5 L2) as (_ & _ & _ & _ & _ & _ & Hn').
  pose proof (req_size_pos k' ltac:(lia)) as [_ Rk]. pose proof (req_size_pos nt ltac:(lia)) as [_ Rn].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd |- *. unfold iv_apart. lia. }
split; [exact L6|].
split.
{ rewrite <- Ht in HBB5. unfold LIVE_SUP_PIN_ACCEPT, LIVE_ARG_S, LIVE_XMALLOC. cbn [sarg]. fold t0 n. lia. }
pose proof (mo_le_trans MT MTL _ _ _ _ _ HMLE2 HMLE3) as HmS3.
pose proof (mo_le_trans MT MTL _ _ _ _ _ HmS3 HMLE5) as HmS5.
apply (mo_le_mono MT MTL S S5 _ _ HmS5). unfold XM_SUP_PIN_ACCEPT. fold t0. rewrite Ht. lia.
Qed.

End e.
End f.
End d.

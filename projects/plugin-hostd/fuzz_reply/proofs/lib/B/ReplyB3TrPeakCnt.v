(* The image-B (fuzz_reply.asan-ubsan) port of the helpers of lib/A/ReplyTrPeakCnt.v
   (sha256 88b1c07a8cac; internal record) at c653c819019 that lib/B/ReplyB3TrPeakCnl.v reads,
   a Theorem Labs lane row G-BCNL: tc_ref, tc_ref_step, tc_lines_short, tc_inv, tc_projg, w_sec_range / _small,
   w_cls_range / _small, pair_bytes, pair_bytes_nonneg, tc_ref_state, and Section inst's tc_out_pos / tc_rm_cap, under
   A's names, statements and proofs, in A's order.  The rest of A's file (the walk tc_pc, tc_dr / tc_rr and the LS
   bounds over fr_LS3c) is not read by ReplyTrPeakCnl.v and is not ported here.  Swaps:
   - the Require header: lib/A image files -> lib/B's (YB1v / YE01 YE2k / YCfn / W_* / _drain_defs / _write), as
     lib/B/ReplyB3LS3p.v (A's `Require Import ACfn` -> `Require YCfn`; lib/A/CfParamsReply added, as ReplyB3LS3p);
     lib/A ReplyLS / ReplyRINV / ReplyLSArms -> lib/B ReplyLSB / ReplyRINVB / ReplyLSBArms; A's ReplyLSDrainPre /
     ReplyLSRemove3 / ReplyLSRrPre facts -> lib/B/ReplyLSBDrainPre.v (the same names); ReplyTrPeak ->
     lib/B/ReplyLSBTrPeak.v; ReplyLSCntL / ReplyTrPeakW / ReplyCnt -> lib/B's files of those names; A's _event,
     ReplyLS3, ReplyLS3c, ReplyLSDrain3 and ReplyLSCntM Requires are dropped (no name of them is read);
   - A's file-level `Local Notation rv` is kept with A's preamble though the 14 helpers do not read it.
   proves no function (kind: invariant lemma). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyRINVB ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBDrainPre ReplyLSBTrPeak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyTrPeakW ReplyCnt ReplyLSCntL.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation rv := (RelayRunT.rev YO0i.sptr).

(* ================================================================== the reference splitter's lines are short *)
(* the splitter keeps at most LINE_LIMIT = 6000 bytes of a line, or skips it (RelayModel.step) *)
Definition tc_ref (st : RelayModel.lstate) : Prop :=
  RelayModel.ls_k st = true \/ Z.of_nat (length (RelayModel.ls_w st)) <= 6000.

Lemma tc_ref_step : forall st b, tc_ref st ->
  tc_ref (fst (RelayModel.step st b)) /\
  (forall l, snd (RelayModel.step st b) = Some l -> Z.of_nat (length l) <= 6000).
Proof.
  intros [ww k] b H. unfold tc_ref in *. cbn [RelayModel.ls_k RelayModel.ls_w] in H.
  unfold RelayModel.step. cbn [RelayModel.ls_k RelayModel.ls_w].
  destruct (Z.eqb b 0).
  - cbn [fst snd RelayModel.ls_k RelayModel.ls_w length]. split; [right; lia|].
    intros l E. destruct k; [discriminate E|]. injection E as <-.
    destruct H as [H|H]; [discriminate H | exact H].
  - destruct k.
    + cbn [fst snd]. split; [left; reflexivity | intros l E; discriminate E].
    + destruct (Nat.eqb_spec (length ww) RelayModel.LINE_LIMIT) as [E|E].
      * cbn [fst snd RelayModel.ls_k]. split; [left; reflexivity | intros l E'; discriminate E'].
      * cbn [fst snd RelayModel.ls_k RelayModel.ls_w]. split; [|intros l E'; discriminate E'].
        (* LINE_LIMIT = 6000 *)
        assert (E6 : Z.of_nat (length ww) <> 6000).
        { intros C. apply E. apply Nat2Z.inj. rewrite C. vm_compute. reflexivity. }
        right. rewrite length_app. cbn [length].
        destruct H as [H|H]; [discriminate H | lia].
Qed.

Lemma tc_lines_short : forall d st, tc_ref st ->
  Forall (fun l => Z.of_nat (length l) <= 6000) (RelayModel.lines st d) /\ tc_ref (RelayModel.feed st d).
Proof.
  induction d as [|b d IH]; intros st H.
  - rewrite RelayModel.lines_nil, RelayModel.feed_nil. split; [constructor | exact H].
  - rewrite RelayModel.lines_cons, RelayModel.feed_cons.
    destruct (tc_ref_step st b H) as [H1 H2].
    destruct (IH _ H1) as [I1 I2]. split; [|exact I2].
    destruct (snd (RelayModel.step st b)) as [l|] eqn:E; [constructor; [exact (H2 l eq_refl) | exact I1] | exact I1].
Qed.

Definition tc_inv (s : drain_b_c.dstate) : Prop :=
  0 <= drain_b_c.ds_ocap s /\ 0 <= drain_b_c.ds_off s /\ tc_ref (drain_b_c.ds_ref s).

Ltac tc_projg := cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka
  drain_b_c.ds_eintr drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap
  drain_b_c.ds_no drain_b_c.ds_ocap].

(* ================================================================== the two weights *)
Lemma w_sec_range : forall x, 0 <= w_sec x <= 1.
Proof. intros x. unfold w_sec. destruct (Psec x); lia. Qed.

(* a line's bytes (<= 6001) are a primary request *)
Lemma w_sec_small : forall x, 1 <= x <= 6001 -> 1 * w_sec x <= 0 * x.
Proof. intros x Hx. unfold w_sec. rewrite is_sec_iff by lia. destruct (Z.leb_spec 64513 x); lia. Qed.

Lemma w_cls_range : forall c x, 0 <= w_cls c x <= 1.
Proof. intros c x. unfold w_cls. destruct (PresetRoom.in_cls c x); lia. Qed.

(* a request of class c is at least lo c bytes *)
Lemma w_cls_small : forall c x, 1 <= x <= 6001 -> PresetRoom.lo c * w_cls c x <= 1 * x.
Proof.
  intros c x Hx. unfold w_cls. pose proof (PresetRoom.lo_pos c).
  destruct (PresetRoom.in_cls c x) eqn:E; [pose proof (PresetRoom.lo_le c x ltac:(lia) E); lia | lia].
Qed.

Definition pair_bytes (e : rentry) (h : hsrc) : Z :=
  Z.of_nat (length (pending_stream h)) + (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0).

Lemma pair_bytes_nonneg : forall e h, 0 <= pair_bytes e h.
Proof. intros e h. unfold pair_bytes. destruct (re_skip e =? 0); lia. Qed.

(* fr_pair_ok's relay / splitter clause (re_eof = 0): the splitter's partial line is the relay's, so a drain reads
   2 * pair_bytes, and the splitter's lines are short *)

Lemma tc_ref_state : forall e h, (re_skip e = 0 \/ re_skip e = 1) -> re_skip e = hs_overlong h ->
  (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) -> Z.of_nat (length (re_U e)) <= APARTIAL ->
  tc_ref (hs_state h).
Proof.
  intros e h Hsk Ho Hu HU. unfold tc_ref, hs_state. cbn [RelayModel.ls_k RelayModel.ls_w].
  rewrite <- Ho. destruct Hsk as [E|E].
  - right. rewrite <- (Hu E), RelayCap.rc_length_bzs. unfold APARTIAL in HU. lia.
  - left. rewrite E. reflexivity.
Qed.

Section inst.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma tc_out_pos : forall m, (forall b, In b (aout_blks (lm_cap m) (lm_out m)) -> 0 <= snd b) -> 0 <= lm_cap m.
Proof.
  intros m H. destruct (Z.eqb_spec (lm_cap m) 0) as [E|E]; [lia|].
  apply (H (lm_out m, lm_cap m)). unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) E). left. reflexivity.
Qed.

(* ---- part 1, drain: the premises of ReplyTrPeak.fr_LS_drain_pre_c5p that the counts need (fr_LS, dr_at_op and
   0 <= t < OPS_MAX are not needed) *)

Lemma tc_rm_cap : forall m, (forall b, In b (model_blks m) -> 0 <= snd b) -> 0 <= lm_cap m.
Proof. intros m Hpos. apply tc_out_pos. intros b Hb. exact (Hpos b (rm3_in_model_out m b Hb)). Qed.

End inst.

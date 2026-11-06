(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (h-decbox-a1-a2, port-reply row G-BLS3-port): image B's ONE LS instance for the
   B cf top's LS rows, the B twin of image A's lib/A/ReplyLSI.v :1-240 (origin/cold/h-hreply-s5-r1d-reply-b1c
   1318828167d3, blob 38aab0d51ccf), its header part only (port-reply 06:42Z: this file carries LSI and the four TX texts;
   the per-row plugs are the G-BLS lanes'):
     LSI B OM fr_CAP := fr_LS3cp B CALL_ROOM_B /\ fr_OUT OM /\ fr_ENT B /\ fr_CAP   (port-reply 06:43Z)
   with ReplyB3LS3p.fr_LS3cp, ReplyLSBo.fr_OUT (s5-r1d's B fr_OUT; no second copy), ReplyB3LS3e.fr_ENT, and fr_CAP a
   Section slot (A's ReplyLScap.v has no B twin yet; B's room round adds it).
   - TX_LS_drain_step_t: A's text (ReplyLSI.v:126-157, the tied form of A's ReplyLS3cTopxPost.v plus `0 <= t < OPS_MAX`,
     last), at B's drain names (W_LLVMFuzzerTestOneInput_drain_defs, W_contract) and ReplyB3LS3Arms's dr3_* / ls3_*;
   - TX_LS_rm_step_t: the B top's LS_rm_step text (ReplyBTop.v:133 at h-hreply-k3 a6411d87d214) plus `0 <= t < OPS_MAX`,
     last, as A's ReplyLSI.v:159-181 adds it; MT generic (the top instantiates ameter_triv); the remove arm's names
     W_LLVMFuzzerTestOneInput_remove.rm_* as the B top states them (A's tx_rm_*_cost copies are not needed at B);
   - TX_LS_rf_room: ReplyLSBoRf.lx_rf_room_p (s5-r1d's B copy of A's ReplyLS3oRf text) plus `0 <= t <= OPS_MAX`;
   - TX_LS_exit_end_e: the B top's LS_exit_end text (ReplyBTop.v:90) with A's ReplyLS3e.v LS_exit_end3e's four added
     premises, last (relay_finish's final capacity, the loop's t bound, fr_hblks at the return, NoDup); B's conclusion
     keeps its NP conjunct (A dropped NP; B's top states it);
   - lsi_lines_run_cap_ge / lsi_drain_run_ocap_ge / lsi_drain_fin_ocap: A's ReplyLSI.v:80-112, word for word (B's
     ReplyLSBTrPeak.tp_send_line).
   proves no function (kind: invariant lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyLS3B_inst.v, with its module paths changed; 19 of its 191 lines of code are new or changed and 21 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, a Theorem Labs lane row G-BLS3-port): image B's ONE LS instance for the
   B cf top's LS rows, the B twin of image A's lib/A/ReplyLSI.v :1-240 (a working branch
   1318828167d3, sha256 39227fa5fa20; internal record), its header part only (per the ruling: this file carries LSI and the four TX texts;
   the per-row plugs are the G-BLS lanes'):
     LSI B OM fr_CAP := fr_LS3cp B CALL_ROOM_B /\ fr_OUT OM /\ fr_ENT B /\ fr_CAP   (a Theorem Labs lane 06:43Z)
   with ReplyB3LS3p.fr_LS3cp, ReplyLSBo.fr_OUT (s5-r1d's B fr_OUT; no second copy), ReplyB3LS3e.fr_ENT, and fr_CAP a
   Section slot (A's ReplyLScap.v has no B twin yet; B's room round adds it).
   - TX_LS_drain_step_t: A's text (ReplyLSI.v:126-157, the tied form of A's ReplyLS3cTopxPost.v plus `0 <= t < OPS_MAX`,
     last), at B's drain names (W_LLVMFuzzerTestOneInput_drain_defs, W_contract) and ReplyB3LS3Arms's dr3_* / ls3_*;
   - TX_LS_rm_step_t: the B top's LS_rm_step text (ReplyBTop.v:133 at a Theorem Labs lane a6411d87d214) plus `0 <= t < OPS_MAX`,
     last, as A's ReplyLSI.v:159-181 adds it; MT generic (the top instantiates ameter_triv); the remove arm's names
     W_LLVMFuzzerTestOneInput_remove.rm_* as the B top states them (A's tx_rm_*_cost copies are not needed at B);
   - TX_LS_rf_room: ReplyLSBoRf.lx_rf_room_p (s5-r1d's B copy of A's ReplyLS3oRf text) plus `0 <= t <= OPS_MAX`;
   - TX_LS_exit_end_e: A's adopted text word for word (ReplyLSI.v:191-221: the top's LS_exit_end with NP DROPPED, A's
     8187c47f9bc, plus ReplyLS3e.v LS_exit_end3e's four added premises, last), at B's names (a Theorem Labs lane 07:06Z);
   - lsi_lines_run_cap_ge / lsi_drain_run_ocap_ge / lsi_drain_fin_ocap: A's ReplyLSI.v:80-112, word for word (B's
     ReplyLSBTrPeak.tp_send_line).
   - LSI and lsi_parts (A's ReplyLSI.v:225-231 and :358-366): the instance and its projections to fr_LS3cp,
     fr_LS3c, fr_LS3 (at YCfn_cf.CALL_ROOM_B), fr_OUT, fr_ENT and the fr_CAP slot. A's lsi_txp is not ported: its
     target txp_LSx lives in A's ReplyLS3cTopxPost.v, whose B twin is a Theorem Labs lane's; the plug files state it there.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT drain_b_c send_line_b_c gestures_end_b_c gesture_end_c relay_remove_b_c relay_instance_gone_b_c
  RelayCap SlotReads SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBArms ReplyLSBTrPeak ReplyRINVB.
(* the arm files after ReplyLSBArms: the wr_* names are B's _write.v's (lib/B/ReplyB3Base.v's ruling) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyLSBo ReplyLSBoRf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
  ReplyB3Base ReplyB3LS3 ReplyB3LSCntL ReplyB3LS3c ReplyB3LS3Arms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_bx_defs W_LLVMFuzzerTestOneInput_gone_base.

From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3cArms ReplyB3LS3o ReplyB3LS3e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyB3LS3p ReplyB3LS3c ReplyB3LS3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_remove.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== g_capout never falls below 0 over a drain *)
(* A's ReplyLSI.v:78-112: ds_ocap changes only through lines_run's send_line calls (Prog/drain_b_c.v), and send_line
   never lowers a capacity that is >= 0 (ReplyLSBTrPeak.tp_send_line) *)
Lemma lsi_lines_run_cap_ge : forall ls live mx no cap H ka j o ha ks, 0 <= cap ->
  cap <= fst (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))).
Proof.
  induction ls as [|l r IH]; intros live mx no cap H ka j o ha ks Hc; cbn [drain_b_c.lines_run fst snd]; [lia|].
  pose proof (proj2 (tp_send_line live mx no cap (Z.of_nat (length l) + 1) j o Hc)) as H1.
  match goal with |- context [drain_b_c.lines_run live mx ?no' ?cap' ?H' ?ka' r ?j' ?o' ?ha' ?ks'] =>
    pose proof (IH live mx no' cap' H' ka' j' o' ha' ks' ltac:(lia)) as H2 end.
  lia.
Qed.
Lemma lsi_drain_run_ocap_ge : forall f live mx s j a, 0 <= drain_b_c.ds_ocap s ->
  drain_b_c.ds_ocap s <= drain_b_c.ds_ocap (fst (snd (drain_b_c.drain_run f live mx s j a))).
Proof.
  induction f as [|f IH]; intros live mx s j a Hs; [cbn; lia|].
  cbn [drain_b_c.drain_run].
  destruct (drain_b_c.ds_eintr s).
  - cbn [fst snd]. etransitivity; [|apply IH]; cbn [drain_b_c.ds_ocap]; lia.
  - destruct (drain_b_c.ds_pend s) as [|r0 rs]; [cbn [fst snd drain_b_c.ds_ocap]; lia|].
    match goal with |- context [if ?b then _ else _] => destruct b end; [cbn [fst snd drain_b_c.ds_ocap]; lia|].
    match goal with |- context [RelayModel.chunk ?u ?k ?d] => destruct (RelayModel.chunk u k d) as [[u' sk'] rl] end.
    match goal with |- context [drain_b_c.lines_run live mx ?no ?cap ?H ?ka rl ?j3 ?o ?ha ?ks] =>
      pose proof (lsi_lines_run_cap_ge rl live mx no cap H ka j3 o ha ks Hs) as Hl;
      destruct (drain_b_c.lines_run live mx no cap H ka rl j3 o ha ks) as [[tr [[oc' H'] ka']] [[o' ha'] ks']] end.
    cbn [fst snd] in Hl |- *.
    etransitivity; [|apply IH]; cbn [drain_b_c.ds_ocap]; lia.
Qed.
Lemma lsi_drain_fin_ocap : forall live mx NO CAP e h, 0 <= CAP ->
  CAP <= drain_b_c.ds_ocap (drain_b_c.drain_fin live mx NO CAP e h).
Proof.
  intros live mx NO CAP e h Hc. unfold drain_b_c.drain_fin, drain_b_c.drain_go.
  exact (lsi_drain_run_ocap_ge _ live mx (drain_b_c.drain_init NO CAP e h) 0 drain_b_c.dadr0 Hc).
Qed.

(* ================================================================== the texts with `0 <= t < OPS_MAX` *)
Section tx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable TfibB : asyms.
Variable MT : ameter_ops.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.

(* A's ReplyLSI.v:126-157 (top_x's LS_drain_step at A's ReplyLS3cTopxPost.v TX text, plus `0 <= t < OPS_MAX` last) *)
Definition TX_LS_drain_step_t : Prop :=
  forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  LSx cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  (exists rest,
     Permutation (ablocks TfibB ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks TfibB ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks TfibB ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) -> dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h1 -> ls3_dpost m j h e' h1 -> ls3_cpost h1 E' H' ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.

(* the B top's LS_rm_step (ReplyBTop.v:133), plus `0 <= t < OPS_MAX` last (A's ReplyLSI.v:159-181) *)
Definition TX_LS_rm_step_t : Prop :=
  forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  LSx cx t m ly0 S0 ->
  mo_le MT S0 S (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h +
                 W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT (hs_expected h1) (hs_held h1) +
                 W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT H' +
                 sr_cost MT (Some (CheckRep.set_held (CheckRep.set_exp_held h1 E' H') H''))) ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (CheckRep.set_exp_held h1 E' H') O2
    (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks TfibB ly S)
       (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0
          (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k)))
    (re_keys (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0
    (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S.

(* the B top's LS_rf_room (ReplyBTop.v:87) in the peak form of s5-r1d's ReplyLSBoRf.v lx_rf_room_p (A's ReplyLS3oRf.v
   text), plus `0 <= t <= OPS_MAX` last (A's ReplyLSI.v:183-189) *)
Definition TX_LS_rf_room : Prop :=
  forall cx t m ly S,
  LSx cx t m ly S -> 0 <= t <= OPS_MAX ->
  ReplyLSBoRf.lx_rf_room_p fr_MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m).
End tx.

(* the cut's own Local Notation (lib/B/W_LLVMFuzzerTestOneInput_cut.v:161), which does not leave its file *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

Section txe.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable TfibB : asyms.
Variable MT : ameter_ops.
Variable XN_LIB : Z -> Z.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable ARX : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable G : list (Z * Z).
(* A's ReplyLSI.v:191-221 word for word: the top's LS_exit_end with NP dropped (A 8187c47f9bc) and ReplyLS3e.v
   LS_exit_end3e's four added premises, last, in its order *)
Definition TX_LS_exit_end_e : Prop :=
  forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_bx_defs.lx_exit_cost MT m ->
  ajournal_gx_x segs TfibB [] ARX G 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  W_LLVMFuzzerTestOneInput_cut.fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  List.NoDup (ablocks TfibB ly' S') ->
  fr_live_post (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
End txe.

(* ================================================================== the instance *)
(* A's ReplyLSI.v:225-231: LSI := fr_LS3cp B /\ fr_OUT OM /\ fr_ENT B /\ fr_CAP (a Theorem Labs lane 06:43Z: B's twin, with
   fr_LS3cp at YCfn_cf.CALL_ROOM_B like ReplyLSB.fr_LS at the B top) *)
Section inst.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition LSI (B : asyms) (OM : Z) (fr_CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
    (cx : lfcx) (t : Z) (m : lmod) (ly : alayout) (S : astate) : Prop :=
  ReplyB3LS3p.fr_LS3cp B YCfn_cf.CALL_ROOM_B cx t m ly S /\ ReplyLSBo.fr_OUT OM cx t m ly S /\ ReplyB3LS3e.fr_ENT B cx m ly S /\
  fr_CAP cx t m ly S.

(* A's ReplyLSI.v:358-366: the parts of LSI the plugs read *)
Lemma lsi_parts : forall B OM fr_CAP cx t m ly S, LSI B OM fr_CAP cx t m ly S ->
  ReplyB3LS3p.fr_LS3cp B YCfn_cf.CALL_ROOM_B cx t m ly S /\ ReplyB3LS3c.fr_LS3c B YCfn_cf.CALL_ROOM_B cx t m ly S /\
  ReplyB3LS3.fr_LS3 B YCfn_cf.CALL_ROOM_B cx t m ly S /\ ReplyLSBo.fr_OUT OM cx t m ly S /\
  ReplyB3LS3e.fr_ENT B cx m ly S /\ fr_CAP cx t m ly S.
Proof.
  intros B OM fr_CAP cx t m ly S (HP & HO & HE & HC). pose proof HP as (H3c & _). pose proof H3c as (H3 & _).
  exact (conj HP (conj H3c (conj H3 (conj HO (conj HE HC))))).
Qed.
End inst.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj X1bk.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0pb X0pa X0p9 X0qn X0qd.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0qe X0p5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qf.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition as_fm_link (st0 : mstate) (g head : aptr) : mstate :=
let hprev := m_prev (get_meta_rec st0 head) in
let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
upd_meta head (m_set_prev (Some g)) st2.

Definition as_fm_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).

Definition as_queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
match get_head st0 h with
| Some head => as_fm_link st0 g head
| None => as_fm_single st0 h g
end.

Lemma as_queue_eq : forall R h g st0 (k : mstate -> X1qu.M R) (bail : X1qu.M R),
m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
queue h g st0 k bail = k (as_queue_st h g st0).
Proof.
intros R h g st0 k bail Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
unfold as_queue_st, as_fm_link, as_fm_single. destruct (get_head st0 h); reflexivity.
Qed.

Definition as_fm_st (st : mstate) (g : aptr) : mstate := as_queue_st LFree g (put_meta g meta0 st).

Lemma as_free_meta_eq : forall R st g (k : mstate -> X1qu.M R) (bail : X1qu.M R), free_meta g st k bail = k (as_fm_st st g).
Proof.
intros. unfold free_meta, as_fm_st. apply as_queue_eq; rewrite get_meta_rec_put_same; reflexivity.
Qed.

Lemma outside_In W x lo hi : outside W x -> In (lo, hi) W -> ~ (lo <= x < hi).
Proof.
induction W as [|[a b] W IH]; cbn; intros HO HI; [destruct HI|].
destruct HI as [E|HI]; [inversion E; subst; tauto|]. apply IH; tauto.
Qed.

Lemma sub_fp_single W lo hi : In (lo, hi) W -> sub_fp [(lo, hi)] W.
Proof. intros HI x HO. cbn. split; [exact (outside_In W x lo hi HO HI)| exact I]. Qed.

Lemma mrep_set_free_head {RCEIL : RunCeiling} : forall st m v,
mrep st m ->
mrep (upd_ctx (set_free_meta_head v) st) (write_to_mem m (wa (CTX + 16)) (le8 (pw st v))).
Proof.
intros st m v MR. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (length_le8 (pw st v)) as L8.
pose proof (munch_write [(CTX + 16, CTX + 24)] m m (CTX + 16) (le8 (pw st v)) (munch_refl _ m)
ltac:(unfold CTX; lia) ltac:(rewrite L8; unfold CTX; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
pose proof (wmono_write asegs m m (wa (CTX + 16)) (le8 (pw st v)) (wmono_refl asegs m)) as WM.
eapply (mrep_ctx_frameW st (upd_ctx (set_free_meta_head v) st) m _ _ MR MU WM); try reflexivity.
- ctx_same.
- left.
pose proof (rw_cells_write asegs m CTX (ctx_head_cells st) 16 (C8 (pw st (c_free_meta_head (ctx st)))) (C8 (pw st v)) X1 eq_refl eq_refl I) as W.
cbn [cbytes cell_upd ctx_head_cells Nat.eqb Z.of_nat Pos.of_succ_nat Pos.succ] in W.
unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
exact W.
- right. split; [reflexivity| ctx_same].
- right. split; [reflexivity| ctx_same].
- right. split; [reflexivity| ctx_same].
- right. split; [reflexivity| ctx_same].
- right. split; [| ctx_same].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_free_meta_head c_seq c_brk]. reflexivity.
Qed.

Section FAILM.
Context {RCEIL : RunCeiling}.
Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.

Hypothesis FL : forall h, c_free_meta_head (ctx st) = Some h ->
meta_slot st h /\ h <> mt /\ exists p, m_prev (get_meta_rec st h) = Some p /\ meta_slot st p /\ p <> mt.

Definition failW : list (Z * Z) :=
(G, G + 40) :: (CTX + 16, CTX + 24)
:: match c_free_meta_head (ctx st) with
| Some h => (conc st h, conc st h + 40)
:: match m_prev (get_meta_rec st h) with Some p => [(conc st p, conc st p + 40)] | None => [] end
| None => []
end.

End FAILM.

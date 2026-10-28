(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1bq X1br X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0qb X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1fr X1h7 X1kd X1k9.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ij X1il X1im X1ip X1in X1ja X1iu X1j8 X1j4 X1j9 X1it.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g3 X1g1 X1g6 X1g5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gy.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Definition rheap_top_known_stmt {RCEIL : RunCeiling} : Prop :=
forall s LB m (p : bptr) A n, RHEAP s LB m -> In (p, A, n) LB -> RBIG <= n -> rtop_known s p.

Lemma rtop_known_indep : forall (s s' : PState) p, rtop_known s p -> rtop_known s' p.
Proof. intros s s' p H. exact H. Qed.

Section CHUNK.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis RMALLOC : rmalloc_stmt.
Hypothesis RFREE : rfree_stmt.
Hypothesis OREALLOC : ogg_realloc_stmt rtop_known.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Hypothesis RTK : rheap_top_known_stmt.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).
Notation POSTQ := (fun (r : Z) st ms => harness_post (x_ra c) (x_sp c) (x_gp c) tpv (x_s0 c) (x_s1 c) (x_s2 c) (x_s3 c) (x_s4 c) (x_s5 c)
(x_s6 c) (x_s7 c) (x_s8 c) (x_s9 c) (x_s10 c) (x_s11 c) (x_st0 c) (x_LB0 c) (x_AB c) (x_lo c) (x_m0 c) r st ms).
Notation chunk_loopP := (chunk_loop raw_malloc raw_calloc raw_realloc raw_free io_notify io_warning
bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M).
Notation page_loopP := (page_loop raw_malloc raw_calloc raw_realloc raw_free io_notify io_warning
bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M).
Notation cleanupP := (cleanup raw_free (St:=PState)).
Notation FIN := (fun o : outcome bptr => match o with
| Returned => X1qx.mret 0
| Cont h => X1qx.mbind (cleanupP h) (fun _ => X1qx.mret 0) end).

Definition chunk_tail (fuel : nat) (h : hstate bptr) (nb : Z) : M PState Z :=
X1qx.mbind
(X1qx.mbind (ogg_sync_buffer raw_malloc raw_realloc raw_free (h_oy h) nb)
(fun p => let '(data, oy) := p in
let h := set_ogg h oy (h_os h) in
match data, (0 <? nb) with
| None, true => X1qx.munr
| _, _ =>
let oy := match data with Some (_, off) => sync_write oy off (ztake nb (x_payload c)) | None => oy end in
let '(r, oy) := ogg_sync_wrote oy nb in
let h := set_bytes_remaining h oy (h_bytes_remaining h - nb) in
X1qx.mbind (page_loopP (page_fuel (h_oy h)) h)
(fun o => match o with
| Returned => X1qx.mret Returned
| Cont h => if h_bytes_remaining h <=? 0 then X1qx.mret (Cont h) else chunk_loopP fuel (x_payload c) h
end)
end)) FIN.

#[using="Type"] Lemma chunk_loop_eq : forall fuel h,
X1qx.mbind (chunk_loopP (S fuel) (x_payload c) h) FIN
= chunk_tail fuel h (if CHUNK <? h_bytes_remaining h then CHUNK else h_bytes_remaining h).
Proof. intros. reflexivity. Qed.

Definition CUTC2 (h : hstate bptr) (nb : Z) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (jn jb : list byte) (s3w s8w : word),
ms = MS (hregs c h (a_S x) (wz nb) (wz (h_bytes_remaining h)) s3w (wz (h_stream_init h)) s8w (wz (h_speex_serialno h))
x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz 0x1c1fc) fc None m (seg_rom rsegs)
/\ frm0 fc
/\ hrep dec_rep c x h st m (CB 8 jn) (CB 8 jb)
/\ 0 <= nb <= h_bytes_remaining h /\ nb <= 200 /\ (nb < h_bytes_remaining h -> nb = 200).

Definition seg_ok (h : hstate bptr) (x : hax) (nb rv : Z) (data : option (bptr * Z)) : Prop :=
sy_returned (h_oy h) = 0 /\
match data with
| None => nb = 0 /\ rv = 0
| Some (q, off) => off = sy_fill (h_oy h) /\ rv = a_D x + off /\ sy_data (h_oy h) = Some q /\ sy_fill (h_oy h) + nb <= sy_storage (h_oy h)
end.
Definition CUTC3 (h : hstate bptr) (nb rv : Z) (data : option (bptr * Z)) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (x : hax) (jn jb : list byte) (s3w s8w : word),
ms = MS (hregs c h (a_S x) (wz nb) (wz (h_bytes_remaining h)) s3w (wz (h_stream_init h)) s8w (wz (h_speex_serialno h))
x1 t0 t1 t2 (wz rv) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz 0x1c208) fc None m (seg_rom rsegs)
/\ frm0 fc
/\ hrep dec_rep c x h st m (CB 8 jn) (CB 8 jb)
/\ 0 <= nb <= h_bytes_remaining h /\ nb <= 200 /\ (0 < h_bytes_remaining h -> 0 < nb)
/\ seg_ok h x nb rv data.

Definition chunk_tail2 (fuel : nat) (h : hstate bptr) (nb : Z) (data : option (bptr * Z)) : M PState Z :=
X1qx.mbind
(let oy := match data with Some (_, off) => sync_write (h_oy h) off (ztake nb (x_payload c)) | None => h_oy h end in
let '(r, oy) := ogg_sync_wrote oy nb in
let h := set_bytes_remaining h oy (h_bytes_remaining h - nb) in
X1qx.mbind (page_loopP (page_fuel (h_oy h)) h)
(fun o => match o with
| Returned => X1qx.mret Returned
| Cont h => if h_bytes_remaining h <=? 0 then X1qx.mret (Cont h) else chunk_loopP fuel (x_payload c) h
end)) FIN.

Definition chunk_tail3 (fuel : nat) (h : hstate bptr) (nb : Z) : M PState Z :=
X1qx.mbind
(let '(r, oy) := ogg_sync_wrote (h_oy h) nb in
let h := set_bytes_remaining h oy (h_bytes_remaining h - nb) in
X1qx.mbind (page_loopP (page_fuel (h_oy h)) h)
(fun o => match o with
| Returned => X1qx.mret Returned
| Cont h => if h_bytes_remaining h <=? 0 then X1qx.mret (Cont h) else chunk_loopP fuel (x_payload c) h
end)) FIN.

Definition CUTC4 (h : hstate bptr) (nb : Z) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (x : hax) (jn jb : list byte) (s3w s8w : word),
ms = MS (hregs c h (a_S x) (wz nb) (wz (h_bytes_remaining h)) s3w (wz (h_stream_init h)) s8w (wz (h_speex_serialno h))
x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz 0x1c214) fc None m (seg_rom rsegs)
/\ frm0 fc
/\ hrep dec_rep c x h st m (CB 8 jn) (CB 8 jb)
/\ 0 <= nb <= h_bytes_remaining h /\ nb <= 200 /\ (0 < h_bytes_remaining h -> 0 < nb)
/\ sy_fill (h_oy h) + nb <= zlength (sy_buf (h_oy h)) /\ sy_fill (h_oy h) + nb < 2^31 /\ sy_returned (h_oy h) = 0.

#[using="DRF RHF RBR CX"] Lemma chunk_head : forall fuel h st ms,
(forall st' ms' nb, CUTC2 h nb st' ms' -> implM rsegs (chunk_tail fuel h nb) st' POSTQ ms') ->
CUTC dec_rep c h st ms ->
implM rsegs (X1qx.mbind (chunk_loopP (S fuel) (x_payload c) h) FIN) st POSTQ ms.
Proof.
intros fuel h st ms REST CC.
first [ sf_destruct 28%nat CC as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x jn jb s0w s3w s8w -> FRM HR | sf_fb; destruct CC as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & jn & jb & s0w & s3w & s8w & -> & FRM & HR) ].
pose proof HR as sfP_; first [ sf_destruct 16%nat sfP_ as (j16 & jsk & lk & LOW & LKOK) _ _ _ _ _ _ _ _ _ _ _ _ _ (_ & _ & _ & _ & _ & _ & _ & MI & _) PURE | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW & LKOK) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & MI & _) & PURE) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof PURE as sfP_; first [ sf_destruct 21%nat sfP_ as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BRR L4K _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BRR & L4K & _) ].
rewrite chunk_loop_eq.
set (nb := if CHUNK <? h_bytes_remaining h then CHUNK else h_bytes_remaining h).
assert (Hnb : 0 <= nb <= h_bytes_remaining h /\ nb <= 200 /\ (nb < h_bytes_remaining h -> nb = 200)).
{ subst nb. unfold CHUNK. destruct (Z.ltb_spec 200 (h_bytes_remaining h)); lia. }
unfold low_cells in LOW.
change (id (hrep dec_rep c x h st m (CB 8 jn) (CB 8 jb))) in HR.
unfold implM. iprefix. unfold hregs, A_CHUNK, wz.

zstep. zstep. zstep.
if_cases K; zify_cond K; [| zstep].
all: apply evt_done; apply REST.
all: unfold CUTC2; sf_eexists 16%nat; first [ unshelve sf_eexists 8%nat; [ exact (F) | exact (fc) | exact (m) | exact (x) | exact (jn) | exact (jb) | exact (s3w) | exact (s8w) | ] | sf_fb; exists F, fc, m, x, jn, jb, s3w, s8w ].
1: replace nb with (h_bytes_remaining h) by (subst nb; unfold CHUNK; destruct (Z.ltb_spec 200 (h_bytes_remaining h)); lia).
2: replace nb with 200 by (subst nb; unfold CHUNK; destruct (Z.ltb_spec 200 (h_bytes_remaining h)); lia).
all: split; [reflexivity|].
all: split; [exact FRM|].
all: split; [unfold id in HR; exact HR| lia].
Qed.

End CHUNK.

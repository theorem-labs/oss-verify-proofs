(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1nt X1rg X1rh X1re X1od X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1qy X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X09u X0af X05l X05m X06d X071.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12c X14x X0r0 X0r9 X0ra X0qz X0v9 X0rb X0wl X0wm X110 X10j X10c
X0x2 X0x1 X0xn X0xq X0xm X0y6.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Definition h_eos0 (h : hstate unit) : hstate unit := set_bits_st h (h_bits h) (h_st h) 0.

Section Cuts.
Variable RT : rt_sig.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.
Local Notation PMh := (PMfd F0 fs0).
Local Notation usp := (x_usp X). Local Notation S1 := (x_S1 X). Local Notation F := (x_F X). Local Notation sf := (x_sf X).
Local Notation tpv := (Z_to_bv 64 0x638c98).

Definition hsig_k (Σ1 : rts RT) (a : haux) (h : hstate unit) (k : Z) : Prop :=
rt_live RT Σ1 = a_P a ++ x_live X /\ List.NoDup (map fst (a_P a)) /\ Permutation (a_P a) (h_own a h)
/\ rt_frames RT Σ1 = [(F, 8%nat)] /\ rt_sp0 RT Σ1 = x_sp0 X /\ rt_pois RT Σ1 = []
/\ x_cr0 X - h_cost h - k <= rt_credit RT Σ1.
Lemma hsig_k_of : forall Σ1 a h, hsig RT X Σ1 a h -> hsig_k Σ1 a h 0.
Proof. intros Σ1 a h (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold hsig_k. repeat split; try assumption. lia. Qed.
Lemma hsig_of_k : forall Σ1 a h, hsig_k Σ1 a h 0 -> hsig RT X Σ1 a h.
Proof. intros Σ1 a h (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold hsig. repeat split; try assumption. lia. Qed.
Lemma hsig_k_weaken : forall Σ1 a h k k', k <= k' -> hsig_k Σ1 a h k -> hsig_k Σ1 a h k'.
Proof. intros Σ1 a h k k' K (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold hsig_k. repeat split; try assumption. lia. Qed.

Definition pc_room (h : hstate unit) : Prop :=
h_packet_count h + 1 + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * h_consumed X h /\ h_st h <> None.

Definition at_HP (h : hstate unit) (op : packet) (pno nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r10 t3 t4 t5 t6 : word)
(v48 v56 v88 j224 j232 gw : word) (ogc kc : list cell),
ASTA RT Σ1 PMh (eq (MS (h_regs X h ra t0 t1 t2 (Z64 (h_speex_serialno h)) a1 a2 a3 a4 a5 a6 a7
(Z64 (F + HO_OP)) (Z64 (h_speex_serialno h)) (Z64 0x7fffffff) (Z64 pno) (Z64 (pk_bytes op)) r10 t3 t4 t5 t6)
Fx (Z64 A_HP) fc None m (seg_rom bsegs))) c
/\ X1cn.frm0 fc /\ hsig RT X Σ1 a h /\ h_iter X h nbr brem0 /\ h_stream_init h = 1 /\ h_eos h = 0 /\ h_packet_count h = 0 /\ 0 <= pno <= h_packet_count h
/\ h_skip_word v48 h
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232 a h) ogc (op_cells (a_Bd a) (Some op) gw kc)
/\ og_junk ogc /\ cells_size kc = 48%nat
/\ pk_off op = 0 /\ 0 <= pk_bytes op /\ pk_off op + pk_bytes op <= os_body_fill (h_os h)
/\ h_packet_count h + 1 + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * h_consumed X h.

Definition at_KT (h : hstate unit) (pno nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r2 r7 r9 r10 t3 t4 t5 t6 : word)
(v48 v56 v88 j224 j232 : word) (ogc opc : list cell),
ASTA RT Σ1 PMh (eq (MS (h_regs X h ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r2 (Z64 (h_eos h)) r7 (Z64 pno) r9 r10 t3 t4 t5 t6)
Fx (Z64 A_KT) fc None m (seg_rom bsegs))) c
/\ X1cn.frm0 fc /\ hsig_k Σ1 a h (10 * H_DEC_CREDIT) /\ h_iter X h nbr brem0 /\ h_stream_init h = 1 /\ (h_eos h = 0 \/ h_eos h = 1)
/\ 0 <= pno <= h_packet_count h + 1 /\ h_skip_word v48 h
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232 a h) ogc opc
/\ og_junk ogc /\ op_junk opc /\ pc_room h.

Definition at_DHk (h : hstate unit) (st : dec_state unit) (b : bits_st unit) (n : nat) (eosf pno nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r8 t3 t4 t5 t6 : word)
(v48 v56 v88 j224 j232 : word) (ogc opc : list cell),
ASTA RT Σ1 PMh (eq (MS (h_regs X h ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z64 pno) (Z64 eosf) (Z64 0x7fffffff) r8 (Z64 (h_skip_samples h))
(Z64 (h_nframes h - Z.of_nat n)) t3 t4 t5 t6) Fx (Z64 A_DH) fc None m (seg_rom bsegs))) c
/\ X1cn.frm0 fc /\ (1 <= n)%nat /\ Z.of_nat n <= h_nframes h /\ (eosf = 0 \/ eosf = 1) /\ h_st h <> None /\ h_eos h = 0 /\ 1 <= pno <= h_packet_count h + 1
/\ hsig_k Σ1 a (set_bits_st h b (Some st) 0) (H_DEC_CREDIT * (10 - Z.of_nat n)) /\ h_iter X h nbr brem0 /\ h_stream_init h = 1
/\ h_skip_word v48 h /\ (v88 <> Z64 0 -> h_skip_samples h < 0)
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a (set_bits_st h b (Some st) 0) (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232 a h) ogc opc
/\ og_junk ogc /\ op_junk opc /\ pc_room h.
End Cuts.

Definition h_hdr_cps (RT : rt_sig) OUT_rep ERR_rep IO_FP X F0 fs0 : Prop :=
hinv_ok OUT_rep IO_FP X -> forall (h : hstate unit) (op : packet) (pno nbr brem0 : Z) (q q' : pst) (r : option (hstate unit)) (bs : list Z),
prun (hP_process_header h (packet_data (h_os h) op) (pk_bytes op)) q = Some (r, q') -> p_err q' = p_err q ++ bs ->
cpsE bsegs (at_HP RT OUT_rep ERR_rep IO_FP X F0 fs0 h op pno nbr brem0) (Spec.X1nu.evw 2 bs)
(fun c => match r with
| None => at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c
| Some h3 => at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count h3) pno nbr brem0 c
end).

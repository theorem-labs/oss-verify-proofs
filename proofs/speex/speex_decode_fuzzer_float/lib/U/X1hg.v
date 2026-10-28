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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ij X1ii X1il X1im X1is X1ip X1iq X1in X1ja X1iu X1j8 X1j4 X1j9 X1it X1j2 X1iv X1iw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g3 X1g1 X1g6 X1g5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h9 X1gy.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require UbDec.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition hrepx {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (x : hax) (h : hstate bptr) (st : PState) (m : mem) (cn cb : cell) (OG OP : list cell) : Prop :=
(exists j16 jsk lk, rw_cells rsegs m (aLOW c) (low_cells c h j16 cn cb jsk lk) /\ lk_ok h lk) /\ csize cn = 8%nat /\ csize cb = 8%nat
/\ (exists stb, rw_cells rsegs m (aSTEREO c) [CB 24 stb])
/\ os_piece m c x h
/\ (rw_cells rsegs m (aOP c) OP /\ cells_size OP = 48%nat)
/\ (rw_cells rsegs m (aOG c) OG /\ cells_size OG = 32%nat)
/\ sync_rep m (aOY c) (a_D x) (h_oy h) (a_sybytes x)
/\ bits_rep rsegs m (aBITS c) (a_Dc x) (h_bits h)
/\ (exists pad, rw_cells rsegs m (aFSZ c) (fsz_cells h pad))
/\ (exists outb, u8arr rsegs m (aOUT c) outb /\ Z.of_nat (length outb) = 8000)
/\ (exists hij, rw_cells rsegs m (aCBK c) [CB 48 hij])
/\ rw_cells rsegs m (aSAV c) (sav_cells c)
/\ dec_piece dec_rep m c x h
/\ hglob c x h st m
/\ hpure c x h.

Lemma hrepx_hrep {RCEIL : RunCeiling} : forall dec_rep c x h st m cn cb OG OP,
hrepx dec_rep c x h st m cn cb OG OP -> hrep dec_rep c x h st m cn cb.
Proof.
intros dec_rep c x h st m cn cb OG OP sfH_; first [ sf_destruct 8%nat sfH_ as L C1 C2 STB OSP [OP1 OP2] [OG1 OG2] REST | sf_fb; destruct sfH_ as (L & C1 & C2 & STB & OSP & [OP1 OP2] & [OG1 OG2] & REST) ].
split; [exact L|]. split; [exact C1|]. split; [exact C2|]. split; [exact STB|]. split; [exact OSP|].
split. { apply rw_cells_forget in OP1. rewrite OP2 in OP1. exact OP1. }
split. { apply rw_cells_forget in OG1. rewrite OG2 in OG1. exact OG1. }
exact REST.
Qed.

Lemma hrep_hrepx {RCEIL : RunCeiling} : forall dec_rep c x h st m cn cb,
hrep dec_rep c x h st m cn cb -> exists ogj opj, hrepx dec_rep c x h st m cn cb [CB 32 ogj] [CB 48 opj].
Proof.
intros dec_rep c x h st m cn cb sfH_; first [ sf_destruct 8%nat sfH_ as L C1 C2 STB OSP [opj OP] [ogj OG] REST | sf_fb; destruct sfH_ as (L & C1 & C2 & STB & OSP & [opj OP] & [ogj OG] & REST) ].
exists ogj, opj. split; [exact L|]. split; [exact C1|]. split; [exact C2|]. split; [exact STB|]. split; [exact OSP|].
split; [split; [exact OP| reflexivity]|]. split; [split; [exact OG| reflexivity]|]. exact REST.
Qed.

Lemma cells32_junk4 : forall m A cs, rw_cells rsegs m A cs -> cells_size cs = 32%nat ->
exists j0 j1 j2 j3, rw_cells rsegs m A [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3].
Proof.
intros m A cs H Hs. apply rw_cells_forget in H. rewrite Hs in H. destruct H as [junk H].
apply (rw_cells_split_CB _ _ _ [] _ _ [] [8; 8; 8; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
sf_eexists 4%nat. exact H.
Qed.
Lemma cells48_junk6 : forall m A cs, rw_cells rsegs m A cs -> cells_size cs = 48%nat ->
exists k0 k1 k2 k3 k4 k5, rw_cells rsegs m A [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
Proof.
intros m A cs H Hs. apply rw_cells_forget in H. rewrite Hs in H. destruct H as [junk H].
apply (rw_cells_split_CB _ _ _ [] _ _ [] [8; 8; 8; 8; 8; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
sf_eexists 6%nat. exact H.
Qed.

Lemma page_cells_size : forall D og, cells_size (page_cells D og) = 32%nat.
Proof. intros. reflexivity. Qed.

Definition page_budget (c : hcx) (h : hstate bptr) (og : page) : Prop :=
exists cold, 0 <= cold /\ 0 <= hpend h
/\ os_lacing_fill (h_os h) <= cold /\ os_body_fill (h_os h) <= cold
/\ os_lacing_storage (h_os h) <= 1568 + cold /\ os_body_storage (h_os h) <= 17408 + 2 * cold
/\ cold + pg_header_len og + pg_body_len og <= hconsumed c h
/\ h_packet_count h <= 162 * cold
/\ h_packet_count h + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * cold.

Lemma page_budget_hbudget : forall c h og, 0 <= pg_header_len og -> 0 <= pg_body_len og ->
page_budget c h og -> hbudget c h.
Proof. intros c h og H1 H2 (cold & B). unfold hbudget. lia. Qed.

Definition PGB {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (h : hstate bptr) (og : page) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (nbr brem0 : Z) (s0w s3w s8w : word) (OP : list cell),
ms = MS (hregs c h (a_S x) s0w (wz brem0) s3w (wz (h_stream_init h)) s8w (wz (h_speex_serialno h)) x1 t0 t1 t2 a0 (wz (1 - h_stream_init h)) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz A_PAGEB) fc None m (seg_rom rsegs)
/\ frm0 fc
/\ hrepx dec_rep c x h st m (C8 (wz nbr)) (C8 (wz brem0)) (page_cells (a_D x) og) OP /\ low_ok h nbr brem0
/\ page_ok (h_oy h) og /\ sy_data (h_oy h) <> None /\ page_budget c h og.

Definition PGS {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (h : hstate bptr) (og : page) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (nbr brem0 : Z) (s3w s5w s8w : word) (OP : list cell),
ms = MS (hregs c h (a_S x) (wz (h_last_granule h)) (wz brem0) s3w s5w s8w (wz (h_speex_serialno h)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz 0x1c260) fc None m (seg_rom rsegs)
/\ frm0 fc /\ h_stream_init h = 1
/\ hrepx dec_rep c x h st m (C8 (wz nbr)) (C8 (wz brem0)) (page_cells (a_D x) og) OP /\ low_ok h nbr brem0
/\ page_ok (h_oy h) og /\ sy_data (h_oy h) <> None /\ page_budget c h og.

Definition PGG {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (h : hstate bptr) (og : page) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (nbr brem0 : Z) (s3w s5w s8w : word) (OP : list cell),
ms = MS (hregs c h (a_S x) (wz (h_last_granule h)) (wz brem0) s3w s5w s8w (wz (h_speex_serialno h)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz 0x1c290) fc None m (seg_rom rsegs)
/\ frm0 fc /\ h_stream_init h = 1
/\ hrepx dec_rep c x h st m (C8 (wz nbr)) (C8 (wz brem0)) (page_cells (a_D x) og) OP /\ low_ok h nbr brem0
/\ page_ok (h_oy h) og /\ sy_data (h_oy h) <> None /\ os_body_returned (h_os h) = 0.

Definition PK {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (h : hstate bptr) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (nbr brem0 pno : Z) (s0w s3w s5w s8w : word),
ms = MS (hregs c h (a_S x) s0w (wz pno) s3w s5w s8w (wz (h_speex_serialno h)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz A_PKT) fc None m (seg_rom rsegs)
/\ frm0 fc /\ h_stream_init h = 1 /\ h_eos h = 0
/\ hrep dec_rep c x h st m (C8 (wz nbr)) (C8 (wz brem0)) /\ low_ok h nbr brem0
/\ 0 <= pno <= h_packet_count h /\ (h_packet_count h = 0 -> os_body_returned (h_os h) = 0).

Definition PPOST {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop) (c : hcx) (br0 : Z)
(o : outcome bptr) (st : PState) (ms : machine_state) : Prop :=
match o with
| Cont h => PGX dec_rep c h st ms /\ h_bytes_remaining h = br0
| Returned => HFIN c st ms
end.

Definition PKPOST {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop) (c : hcx) (br0 : Z) (oy0 : sync_st bptr)
(o : outcome bptr) (st : PState) (ms : machine_state) : Prop :=
match o with
| Cont h => PGN dec_rep c h st ms /\ h_bytes_remaining h = br0 /\ h_oy h = oy0
| Returned => HFIN c st ms
end.

Notation page_loopP := (page_loop raw_malloc raw_calloc raw_realloc raw_free io_notify io_warning
bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M).
Notation packet_loopP := (packet_loop raw_calloc raw_realloc raw_free io_notify io_warning
bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M).
Notation cleanupP := (cleanup raw_free (St:=PState)).

Definition page_restP (fuel' : nat) (hdr : list Z) (h : hstate bptr) : M PState (outcome bptr) :=
match granule_step h hdr with
| None => X1qx.mbind (cleanupP h) (fun _ => X1qx.mret Returned)
| Some skip =>
let h := set_granule h (ogg_page_granulepos hdr) skip in
X1qx.mbind (packet_loopP (packet_fuel (h_os h)) h 0)
(fun o => match o with
| Returned => X1qx.mret Returned
| Cont h => page_loopP fuel' h
end)
end.

Definition page_rest2P (fuel' : nat) (oy : sync_st bptr) (og : page) (h : hstate bptr) : M PState (outcome bptr) :=
let hdr := page_header oy og in
let body := page_body oy og in
let serial := ogg_page_serialno hdr in
let h := (if negb (serial =? os_serialno (h_os h)) then
let '(r, os) := ogg_stream_reset_serialno (h_os h) serial in set_ogg h (h_oy h) os
else h) in
X1qx.mbind (ogg_stream_pagein raw_realloc raw_free (h_os h) hdr body)
(fun x => let '(r, os) := x in page_restP fuel' hdr (set_ogg h (h_oy h) os)).

Definition page_bodyP (fuel' : nat) (h : hstate bptr) (og : page) : M PState (outcome bptr) :=
let serial := ogg_page_serialno (page_header (h_oy h) og) in
X1qx.mbind (if h_stream_init h =? 0 then
X1qx.mbind (ogg_stream_init raw_malloc raw_free serial) (fun x => let '(r, os) := x in X1qx.mret (set_stream_init h os))
else X1qx.mret h)
(fun h' => page_rest2P fuel' (h_oy h) og h').

Lemma page_loop_S : forall fuel' (h : hstate bptr),
page_loopP (S fuel') h =
match ogg_sync_pageout (h_oy h) with
| None => X1qx.munr
| Some ((r, oog), oy) =>
if negb (r =? 1) then X1qx.mret (Cont (set_ogg h oy (h_os h)))
else match oog with
| None => X1qx.munr
| Some og => page_bodyP fuel' (set_ogg h oy (h_os h)) og
end
end.
Proof. intros. reflexivity. Qed.

Lemma ubytes_firstn : forall n (l : list byte), ubytes (firstn n l) = firstn n (ubytes l).
Proof. intros. unfold ubytes. rewrite firstn_map. reflexivity. Qed.
Lemma ubytes_skipn : forall n (l : list byte), ubytes (skipn n l) = skipn n (ubytes l).
Proof. intros. unfold ubytes. rewrite skipn_map. reflexivity. Qed.
Lemma length_ubytes : forall (l : list byte), length (ubytes l) = length l.
Proof. intros. unfold ubytes. apply map_length. Qed.

Lemma zslice_of_prefix : forall (buf : list Z) (ub : list Z) a n,
firstn (length buf) ub = buf -> (length buf <= length ub)%nat -> 0 <= a -> 0 <= n -> a + n <= Z.of_nat (length buf) ->
zslice a n buf = firstn (Z.to_nat n) (skipn (Z.to_nat a) ub).
Proof.
intros buf ub a n PRE LE Ha Hn Han. unfold zslice, ztake, zdrop. rewrite <- PRE.
rewrite skipn_firstn_comm. rewrite firstn_firstn. f_equal. lia.
Qed.

Lemma page_hs : forall m A D (oy : sync_st bptr) bytes og,
sync_rep m A D oy bytes -> sync_inv oy -> page_ok oy og -> sy_data oy <> None ->
let hs := firstn (Z.to_nat (pg_header_len og)) (skipn (Z.to_nat (pg_hdr og)) bytes) in
let bs := firstn (Z.to_nat (pg_body_len og)) (skipn (Z.to_nat (pg_hdr og + pg_header_len og)) bytes) in
bytes_at rsegs m (D + pg_hdr og) hs /\ bytes_at rsegs m (D + pg_hdr og + pg_header_len og) bs
/\ Z.of_nat (length hs) = pg_header_len og /\ Z.of_nat (length bs) = pg_body_len og
/\ ubytes hs = page_header oy og /\ ubytes bs = page_body oy og
/\ pg_header_len og = 27 + znth (ubytes hs) 26 /\ 0 <= znth (ubytes hs) 26 <= 255
/\ 0 <= pg_hdr og /\ pg_hdr og + pg_header_len og + pg_body_len og <= Z.of_nat (length bytes)
/\ 0 <= pg_body_len og.
Proof.
intros m A D oy bytes og sfH_; first [ sf_destruct 4%nat sfH_ as OBJ FOK DAT SEP | sf_fb; destruct sfH_ as (OBJ & FOK & DAT & SEP) ]; intros SINV POK NN. cbv zeta.
pose proof POK as sfP_; first [ sf_destruct 7%nat sfP_ as P0 P1 P2 P3 P4 P5 P6 | sf_fb; destruct sfP_ as (P0 & P1 & P2 & P3 & P4 & P5 & P6) ].
pose proof SINV as sfP_; first [ sf_destruct 5%nat sfP_ as I1 I2 I3 I4 I5 | sf_fb; destruct sfP_ as (I1 & I2 & I3 & I4 & I5) ]. unfold zlength in I2, P5.
unfold sync_data in DAT. destruct (sy_data oy) as [p|]; [| exfalso; exact (NN eq_refl)].
first [ sf_destruct 5%nat DAT as D1 ARR LEN PRE LE | sf_fb; destruct DAT as (D1 & ARR & LEN & PRE & LE) ]. destruct ARR as [BA WR].
pose proof (znth_bytes_ok (sy_buf oy) (pg_hdr og + 26) I5) as NS.
assert (HH : ubytes (firstn (Z.to_nat (pg_header_len og)) (skipn (Z.to_nat (pg_hdr og)) bytes)) = page_header oy og).
{ unfold page_header. rewrite ubytes_firstn, ubytes_skipn. symmetry. apply zslice_of_prefix; try assumption; try lia.
rewrite length_ubytes. exact LE. }
assert (HB : ubytes (firstn (Z.to_nat (pg_body_len og)) (skipn (Z.to_nat (pg_hdr og + pg_header_len og)) bytes)) = page_body oy og).
{ unfold page_body. rewrite ubytes_firstn, ubytes_skipn. symmetry. apply zslice_of_prefix; try assumption; try lia.
rewrite length_ubytes. exact LE. }
assert (N26 : znth (page_header oy og) 26 = znth (sy_buf oy) (pg_hdr og + 26)).
{ unfold page_header. apply znth_zslice; lia. }
split. { replace (D + pg_hdr og) with (D + Z.of_nat (Z.to_nat (pg_hdr og))) by lia. apply bytes_at_sub; [exact BA| lia]. }
split. { replace (D + pg_hdr og + pg_header_len og) with (D + Z.of_nat (Z.to_nat (pg_hdr og + pg_header_len og))) by lia. apply bytes_at_sub; [exact BA| lia]. }
split. { rewrite firstn_length_le; [lia|]. rewrite skipn_length. lia. }
split. { rewrite firstn_length_le; [lia|]. rewrite skipn_length. lia. }
split; [exact HH|]. split; [exact HB|]. rewrite HH, N26. lia.
Qed.

Definition stream_init_post2 {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (A lo B serialno : Z) (m : mem)
(r : Z * stream_st bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (LB' : list block),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (fst r)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
/\ cmod [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 408)] LB (bv_unsigned sp) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ RHEAP s' LB' m' /\ (forall b, In b LB -> In b LB')
/\ match r with
| (rc, os') =>
(rc = 0 /\ exists pb pl pg Bd L Gv jb jl jg,
os' = init_os (Some pb) (Some pl) (Some pg) serialno
/\ LB' = (pg, Gv, 8192) :: (pl, L, 4096) :: (pb, Bd, 16384) :: LB
/\ rblock_range Bd 16384 /\ rblock_range L 4096 /\ rblock_range Gv 8192
/\ rw_cells rsegs m' A (stream_cells Bd L Gv zero_hdr os')
/\ rw_cells rsegs m' Bd [CB 16384 jb] /\ rw_cells rsegs m' L [CB 4096 jl] /\ rw_cells rsegs m' Gv [CB 8192 jg])
\/ (rc = -1 /\ os' = stream_zero /\ Permutation LB' LB
/\ rw_cells rsegs m' A (stream_cells 0 0 0 zero_hdr stream_zero))
end.

Definition ogg_stream_init_stmt2 {RCEIL : RunCeiling} : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (A lo B serialno : Z) (junk : list byte) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 408 <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 - RMALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP -> -2^31 <= serialno < 2^31 ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 serialno -> rw_cells rsegs m A [CB 408 junk] ->
implM rsegs (ogg_stream_init raw_malloc raw_free serialno) s
(stream_init_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB A lo B serialno m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_init) fc None m (seg_rom rsegs)).

Definition pagein_post2 {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (pb pl pg : bptr) (A G Dsy lo B : Z) (og : page) (shdr hs bs : list byte) (m : mem)
(r : Z * stream_st bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (LB' : list block),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (fst r)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ RHEAP s' LB' m'
/\ (forall b, In b LB -> blk_id b <> pb -> blk_id b <> pl -> blk_id b <> pg -> In b LB')
/\ cmod [(A, A + 408)] (lb_remove pg (lb_remove pl (lb_remove pb LB))) (bv_unsigned sp) m m'
/\ rw_cells rsegs m' G (page_cells Dsy og) /\ bytes_at rsegs m' (Dsy + pg_hdr og) hs
/\ bytes_at rsegs m' (Dsy + pg_hdr og + pg_header_len og) bs
/\ (fst r = 0 \/ fst r = -1)
/\ ( (exists (Bd' L' Gv' : Z) (pb' pl' pg' : bptr) bodybytes' lws' gws',
os_body_data (snd r) = Some pb' /\ os_lacing_vals (snd r) = Some pl' /\ os_granule_vals (snd r) = Some pg'
/\ In (pb', Bd', os_body_storage (snd r)) LB' /\ In (pl', L', os_lacing_storage (snd r) * 4) LB'
/\ In (pg', Gv', os_lacing_storage (snd r) * 8) LB'
/\ rtop_known s' pb' /\ rtop_known s' pl' /\ rtop_known s' pg'
/\ stream_blocks LB' (snd r) Bd' L' Gv' /\ stream_fields_ok (snd r)
/\ rw_cells rsegs m' A (stream_cells Bd' L' Gv' shdr (snd r))
/\ stream_arrays m' (snd r) Bd' L' Gv' bodybytes' lws' gws'
/\ Permutation LB' ((pb', Bd', os_body_storage (snd r)) :: (pl', L', os_lacing_storage (snd r) * 4)
:: (pg', Gv', os_lacing_storage (snd r) * 8)
:: lb_remove pg (lb_remove pl (lb_remove pb LB))))
\/ (snd r = stream_zero /\ rw_cells rsegs m' A (stream_cells 0 0 0 zero_hdr stream_zero)
/\ Permutation LB' (lb_remove pg (lb_remove pl (lb_remove pb LB)))) ).

Definition ogg_stream_pagein_stmt2 {RCEIL : RunCeiling} : Prop :=
forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (os : stream_st bptr) (pb pl pg psy : bptr)
(A G Dsy nsy Bd L Gv lo B : Z) (og : page) (shdr hs bs bodybytes : list byte) (lws gws : list word) (errv : word),
RHEAP s LB m ->
stream_blocks LB os Bd L Gv ->
os_body_data os = Some pb -> os_lacing_vals os = Some pl -> os_granule_vals os = Some pg ->
In (pb, Bd, os_body_storage os) LB -> In (pl, L, os_lacing_storage os * 4) LB -> In (pg, Gv, os_lacing_storage os * 8) LB ->
rtop_known s pb -> rtop_known s pl -> rtop_known s pg ->
In (psy, Dsy, nsy) LB -> psy <> pb -> psy <> pl -> psy <> pg ->
rw_cells rsegs m A (stream_cells Bd L Gv shdr os) -> length shdr = 284%nat ->
stream_arrays m os Bd L Gv bodybytes lws gws ->
stream_fields_ok os -> stream_inv os -> body_inv os -> lacing_vals_ok (os_lacing os) ->
rw_cells rsegs m G (page_cells Dsy og) ->
bytes_at rsegs m (Dsy + pg_hdr og) hs -> bytes_at rsegs m (Dsy + pg_hdr og + pg_header_len og) bs ->
length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat -> Z.of_nat (length hs) = pg_header_len og ->
Z.of_nat (length bs) = pg_body_len og -> zsum (lacing_of (ubytes hs)) <= pg_body_len og ->
0 <= pg_hdr og -> pg_hdr og + pg_header_len og + pg_body_len og <= nsy ->
(os_lacing_storage os + znth (ubytes hs) 26 + 33) * 8 < MMAP_THRESHOLD ->
os_body_storage os + pg_body_len og + 1024 < MMAP_THRESHOLD ->
1024 <= os_lacing_storage os ->
rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 408 <= B -> bv_unsigned sp <= G ->
(A + 408 <= G \/ G + 32 <= A) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 176 - OGG_REALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
implM rsegs (ogg_stream_pagein raw_realloc raw_free os (ubytes hs) (ubytes bs)) s
(pagein_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB pb pl pg A G Dsy lo B og shdr hs bs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_pagein) fc None m (seg_rom rsegs)).

Lemma hglob_frame_lo {RCEIL : RunCeiling} : rheap_frame_stmt -> rheap_block_range_stmt ->
forall (c : hcx) x h st mb m W,
hcx_ok c -> hglob c x h st mb ->
munch W mb m -> wmono rsegs mb m -> Forall (fun iv => x_lo c <= fst iv /\ snd iv <= usp c) W ->
mem_inv rsegs m -> stk rsegs m (x_lo c) (hsp c) ->
hglob c x h st m.
Proof.
intros RHF RBR c x h st mb m W CX sfH_; first [ sf_destruct 11%nat sfH_ as HP PERM PAY TP SEW [errv ERR] AUX _ _ PE SO | sf_fb; destruct sfH_ as (HP & PERM & PAY & TP & SEW & [errv ERR] & AUX & _ & _ & PE & SO) ]; intros MU WM FW MI ST.
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ]. unfold RFUZZ_STACK in LO.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
assert (HL : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
assert (OUTF : forall a, (a < x_lo c \/ usp c <= a) -> outside W a).
{ intros a Ha. clear -Ha FW LO. induction FW as [|[lo1 hi1] W' HH FW IH]; cbn; [exact I|]. cbn in HH. split; [lia| exact IH]. }
split. { eapply RHF; [exact HP| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. intros [lo1 hi1] HH. left. cbn in *. lia. }
split; [exact PERM|].
split. { eapply bytes_at_agree; [exact AG| exact PAY|]. intros a Ha. apply OUTF.
pose proof (bytes_at_bound _ _ _ _ PAY) as PB. rewrite to_bytes_length in PB, Ha.
destruct PIN as [[NE IN]|[E EP]].
- left. pose proof (RBR _ _ _ _ HP (HL _ IN)) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. cbn in B4. unfold zlength in *. lia.
- left. rewrite EP in Ha. rewrite E in Ha. cbn in Ha. unfold REMPTY in *. lia. }
split. { eapply rtables_pristine_agree; [exact AG| | exact TP]. intros a Ha. apply OUTF. left. unfold RTABLES_HI in Ha. lia. }
split. { eapply stderr_wfile_agree; [exact AG| | exact SEW]. intros a Ha. apply OUTF. left. unfold stderr_addr in Ha. lia. }
split. { exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. apply OUTF. left. cbn in Ha. unfold RERRNO in Ha. lia. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. intros [lo1 hi1] HH. cbn in *. unfold RAUXV_CELL. lia. }
split; [exact MI|]. split; [exact ST|].
split. { eapply (pres_except_frame RBR c st (a_LB x)); [exact CX| exact HP| exact HL| exact PE| exact AG|].
eapply Forall_impl; [| exact FW]. intros [lo1 hi1] HH. cbn in *. lia. }
exact SO.
Qed.

Ltac prune_for_lia :=
repeat match goal with
| H : _ \/ _ |- _ => clear H
| H : _ <-> _ |- _ => clear H
| H : Permutation _ _ |- _ => clear H
| H : List.NoDup _ |- _ => clear H
| H : @ex _ _ |- _ => clear H
| H : forall _, _ |- _ => clear H
end.
Ltac plia := prune_for_lia; lia.
Ltac phlia := first [ plia | unfold rblock_range, RERRNO, RTABLES_LO, RTABLES_HI, RAUXV_CELL, REMPTY, RGOT_SSP, RSSP_GUARD, alloc_ceiling in *; plia ].
Ltac side_conjc :=
lazymatch goal with
| |- _ /\ _ => split; side_conjc
| |- outside _ _ => cbn [outside fst snd]; phlia
| |- ~ in_ivs _ _ => cbn [in_ivs fst snd]; phlia
| |- rclient_addr _ _ _ => unfold rclient_addr;
first [ left; phlia
| right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; phlia
| right; right; eexists; split; [ solve [eauto 12 using in_eq, in_cons] | cbn [blk_addr blk_size fst snd]; phlia ] ]
| |- stderr_addr _ -> _ => unfold stderr_addr; intros ?; side_conjc
| |- _ => first [ phlia | assumption ]
end.
Ltac side1c :=
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn beta; cbn [cells_size csize Nat.add Nat.mul length] in Ha; fold_of_nat_lits_in Ha;
prune_for_lia; rewrite ?Z2Nat.id in Ha by lia; try unfold stderr_addr in Ha; side_conjc.

Definition granule_sel (fs gfs nf lg pg nbp : Z) : option Z :=
let a := nbp * gfs * nf in
let b := pg - lg in
if (a <? b) || (INT64_MAX ÷ 640 - a <? - b) || (INT64_MAX ÷ 640 <? a - b) then None
else let skip := s32 (fs * (a - b) ÷ gfs) in
if skip =? INT_MIN then None else Some skip.

Lemma ga_lxl64 : forall x, -2^63 <= x < 2^63 ->
Z.lxor (Z.land x 18446744073709551615) 9223372036854775808 = x + 9223372036854775808.
Proof.
intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
apply UbDec.lxs64. exact Hx.
Qed.

Lemma ga_lxs_sub : forall x y, -2^63 <= x - y < 2^63 ->
Z.lxor (Z.land (x + - Z.land y 18446744073709551615) 18446744073709551615) 9223372036854775808 = x - y + 9223372036854775808.
Proof.
intros x y Hxy. change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by lia.
replace ((x + - (y mod 2 ^ 64)) mod 2 ^ 64) with ((x - y) mod 2 ^ 64).
- apply UbDec.lxs64. exact Hxy.
- rewrite <- Zminus_mod_idemp_r. f_equal.
Qed.

Local Ltac ga_gn := repeat first [ rewrite ga_lxs_sub by lia | rewrite ga_lxl64 by lia | rewrite UbDec.lxor_sign_nn by lia ].
Local Ltac ga_bsame := lazymatch goal with
| |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 (Z.b2z ?X)) (Z_to_bv 64 (Z.b2z ?Y))) then _ else _) _ _ _ _) =>
replace Y with X by (apply Bool.eq_iff_eq_true; rewrite !Z.ltb_lt; split; intros; lia);
rewrite UbDec.bv_eqb_same_k; cbn [negb]
end.

Lemma ga_zsl : forall x y, Z_to_bv 64 (x + - Z.land y 18446744073709551615) = Z_to_bv 64 (x - y).
Proof.
intros x y. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
apply UbDec.zbv_sub_modr_k.
Qed.
Lemma ga_zneg : forall y, Z_to_bv 64 (- Z.land y 18446744073709551615) = Z_to_bv 64 (- y).
Proof.
intros y. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
replace (- (y mod 2 ^ 64)) with (0 - y mod 2 ^ 64) by lia. rewrite UbDec.zbv_sub_modr_k. f_equal.
Qed.
Local Ltac ga_lt_t H := rewrite (proj2 (Z.ltb_lt _ _) H).
Local Ltac ga_lt_f H := rewrite (proj2 (Z.ltb_ge _ _) H).
Lemma ga_c7 : forall fs p, 0 < fs < 2^63 -> 0 <= p < 2^63 ->
(0 <? Z.lor (Z.lxor fs 18446744073709551615) (Z.lxor p 9223372036854775808)) = true.
Proof.
intros fs p Hf Hp. rewrite zb_lxor_ones by lia. rewrite UbDec.lxor_sign_nn by lia. apply Z.ltb_lt.
assert (N0 : 0 <= Z.lor (18446744073709551615 - fs) (p + 9223372036854775808)) by (apply Z.lor_nonneg; lia).
assert (N1 : Z.lor (18446744073709551615 - fs) (p + 9223372036854775808) <> 0) by (intros E; apply Z.lor_eq_0_iff in E; lia).
lia.
Qed.
Lemma ga_vdiv : forall x y, -2^63 <= x < 2^63 -> 0 < y < 2^63 ->
v_div (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.quot x y).
Proof.
intros x y Hx Hy. unfold v_div. rewrite unsigned_lit by lia.
replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). unfold zsig. rewrite !zb_signed_small by lia. reflexivity.
Qed.

Lemma granule_arith : forall (Q : machine_state -> Prop) (SP lg fs gfs nbp nf pg : Z)
(ra gp tp t0 t1 t2 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 w16 w24 w48 w76 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (j16 jsk lk : list byte),
0 <= SP -> SP + 80 < 2^63 ->
rw_cells rsegs m SP [CB 16 j16; C8 w16; C8 w24; CB 16 jsk; C8 w48; C8 (Z_to_bv 64 gfs); C8 (Z_to_bv 64 pg); CB 4 lk; C4 w76] ->
mem_inv rsegs m ->
0 <= nbp <= 255 -> 0 < fs <= 640 -> gfs = fs -> 1 <= nf <= 10 -> 0 < pg < 2^63 -> -2^63 <= lg < 2^63 ->
(0 < lg \/ pg < INT64_MAX + lg) ->
(granule_sel fs gfs nf lg pg nbp = None -> forall y8 y10 y11 y12 y13 y14 y15 : word,
evt rsegs Q (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 y8 s1 y10 y11 y12 y13 y14 y15 a6 a7 s2 (Z_to_bv 64 nbp) s4 s5 s6 s7 s8 (Z_to_bv 64 nf) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1c778) fc None m (seg_rom rsegs))) ->
(forall skip, granule_sel fs gfs nf lg pg nbp = Some skip -> forall y10 y11 y12 y13 y14 y15 : word,
evt rsegs Q (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 (fs * (nbp * gfs * nf - (pg - lg)) ÷ gfs)) s1 y10 y11 y12 y13 y14 y15 a6 a7 s2 (Z_to_bv 64 nbp) s4 s5 s6 s7 s8 (Z_to_bv 64 nf) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1c384) fc None m (seg_rom rsegs))) ->
evt rsegs Q (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 lg) s1 (Z_to_bv 64 fs) a1 a2 (Z_to_bv 64 nbp) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 nf) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1c2d0) fc None m (seg_rom rsegs)).
Proof.
intros until lk. intros SP0 SP1 LOW MI NBP FS GFS NF PG LG C KC KP. subst gfs.
pose proof (ro_cells_image rsegs m 0x10740 [Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 0]
MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as ROC.
pose proof (ro_cells_image rsegs m 0x10750 [Z_to_bv 8 52; Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 0]
MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as ROD.
cbn [length] in ROC, ROD.
assert (P1 : 0 <= nbp * fs <= 163200) by nia.
assert (P2 : 0 <= nbp * fs * nf <= 1632000) by nia.
assert (BR : -2^63 < pg - lg < 2^63) by (unfold INT64_MAX in C; lia).
zstep. zstep. zstep. zstep. rewrite (UbDec.swrap32_small_k (nbp * fs)) by lia. rewrite UbDec.bv_eqb_same_k. cbn [negb].
zstep. zstep. zstep. zstep. zstep. zstep. ga_gn. ga_bsame.
zstep. zstep. zstep. rewrite (UbDec.swrap32_small_k (nbp * fs + 0)) by lia. rewrite Z.add_0_r, ga_zsl.
rewrite UbDec.lts_lit_k by nia. replace (nf * (nbp * fs)) with (nbp * fs * nf) by ring.
destruct (Z.ltb_spec (nbp * fs * nf) (pg - lg)) as [AB|AB]; cbv iota.
{ apply KC. unfold granule_sel. cbv zeta. ga_lt_t AB. reflexivity. }
zstep. zstep. zstep. zstep. ga_gn. ga_bsame.
zstep. zstep. zstep. zstep. rewrite ?ga_zneg, ?ga_zsl.
lazymatch goal with |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
rewrite (UbDec.lts_lit_k x y) by lia; destruct (Z.ltb_spec x y) as [CB|CB]; cbn [negb] end.
{ apply KC. unfold granule_sel. cbv zeta. ga_lt_f AB. change (INT64_MAX ÷ 640) with 14411518807585587.
replace (14411518807585587 - nbp * fs * nf <? - (pg - lg)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }

zstep. zstep. zstep. zstep. ga_gn. ga_bsame.
zstep. zstep. zstep. rewrite ?ga_zneg, ?ga_zsl.
lazymatch goal with |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
rewrite (UbDec.lts_lit_k x y) by lia; destruct (Z.ltb_spec x y) as [DB|DB]; cbn [negb] end.
2:{ apply KC. unfold granule_sel. cbv zeta. ga_lt_f AB. change (INT64_MAX ÷ 640) with 14411518807585587.
replace (14411518807585587 - nbp * fs * nf <? - (pg - lg)) with false by (symmetry; apply Z.ltb_ge; lia).
replace (14411518807585587 <? nbp * fs * nf - (pg - lg)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }

zstep. zstep. zstep. zstep.
assert (ABR : 0 <= nbp * fs * nf - (pg - lg) < 14411518807585588) by lia.
assert (MR : 0 <= fs * (nbp * fs * nf - (pg - lg)) < 2^63).
{ split; [apply Z.mul_nonneg_nonneg; lia|].
apply Z.le_lt_trans with (640 * (nbp * fs * nf - (pg - lg))); [apply Z.mul_le_mono_nonneg_r; lia| lia]. }
rewrite !zb_signed_small by lia. rewrite !Z.shiftr_div_pow2 by lia. rewrite !Z.div_small by lia.
rewrite UbDec.bv_eqb_same_k. cbn [negb].
zstep. zstep. rewrite (UbDec.bv_eqb_lit_ne_k fs 0) by lia.
zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite ga_c7 by lia. cbn [Z.b2z]. rewrite (UbDec.bv_eqb_lit_ne_k 1 0) by lia.
zstep. zstep. zstep. zstep.
rewrite ga_vdiv by lia.
set (q := fs * (nbp * fs * nf - (pg - lg)) ÷ fs) in *.
assert (QE : q = nbp * fs * nf - (pg - lg)) by (unfold q; rewrite (Z.mul_comm fs (nbp * fs * nf - (pg - lg))); apply Z.quot_mul; lia).
rewrite (unsigned_lit q) by lia. rewrite Z.add_0_r.
replace (bv_swrap 32 q) with (s32 q) by (rewrite UbDec.swrap32_eq_k; unfold s32; reflexivity).
assert (SR : -2^31 <= s32 q < 2^31) by (unfold s32; pose proof (Z.mod_pos_bound (q + 2^31) (2^32) ltac:(lia)); lia).
assert (GS : granule_sel fs fs nf lg pg nbp = if s32 q =? INT_MIN then None else Some (s32 q)).
{ unfold granule_sel. cbv zeta. ga_lt_f AB. change (INT64_MAX ÷ 640) with 14411518807585587.
replace (14411518807585587 - nbp * fs * nf <? - (pg - lg)) with false by (symmetry; apply Z.ltb_ge; lia).
replace (14411518807585587 <? nbp * fs * nf - (pg - lg)) with false by (symmetry; apply Z.ltb_ge; lia).
reflexivity. }
destruct (Z.eq_dec (s32 q) (-2147483648)) as [SE|SN].
- rewrite SE, UbDec.bv_eqb_same_k. cbv iota. apply KC. rewrite GS, SE. reflexivity.
- rewrite (UbDec.bv_eqb_lit_ne_k (s32 q) (-2147483648)) by lia. cbv iota. apply (KP (s32 q)). rewrite GS.
replace (s32 q =? INT_MIN) with false by (symmetry; apply Z.eqb_neq; unfold INT_MIN; lia). reflexivity.
Qed.

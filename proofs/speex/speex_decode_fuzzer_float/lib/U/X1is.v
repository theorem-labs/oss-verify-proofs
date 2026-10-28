(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0om X0qn X0px X0qc X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1m6 X1ik X1ij X1im.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1qx X1r3 X1r4 X1qz X1r0.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section STI.
Context {RCEIL : RunCeiling}.
Hypothesis HM : rmalloc_stmt.
Hypothesis HF : rfree_stmt.

#[using="HM"] Lemma malloc_site1 : forall {R} (k : option bptr -> @X1qx.M PState R) (Q : R -> PState -> machine_state -> Prop)
(s : PState) (LB : list block) (n A lo B : Z) (errv : word) (cs : list cell)
(sp gp tp : word) (f0 f1 f2 f3 f4 f5 : word)
(x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
RHEAP s LB m -> 0 <= n < 2^32 ->
rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 408 <= B ->
stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - RMALLOC_STACK ->
rw_cells rsegs m 316332 [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
rw_cells rsegs m (bv_unsigned sp + -48) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 f5] ->
rw_cells rsegs m A cs -> cells_size cs = 408%nat ->
(forall (m' : mem) (s' : PState) (r : option bptr) (errv' : word) (y5 y6 y7 va0 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
rauxv_ok m' B -> stk rsegs m' lo (bv_unsigned sp + -48) ->
rw_cells rsegs m' 316332 [C4 errv'] -> mem_inv rsegs m' ->
rheap_pres LB (bv_unsigned sp + -48) m m' ->
ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rw_cells rsegs m' (bv_unsigned sp + -48) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 f5] ->
rw_cells rsegs m' A cs ->
match r with
| None => va0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
| Some p => exists Ab junk, va0 = Z_to_bv 64 Ab /\ rblock_range Ab n /\ RHEAP s' ((p, Ab, n) :: LB) m'
/\ rw_cells rsegs m' Ab [CB (Z.to_nat n) junk]
end ->
implM rsegs (k r) s' Q
(MS (mkR (Z_to_bv 64 196680) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp y5 y6 y7 x8 x9 va0 y11 y12 y13 y14 y15 y16 y17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
F (Z_to_bv 64 196680) fc None m' (seg_rom rsegs))) ->
implM rsegs (X1qx.mbind (raw_malloc n) k) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 196676) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros HP Hn AUX SPB SPA AB ST CEIL LO ERR MI TP FR OS SZ K.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold RMALLOC_STACK in LO.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
unfold implM. iprefix. zstep. apply evt_done. eapply implM_bind.
{ unfold rmalloc_stmt, rmalloc_stmt_at in HM.
eapply HM with (s := s) (LB := LB) (n := n) (lo := lo) (B := B) (errv := errv).
- exact HP.
- exact AUX.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST.
- exact CEIL.
- rewrite unsigned_lit by lia. unfold RMALLOC_STACK. lia.
- rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR.
- exact MI.
- exact TP.
- reflexivity.
- exact Hn. }
cbv beta. intros r ps ms PO.
first [ sf_destruct 26%nat PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' errv' -> MI' ST' ERR' AUX' HPR FA SO RES | sf_fb; destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FA & SO & RES) ].
rewrite unsigned_lit in ST', HPR by lia.
rewrite TP, unsigned_lit in ERR' by (unfold RATP; lia). unfold RATP in ERR'. replace (316496 + -164) with 316332 in ERR' by reflexivity.
replace (ret_pc (Z_to_bv 64 196680)) with (Z_to_bv 64 196680) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in FR; [| left; cbn; lia].
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in OS; [| left; cbn; lia].
eapply K; try eassumption.
destruct r as [p|].
- first [ sf_destruct 7%nat RES as Ab junk Ha0 BR HP' BLK _ | sf_fb; destruct RES as (Ab & junk & Ha0 & BR & HP' & BLK & _) ]. exists Ab, junk. auto.
- exact RES.
Qed.

#[using="HM"] Lemma malloc_site2 : forall {R} (k : option bptr -> @X1qx.M PState R) (Q : R -> PState -> machine_state -> Prop)
(s : PState) (LB : list block) (n A lo B : Z) (errv : word) (cs : list cell)
(sp gp tp : word) (f0 f1 f2 f3 f4 f5 : word)
(x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
RHEAP s LB m -> 0 <= n < 2^32 ->
rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 408 <= B ->
stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - RMALLOC_STACK ->
rw_cells rsegs m 316332 [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
rw_cells rsegs m (bv_unsigned sp + -48) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 f5] ->
rw_cells rsegs m A cs -> cells_size cs = 408%nat ->
(forall (m' : mem) (s' : PState) (r : option bptr) (errv' : word) (y5 y6 y7 va0 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
rauxv_ok m' B -> stk rsegs m' lo (bv_unsigned sp + -48) ->
rw_cells rsegs m' 316332 [C4 errv'] -> mem_inv rsegs m' ->
rheap_pres LB (bv_unsigned sp + -48) m m' ->
ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rw_cells rsegs m' (bv_unsigned sp + -48) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 f5] ->
rw_cells rsegs m' A cs ->
match r with
| None => va0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
| Some p => exists Ab junk, va0 = Z_to_bv 64 Ab /\ rblock_range Ab n /\ RHEAP s' ((p, Ab, n) :: LB) m'
/\ rw_cells rsegs m' Ab [CB (Z.to_nat n) junk]
end ->
implM rsegs (k r) s' Q
(MS (mkR (Z_to_bv 64 196696) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp y5 y6 y7 x8 x9 va0 y11 y12 y13 y14 y15 y16 y17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
F (Z_to_bv 64 196696) fc None m' (seg_rom rsegs))) ->
implM rsegs (X1qx.mbind (raw_malloc n) k) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 196692) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros HP Hn AUX SPB SPA AB ST CEIL LO ERR MI TP FR OS SZ K.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold RMALLOC_STACK in LO.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
unfold implM. iprefix. zstep. apply evt_done. eapply implM_bind.
{ unfold rmalloc_stmt, rmalloc_stmt_at in HM.
eapply HM with (s := s) (LB := LB) (n := n) (lo := lo) (B := B) (errv := errv).
- exact HP.
- exact AUX.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST.
- exact CEIL.
- rewrite unsigned_lit by lia. unfold RMALLOC_STACK. lia.
- rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR.
- exact MI.
- exact TP.
- reflexivity.
- exact Hn. }
cbv beta. intros r ps ms PO.
first [ sf_destruct 26%nat PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' errv' -> MI' ST' ERR' AUX' HPR FA SO RES | sf_fb; destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FA & SO & RES) ].
rewrite unsigned_lit in ST', HPR by lia.
rewrite TP, unsigned_lit in ERR' by (unfold RATP; lia). unfold RATP in ERR'. replace (316496 + -164) with 316332 in ERR' by reflexivity.
replace (ret_pc (Z_to_bv 64 196696)) with (Z_to_bv 64 196696) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in FR; [| left; cbn; lia].
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in OS; [| left; cbn; lia].
eapply K; try eassumption.
destruct r as [p|].
- first [ sf_destruct 7%nat RES as Ab junk Ha0 BR HP' BLK _ | sf_fb; destruct RES as (Ab & junk & Ha0 & BR & HP' & BLK & _) ]. exists Ab, junk. auto.
- exact RES.
Qed.

#[using="HM"] Lemma malloc_site3 : forall {R} (k : option bptr -> @X1qx.M PState R) (Q : R -> PState -> machine_state -> Prop)
(s : PState) (LB : list block) (n A lo B : Z) (errv : word) (cs : list cell)
(sp gp tp : word) (f0 f1 f2 f3 f4 f5 : word)
(x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
RHEAP s LB m -> 0 <= n < 2^32 ->
rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 408 <= B ->
stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - RMALLOC_STACK ->
rw_cells rsegs m 316332 [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
rw_cells rsegs m (bv_unsigned sp + -48) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 f5] ->
rw_cells rsegs m A cs -> cells_size cs = 408%nat ->
(forall (m' : mem) (s' : PState) (r : option bptr) (errv' : word) (y5 y6 y7 va0 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
rauxv_ok m' B -> stk rsegs m' lo (bv_unsigned sp + -48) ->
rw_cells rsegs m' 316332 [C4 errv'] -> mem_inv rsegs m' ->
rheap_pres LB (bv_unsigned sp + -48) m m' ->
ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rw_cells rsegs m' (bv_unsigned sp + -48) [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 f5] ->
rw_cells rsegs m' A cs ->
match r with
| None => va0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
| Some p => exists Ab junk, va0 = Z_to_bv 64 Ab /\ rblock_range Ab n /\ RHEAP s' ((p, Ab, n) :: LB) m'
/\ rw_cells rsegs m' Ab [CB (Z.to_nat n) junk]
end ->
implM rsegs (k r) s' Q
(MS (mkR (Z_to_bv 64 196712) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp y5 y6 y7 x8 x9 va0 y11 y12 y13 y14 y15 y16 y17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
F (Z_to_bv 64 196712) fc None m' (seg_rom rsegs))) ->
implM rsegs (X1qx.mbind (raw_malloc n) k) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 196708) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros HP Hn AUX SPB SPA AB ST CEIL LO ERR MI TP FR OS SZ K.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold RMALLOC_STACK in LO.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
unfold implM. iprefix. zstep. apply evt_done. eapply implM_bind.
{ unfold rmalloc_stmt, rmalloc_stmt_at in HM.
eapply HM with (s := s) (LB := LB) (n := n) (lo := lo) (B := B) (errv := errv).
- exact HP.
- exact AUX.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST.
- exact CEIL.
- rewrite unsigned_lit by lia. unfold RMALLOC_STACK. lia.
- rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR.
- exact MI.
- exact TP.
- reflexivity.
- exact Hn. }
cbv beta. intros r ps ms PO.
first [ sf_destruct 26%nat PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' errv' -> MI' ST' ERR' AUX' HPR FA SO RES | sf_fb; destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FA & SO & RES) ].
rewrite unsigned_lit in ST', HPR by lia.
rewrite TP, unsigned_lit in ERR' by (unfold RATP; lia). unfold RATP in ERR'. replace (316496 + -164) with 316332 in ERR' by reflexivity.
replace (ret_pc (Z_to_bv 64 196712)) with (Z_to_bv 64 196712) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in FR; [| left; cbn; lia].
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in OS; [| left; cbn; lia].
eapply K; try eassumption.
destruct r as [p|].
- first [ sf_destruct 7%nat RES as Ab junk Ha0 BR HP' BLK _ | sf_fb; destruct RES as (Ab & junk & Ha0 & BR & HP' & BLK & _) ]. exists Ab, junk. auto.
- exact RES.
Qed.

#[using="Type"] Lemma stream_cells_init : forall m A Bd L Gv ser (z16 z320 z24 : list byte),
z16 = repeat (Z_to_bv 8 0) 16 -> z320 = repeat (Z_to_bv 8 0) 320 -> z24 = repeat (Z_to_bv 8 0) 24 ->
rw_cells rsegs m A [C8 (Z_to_bv 64 Bd); C8 (Z_to_bv 64 16384); CB 16 z16; C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 Gv); C8 (Z_to_bv 64 1024);
CB 320 z320; C8 (Z_to_bv 64 ser); CB 24 z24] ->
forall b l g, rw_cells rsegs m A (stream_cells Bd L Gv zero_hdr (mkStream b [] 16384 0 0 l [] g [] 1024 0 0 0 0 0 0 ser 0 0 0)).
Proof.
intros m A Bd L Gv ser z16 z320 z24 -> -> -> H b l g.
eapply rw_cells_recell; [exact H| vm_compute; repeat split; reflexivity| | reflexivity].
unfold stream_cells, wz, zero_hdr. cbn [os_body_storage os_body_fill os_body_returned os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned
os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos].
cbn [cells_bytes cbytes].
generalize (le8 (Z_to_bv 64 Bd)) (le8 (Z_to_bv 64 L)) (le8 (Z_to_bv 64 Gv)) (le8 (Z_to_bv 64 ser)). intros lb ll lg ls.
vm_compute. reflexivity.
Qed.
#[using="Type"] Lemma stream_cells_init0 : forall m A Bd L Gv (z16 z352 : list byte),
z16 = repeat (Z_to_bv 8 0) 16 -> z352 = repeat (Z_to_bv 8 0) 352 ->
rw_cells rsegs m A [C8 (Z_to_bv 64 Bd); C8 (Z_to_bv 64 16384); CB 16 z16; C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 Gv); C8 (Z_to_bv 64 1024); CB 352 z352] ->
forall b l g, rw_cells rsegs m A (stream_cells Bd L Gv zero_hdr (mkStream b [] 16384 0 0 l [] g [] 1024 0 0 0 0 0 0 0 0 0 0)).
Proof.
intros m A Bd L Gv z16 z352 -> -> H b l g.
eapply rw_cells_recell; [exact H| vm_compute; repeat split; reflexivity| | reflexivity].
unfold stream_cells, wz, zero_hdr. cbn [os_body_storage os_body_fill os_body_returned os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned
os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos].
cbn [cells_bytes cbytes].
generalize (le8 (Z_to_bv 64 Bd)) (le8 (Z_to_bv 64 L)) (le8 (Z_to_bv 64 Gv)). intros lb ll lg.
vm_compute. reflexivity.
Qed.

Definition init_os (b l g : option bptr) (ser : Z) : stream_st bptr :=
mkStream b [] 16384 0 0 l [] g [] 1024 0 0 0 0 0 0 ser 0 0 0.

Definition stream_init_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
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

#[using="HM HF"] Lemma ogg_stream_init_spec :
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
(stream_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB A lo B serialno m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_init) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros HP AUX SPB SPA AB ST CEIL LO ERR MI TP Hser -> -> OS.
unfold A_ogg_stream_init. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold RMALLOC_STACK in LO.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
rewrite TP, unsigned_lit in ERR by (unfold RATP; lia). unfold RATP in ERR. replace (316496 + -164) with 316332 in ERR by reflexivity.
pose proof AUX as AUX0. first [ sf_destruct 16%nat AUX0 as av x3_ x4_ x5_ x16_ x6_ x11_ x12_ x23_ rnd _ _ _ AC1 AC2 _ | sf_fb; destruct AUX0 as (av & x3_ & x4_ & x5_ & x16_ & x6_ & x11_ & x12_ & x23_ & rnd & _ & _ & _ & AC1 & AC2 & _) ].
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 408)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold ogg_stream_init.
unfold implM. iprefix.
carve_frame 48%nat ST.

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
zstep. if_cases CN0; zify_cond CN0; rewrite ?unsigned_lit in CN0 by lia; [exfalso; lia|].

apply (rw_cells_split_CB _ _ _ [] _ _ [] [16; 392]%nat) in OS; [|reflexivity]. cbn [mk_CB_cells app] in OS.
apply (proj1 (rw_cells_app _ _ _ [CB 16 (take 16 junk)] [CB 392 (take 392 (drop 16 junk))])) in OS. destruct OS as [OS0 OS1]. cbn [cells_size csize Nat.add] in OS1.
replace (A + Z.of_nat 16) with (A + 16) in OS1 by lia.
zstep. zstep. zstep. zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
call (memset_callZ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx (bv_unsigned sp + -48) (A + 16) 0 392) end.
all: try (change (Z.to_nat 392) with 392%nat; exact OS1). all: try exact MI. all: try lia.
rename POST into OS1. change (Z.to_nat 392) with 392%nat in OS1. change (0 mod 256) with 0 in OS1.

zstep. zstep. lstep. lstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with OSa : rw_cells rsegs mx A ?ca, OSb : rw_cells rsegs mx (A + 16) ?cb |- _ =>
pose proof (rw_cells_join _ _ _ _ _ OSa ltac:(cbn [cells_size csize Nat.add]; replace (A + Z.of_nat 16) with (A + 16) by lia; exact OSb)) as OS;
clear OSa OSb; cbn [app] in OS end end.
apply evt_done.
eapply (malloc_site1 _ _ s LB 16384 A lo B errv _ sp gp tp).
all: lazymatch goal with
| |- rw_cells _ _ _ _ => first [exact OS | exact FR | exact ERR]
| |- RHEAP _ _ _ => eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|];
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil
| |- rauxv_ok _ _ => eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil
| |- stk _ _ _ _ => exact ST
| |- mem_inv _ _ => eassumption
| |- _ = Z_to_bv 64 RATP => exact TP
| |- cells_size _ = _ => reflexivity
| |- forall m', _ => idtac
| |- word => exact (Z_to_bv 64 0)
| |- _ => try (unfold RMALLOC_STACK; lia)
end.
clear AUX ST ERR FR OS HP. rename MU into MU0. rename WM into WM0.
intros m1' s1' r1 errv1 y5 y6 y7 va1 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 AUX ST ERR MI1 HPR1 FA1 SO1 FR OS RES1.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 408)] m1') as MU. pose proof (wmono_refl rsegs m1') as WM.
destruct r1 as [pb|]; [first [ sf_destruct 6%nat RES1 as Bd jb -> BRb HP BLKb | sf_fb; destruct RES1 as (Bd & jb & -> & BRb & HP & BLKb) ]; pose proof BRb as sfP_; first [ sf_destruct 5%nat sfP_ as Bb1 Bb2 Bb3 Bb4 Bb5 | sf_fb; destruct sfP_ as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5) ]; unfold alloc_ceiling in Bb4
| destruct RES1 as [-> HP]].

all: unfold implM; iprefix; zstep; lstep; zstep; apply evt_done.
all: [> eapply (malloc_site2 _ _ s1' _ 4096 A lo B errv1 _ sp gp tp) | eapply (malloc_site2 _ _ s1' _ 4096 A lo B errv1 _ sp gp tp) ].
all: lazymatch goal with
| |- rw_cells _ _ _ _ => first [exact OS | exact FR | exact ERR]
| |- RHEAP _ _ _ => eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|];
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil
| |- rauxv_ok _ _ => eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil
| |- stk _ _ _ _ => exact ST
| |- mem_inv _ _ => eassumption
| |- _ = Z_to_bv 64 RATP => exact TP
| |- cells_size _ = _ => reflexivity
| |- forall m', _ => idtac
| |- word => exact (Z_to_bv 64 0)
| |- _ => try (unfold RMALLOC_STACK; lia)
end.
all: clear AUX ST ERR FR OS HP MI1; rename MU into MU1; rename WM into WM1.
all: intros m2' s2' r2 errv2 z5 z6 z7 va2 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 AUX ST ERR MI2 HPR2 FA2 SO2 FR OS RES2.
all: pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 408)] m2') as MU; pose proof (wmono_refl rsegs m2') as WM.
all: try (apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR2) in BLKb; [| eapply (rclient_range_block _ _ pb Bd 16384); [left; reflexivity| lia| cbn; lia]]).
all: destruct r2 as [pl|]; [first [ sf_destruct 6%nat RES2 as L jl -> BRl HP BLKl | sf_fb; destruct RES2 as (L & jl & -> & BRl & HP & BLKl) ]; pose proof BRl as sfP_; first [ sf_destruct 5%nat sfP_ as Bl1 Bl2 Bl3 Bl4 Bl5 | sf_fb; destruct sfP_ as (Bl1 & Bl2 & Bl3 & Bl4 & Bl5) ]; unfold alloc_ceiling in Bl4
| destruct RES2 as [-> HP]].

all: unfold implM; iprefix; zstep; lstep; zstep; apply evt_done.
all: eapply (malloc_site3 _ _ s2' _ 8192 A lo B errv2 _ sp gp tp).
all: lazymatch goal with
| |- rw_cells _ _ _ _ => first [exact OS | exact FR | exact ERR]
| |- RHEAP _ _ _ => eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|];
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil
| |- rauxv_ok _ _ => eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil
| |- stk _ _ _ _ => exact ST
| |- mem_inv _ _ => eassumption
| |- _ = Z_to_bv 64 RATP => exact TP
| |- cells_size _ = _ => reflexivity
| |- forall m', _ => idtac
| |- word => exact (Z_to_bv 64 0)
| |- _ => try (unfold RMALLOC_STACK; lia)
end.
all: clear AUX ST ERR FR OS HP MI2; rename MU into MU2; rename WM into WM2.
all: intros m3' s3' r3 errv3 u5 u6 u7 va3 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 AUX ST ERR MI3 HPR3 FA3 SO3 FR OS RES3.
all: pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 408)] m3') as MU; pose proof (wmono_refl rsegs m3') as WM.
all: try (apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR3) in BLKb; [| eapply (rclient_range_block _ _ pb Bd 16384); [first [left; reflexivity | right; left; reflexivity]| lia| cbn; lia]]).
all: try (apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR3) in BLKl; [| eapply (rclient_range_block _ _ pl L 4096); [left; reflexivity| lia| cbn; lia]]).
all: destruct r3 as [pg|]; [first [ sf_destruct 6%nat RES3 as Gv jg -> BRg HP BLKg | sf_fb; destruct RES3 as (Gv & jg & -> & BRg & HP & BLKg) ]; pose proof BRg as sfP_; first [ sf_destruct 5%nat sfP_ as Bg1 Bg2 Bg3 Bg4 Bg5 | sf_fb; destruct sfP_ as (Bg1 & Bg2 & Bg3 & Bg4 & Bg5) ]; unfold alloc_ceiling in Bg4
| destruct RES3 as [-> HP]].

all: unfold implM; iprefix; lstep.
all: zstep; if_cases CK1; zify_cond CK1; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CK1 by lia; try (exfalso; lia).
all: repeat (lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 0x30070) _ _ _ _) =>
zstep; if_cases CK2; zify_cond CK2; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CK2 by lia; try (exfalso; lia)
| |- evt _ _ (MS _ _ (Z_to_bv 64 0x30074) _ _ _ _) =>
zstep; if_cases CK3; zify_cond CK3; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CK3 by lia; try (exfalso; lia)
end).

1: {
zstep. zstep. zstep.

zstep. zstep. zstep. zstep. zstep. zstep. zstep.
lazymatch goal with FRx : rw_cells rsegs _ (bv_unsigned sp + -48) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
zstep. zstep.
apply evt_done. cbv beta iota. apply impl_ret_ok. apply evt_done. cbn [fst snd].
lazymatch goal with OSx : rw_cells rsegs ?mx A _ |- _ =>
pose proof (stream_cells_init mx A Bd L Gv serialno _ _ _ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) OSx
(Some pb) (Some pl) (Some pg)) as OSF; clear OSx end.
unfold stream_init_post. sf_eexists 14%nat.
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end. eexists. exists ((pg, Gv, 8192) :: (pl, L, 4096) :: (pb, Bd, 16384) :: LB).
split; [reflexivity|]. split; [assumption|]. split; [assumption|].
split. { rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_nil. }
split. { eapply cmod_trans; [eapply cmod_of_munch; [exact MU0| exact WM0]|].
eapply cmod_trans; [eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -48) (bv_unsigned sp));
[eapply cmod_of_rheap_pres; exact HPR1| lia| intros bq Hbq; exact Hbq| intros xq Hxq; exact Hxq]|].
eapply cmod_trans; [eapply cmod_of_munch; [exact MU1| exact WM1]|].
eapply cmod_trans; [eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -48) (bv_unsigned sp));
[eapply cmod_of_rheap_pres; exact HPR2| lia| intros bq Hbq; cbn; auto| intros xq Hxq; exact Hxq]|].
eapply cmod_trans; [eapply cmod_of_munch; [exact MU2| exact WM2]|].
eapply cmod_trans; [eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -48) (bv_unsigned sp));
[eapply cmod_of_rheap_pres; exact HPR3| lia| intros bq Hbq; cbn; auto| intros xq Hxq; exact Hxq]|].
apply cmod_of_munch; [exact MU| exact WM]. }
split; [congruence|]. split; [congruence|].
split. { eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil. }
split. { intros bq Hbq. cbn. auto. }
left. split; [reflexivity|]. first [ unshelve sf_eexists 9%nat; [ exact (pb) | exact (pl) | exact (pg) | exact (Bd) | exact (L) | exact (Gv) | exact (jb) | exact (jl) | exact (jg) | ] | sf_fb; exists pb, pl, pg, Bd, L, Gv, jb, jl, jg ].
split; [reflexivity|]. split; [reflexivity|]. split; [exact BRb|]. split; [exact BRl|]. split; [exact BRg|].
split; [exact OSF|]. split; [exact BLKb|]. split; [exact BLKl| exact BLKg]. }

all: zstep; zstep; apply evt_done; cbv beta iota; eapply implM_bind.
all: try (lazymatch goal with
| HPx : RHEAP ?sc ?LBc _, OSx : rw_cells rsegs ?mx ?Av [C8 (Z_to_bv 64 ?XB); _; _; C8 (Z_to_bv 64 ?XL); C8 (Z_to_bv 64 ?XG); _; _] |- implM _ (ogg_stream_clear _ ?osv) _ _ _ =>
pose proof (RHEAP_blocks_nodup_proof _ _ _ HPx) as ND; cbn [map blk_id fst] in ND;
eapply (ogg_stream_clear_spec HF) with (s := sc) (LB := LBc) (os := osv) (A := Av) (Bd := XB) (L := XL) (Gv := XG) (hdr := zero_hdr);
[ eapply RHEAP_frame_proof; [exact HPx| exact MU| exact WM|];
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil
| idtac
| reflexivity
| eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| lia
| rewrite unsigned_lit by lia; exact ST
| exact CEIL
| rewrite unsigned_lit by lia; unfold RFREE_STACK; lia
| rewrite TP, unsigned_lit by (unfold RATP; lia); unfold RATP; exact ERR
| eassumption
| exact TP
| reflexivity
| eapply (stream_cells_init0 mx Av XB XL XG); [vm_compute; reflexivity| vm_compute; reflexivity| exact OSx] ]
end).
all: try (lazymatch goal with |- stream_blocks _ _ _ _ _ =>
unfold stream_blocks; cbn [os_body_data os_lacing_vals os_granule_vals]; repeat split;
try (eexists; cbn; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity]);
try (intros p q Hp Hq; first [discriminate Hp | discriminate Hq | injection Hp as <-; injection Hq as <-; intros E; clear -ND E; subst;
repeat (apply List.NoDup_cons_iff in ND; destruct ND as [?NI ND]); cbn in *; tauto]) end).
all: clear AUX ST ERR; rename MU into MU3; rename WM into WM3.
all: intros osr ps4 ms4 PO;
first [ sf_destruct 26%nat PO as q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 m5 -> MI5 ST ERR AUX CMc FA4 SO4 HP5 -> OSZ | sf_fb; destruct PO as (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & m5 & -> & MI5 & ST & ERR & AUX & CMc & FA4 & SO4 & HP5 & -> & OSZ) ].
all: rewrite unsigned_lit in ST, CMc by lia.
all: pose proof (RHEAP_blocks_nodup_proof _ _ _ HP) as ND; cbn [map blk_id fst] in ND.
all: rewrite TP, unsigned_lit in ERR by (unfold RATP; lia); unfold RATP in ERR; replace (316496 + -164) with 316332 in ERR by reflexivity.
all: repeat match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

all: lazymatch goal with FRx : rw_cells rsegs _ (bv_unsigned ?spv + -48) _ |- _ =>
apply (cmod_rw_cells _ _ _ _ _ _ _ CMc) in FRx; [| left; cbn; lia| cbn; lia] end.
all: apply implM_ret.

all: zstep; zstep; zstep; zstep; zstep; zstep; zstep.
all: lazymatch goal with FRx : rw_cells rsegs _ (bv_unsigned ?spv + -48) _ |- _ => release_frame FRx ST (bv_unsigned spv) end.
all: zstep; zstep.
all: lazymatch type of HP5 with RHEAP _ ?LBf _ =>
assert (INCL : forall b, In b LB -> In b LBf) by
(intros bq Hbq; pose proof (in_map_blk_id _ _ Hbq) as HIDb; unfold stream_clear_LB;
cbn [os_body_data os_lacing_vals os_granule_vals lb_remove_opt];
repeat (apply lb_remove_keep);
first [ intros E; exfalso; rewrite <- E in ND;
first [ solve [apply (nodup_in_tail _ [] _ ND); cbn; tauto]
| solve [apply (nodup_in_tail _ [_] _ ND); cbn; tauto]
| solve [apply (nodup_in_tail _ [_; _] _ ND); cbn; tauto] ]
| cbn; repeat (first [exact Hbq | right]) ]) end.
all: lazymatch type of HP5 with RHEAP _ ?LBf _ => lazymatch type of HP with RHEAP _ ?LB3 _ =>
assert (SUB3 : forall b, In b LBf -> In b LB3) by (intros bq Hbq; unfold stream_clear_LB in Hbq; do 3 apply lb_remove_opt_sub in Hbq; exact Hbq) end end.
all: apply evt_done; unfold stream_init_post; sf_eexists 14%nat.
all: lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end; eexists.
all: lazymatch type of HP5 with RHEAP _ ?LBf _ => exists LBf end.
all: split; [reflexivity|]; split; [assumption|]; split; [assumption|].
all: split; [rewrite TP, unsigned_lit by (unfold RATP; lia); unfold RATP; exact ERR|].
all: split; [exact AUX|].
all: split; [ eapply cmod_trans; [eapply cmod_of_munch; [exact MU0| exact WM0]|];
eapply cmod_trans; [eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -48) (bv_unsigned sp));
[eapply cmod_of_rheap_pres; exact HPR1| lia| intros bq Hbq; exact Hbq| intros xq Hxq; exact Hxq]|];
eapply cmod_trans; [eapply cmod_of_munch; [exact MU1| exact WM1]|];
eapply cmod_trans; [eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -48) (bv_unsigned sp));
[eapply cmod_of_rheap_pres; exact HPR2| lia| intros bq Hbq; cbn; auto| intros xq Hxq; exact Hxq]|];
eapply cmod_trans; [eapply cmod_of_munch; [exact MU2| exact WM2]|];
eapply cmod_trans; [eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -48) (bv_unsigned sp));
[eapply cmod_of_rheap_pres; exact HPR3| lia| intros bq Hbq; cbn; auto| intros xq Hxq; exact Hxq]|];
eapply cmod_trans; [eapply cmod_of_munch; [exact MU3| exact WM3]|];
eapply (cmod_weaken [(A, A + 408)] _ _ _ (bv_unsigned sp + -48) (bv_unsigned sp));
[ eapply (cmod_drop_low (bv_unsigned sp + -48 - 16) (bv_unsigned sp + -48)); [exact CMc| lia| lia|];
intros bq Hbq; left;
pose proof (RHEAP_block_range_proof _ _ _ _ HP (SUB3 bq Hbq)) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ X4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & X4 & _) ]; unfold alloc_ceiling in X4; lia
| lia | exact INCL | intros xq Hxq; cbn in Hxq |- *; tauto ] |].
all: split; [congruence|]; split; [congruence|].
all: split; [exact HP5|].
all: split; [exact INCL| right; split; [reflexivity|]; split; [reflexivity|]; split; [| exact OSZ]].

all: unfold stream_clear_LB; cbn [os_body_data os_lacing_vals os_granule_vals lb_remove_opt init_os].
all: repeat (rewrite lbr_cons; cbn [blk_id fst];
first [ rewrite bp_eqb_refl
| rewrite bp_eqb_neq by (intros E; clear -ND E; subst;
repeat (apply List.NoDup_cons_iff in ND; destruct ND as [?NI ND]); cbn in *; tauto) ]).
all: repeat (rewrite (lbr_notin _ LB) by (clear -ND; repeat (apply List.NoDup_cons_iff in ND; destruct ND as [?NI ND]); cbn in *; tauto)).
all: apply Permutation_refl.
Qed.
End STI.

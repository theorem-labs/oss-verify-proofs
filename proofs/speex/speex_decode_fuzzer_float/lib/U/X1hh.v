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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h9 X1gy X1hg X1hf.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Definition pkt_bodyP (fuel' : nat) (h : hstate bptr) (op : packet) (pdata : list Z) (packet_no : Z) : M PState (outcome bptr) :=
X1qx.mbind
(if h_packet_count h =? 0 then
X1qx.mbind (process_header raw_calloc raw_free io_notify h pdata (pk_bytes op))
(fun ph => match ph with
| None => X1qx.mbind (cleanupP h) (fun _ => X1qx.mret None)
| Some h => X1qx.mret (Some (h, packet_no))
end)
else if h_packet_count h <=? 1 + h_extra_headers h then X1qx.mret (Some (h, packet_no))
else
let packet_no := packet_no + 1 in
let eos := if negb (pk_e_o_s op =? 0) && (os_serialno (h_os h) =? h_speex_serialno h) then 1 else h_eos h in
X1qx.mbind (speex_bits_read_from raw_realloc io_notify io_warning (h_bits h) pdata (pk_bytes op))
(fun b => match h_st h with
| None => X1qx.munr
| Some st => X1qx.mbind (decode_loop io_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M (Z.to_nat (h_nframes h)) st b)
(fun x => let '(st, b) := x in X1qx.mret (Some (set_bits_st h b (Some st) eos, packet_no)))
end))
(fun ro => match ro with
| None => X1qx.mret Returned
| Some (h, packet_no) => packet_loopP fuel' (incr_packet_count h) packet_no
end).

Lemma packet_loop_S : forall fuel' (h : hstate bptr) pn,
packet_loopP (S fuel') h pn =
if negb (h_eos h =? 0) then X1qx.mret (Cont h) else
match ogg_stream_packetout (h_os h) with
| None => X1qx.munr
| Some ((r, oop), os) =>
let h := set_ogg h (h_oy h) os in
if negb (r =? 1) then X1qx.mret (Cont h) else
match oop with
| None => X1qx.munr
| Some op =>
let pdata := packet_data os op in
let sser := if (5 <=? pk_bytes op) && list_eqb (ztake 5 pdata) SPEEX_STR then os_serialno os else h_speex_serialno h in
let h := set_serialno h sser in
if (sser =? -1) || negb (os_serialno os =? sser) then X1qx.mret (Cont h)
else pkt_bodyP fuel' h op pdata pn
end
end.
Proof. intros. reflexivity. Qed.

Lemma pko_facts : forall (os os' : stream_st bptr) r opo,
stream_inv os -> body_inv os -> ogg_stream_packetout os = Some ((r, opo), os') ->
stream_inv os' /\ body_inv os' /\ os_lacing os' = os_lacing os /\ os_granules os' = os_granules os /\ os_body os' = os_body os
/\ os_body_data os' = os_body_data os /\ os_lacing_vals os' = os_lacing_vals os /\ os_granule_vals os' = os_granule_vals os
/\ os_body_storage os' = os_body_storage os /\ os_lacing_storage os' = os_lacing_storage os
/\ os_lacing_fill os' = os_lacing_fill os /\ os_body_fill os' = os_body_fill os /\ os_serialno os' = os_serialno os
/\ os_lacing_returned os <= os_lacing_returned os' <= os_lacing_fill os
/\ (r = 1 -> opo <> None /\ os_lacing_returned os < os_lacing_returned os')
/\ match opo with
| Some p => 0 <= pk_off p /\ 0 <= pk_bytes p /\ pk_off p + pk_bytes p <= os_body_fill os /\ zlength (packet_data os' p) = pk_bytes p
| None => True end.
Proof.
intros os os' r opo SINV BINV E.
pose proof (ogg_stream_packetout_frame os r opo os' SINV E) as sfP_; first [ sf_destruct 12%nat sfP_ as S1 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 | sf_fb; destruct sfP_ as (S1 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11) ].
pose proof (ogg_stream_packetout_body_inv os r opo os' SINV BINV E) as sfP_; first [ sf_destruct 4%nat sfP_ as B1 B2 B3 B4 | sf_fb; destruct sfP_ as (B1 & B2 & B3 & B4) ].
assert (LG : os_lacing os' = os_lacing os /\ os_granules os' = os_granules os).
{ unfold ogg_stream_packetout in E. destruct (ogg_stream_check os). { inversion E; subst. auto. }
unfold packetout in E.
destruct (os_lacing_packet os <=? os_lacing_returned os); [inversion E; subst; auto|].
destruct (negb (Z.land (znth (os_lacing os) (os_lacing_returned os)) 1024 =? 0)); [inversion E; subst; auto|].
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|]; [| discriminate]. inversion E; subst. auto. }
destruct LG as [LG1 LG2].
repeat (split; [assumption|]). exact B4.
Qed.

Lemma pko_ret : forall (os os' : stream_st bptr) r opo,
ogg_stream_packetout os = Some ((r, opo), os') -> r = 1 \/ r = 0 \/ r = -1.
Proof.
intros os os' r opo E. unfold ogg_stream_packetout in E. destruct (ogg_stream_check os). { inversion E; lia. }
unfold packetout in E.
destruct (os_lacing_packet os <=? os_lacing_returned os); [inversion E; lia|].
destruct (negb (Z.land (znth (os_lacing os) (os_lacing_returned os)) 1024 =? 0)); [inversion E; lia|].
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|]; [| discriminate]. inversion E; lia.
Qed.

Lemma pko_off : forall (os os' : stream_st bptr) r p,
ogg_stream_packetout os = Some ((r, Some p), os') -> pk_off p = os_body_returned os.
Proof.
intros os os' r p E. unfold ogg_stream_packetout in E. destruct (ogg_stream_check os); [discriminate|].
unfold packetout in E.
destruct (os_lacing_packet os <=? os_lacing_returned os); [discriminate|].
destruct (negb (Z.land (znth (os_lacing os) (os_lacing_returned os)) 1024 =? 0)); [discriminate|].
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|]; [| discriminate]. inversion E; subst. reflexivity.
Qed.

Lemma ubytes_inj : forall (l1 l2 : list byte), ubytes l1 = ubytes l2 -> l1 = l2.
Proof.
induction l1 as [|b l1 IH]; intros [|b' l2] E; cbn in E; try discriminate; [reflexivity|].
inversion E. f_equal; [apply bv_eq; assumption| apply IH; assumption].
Qed.

Lemma stream_rep_pko {RCEIL : RunCeiling} : forall m m' c x h (oy : sync_st bptr) r opo os',
stream_rep m c x h -> ogg_stream_packetout (h_os h) = Some ((r, opo), os') ->
rw_cells rsegs m' (aOS c) (stream_cells (a_Bd x) (a_L x) (a_Gv x) (a_hdr x) os') -> stream_fields_ok os' ->
u32arr rsegs m' (a_L x) (a_lws x) -> u64arr rsegs m' (a_Gv x) (a_gws x) -> u8arr rsegs m' (a_Bd x) (a_body x) ->
stream_rep m' c x (set_ogg h oy os').
Proof.
intros m m' c x h oy r opo os' SR E OS' FOK' AL AG AB.
first [ sf_destruct 34%nat SR as OS LH F1 SINV BINV LOK GOK UL UG UB W1 L1 L2 L3 PB1 PB2 N1 N2 N3 Z1 Z2 Z3 R1 R2 R3 C1 C2 C3 E1 E2 E3 G1 G2 G3 | sf_fb; destruct SR as (OS & LH & F1 & SINV & BINV & LOK & GOK & UL & UG & UB & W1 & L1 & L2 & L3 & PB1 & PB2 & N1 & N2 & N3 & Z1 & Z2 & Z3 & R1 & R2 & R3 & C1 & C2 & C3 & E1 & E2 & E3 & G1 & G2 & G3) ].
pose proof (pko_facts _ _ _ _ SINV BINV E) as sfP_; first [ sf_destruct 16%nat sfP_ as SINV' BINV' ELAC EGRA EBODY EBD ELV EGV EBS ELS ELF EBF ESN RETB R1F OPF | sf_fb; destruct sfP_ as (SINV' & BINV' & ELAC & EGRA & EBODY & EBD & ELV & EGV & EBS & ELS & ELF & EBF & ESN & RETB & R1F & OPF) ].
unfold stream_rep. cbn [h_os set_ogg]. rewrite ELAC, EGRA, EBODY, EBD, ELV, EGV, EBS, ELS.
repeat (split; [assumption|]).
destruct G3 as [G|G]; [left; exact G| right].
unfold ogg_stream_packetout, ogg_stream_check in E. rewrite G in E. cbn in E. inversion E. reflexivity.
Qed.

Lemma land_512 : forall v, Z.land v 512 = 0 \/ Z.land v 512 = 512.
Proof.
intros v. change 512 with (2^9).
destruct (Z.testbit v 9) eqn:T; [right|left]; apply Z.bits_inj'; intros i Hi;
rewrite Z.land_spec, Z.pow2_bits_eqb by lia; [|rewrite Z.bits_0];
(destruct (Z.eqb_spec 9 i) as [<-|NE]; [rewrite T; reflexivity| cbn; rewrite ?Bool.andb_false_r; reflexivity]).
Qed.
Lemma pko_eos_range : forall (os os' : stream_st bptr) r op,
ogg_stream_packetout os = Some ((r, Some op), os') -> 0 <= pk_e_o_s op <= 512.
Proof.
intros os os' r op E. unfold ogg_stream_packetout in E. destruct (ogg_stream_check os); [inversion E|].
unfold packetout in E.
destruct (os_lacing_packet os <=? os_lacing_returned os); [inversion E|].
destruct (negb (Z.land (znth (os_lacing os) (os_lacing_returned os)) 1024 =? 0)); [inversion E|].
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|] eqn:G; [| discriminate]. inversion E; subst. cbn [pk_e_o_s].
apply gather255_facts in G; [| apply Z.land_nonneg; right; lia].
destruct G as [_ [-> | ->]]; [| lia]. destruct (land_512 (znth (os_lacing os) (os_lacing_returned os))) as [-> | ->]; lia.
Qed.

Lemma pko_stream_zero : forall r opo os',
ogg_stream_packetout (stream_zero : stream_st bptr) = Some ((r, opo), os') -> r = 0.
Proof. intros r opo os' E. vm_compute in E. congruence. Qed.

Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. unfold le4. rewrite <- store_bytes_8'. reflexivity. Qed.

Definition stream_cells_lw (Bd L G : Z) (hdr : list byte) (os : stream_st bptr) : list cell :=
[C8 (wz Bd); C8 (wz (os_body_storage os)); C8 (wz (os_body_fill os)); C8 (wz (os_body_returned os));
C8 (wz L); C8 (wz G); C8 (wz (os_lacing_storage os)); C8 (wz (os_lacing_fill os));
C8 (wz (os_lacing_packet os)); C8 (wz (os_lacing_returned os));
CB 284 hdr;
C4 (wz (os_header_fill os)); C4 (wz (os_e_o_s os)); C4 (wz (os_b_o_s os));
C4 (wz (os_serialno os)); CB 4 (skipn 4 (le8 (wz (os_serialno os))));
C8 (wz (os_pageno os)); C8 (wz (os_packetno os)); C8 (wz (os_granulepos os))].

Lemma stream_cells_lw_view : forall m A Bd L G hdr os,
rw_cells rsegs m A (stream_cells Bd L G hdr os) -> rw_cells rsegs m A (stream_cells_lw Bd L G hdr os).
Proof.
intros m A Bd L G hdr os [[WF BY] WR]. cbn in WF.
split; [split|].
- cbn. tauto.
- unfold stream_cells in BY. unfold stream_cells_lw. cbn [cells_bytes cbytes] in BY |- *.
rewrite <- (firstn_skipn 4 (le8 (wz (os_serialno os)))) in BY. rewrite firstn4_le8 in BY.
rewrite <- !app_assoc in BY. exact BY.
- cbn in WR |- *. exact WR.
Qed.

Lemma swrap32_u64_small : forall v, -2^31 <= v < 2^31 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 v)) = v.
Proof.
intros v Hv. rewrite Z_to_bv_unsigned. change (bv_wrap 64 v) with (v mod 2^64).
rewrite X1nj.swrap32_mod64. apply X1nj.swrap32_small. exact Hv.
Qed.

Lemma sx32_signed_small : forall v, -2^31 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold sx32. rewrite swrap32_u64_small by exact Hv. reflexivity. Qed.

Definition SPEEX_BYTES : list byte := map (Z_to_bv 8) SPEEX_STR.
Lemma ubytes_SPEEX : ubytes SPEEX_BYTES = SPEEX_STR. Proof. reflexivity. Qed.
Definition A_SPEEX_LIT : Z := 0x103ea.
Lemma speex_lit_ro : ro_bytes rsegs A_SPEEX_LIT SPEEX_BYTES.
Proof. cbn. repeat split; vm_compute; reflexivity. Qed.
Lemma speex_lit_at : forall m, mem_inv rsegs m -> u8ro rsegs m A_SPEEX_LIT SPEEX_BYTES.
Proof. intros m MI. apply (ro_bytes_at rsegs m _ _ MI); [unfold A_SPEEX_LIT; lia| unfold A_SPEEX_LIT; cbn; lia| apply speex_lit_ro]. Qed.

Lemma ztake5_packet : forall (os : stream_st bptr) op (ab : list byte),
take (length (os_body os)) (ubytes ab) = os_body os -> zlength (os_body os) = os_body_fill os ->
0 <= pk_off op -> 5 <= pk_bytes op -> pk_off op + pk_bytes op <= os_body_fill os ->
ztake 5 (packet_data os op) = ubytes (firstn 5 (skipn (Z.to_nat (pk_off op)) ab)).
Proof.
intros os op ab PB BL O1 O2 O3. unfold packet_data, zslice, ztake, zdrop. unfold zlength in BL.
rewrite <- PB. unfold ubytes. rewrite firstn_firstn, skipn_firstn_comm, firstn_firstn, <- firstn_map, <- skipn_map.
f_equal. f_equal. lia.
Qed.

Section PKT1.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).
Notation PK := (PK dec_rep c).

Definition PKB (h : hstate bptr) (op : packet) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (nbr brem0 : Z) (ogj : list byte) (gw : word) (pno : Z) (s0w s3w : word),
ms = MS (hregs c h (a_S x) s0w (wz pno) s3w (wz 2147483647) (wz (pk_bytes op)) (wz (h_speex_serialno h)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz 0x1c418) fc None m (seg_rom rsegs)
/\ frm0 fc /\ h_stream_init h = 1 /\ h_eos h = 0
/\ h_speex_serialno h = os_serialno (h_os h) /\ h_speex_serialno h <> -1
/\ hrepx dec_rep c x h st m (C8 (wz nbr)) (C8 (wz brem0)) [CB 32 ogj]
[C8 (wz (a_Bd x + pk_off op)); C8 (wz (pk_bytes op)); C8 (wz (pk_b_o_s op)); C8 (wz (pk_e_o_s op)); C8 gw; C8 (wz (pk_packetno op))]
/\ low_ok h nbr brem0
/\ 0 <= pk_off op /\ 0 <= pk_bytes op /\ pk_off op + pk_bytes op <= os_body_fill (h_os h)
/\ zlength (packet_data (h_os h) op) = pk_bytes op
/\ os_body_data (h_os h) <> None
/\ 0 <= pk_e_o_s op <= 512
/\ 0 <= pno <= h_packet_count h /\ (h_packet_count h = 0 -> pk_off op = 0).

#[using="DRF RHF RBR CX"] Lemma pkt_head : forall fuel' h pn st ms,
PK h st ms ->
(forall h2 op st2 ms2, PKB h2 op st2 ms2 -> h_oy h2 = h_oy h -> h_bytes_remaining h2 = h_bytes_remaining h ->
h_packet_count h2 = h_packet_count h ->
os_lacing_fill (h_os h2) - os_lacing_returned (h_os h2) < os_lacing_fill (h_os h) - os_lacing_returned (h_os h) ->
implM rsegs (pkt_bodyP fuel' h2 op (packet_data (h_os h2) op) pn) st2 (PKPOST dec_rep c (h_bytes_remaining h) (h_oy h)) ms2) ->
implM rsegs (packet_loopP (S fuel') h pn) st (PKPOST dec_rep c (h_bytes_remaining h) (h_oy h)) ms.
Proof.
intros fuel' h pn st ms PG K. rewrite packet_loop_S.
first [ sf_destruct 35%nat PG as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 pno s0w s3w s5w s8w -> FRM SI1 EOS0 HR LOK PNO PZ | sf_fb; destruct PG as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & pno & s0w & s3w & s5w & s8w & -> & FRM & SI1 & EOS0 & HR & LOK & PNO & PZ) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
destruct (hrep_hrepx _ _ _ _ _ _ _ _ HR) as (ogj & opj & HRX). clear HR.
pose proof HRX as sfP_; first [ sf_destruct 16%nat sfP_ as (j16 & jsk & lk & LOW & LKOK) _ _ (stb & STB) OSP (OPK & OPS) (OG & OGS) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG PURE | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW & LKOK) & _ & _ & (stb & STB) & OSP & (OPK & OPS) & (OG & OGS) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
assert (EOSB : 0 <= h_eos h <= 1) by lia. assert (SIB : 0 <= h_stream_init h <= 1) by lia.
rewrite EOS0. cbn [Z.eqb negb].
unfold os_piece in OSP. rewrite SI1 in OSP. cbn [Z.eqb] in OSP.
pose proof OSP as sfP_; first [ sf_destruct 34%nat sfP_ as OS LH FOK SINV BINV LOK' GOK UL UG UB W1 L1 L2 L3 PB1 PB2 N1 N2 N3 Z1 Z2 Z3 R1 R2 R3 C1 C2 C3 E1 E2 E3 G1 G2 G3 | sf_fb; destruct sfP_ as (OS & LH & FOK & SINV & BINV & LOK' & GOK & UL & UG & UB & W1 & L1 & L2 & L3 & PB1 & PB2 & N1 & N2 & N3 & Z1 & Z2 & Z3 & R1 & R2 & R3 & C1 & C2 & C3 & E1 & E2 & E3 & G1 & G2 & G3) ].
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as Fa Fb Fc Fd Fe Ff Fg Fh Fi Fj Fk Fl | sf_fb; destruct sfP_ as (Fa & Fb & Fc & Fd & Fe & Ff & Fg & Fh & Fi & Fj & Fk & Fl) ]. unfold int31 in Fd, Fe, Ff, Fg, Fh, Fi, Fj.
pose proof SINV as sfP_; first [ sf_destruct 5%nat sfP_ as I1 I2 I3 I4 I5 | sf_fb; destruct sfP_ as (I1 & I2 & I3 & I4 & I5) ]. unfold zlength in I3, I4.
pose proof (u8arr_bound _ _ _ _ UB) as BDB. pose proof (u32arr_bound _ _ _ _ UL) as BDL. pose proof (u64arr_bound _ _ _ _ UG) as BDG.

destruct (ogg_stream_packetout (h_os h)) as [[[r opo] os']|] eqn:EPK.
2:{ exfalso. exact (ogg_stream_packetout_total _ (stream_inv_lacing_inv _ SINV) EPK). }
pose proof (pko_facts _ _ _ _ SINV BINV EPK) as sfP_; first [ sf_destruct 16%nat sfP_ as SINV' BINV' ELAC EGRA EBODY EBD ELV EGV EBS ELS ELF EBF ESN RETB R1F OPF | sf_fb; destruct sfP_ as (SINV' & BINV' & ELAC & EGRA & EBODY & EBD & ELV & EGV & EBS & ELS & ELF & EBF & ESN & RETB & R1F & OPF) ].

first [ pose proof (cells48_junk6 _ _ _ OPK OPS) as sfP_; sf_destruct 7%nat sfP_ as k0 k1 k2 k3 k4 k5 OPJ | sf_fb; destruct (cells48_junk6 _ _ _ OPK OPS) as (k0 & k1 & k2 & k3 & k4 & k5 & OPJ) ]. clear OPK.
unfold low_cells, wz in LOW.
pose proof (munch_refl [(aOS c, aOS c + 408); (aOP c, aOP c + 48)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
change (id (rw_cells rsegs m RERRNO [C4 errv])) in ERR. change (id (bytes_at rsegs m (x_P c) (to_bytes (x_payload c)))) in PAY.
unfold implM. iprefix. unfold hregs, wz.

zstep. zstep. zstep.
callx (eapply (ogg_stream_packetout_spec (aOS c) (a_Bd x) (a_L x) (a_Gv x) (aOP c) (a_hdr x) (h_os h) (a_lws x) (a_gws x) k0 k1 k2 k3 k4 k5);
first [ exact LH | exact FOK | exact LOK' | exact W1 | exact L1 | exact L2 | exact MI | exact OS | exact UL | exact UG | exact OPJ | exact Z1 | exact EPK
| reflexivity | apply stream_inv_lacing_inv; exact SINV | lia | idtac ]).
rename PC into OS1. rename PC0 into FOK1. rename POST into OPC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG. unfold id in ERR, PAY.
pose proof (pko_ret _ _ _ _ EPK) as RR.
assert (HL0 : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
pose proof (pay_range RBR c _ _ _ CX HP HL0) as PRANGE.
assert (NUL : sy_data (h_oy h) = None -> a_D x = 0 /\ sy_storage (h_oy h) = 0).
{ intros ED. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT. rewrite ED in DAT. first [ sf_destruct 4%nat DAT as -> _ _ -> | sf_fb; destruct DAT as (-> & _ & _ & ->) ]. auto. }
assert (SYR : a_D x + sy_storage (h_oy h) <= alloc_ceiling).
{ destruct (sy_data (h_oy h)) eqn:ED.
- destruct (SYBLK ltac:(congruence)) as [(B1 & _ & _ & B4 & _) _]. lia.
- destruct (NUL eq_refl) as [-> ->]. unfold alloc_ceiling. lia. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| side1c| side1c].
eapply (dec_piece_agree2 _ _ _ _ _ _ _ DRF AG) in DEC.
2:{ intros a (bb & Hbb & Ra). unfold dec_piece in DEC. destruct (h_st h); [| destruct DEC as [_ E']; rewrite E' in Hbb; destruct Hbb].
destruct DEC as (_ & _ & BRD). pose proof (BRD bb Hbb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4. cbn [outside fst snd]. lia. }
eapply (pay_keep c _ _ _ CX AG) in PAY.
2:{ intros NE IN a Ha. cbn [outside fst snd]. destruct PRANGE as [PR|PR]; [unfold alloc_ceiling in PR; lia| rewrite PR in Ha; lia]. }
xport AG side1c.
assert (HG1 : hglob c x h st m1).
{ eapply hglob_frame; [exact RHF| exact RBR| exact CX| exact HG| exact MU| exact WM| | assumption| assumption].
unfold in_frame. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
pose proof (stream_rep_pko m m1 c x h (h_oy h) r opo os' OSP EPK OS1 FOK1 UL UG UB) as SR1.
clear HP AUX PE MU WM.

assert (HREP1 : forall sser OPc, rw_cells rsegs m1 (aOP c) OPc -> cells_size OPc = 48%nat -> -2^31 <= sser < 2^31 ->
hrepx dec_rep c x (set_serialno (set_ogg h (h_oy h) os') sser) st m1 (C8 (Z_to_bv 64 nbr)) (C8 (Z_to_bv 64 brem0)) [CB 32 ogj] OPc).
{ intros sser OPc HOP HOS SSR'.
split; [exists j16, jsk, lk; split; [exact LOW| unfold lk_ok in LKOK |- *; cbn [h_st set_serialno set_ogg]; exact LKOK]|]. split; [reflexivity|]. split; [reflexivity|]. split; [exists stb; assumption|].
split; [unfold os_piece; cbn [h_stream_init h_os set_serialno set_ogg]; rewrite SI1; cbn [Z.eqb]; exact SR1|].
split; [split; [exact HOP| exact HOS]|]. split; [split; [assumption| reflexivity]|].
split; [exact SY|]. split; [exact BI|]. split; [exists pad; assumption|]. split; [exists outb; split; assumption|].
split; [exists hij; assumption|]. split; [assumption|]. split; [exact DEC|].
split. { unfold hglob, owned in HG1 |- *. cbn [h_st h_bits h_os h_oy set_serialno set_ogg]. rewrite EBD, ELV, EGV. exact HG1. }
unfold hpure in PURE |- *. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os set_serialno set_ogg].
unfold hbudget, hconsumed, hpend in *. cbn [h_packet_count h_oy h_os h_bytes_remaining set_serialno set_ogg]. rewrite ELS, EBS, ELF, EBF.
repeat (split; [assumption|]). plia. }

assert (EXIT : forall (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y24 y28 y29 y30 y31 : word) (sser : Z) OPc,
rw_cells rsegs m1 (aOP c) OPc -> cells_size OPc = 48%nat -> -2^31 <= sser < 2^31 ->
evt rsegs (fun ms1 => impl rsegs (at_node rsegs) ((X1qx.mret (Cont (set_serialno (set_ogg h (h_oy h) os') sser))) st)
(epost (fun p ms2 => PKPOST dec_rep c (h_bytes_remaining h) (h_oy h) (fst p) (snd p) ms2)) ms1)
(MS (mkR y1 (Z_to_bv 64 (aLOW c)) (x_gp c) (Z_to_bv 64 RATP) y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 (a_S x)) y19 (Z_to_bv 64 (h_extra_headers h)) y21 y22 (Z_to_bv 64 (h_packet_count h)) y24
(Z_to_bv 64 (h_nframes h)) (Z_to_bv 64 sser) (Z_to_bv 64 (h_channels h)) y28 y29 y30 y31)
F (Z_to_bv 64 0x1c6e8) fc None m1 (seg_rom rsegs))).
{ intros. zstep. zstep. zstep. apply evt_done. apply implM_ret. apply evt_done. cbn [fst snd]. split; [| split; reflexivity].
unfold PGN. sf_eexists 16%nat. first [ unshelve sf_eexists 10%nat; [ exact (F) | exact (fc) | exact (m1) | exact (x) | exact (nbr) | exact (brem0) | exact (y8) | exact (y19) | exact (y21) | exact (y24) | ] | sf_fb; exists F, fc, m1, x, nbr, brem0, y8, y19, y21, y24 ].
split; [unfold hregs, wz; cbn [h_nframes h_last_granule h_packet_count h_speex_serialno h_channels h_eos h_stream_init h_extra_headers set_serialno set_ogg]; rewrite EOS0; reflexivity|].
split; [exact FRM|]. split; [exact SI1|]. split; [| exact LOK]. eapply hrepx_hrep. apply HREP1; eassumption. }
assert (EXIT2 : forall (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y24 y26 y28 y29 y30 y31 : word) OPc,
rw_cells rsegs m1 (aOP c) OPc -> cells_size OPc = 48%nat ->
evt rsegs (fun ms1 => impl rsegs (at_node rsegs) ((X1qx.mret (Cont (set_serialno (set_ogg h (h_oy h) os') (-1)))) st)
(epost (fun p ms2 => PKPOST dec_rep c (h_bytes_remaining h) (h_oy h) (fst p) (snd p) ms2)) ms1)
(MS (mkR y1 (Z_to_bv 64 (aLOW c)) (x_gp c) (Z_to_bv 64 RATP) y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 (a_S x)) y19 (Z_to_bv 64 (h_extra_headers h)) y21 y22 (Z_to_bv 64 (h_packet_count h)) y24
(Z_to_bv 64 (h_nframes h)) y26 (Z_to_bv 64 (h_channels h)) y28 y29 y30 y31)
F (Z_to_bv 64 0x1c704) fc None m1 (seg_rom rsegs))).
{ intros. zstep. zstep. zstep. apply evt_done. apply implM_ret. apply evt_done. cbn [fst snd]. split; [| split; reflexivity].
unfold PGN. sf_eexists 16%nat. first [ unshelve sf_eexists 10%nat; [ exact (F) | exact (fc) | exact (m1) | exact (x) | exact (nbr) | exact (brem0) | exact (y8) | exact (y19) | exact (y21) | exact (y24) | ] | sf_fb; exists F, fc, m1, x, nbr, brem0, y8, y19, y21, y24 ].
split; [unfold hregs, wz; cbn [h_nframes h_last_granule h_packet_count h_speex_serialno h_channels h_eos h_stream_init h_extra_headers set_serialno set_ogg]; rewrite EOS0; reflexivity|].
split; [exact FRM|]. split; [exact SI1|]. split; [| exact LOK]. eapply hrepx_hrep. apply HREP1; [eassumption| eassumption| lia]. }

zstep. zstep. if_cases B1; rewrite zbv_eqb_signed in B1 by lia.
-
apply (proj1 (Z.eqb_neq _ _)) in B1 || (apply Bool.negb_true_iff in B1; apply (proj1 (Z.eqb_neq _ _)) in B1).
replace (negb (r =? 1)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact B1).
replace (set_ogg h (h_oy h) os') with (set_serialno (set_ogg h (h_oy h) os') (h_speex_serialno h)) by (destruct h; reflexivity).
eapply EXIT; [exact OPC| destruct opo; reflexivity| lia].
-
assert (RONE : r = 1) by (destruct (Z.eqb_spec r 1); [assumption| discriminate]). clear B1. subst r.
destruct (R1F eq_refl) as [OPNZ RLT]. destruct opo as [op|]; [| exfalso; exact (OPNZ eq_refl)]. clear OPNZ R1F.
cbn [Z.eqb Pos.eqb negb].
change (h_speex_serialno (set_ogg h (h_oy h) os')) with (h_speex_serialno h).
first [ sf_destruct 4%nat OPF as OF1 OF2 OF3 OF4 | sf_fb; destruct OPF as (OF1 & OF2 & OF3 & OF4) ].
assert (BDNZ : os_body_data (h_os h) <> None).
{ destruct G3 as [(G & _)|G]; [exact G|]. exfalso. rewrite G in EPK. pose proof (pko_stream_zero _ _ _ EPK). lia. }
pose proof BINV' as (BL' & _). rewrite EBODY, EBF in BL'.
cbn [op_cells] in OPC.
set (sser := if (5 <=? pk_bytes op) && list_eqb (ztake 5 (packet_data os' op)) SPEEX_STR then os_serialno os' else h_speex_serialno h).
assert (SSR2 : -2^31 <= sser < 2^31) by (subst sser; destruct (_ && _); lia).

assert (JOIN : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (ss : Z), ss = sser ->
evt rsegs (fun ms1 => impl rsegs (at_node rsegs)
((if (sser =? -1) || negb (os_serialno os' =? sser)
then X1qx.mret (Cont (set_serialno (set_ogg h (h_oy h) os') sser))
else pkt_bodyP fuel' (set_serialno (set_ogg h (h_oy h) os') sser) op (packet_data os' op) pn) st)
(epost (fun p ms2 => PKPOST dec_rep c (h_bytes_remaining h) (h_oy h) (fst p) (snd p) ms2)) ms1)
(MS (mkR y1 (Z_to_bv 64 (aLOW c)) (x_gp c) (Z_to_bv 64 RATP) y5 y6 y7 s0w (Z_to_bv 64 pno) y10 y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 (a_S x)) s3w (Z_to_bv 64 (h_extra_headers h)) s5w (Z_to_bv 64 (h_eos h)) (Z_to_bv 64 (h_packet_count h)) (Z_to_bv 64 (pk_bytes op))
(Z_to_bv 64 (h_nframes h)) (Z_to_bv 64 ss) (Z_to_bv 64 (h_channels h)) y28 y29 y30 y31)
F (Z_to_bv 64 0x1c400) fc None m1 (seg_rom rsegs))).
{ intros until ss. intros ->.

zstep. zstep. if_cases B3; rewrite zbv_eqb_signed in B3 by lia.
-
rewrite B3. cbn [orb]. scond B3. rewrite B3.
eapply EXIT2; [exact OPC| reflexivity].
- rewrite B3. cbn [orb]. scond B3.

pose proof OS1 as OSu. unfold stream_cells, wz in OSu.
zstep. zstep. clear OSu. if_cases B4; rewrite zbv_eqb_signed in B4 by lia.
+
replace (negb (os_serialno os' =? sser)) with true by (symmetry; first [exact B4| apply Bool.negb_true_iff; exact B4]).
eapply EXIT; [exact OPC| reflexivity| exact SSR2].
+
assert (SEQ : os_serialno os' = sser).
{ scond B4. exact B4. }
rewrite (proj2 (Z.eqb_eq _ _) SEQ). cbn [negb].
zstep. zstep.
apply evt_done. apply (K (set_serialno (set_ogg h (h_oy h) os') sser) op st).
* unfold PKB. sf_eexists 16%nat. first [ unshelve sf_eexists 11%nat; [ exact (F) | exact (fc) | exact (m1) | exact (x) | exact (nbr) | exact (brem0) | exact (ogj) | exact (x16) | exact (pno) | exact (s0w) | exact (s3w) | ] | sf_fb; exists F, fc, m1, x, nbr, brem0, ogj, x16, pno, s0w, s3w ].
split; [unfold hregs, wz; cbn [h_nframes h_last_granule h_packet_count h_speex_serialno h_channels h_eos h_stream_init set_serialno set_ogg]; rewrite ?EOS0; reflexivity|].
split; [exact FRM|]. split; [exact SI1|]. split; [exact EOS0|].
split; [cbn [h_speex_serialno h_os set_serialno set_ogg]; symmetry; exact SEQ|].
split; [cbn [h_speex_serialno set_serialno set_ogg]; exact B3|].
split; [apply HREP1; [exact OPC| reflexivity| exact SSR2]|].
split; [unfold low_ok in LOK |- *; cbn [h_bytes_remaining set_serialno set_ogg]; exact LOK|].
pose proof (pko_eos_range _ _ _ _ EPK) as [EO1 EO2].
cbn [h_os h_packet_count set_serialno set_ogg]. rewrite EBF, EBD.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [split; assumption|].
split; [exact PNO|]. intros PC0'. rewrite (pko_off _ _ _ _ EPK). apply PZ. exact PC0'.
* reflexivity.
* reflexivity.
* reflexivity.
* cbn [h_os set_serialno set_ogg]. lia. }

zstep. zstep. zstep. if_cases B2; scond B2.
+
apply JOIN. subst sser. replace (5 <=? pk_bytes op) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
+
assert (LENB : (Z.to_nat (pk_off op) + 5 <= length (a_body x))%nat) by (unfold zlength in BL'; lia).
pose proof (bytes_at_sub m1 (a_Bd x) (a_body x) (Z.to_nat (pk_off op)) 5 (proj1 UB) LENB) as HX.
rewrite Z2Nat.id in HX by lia.
set (xs := firstn 5 (skipn (Z.to_nat (pk_off op)) (a_body x))) in HX.
assert (LX : length xs = 5%nat) by (subst xs; rewrite length_firstn, length_skipn; lia).
pose proof (speex_lit_at m1 MI0) as HY.
assert (ZT : ztake 5 (packet_data os' op) = ubytes xs).
{ subst xs. apply ztake5_packet; [rewrite EBODY; exact PB1| rewrite EBODY, EBF; exact BL'| lia| lia| rewrite EBF; lia]. }

zstep. zstep. zstep. zstep.
replace (Z_to_bv 64 5) with (wz (Z.of_nat (length xs))) by (rewrite LX; reflexivity).
zstep.
eapply evt_cut; [apply bcmp_spec; [exact HX| exact HY| rewrite LX; reflexivity| rewrite LX; cbn; lia] |].
cbv beta. intros ms' PO.
first [ sf_destruct 17%nat PO as q0 q1 q2 ra0 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 -> IFF | sf_fb; destruct PO as (q0 & q1 & q2 & ra0 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & q14 & -> & IFF) ].
replace (ret_pc (Z_to_bv 64 0x1c3f8)) with (Z_to_bv 64 0x1c3f8) by (symmetry; rpc).

zstep. if_cases B5.
*
apply JOIN. subst sser. replace (5 <=? pk_bytes op) with true by (symmetry; apply Z.leb_le; lia).
rewrite ZT. cbn [andb].
destruct (list_eqb (ubytes xs) SPEEX_STR) eqn:EQ; [| reflexivity].
exfalso. apply list_eqb_eq in EQ. rewrite <- ubytes_SPEEX in EQ. apply ubytes_inj in EQ.
apply IFF in EQ. unfold wz in EQ. rewrite EQ, bv_eqb_refl in B5. discriminate.
*
assert (EQX : xs = SPEEX_BYTES).
{ apply IFF. apply Bool.negb_false_iff in B5. rewrite bv_eqb_Z in B5. apply (proj1 (Z.eqb_eq _ _)) in B5.
rewrite unsigned_lit in B5 by lia. apply bv_eq. unfold wz. rewrite unsigned_lit by lia. exact B5. }
pose proof (stream_cells_lw_view _ _ _ _ _ _ _ OS1) as OSV. unfold stream_cells_lw, wz in OSV.
zstep. clear OSV. rewrite sx32_signed_small by lia.
apply JOIN. subst sser. replace (5 <=? pk_bytes op) with true by (symmetry; apply Z.leb_le; lia).
rewrite ZT, EQX, ubytes_SPEEX. rewrite (proj2 (list_eqb_eq _ _) eq_refl). reflexivity.
Qed.
End PKT1.

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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h9 X1gy X1hg X1hf X1hh.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Definition PKBX {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (pc : Z) (S3 : word -> Prop) (X : Prop) (h : hstate bptr) (op : packet) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (nbr brem0 : Z) (ogj : list byte) (gw : word) (pno : Z) (s0w s3w : word),
ms = MS (hregs c h (a_S x) s0w (wz pno) s3w (wz 2147483647) (wz (pk_bytes op)) (wz (h_speex_serialno h)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz pc) fc None m (seg_rom rsegs)
/\ frm0 fc /\ h_stream_init h = 1 /\ h_eos h = 0
/\ h_speex_serialno h = os_serialno (h_os h) /\ h_speex_serialno h <> -1
/\ hrepx dec_rep c x h st m (C8 (wz nbr)) (C8 (wz brem0)) [CB 32 ogj]
[C8 (wz (a_Bd x + pk_off op)); C8 (wz (pk_bytes op)); C8 (wz (pk_b_o_s op)); C8 (wz (pk_e_o_s op)); C8 gw; C8 (wz (pk_packetno op))]
/\ low_ok h nbr brem0
/\ 0 <= pk_off op /\ 0 <= pk_bytes op /\ pk_off op + pk_bytes op <= os_body_fill (h_os h)
/\ zlength (packet_data (h_os h) op) = pk_bytes op
/\ os_body_data (h_os h) <> None
/\ 0 <= pk_e_o_s op <= 512
/\ 0 <= pno <= h_packet_count h
/\ S3 s3w
/\ X.
Notation PKH dec_rep c h op := (PKBX dec_rep c 0x1c55c (fun _ => True) (h_packet_count h = 0 /\ pk_off op = 0) h op).
Notation PKD dec_rep c h op := (PKBX dec_rep c 0x1c42c (fun w => w = wz (h_speex_serialno h)) (h_packet_count h <> 0 /\ 1 + h_extra_headers h < h_packet_count h) h op).

Definition PKE {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (h : hstate bptr) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (pnv nbr brem0 : Z) (s0w s5w s8w s10w : word),
ms = MS (hregs c h (a_S x) s0w (wz pnv) (wz (h_speex_serialno h)) s5w s8w s10w x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz 0x1c6c8) fc None m (seg_rom rsegs)
/\ frm0 fc /\ h_stream_init h = 1 /\ h_packet_count h <> 0 /\ 0 <= pnv <= h_packet_count h + 1
/\ hrep dec_rep c x h st m (C8 (wz nbr)) (C8 (wz brem0)) /\ low_ok h nbr brem0
/\ h_packet_count h + 1 + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * hconsumed c h.

Lemma PK_budget {RCEIL : RunCeiling} : forall dec_rep c h st ms, PK dec_rep c h st ms -> hbudget c h.
Proof.
intros dec_rep c h st ms PG.
first [ sf_destruct 35%nat PG as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 pno s0w s3w s5w s8w _ _ _ _ HR _ _ _ | sf_fb; destruct PG as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & pno & s0w & s3w & s5w & s8w & _ & _ & _ & _ & HR & _ & _ & _) ].
first [ sf_destruct 16%nat HR as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PURE | sf_fb; destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PURE) ].
first [ sf_destruct 22%nat PURE as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BUD | sf_fb; destruct PURE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BUD) ]. exact BUD.
Qed.

Lemma PKB_lacing {RCEIL : RunCeiling} : forall dec_rep c h op st ms, PKB dec_rep c h op st ms ->
0 <= os_lacing_returned (h_os h) <= os_lacing_fill (h_os h).
Proof.
intros dec_rep c h op st ms PB.
first [ sf_destruct 35%nat PB as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 ogj gw pno s0w s3w _ _ SI1 _ _ _ HRX _ | sf_fb; destruct PB as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & ogj & gw & pno & s0w & s3w & _ & _ & SI1 & _ & _ & _ & HRX & _) ].
first [ sf_destruct 6%nat HRX as _ _ _ _ OSP _ | sf_fb; destruct HRX as (_ & _ & _ & _ & OSP & _) ]. unfold os_piece in OSP. rewrite SI1 in OSP. cbn [Z.eqb] in OSP.
first [ sf_destruct 5%nat OSP as _ _ _ ((I1 & I1') & I2 & _) _ | sf_fb; destruct OSP as (_ & _ & _ & ((I1 & I1') & I2 & _) & _) ]. lia.
Qed.

Lemma hrep_incr {RCEIL : RunCeiling} : forall dec_rep c x h st m cn cb,
hrep dec_rep c x h st m cn cb -> h_packet_count h <> 0 ->
h_packet_count h + 1 + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * hconsumed c h ->
os_lacing_returned (h_os h) <= os_lacing_fill (h_os h) ->
hrep dec_rep c x (incr_packet_count h) st m cn cb.
Proof.
intros dec_rep c x h st m cn cb HR NZ BUD' LE.
first [ sf_destruct 16%nat HR as LOW C1 C2 STB OSP OP OG SY BI FSZ OUT CBK SAV DEC HG PURE | sf_fb; destruct HR as (LOW & C1 & C2 & STB & OSP & OP & OG & SY & BI & FSZ & OUT & CBK & SAV & DEC & HG & PURE) ].
split; [exact LOW|]. split; [exact C1|]. split; [exact C2|]. split; [exact STB|]. split; [exact OSP|].
split; [exact OP|]. split; [exact OG|]. split; [exact SY|]. split; [exact BI|]. split; [exact FSZ|].
split; [exact OUT|]. split; [exact CBK|]. split; [exact SAV|]. split; [exact DEC|]. split; [exact HG|].
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
unfold hbudget, hconsumed, hpend in BUD, BUD'. unfold MAX_FUZZ_SIZE in L4K.
unfold hpure. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os incr_packet_count].
do 14 (split; [assumption|]). split; [lia|]. do 5 (split; [assumption|]).
split; [destruct (h_st h); [lia| exfalso; exact (NZ STR)]|].
unfold hbudget, hconsumed, hpend. cbn [h_packet_count h_oy h_os h_bytes_remaining incr_packet_count]. lia.
Qed.

Section PKT2.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).
Notation PK := (PK dec_rep c).
Notation PKB := (PKB dec_rep c).
Notation PKE := (PKE dec_rep c).

Definition pkt_path_stmt (CUT : hstate bptr -> packet -> PState -> machine_state -> Prop) : Prop :=
forall fuel' h op pn st ms (br0 : Z) (oy0 : sync_st bptr),
CUT h op st ms -> h_oy h = oy0 -> h_bytes_remaining h = br0 ->
h_packet_count h + 1 + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * hconsumed c h ->
(forall h' pn' st' ms', PK h' st' ms' -> h_oy h' = oy0 -> h_bytes_remaining h' = br0 ->
os_lacing_fill (h_os h') - os_lacing_returned (h_os h') <= os_lacing_fill (h_os h) - os_lacing_returned (h_os h) ->
implM rsegs (packet_loopP fuel' h' pn') st' (PKPOST dec_rep c br0 oy0) ms') ->
implM rsegs (pkt_bodyP fuel' h op (packet_data (h_os h) op) pn) st (PKPOST dec_rep c br0 oy0) ms.
Hypothesis HDR : pkt_path_stmt (fun h op => PKH dec_rep c h op).
Hypothesis DATA : pkt_path_stmt (fun h op => PKD dec_rep c h op).

#[using="Type"] Lemma pk_tail : forall fuel' h pn st ms (br0 : Z) (oy0 : sync_st bptr),
PKE h st ms -> h_oy h = oy0 -> h_bytes_remaining h = br0 ->
(forall st' ms', PK (incr_packet_count h) st' ms' ->
implM rsegs (packet_loopP fuel' (incr_packet_count h) pn) st' (PKPOST dec_rep c br0 oy0) ms') ->
implM rsegs (packet_loopP fuel' (incr_packet_count h) pn) st (PKPOST dec_rep c br0 oy0) ms.
Proof.
intros fuel' h pn st ms br0 oy0 PE EOY EBR K.
first [ sf_destruct 35%nat PE as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x pnv nbr brem0 s0w s5w s8w s10w -> FRM SI1 NZ PNV HR LOK BUD' | sf_fb; destruct PE as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & pnv & nbr & brem0 & s0w & s5w & s8w & s10w & -> & FRM & SI1 & NZ & PNV & HR & LOK & BUD') ].
pose proof HR as sfP_; first [ sf_destruct 16%nat sfP_ as (j16 & jsk & lk & LOW & _) _ _ _ OSP _ _ _ _ _ _ _ _ _ _ PURE | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW & _) & _ & _ & _ & OSP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PURE) ].
unfold low_cells, wz in LOW.
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
unfold os_piece in OSP. rewrite SI1 in OSP. cbn [Z.eqb] in OSP.
pose proof OSP as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ SINV _ | sf_fb; destruct sfP_ as (_ & _ & _ & SINV & _) ]. pose proof SINV as (I1 & I2 & _).
unfold hbudget, hconsumed, hpend in BUD, BUD'. pose proof L4K as L4K'. unfold MAX_FUZZ_SIZE in L4K'.
assert (PC1 : 0 <= h_packet_count h + 1 < 2^31 - 1) by lia. assert (EOSB : 0 <= h_eos h <= 1) by lia.
assert (HR1 : hrep dec_rep c x (incr_packet_count h) st m (C8 (wz nbr)) (C8 (wz brem0))).
{ apply hrep_incr; [exact HR| exact NZ| unfold hconsumed, hpend; exact BUD'| lia]. }
unfold implM. iprefix. unfold hregs, wz.

zstep. rewrite swrap32_small by lia. zstep. rewrite lts_succ_false by lia. cbv iota.
zstep. zstep. zstep. if_cases BE; scond BE.
-
apply evt_done. apply (K st).
unfold X1hg.PK. sf_eexists 16%nat. first [ unshelve sf_eexists 11%nat; [ exact (F) | exact (fc) | exact (m) | exact (x) | exact (nbr) | exact (brem0) | exact (pnv) | exact (s0w) | exact (Z_to_bv 64 (h_speex_serialno h)) | exact (s5w) | exact (s8w) | ] | sf_fb; exists F, fc, m, x, nbr, brem0, pnv, s0w, (Z_to_bv 64 (h_speex_serialno h)), s5w, s8w ].
split; [unfold hregs, wz; cbn [h_nframes h_last_granule h_packet_count h_speex_serialno h_channels h_eos h_stream_init h_extra_headers incr_packet_count];
rewrite ?BE; reflexivity|].
split; [exact FRM|]. split; [exact SI1|]. split; [exact BE|]. split; [exact HR1|].
split; [unfold low_ok in LOK |- *; cbn [h_bytes_remaining incr_packet_count]; exact LOK|].
cbn [h_packet_count incr_packet_count]. split; [lia| intros; lia].
-
assert (E1 : h_eos h = 1) by lia.
zstep. zstep. zstep. zstep. apply evt_done.
destruct fuel' as [|f'']; [apply implM_unr|]. rewrite packet_loop_S.
cbn [h_eos incr_packet_count]. rewrite E1. cbn [Z.eqb negb].
apply implM_ret. apply evt_done. cbn [fst snd]. split; [| split; [exact EBR| exact EOY]].
unfold PGN. sf_eexists 16%nat. first [ unshelve sf_eexists 10%nat; [ exact (F) | exact (fc) | exact (m) | exact (x) | exact (nbr) | exact (brem0) | exact (s0w) | exact (Z_to_bv 64 (h_speex_serialno h)) | exact (s5w) | exact (s8w) | ] | sf_fb; exists F, fc, m, x, nbr, brem0, s0w, (Z_to_bv 64 (h_speex_serialno h)), s5w, s8w ].
split; [unfold hregs, wz; cbn [h_nframes h_last_granule h_packet_count h_speex_serialno h_channels h_eos h_stream_init h_extra_headers incr_packet_count];
rewrite E1; reflexivity|].
split; [exact FRM|]. split; [exact SI1|]. split; [exact HR1|].
unfold low_ok in LOK |- *. cbn [h_bytes_remaining incr_packet_count]. exact LOK.
Qed.

#[using="HDR DATA"] Lemma pkt_body : pkt_path_stmt PKB.
Proof.
intros fuel' h op pn st ms br0 oy0 PB EOY EBR BUD' K.
pose proof PB as PB0.
first [ sf_destruct 43%nat PB as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 ogj gw pno s0w s3w -> FRM SI1 EOS0 SSE SNM1 HRX LOK OF1 OF2 OF3 OF4 BDNZ EOSR PNO PZ | sf_fb; destruct PB as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & ogj & gw & pno & s0w & s3w & -> & FRM & SI1 & EOS0 & SSE & SNM1 & HRX & LOK & OF1 & OF2 & OF3 & OF4 & BDNZ & EOSR & PNO & PZ) ].
pose proof HRX as sfP_; first [ sf_destruct 16%nat sfP_ as (j16 & jsk & lk & LOW & LKOK) _ _ (stb & STB) OSP (OPK & OPS) (OG & OGS) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG PURE | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW & LKOK) & _ & _ & (stb & STB) & OSP & (OPK & OPS) & (OG & OGS) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE) ].
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
unfold os_piece in OSP. rewrite SI1 in OSP. cbn [Z.eqb] in OSP.
pose proof OSP as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ SINV _ | sf_fb; destruct sfP_ as (_ & _ & _ & SINV & _) ]. pose proof SINV as (I1 & I2 & _).
assert (EOSB : 0 <= h_eos h <= 1) by lia.
unfold implM. iprefix. unfold hregs, wz.

zstep. if_cases B1; scond B1.
-
apply evt_done. apply (HDR fuel' h op pn st _ br0 oy0); [| exact EOY| exact EBR| exact BUD'| exact K].
unfold PKBX. sf_eexists 16%nat. first [ unshelve sf_eexists 11%nat; [ exact (F) | exact (fc) | exact (m) | exact (x) | exact (nbr) | exact (brem0) | exact (ogj) | exact (gw) | exact (pno) | exact (s0w) | exact (s3w) | ] | sf_fb; exists F, fc, m, x, nbr, brem0, ogj, gw, pno, s0w, s3w ].
split; [unfold hregs, wz; rewrite ?EOS0; reflexivity|]. repeat (split; [assumption|]). split; [exact I|]. split; [exact B1| apply PZ; exact B1].
-
zstep. first [rewrite swrap32_small by lia| rewrite swrap32_u64_plus1 by lia| rewrite swrap32_land64_plus1 by lia]. zstep. rewrite lts_succ_false by lia. cbv iota.
zstep. zstep. if_cases B2; scond B2.
+
unfold pkt_bodyP. replace (h_packet_count h =? 0) with false by (symmetry; apply Z.eqb_neq; exact B1).
replace (h_packet_count h <=? 1 + h_extra_headers h) with true by (symmetry; apply Z.leb_le; lia).
apply evt_done.

lazymatch goal with |- impl _ _ _ _ ?msx => change (implM rsegs (packet_loopP fuel' (incr_packet_count h) pn) st (PKPOST dec_rep c br0 oy0) msx) end.
unfold implM. iprefix. zstep. apply evt_done.
apply (pk_tail fuel' h pn st _ br0 oy0); [| exact EOY| exact EBR|].
2:{ intros st' ms' PK'. apply (K _ pn st' ms' PK'); [exact EOY| exact EBR| cbn [h_os incr_packet_count]; lia]. }
unfold PKE. sf_eexists 16%nat. first [ unshelve sf_eexists 11%nat; [ exact (F) | exact (fc) | exact (m) | exact (x) | exact (pno) | exact (nbr) | exact (brem0) | exact (s0w) | exact (Z_to_bv 64 2147483647) | exact (Z_to_bv 64 (pk_bytes op)) | exact (Z_to_bv 64 (h_speex_serialno h)) | ] | sf_fb; exists F, fc, m, x, pno, nbr, brem0, s0w, (Z_to_bv 64 2147483647), (Z_to_bv 64 (pk_bytes op)), (Z_to_bv 64 (h_speex_serialno h)) ].
split; [unfold hregs, wz; rewrite EOS0; reflexivity|].
split; [exact FRM|]. split; [exact SI1|]. split; [exact B1|]. split; [lia|]. split; [eapply hrepx_hrep; exact HRX|]. split; [exact LOK| exact BUD'].
+
apply evt_done. apply (DATA fuel' h op pn st _ br0 oy0); [| exact EOY| exact EBR| exact BUD'| exact K].
unfold PKBX. sf_eexists 16%nat. first [ unshelve sf_eexists 11%nat; [ exact (F) | exact (fc) | exact (m) | exact (x) | exact (nbr) | exact (brem0) | exact (ogj) | exact (gw) | exact (pno) | exact (s0w) | exact (Z_to_bv 64 (h_speex_serialno h)) | ] | sf_fb; exists F, fc, m, x, nbr, brem0, ogj, gw, pno, s0w, (Z_to_bv 64 (h_speex_serialno h)) ].
split; [unfold hregs, wz; rewrite ?EOS0; reflexivity|]. repeat (split; [assumption|]). split; [reflexivity|]. first [split; [exact B1| lia]| lia].
Qed.

#[using="DRF RHF RBR CX HDR DATA"] Lemma pkt_loop_ok : forall (n : nat) fuel h pn st ms,
PK h st ms ->
(Z.to_nat (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) < n)%nat ->
(Z.to_nat (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) < fuel)%nat ->
implM rsegs (packet_loopP fuel h pn) st (PKPOST dec_rep c (h_bytes_remaining h) (h_oy h)) ms.
Proof.
induction n as [|n IH]; intros fuel h pn st ms PG MEAS FUEL; [lia|].
destruct fuel as [|fuel']; [lia|].
pose proof (PK_budget _ _ _ _ _ PG) as BUD. unfold hbudget in BUD.
eapply pkt_head; [exact DRF| exact RHF| exact RBR| exact CX| exact PG|].
intros h2 op st2 ms2 PB EOY EBR EPC DECR.
apply (pkt_body fuel' h2 op pn st2 ms2 (h_bytes_remaining h) (h_oy h) PB EOY EBR).
{ unfold hconsumed, hpend in *. rewrite EOY, EBR, EPC. lia. }
pose proof (PKB_lacing _ _ _ _ _ _ PB) as LAC2.
intros h' pn' st' ms' PK' EOY' EBR' LE'. rewrite <- EOY', <- EBR'.
apply IH; [exact PK'| lia| lia].
Qed.
End PKT2.

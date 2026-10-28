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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gp X1gq X1gr.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

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

Hypothesis PAGE : forall h st ms, PG1 dec_rep c h st ms ->
implM rsegs (page_loopP (page_fuel (h_oy h)) h) st (PGPOST dec_rep c h) ms.
Hypothesis CLEAN : forall {B} (k : unit -> M PState B) (Q : B -> PState -> machine_state -> Prop) h st ms,
CLN dec_rep c h st ms ->
(forall st' ms', HFIN c st' ms' -> implM rsegs (k tt) st' Q ms') ->
implM rsegs (X1qx.mbind (cleanupP h) k) st Q ms.

Notation chunk_tail := (chunk_tail c).
Notation chunk_tail2 := (chunk_tail2 c).
Notation chunk_tail3 := (chunk_tail3 c).
Notation CUTC2 := (CUTC2 dec_rep c).
Notation CUTC3 := (CUTC3 dec_rep c).
Notation CUTC4 := (CUTC4 dec_rep c).
Notation seg_ok := (seg_ok c).

#[using="DRF RHF RBR CX PAGE CLEAN"] Lemma chunk_wrote : forall fuel,
(forall h st ms, CUTC dec_rep c h st ms -> (Z.to_nat (h_bytes_remaining h) < fuel)%nat ->
implM rsegs (X1qx.mbind (chunk_loopP fuel (x_payload c) h) FIN) st POSTQ ms) ->
forall h nb st ms, CUTC4 h nb st ms -> (Z.to_nat (h_bytes_remaining h) < S fuel)%nat ->
implM rsegs (chunk_tail3 fuel h nb) st POSTQ ms.
Proof.
intros fuel IH h nb st ms CC Hfuel.
first [ sf_destruct 33%nat CC as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x jn jb s3w s8w -> FRM HR Hnb1 Hnb2 Hnb3 BUFL F31 RET0 | sf_fb; destruct CC as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & jn & jb & s3w & s8w & -> & FRM & HR & Hnb1 & Hnb2 & Hnb3 & BUFL & F31 & RET0) ].

pose proof HR as sfP_; first [ sf_destruct 16%nat sfP_ as (j16a & jska & lka & LOWa & LKOKa) _ _ _ _ _ _ _ _ _ _ _ _ _ (_ & _ & _ & _ & _ & _ & _ & MIa & _) _ | sf_fb; destruct sfP_ as ((j16a & jska & lka & LOWa & LKOKa) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & MIa & _) & _) ].
unfold low_cells in LOWa. change (id (hrep dec_rep c x h st m (CB 8 jn) (CB 8 jb))) in HR.
pose proof (munch_refl [(aLOW c, aLOW c + 80)] m) as MUa. pose proof (wmono_refl rsegs m) as WMa.
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as _ _ _ _ _ _ _ CEILa LOa _ SPBa | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & CEILa & LOa & _ & SPBa) ].
unfold RFUZZ_STACK in LOa. unfold alloc_ceiling in CEILa.
unfold implM. iprefix. unfold hregs, wz.
zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st POSTQ msx) end.
lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) => set (mA := mx) in * end.
unfold id in HR. eapply (hrep_relow dec_rep c x h st m mA) in HR; [| exact DRF| exact RHF| exact RBR| exact CX| exact MUa| exact WMa| assumption| unfold low_cells; exact LOWa| exact LKOKa| reflexivity| reflexivity].
clearbody mA. clear MUa WMa LOWa CEILa LOa SPBa j16a jska lka LKOKa. clear m. rename mA into m.
first [ sf_destruct 16%nat HR as (j16 & jsk & lk & LOW & LKOK) _ _ (stb & STB) OSP (opj & OPK) (ogj & OGJ) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG PURE | sf_fb; destruct HR as ((j16 & jsk & lk & LOW & LKOK) & _ & _ & (stb & STB) & OSP & (opj & OPK) & (ogj & OGJ) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
assert (HL0 : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
pose proof (pay_range RBR c _ _ _ CX HP HL0) as PRANGE.
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ]. unfold hbudget, hconsumed, hpend in BUD.
pose proof SYOK as (SYI2 & SYST & SYNUL). pose proof SYI2 as [SYI _].
unfold low_cells, wz in LOW.
pose proof (munch_refl [(aOY c, aOY c + 32)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
change (id (bytes_at rsegs m (x_P c) (to_bytes (x_payload c)))) in PAY. change (id (rw_cells rsegs m RERRNO [C4 errv])) in ERR.
unfold chunk_tail3, implM. iprefix. unfold hregs, wz.

zstep. zstep.
callx (eapply ogg_sync_wrote_spec with (A := aOY c) (D := a_D x) (sy := h_oy h) (bytes := a_sybytes x) (n := nb);
[reflexivity| reflexivity| lia| lia| exact SY| exact MI]).
rename POST into SY2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (mW := mx) in * end.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG. unfold id in PAY, ERR.
clear SY.   xportx AG side1.
assert (HG1 : hglob c x h st mW).
{ eapply hglob_frame; [exact RHF| exact RBR| exact CX| exact HG| exact MU| exact WM| | assumption| assumption].
unfold in_frame. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
clearbody mW. clear MU WM AG PAY ERR TP SEW HP AUX PE ST.

destruct (ogg_sync_wrote (h_oy h) nb) as [rw oy2] eqn:EW. cbn [fst snd] in SY2 |- *.
pose proof (ogg_sync_wrote_inv (h_oy h) nb rw oy2 SYI ltac:(lia) BUFL EW) as sfP_; first [ sf_destruct 7%nat sfP_ as WI WB WF0 WF1 WR WS WD | sf_fb; destruct sfP_ as (WI & WB & WF0 & WF1 & WR & WS & WD) ].
pose proof (ogg_sync_wrote_inv2 (h_oy h) nb rw oy2 SYI2 ltac:(lia) BUFL EW) as WI2.
set (h2 := set_bytes_remaining h oy2 (h_bytes_remaining h - nb)).
assert (HG2 : hglob c x h2 st mW).
{ unfold hglob, owned in HG1 |- *. cbn [h_oy h_st h_bits h_os h2 set_bytes_remaining]. rewrite WD, WS. exact HG1. }
clear HG HG1.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st POSTQ msx) end.
apply implM_bind_assoc. eapply implM_bind.
{ apply PAGE. unfold PG1. sf_eexists 16%nat. first [ unshelve sf_eexists 9%nat; [ exact (F) | exact (fc) | exact (mW) | exact (x) | exact (jb) | exact (nb) | exact ((h_bytes_remaining h)) | exact (s3w) | exact (s8w) | ] | sf_fb; exists F, fc, mW, x, jb, nb, (h_bytes_remaining h), s3w, s8w ]. split; [reflexivity|]. split; [exact FRM|].
split.
{ unfold hrep. split; [exists j16, jsk, lk; split; [unfold low_cells, wz; exact LOW| exact LKOK]|]. split; [reflexivity|]. split; [reflexivity|].
split; [exists stb; assumption|]. split; [exact OSP|]. split; [exists opj; assumption|]. split; [exists ogj; assumption|].
split; [exact SY2|]. split; [exact BI|]. split; [exists pad; assumption|]. split; [exists outb; split; assumption|].
split; [exists hij; assumption|]. split; [assumption|]. split; [exact DEC|]. split; [exact HG2|].
unfold hpure. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os h2 set_bytes_remaining].
split. { split; [exact WI2|]. rewrite WS, WD. split; [exact SYST| exact SYNUL]. }
split; [exact BOK|]. split; [exact OWN|]. split; [rewrite WS, WD; exact SYBLK|]. split; [rewrite WS; exact SYLEN|].
repeat (split; [assumption|]).
split; [lia|]. split; [exact L4K|]. split; [exact STR|].
unfold hbudget, hconsumed, hpend in BUD |- *. cbn [h_packet_count h_oy h_os h_bytes_remaining h2 set_bytes_remaining].
rewrite WR, RET0. destruct (Z.eq_dec rw 0) as [E|E]; [rewrite (WF0 E)| rewrite (WF1 E)]; lia. }
unfold low_ok. cbn. unfold MAX_FUZZ_SIZE in L4K. lia. }

cbv beta. intros o st' ms' PO. destruct o as [h3|].
2:{   apply implM_retb. apply implM_ret. apply evt_done. exact PO. }

destruct PO as [PO EBR]. cbn [h_bytes_remaining h2 set_bytes_remaining] in EBR.
clear - DRF RMALLOC RFREE OREALLOC RHF RBR RND RBD RTK CX PAGE CLEAN IH Hfuel Hnb1 Hnb2 Hnb3 PO EBR.
first [ sf_destruct 30%nat PO as y1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F3 fc3 m3 x3 jb3 nbr brem0 s0w s3w3 s8w3 -> FRM3 HR3 LOK | sf_fb; destruct PO as (y1 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & m3 & x3 & jb3 & nbr & brem0 & s0w & s3w3 & s8w3 & -> & FRM3 & HR3 & LOK) ].
pose proof HR3 as sfP_; first [ sf_destruct 16%nat sfP_ as (j16 & jsk & lk & LOW & LKOK) _ _ _ _ _ _ _ _ _ _ _ _ _ (HP3 & PERM3 & _ & _ & _ & _ & _ & MI3 & _) PURE3 | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW & LKOK) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HP3 & PERM3 & _ & _ & _ & _ & _ & MI3 & _) & PURE3) ].
pose proof PURE3 as sfP_; first [ sf_destruct 21%nat sfP_ as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BRR3 L4K3 _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BRR3 & L4K3 & _) ].
unfold low_ok in LOK.
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
unfold low_cells, wz in LOW. change (id (hrep dec_rep c x3 h3 st' m3 (C8 (wz nbr)) (CB 8 jb3))) in HR3.
pose proof (munch_refl [] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
unfold implM. iprefix. unfold hregs, A_CHUNKX, wz.

zstep. zstep. zstep.
if_cases K; zify_cond K.
-
replace (h_bytes_remaining h3 <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
apply evt_done. apply IH; [| lia].
unfold CUTC. sf_eexists 16%nat. first [ unshelve sf_eexists 9%nat; [ exact (F3) | exact (fc3) | exact (m3) | exact (x3) | exact ((le8 (Z_to_bv 64 nbr))) | exact (jb3) | exact (s0w) | exact (s3w3) | exact (s8w3) | ] | sf_fb; exists F3, fc3, m3, x3, (le8 (Z_to_bv 64 nbr)), jb3, s0w, s3w3, s8w3 ].
replace (brem0 + - nbr) with (h_bytes_remaining h3) by lia.
split; [reflexivity|]. split; [exact FRM3|].
unfold id in HR3. first [ sf_destruct 4%nat HR3 as _ _ _ REST | sf_fb; destruct HR3 as (_ & _ & _ & REST) ]. split; [| split; [reflexivity| split; [reflexivity| exact REST]]].
exists j16, jsk, lk. split; [| exact LKOK]. apply (low_junkify_cn m3 _ c h3 j16 (Z_to_bv 64 nbr) (CB 8 jb3) jsk lk). unfold low_cells, wz. exact LOW.
-
replace (h_bytes_remaining h3 <=? 0) with true by (symmetry; apply Z.leb_le; lia).
do 6 zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st' POSTQ msx) end.
apply implM_retb. cbv beta iota. apply CLEAN.
2:{ intros st'' ms'' HF. apply implM_ret. apply evt_done. exact HF. }
unfold CLN. sf_eexists 23%nat. first [ unshelve sf_eexists 6%nat; [ exact (F3) | exact (fc3) | exact (m3) | exact (x3) | exact ((C8 (Z_to_bv 64 nbr))) | exact ((CB 8 jb3)) | ] | sf_fb; exists F3, fc3, m3, x3, (C8 (Z_to_bv 64 nbr)), (CB 8 jb3) ].
split; [reflexivity|]. split; [exact FRM3|]. unfold id in HR3. exact HR3.
Qed.

#[using="DRF RMALLOC RFREE OREALLOC RHF RBR RND RBD RTK CX PAGE CLEAN"] Theorem chunk_loop_ok : forall fuel h st ms,
CUTC dec_rep c h st ms -> (Z.to_nat (h_bytes_remaining h) < fuel)%nat ->
implM rsegs (X1qx.mbind (chunk_loopP fuel (x_payload c) h) FIN) st POSTQ ms.
Proof.
induction fuel as [|fuel IH]; intros h st ms CC Hfuel; [lia|].
eapply (chunk_head dec_rep DRF RHF RBR c CX fuel); [| exact CC].
intros st' ms' nb CC2.
apply (chunk_rest dec_rep DRF RMALLOC RFREE OREALLOC RHF RBR RND RBD RTK c CX (@CLEAN) fuel); [| exact CC2| exact Hfuel].
intros h1 nb1 rv data st1 ms1 CC3 Hf1.
apply (chunk_memcpy dec_rep DRF RHF RBR RND RBD c CX fuel h1 nb1 rv data st1 ms1); [| exact CC3].
intros h4 st4 ms4 CC4 E4. apply (chunk_wrote fuel IH); [exact CC4| rewrite E4; exact Hf1].
Qed.
End CHUNK.

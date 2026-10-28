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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gp.
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

#[using="DRF RMALLOC RFREE OREALLOC RHF RBR RND RBD RTK CX CLEAN"] Lemma chunk_rest : forall fuel,
(forall h nb rv data st ms, CUTC3 h nb rv data st ms -> (Z.to_nat (h_bytes_remaining h) < S fuel)%nat ->
implM rsegs (chunk_tail2 fuel h nb data) st POSTQ ms) ->
forall h nb st ms, CUTC2 h nb st ms -> (Z.to_nat (h_bytes_remaining h) < S fuel)%nat ->
implM rsegs (chunk_tail fuel h nb) st POSTQ ms.
Proof.
intros fuel COPY h nb st ms CC Hfuel.
first [ sf_destruct 30%nat CC as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x jn jb s3w s8w -> FRM HR Hnb1 Hnb2 Hnb3 | sf_fb; destruct CC as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & jn & jb & s3w & s8w & -> & FRM & HR & Hnb1 & Hnb2 & Hnb3) ].
pose proof HR as sfP_; first [ sf_destruct 16%nat sfP_ as (j16 & jsk & lk & LOW & LKOK) _ _ _ _ _ _ _ _ _ _ _ _ _ HG PURE | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW & LKOK) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HG & PURE) ].
pose proof HG as sfP_; first [ sf_destruct 9%nat sfP_ as HP0 PERM _ _ _ _ _ MI _ | sf_fb; destruct sfP_ as (HP0 & PERM & _ & _ & _ & _ & _ & MI & _) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
assert (HL0 : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
pose proof (pay_range RBR c _ _ _ CX HP0 HL0) as PRANGE. pose proof (RND _ _ _ HP0) as ND. clear HP0.
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ]. unfold hbudget, hconsumed, hpend in BUD.
pose proof SYOK as (SYI2 & SYST & SYNUL). pose proof SYI2 as [SYI _].
assert (NUL : sy_data (h_oy h) = None -> a_D x = 0 /\ sy_storage (h_oy h) = 0).
{ intros ED. pose proof HR as sfP_; first [ sf_destruct 9%nat sfP_ as _ _ _ _ _ _ _ SY0 _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & SY0 & _) ]. first [ sf_destruct 4%nat SY0 as _ _ DAT _ | sf_fb; destruct SY0 as (_ & _ & DAT & _) ]. unfold sync_data in DAT. rewrite ED in DAT.
first [ sf_destruct 4%nat DAT as -> _ _ -> | sf_fb; destruct DAT as (-> & _ & _ & ->) ]. auto. }
assert (SYR : a_D x + sy_storage (h_oy h) <= alloc_ceiling).
{ destruct (sy_data (h_oy h)) eqn:ED.
- destruct (SYBLK ltac:(congruence)) as [(_ & _ & _ & B4 & _) _]. exact B4.
- destruct (NUL eq_refl) as [-> ->]. unfold alloc_ceiling. lia. }
unfold low_cells in LOW. change (id (hrep dec_rep c x h st m (CB 8 jn) (CB 8 jb))) in HR.
pose proof (munch_refl [(aLOW c, aLOW c + 80)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold chunk_tail. unfold implM. iprefix. unfold hregs, wz.

zstep. zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st POSTQ msx) end.
lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) => set (mA := mx) in * end.
unfold id in HR. eapply (hrep_relow dec_rep c x h st m mA) in HR; [| exact DRF| exact RHF| exact RBR| exact CX| exact MU| exact WM| assumption| unfold low_cells; exact LOW| exact LKOK| reflexivity| reflexivity].
clearbody mA. clear MU WM MI LOW HG.
first [ sf_destruct 16%nat HR as (j16' & jsk' & lk' & LOW & LKOK') _ _ (stb & STB) OSP (opj & OPK) (ogj & OGJ) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG _ | sf_fb; destruct HR as ((j16' & jsk' & lk' & LOW & LKOK') & _ & _ & (stb & STB) & OSP & (opj & OPK) & (ogj & OGJ) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & _) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP _ PAY TP SEW (errv1 & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & _ & PAY & TP & SEW & (errv1 & ERR) & AUX & MI & ST & PE & SO) ].
apply implM_bind_assoc. eapply implM_bind.
{ eapply implM_leaves.
eapply (ogg_sync_buffer_spec rtop_known rtop_known_indep OREALLOC RMALLOC RFREE)
with (A := aOY c) (D := a_D x) (lo := x_lo c) (B := x_AB c) (LB := a_LB x) (sy := h_oy h) (size := nb);
rewrite ?(unsigned_lit (aLOW c)) by (clear - CEIL' SPB LO c RCEIL; lia);
first [ exact HP | exact SY | exact SYI | exact AUX | exact ST | exact MI | reflexivity | (clear - BRR PRANGE Hnb2 Hnb1 nb h c RCEIL SPAB CEIL; lia)
| unfold RATP; rewrite unsigned_lit by lia; exact ERR
| unfold OGG_REALLOC_STACK; (clear - LO c; lia)
| unfold MAX_FUZZ_SIZE, MMAP_THRESHOLD in *; (clear - BUD L4K PCR Hfuel x Hnb1 nb h fuel c RCEIL; lia)
| idtac ].
destruct (sy_data (h_oy h)) as [p|] eqn:ED; [| exact I].
assert (IN : In (p, a_D x, sy_storage (h_oy h)) (a_LB x)).
{ eapply Permutation_in; [apply Permutation_sym; exact PERM|]. unfold owned. rewrite ED. cbn [opt_blk]. rewrite !in_app_iff. cbn. clear. tauto. }
split; [exact IN|]. intros _. eapply RTK; [exact HP| exact IN|]. destruct (SYBLK ltac:(congruence)) as [_ GE]. unfold RBIG. lia. }
cbv beta. intros [data oy1] st1 ms1 [PO LEAF].
first [ sf_destruct 34%nat PO as y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 m1 errv2 rv D' bytes' LB' -> MI1 ST1 ERR2 AUX2 EFA ESO HP1 CM SY1 SYI1 Erv Hoff CASES | sf_fb; destruct PO as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m1 & errv2 & rv & D' & bytes' & LB' & -> & MI1 & ST1 & ERR2 & AUX2 & EFA & ESO & HP1 & CM & SY1 & SYI1 & Erv & Hoff & CASES) ].
cbn [fst snd] in SY1, SYI1, Erv, Hoff, CASES.
rewrite ?(unsigned_lit (aLOW c)) in ST1 by lia. rewrite ?(unsigned_lit (aLOW c)) in CM by lia.
unfold RATP in ERR2. rewrite ?unsigned_lit in ERR2 by lia. change (0x4d450 + -164) with RERRNO in ERR2.
replace (ret_pc (Z_to_bv 64 0x1c208)) with (Z_to_bv 64 0x1c208) by (symmetry; rpc).
assert (Hnb0 : 0 <= nb) by lia.
pose proof (sync_buffer_leaf (h_oy h) oy1 nb st st1 data Hnb0 SYOK LEAF) as (SYOK1 & LCASE). clear LEAF.
pose proof (agree_of_cmod _ _ _ _ _ CM) as AG.
pose proof (sync_call_P RBD RBR c x h st mA CX HP ND PERM NUL) as OWNP.
assert (OWNB : forall a, a_Dc x <= a < a_Dc x + sb_buf_size (h_bits h) ->
rclient_addr (lb_remove_opt (sy_data (h_oy h)) (a_LB x)) (hsp c) a /\ outside [(hsp c - 32, hsp c); (aOY c, aOY c + 32); (a_D x, a_D x + sy_storage (h_oy h))] a).
{ intros a Ha. apply (OWNP (sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h))); [| cbn; exact Ha].
unfold owned_pre. rewrite !in_app_iff. cbn. clear. tauto. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| side1| exact OWNB].
eapply (os_piece_agree2 _ _ _ _ _ _ AG) in OSP; [| side1|].
2:{ intros a (bb & Hbb & Ra). apply (OWNP bb); [| exact Ra]. unfold stream_blks in Hbb. unfold owned_pre.
rewrite !in_app_iff in Hbb. rewrite !in_app_iff. clear - Hbb. tauto. }
eapply (dec_piece_agree2 _ _ _ _ _ _ _ DRF AG) in DEC.
2:{ intros a (bb & Hbb & Ra). apply (OWNP bb); [| exact Ra]. unfold owned_pre. rewrite !in_app_iff.
unfold dec_piece in DEC. destruct (h_st h); [left; left; exact Hbb| destruct DEC as [_ E0]; rewrite E0 in Hbb; destruct Hbb]. }
assert (SYRR : a_D x + sy_storage (h_oy h) <= 0x10000 \/ 0x6e000 <= a_D x).
{ destruct (sy_data (h_oy h)) eqn:ED; [| destruct (NUL eq_refl) as [-> ->]; lia].
destruct (SYBLK ltac:(congruence)) as [(_ & _ & _ & _ & B5) _]. exact B5. }
assert (HL1 : forall b, In b (x_LB0 c) -> In b (lb_remove_opt (sy_data (h_oy h)) (a_LB x))).
{ intros b Hb. destruct (sy_data (h_oy h)) as [p|] eqn:ED; cbn [lb_remove_opt]; [| apply HL0; exact Hb].
eapply in_lb_remove_LB0; [exact ND| exact PERM| | exact Hb]. unfold owned. rewrite ED. rewrite !map_app. rewrite !in_app_iff. cbn. clear. tauto. }
assert (OWNPAY : x_payload c <> [] -> In (x_pb c, x_P c, zlength (x_payload c)) (x_LB0 c) -> forall a, x_P c <= a < x_P c + zlength (x_payload c) ->
rclient_addr (lb_remove_opt (sy_data (h_oy h)) (a_LB x)) (hsp c) a /\ outside [(hsp c - 32, hsp c); (aOY c, aOY c + 32); (a_D x, a_D x + sy_storage (h_oy h))] a).
{ intros NE IN a Ha. apply (OWNP (x_pb c, x_P c, zlength (x_payload c))); [apply in_app_iff; right; exact IN| cbn; exact Ha]. }
eapply (pay_keep c _ _ _ CX AG) in PAY; [| exact OWNPAY].
clear SY ERR MI ST AUX. xport AG side1.

pose proof (perm_after_sync_buffer c x h oy1 D' bytes' LB' st1 ND PERM CASES) as PERM1.
set (xx := hax_sync x LB' D' bytes') in PERM1. set (h1 := set_ogg h oy1 (h_os h)) in PERM1.
assert (PE1 : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m1).
{ eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP); [exact HL0| exact PE| exact AG|].
intros a Hc Hout Hx. destruct Hc as [Hc|[Hc|(bb & Hbb & Rbb)]].
- split; [left; lia| cbn; lia].
- split; [right; left; exact Hc| cbn; unfold ralloc_static, RLIBC, RCTX in Hc; lia].
- apply (OWNP bb); [apply in_app_iff; right; exact Hbb| exact Rbb]. }
assert (HG1 : hglob c xx h1 st1 m1).
{ split; [exact HP1|]. split; [exact PERM1|]. split; [exact PAY|]. split; [exact TP|]. split; [exact SEW|].
split; [exists errv2; exact ERR2|]. split; [exact AUX2|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact PE1|].
cbn. congruence. }

unfold low_cells, wz in LOW. unfold implM. iprefix.
assert (PURE1 : hpure c xx h1).
{ unfold hpure. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os h1 set_ogg a_D a_sybytes a_Dc xx hax_sync].
split; [exact SYOK1|]. split; [exact BOK|]. split; [exact OWN|].
split.
{ intros NE. destruct CASES as [(ELB & ED' & E3 & E4) | [(q & E1 & ELB & RB & _) | (E1 & ED' & ELB)]].
- rewrite ED', E4. apply SYBLK. rewrite <- E3. exact NE.
- split; [exact RB|]. destruct LCASE as [[_ ->]|(R0 & F0 & _ & _ & _ & DD)]; [exfalso; apply NE; reflexivity|].
destruct data as [[q' off]|].
+ first [ sf_destruct 4%nat DD as _ _ _ [[E5 E6]|E6] | sf_fb; destruct DD as (_ & _ & _ & [[E5 E6]|E6]) ]; [| pose proof (proj1 (proj1 SYI1)); lia].
rewrite E6. apply (proj2 (SYBLK ltac:(rewrite <- E5; exact NE))).
+ destruct DD as (_ & E5 & E6). rewrite E6. apply (proj2 (SYBLK ltac:(rewrite <- E5; exact NE))).
- exfalso. apply NE. rewrite E1. reflexivity. }
split.
{ first [ sf_destruct 4%nat SY1 as _ _ DAT _ | sf_fb; destruct SY1 as (_ & _ & DAT & _) ]. unfold sync_data in DAT. destruct (sy_data oy1); [first [ sf_destruct 4%nat DAT as _ _ L _ | sf_fb; destruct DAT as (_ & _ & L & _) ]; exact L|].
first [ sf_destruct 4%nat DAT as _ -> _ -> | sf_fb; destruct DAT as (_ & -> & _ & ->) ]. reflexivity. }
split; [exact BBR|]. split; [exact BSZ|]. split; [exact FS|]. split; [exact GFS|]. split; [exact NFR|]. split; [exact CHR|].
split; [exact RTR|]. split; [exact EXR|]. split; [exact SSR|]. split; [exact PCR|]. split; [exact LGR|]. split; [exact SIR|].
split; [exact EOR|]. split; [exact BRR|]. split; [exact L4K|]. split; [exact STR|].
unfold hbudget, hconsumed, hpend in BUD |- *. cbn [h_packet_count h_oy h_os h_bytes_remaining h1 set_ogg].
destruct LCASE as [[_ ->]|(R0 & F0 & _)]; [cbn -[Z.mul]; lia| rewrite R0, F0; lia]. }
assert (CONT3 : forall x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (mm : mem),
mm = m1 -> match data with None => nb = 0 /\ rv = 0 | Some _ => True end ->
evt rsegs (fun ms' => impl rsegs (at_node rsegs) (chunk_tail2 fuel h1 nb data st1) (epost (fun p ms => POSTQ (fst p) (snd p) ms)) ms')
(MS (mkR x1' (Z_to_bv 64 (aLOW c)) (x_gp c) (Z_to_bv 64 RATP) t0' t1' t2' (Z_to_bv 64 nb) (Z_to_bv 64 (h_bytes_remaining h))
(Z_to_bv 64 rv) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (a_S x)) s3w (Z_to_bv 64 (h_extra_headers h))
(Z_to_bv 64 (h_stream_init h)) (Z_to_bv 64 (h_eos h)) (Z_to_bv 64 (h_packet_count h)) s8w (Z_to_bv 64 (h_nframes h))
(Z_to_bv 64 (h_speex_serialno h)) (Z_to_bv 64 (h_channels h)) t3' t4' t5' t6') F (Z_to_bv 64 0x1c208) fc None mm (seg_rom rsegs))).
{ intros until mm. intros -> HD. apply evt_done. apply (COPY h1 nb rv data st1); [| cbn; lia].
unfold CUTC3. sf_eexists 15%nat. first [ unshelve sf_eexists 8%nat; [ exact (F) | exact (fc) | exact (m1) | exact (xx) | exact (jn) | exact (jb) | exact (s3w) | exact (s8w) | ] | sf_fb; exists F, fc, m1, xx, jn, jb, s3w, s8w ]. split; [reflexivity|]. split; [exact FRM|].
split.
{ unfold hrep. split; [exists j16', jsk', lk'; split; [unfold low_cells, wz; cbn [h_granule_frame_size h_last_granule h_rate h1 set_ogg]; exact LOW| exact LKOK']|].
split; [reflexivity|]. split; [reflexivity|]. split; [exists stb; exact STB|].
split; [exact OSP|]. split; [exists opj; exact OPK|]. split; [exists ogj; exact OGJ|].
split; [exact SY1|]. split; [exact BI|]. split; [exists pad; exact FSZ|]. split; [exists outb; split; [exact OUT| exact LOUT]|].
split; [exists hij; exact HI|]. split; [exact SAV|]. split; [exact DEC|]. split; [exact HG1| exact PURE1]. }
cbn [h_bytes_remaining h1 set_ogg]. split; [lia|]. split; [lia|]. split; [lia|].
unfold seg_ok. cbn [h_oy h1 set_ogg a_D xx hax_sync].
destruct LCASE as [[-> ->]|(R0 & F0 & _ & _ & _ & DD)].
- split; [reflexivity| exact HD].
- split; [exact R0|]. destruct data as [[q off]|]; [| exact HD].
first [ sf_destruct 4%nat DD as Hoff' Hd Hroom _ | sf_fb; destruct DD as (Hoff' & Hd & Hroom & _) ]. subst off. split; [reflexivity|]. split; [rewrite Erv; reflexivity|]. split; [exact Hd| exact Hroom]. }
assert (RVD : 0 <= rv < 2^64 /\ match data with None => rv = 0 | Some _ => 0 < rv end).
{ destruct data as [[q off]|]; [| rewrite Erv; cbn; lia]. destruct LCASE as [[E _]|(_ & _ & _ & _ & _ & (Hoff' & Hd & Hroom & _))]; [discriminate E|].
first [ sf_destruct 4%nat SY1 as _ _ DAT _ | sf_fb; destruct SY1 as (_ & _ & DAT & _) ]. unfold sync_data in DAT. rewrite Hd in DAT. destruct DAT as (Dpos & _).
first [ sf_destruct 5%nat PURE1 as _ _ _ SB1 _ | sf_fb; destruct PURE1 as (_ & _ & _ & SB1 & _) ]. cbn [h_oy h1 set_ogg a_D xx hax_sync] in SB1.
destruct (SB1 ltac:(rewrite Hd; discriminate)) as [(_ & _ & _ & B4 & _) _]. unfold alloc_ceiling in B4.
pose proof (proj1 SYI1) as [R1 R2]. rewrite Erv. subst off. lia. }
destruct RVD as [RVB RVD].

clear RVB.
destruct data as [[q off]|].
- apply (CONT3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 eq_refl I).
- destruct (Z.ltb_spec 0 nb) as [POS|NPOS].
+
apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st1 POSTQ msx) end.
eapply implM_bind with (Q1 := fun _ _ _ => False); [| intros ? ? ? []].
replace (0 <? nb) with true by (symmetry; apply Z.ltb_lt; lia).
apply implM_unr.
+ replace (0 <? nb) with false by (symmetry; apply Z.ltb_ge; lia). assert (NB0 : nb = 0) by lia. apply (CONT3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 eq_refl (conj NB0 RVD)).
Qed.

End CHUNK.

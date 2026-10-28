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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac wl_unf := try unfold alloc_ceiling in *.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c4.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c4.
Local Ltac plia_gen stock ::= plia_size stock.
Local Ltac lia ::= plia_gen ltac:(idtac; lean_lia ltac:(wl_unf)).
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
#[using="Type"] Lemma bytes_at_prefix : forall m A (l1 l2 : list byte), bytes_at rsegs m A (l1 ++ l2) -> bytes_at rsegs m A l1.
Proof. intros m A l1 l2 H. apply bytes_at_app in H. exact (proj1 H). Qed.

#[using="DRF RHF RBR RND RBD CX"] Lemma chunk_memcpy : forall fuel h nb rv data st ms,
(forall h' st' ms', CUTC4 h' nb st' ms' -> h_bytes_remaining h' = h_bytes_remaining h ->
implM rsegs (chunk_tail3 fuel h' nb) st' POSTQ ms') ->
CUTC3 h nb rv data st ms ->
implM rsegs (chunk_tail2 fuel h nb data) st POSTQ ms.
Proof.
intros fuel h nb rv data st ms WROTE CC.
first [ sf_destruct 30%nat CC as x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x jn jb s3w s8w -> FRM HR Hnb1 Hnb2 Hnb3 SEG | sf_fb; destruct CC as (x1 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & jn & jb & s3w & s8w & -> & FRM & HR & Hnb1 & Hnb2 & Hnb3 & SEG) ].
first [ sf_destruct 16%nat HR as (j16 & jsk & lk & LOW & LKOK) _ _ (stb & STB) OSP (opj & OPK) (ogj & OGJ) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG PURE | sf_fb; destruct HR as ((j16 & jsk & lk & LOW & LKOK) & _ & _ & (stb & STB) & OSP & (opj & OPK) & (ogj & OGJ) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
assert (HL0 : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
pose proof (pay_range RBR c _ _ _ CX HP HL0) as PRANGE. pose proof (RND _ _ _ HP) as ND.
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ]. unfold hbudget, hconsumed, hpend in BUD.
pose proof SYOK as (SYI2 & SYST & SYNUL). pose proof SYI2 as [SYI _]. pose proof SYI as (I1 & I2 & _).
pose proof (bytes_at_bound _ _ _ _ PAY) as PB. rewrite to_bytes_length in PB.
assert (PLT : x_P c + zlength (x_payload c) < 2^64).
{ destruct PIN as [[NE IN]|[E EP]]; [| rewrite EP, E; unfold zlength, REMPTY; cbn; lia].
pose proof (RBR _ _ _ _ HP (HL0 _ IN)) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4' _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4' & _) ]. cbn in B4'. unfold alloc_ceiling in B4'. lia. }
destruct SEG as [RET0 SEG].
unfold low_cells, wz in LOW. change (id (bytes_at rsegs m (x_P c) (to_bytes (x_payload c)))) in PAY.
unfold chunk_tail2, implM. iprefix. unfold hregs, wz.

zstep. zstep. unfold id in PAY.
destruct data as [[q off]|].
-
first [ sf_destruct 4%nat SEG as -> -> Hd Hroom | sf_fb; destruct SEG as (-> & -> & Hd & Hroom) ].
pose proof SY as sfP_; first [ sf_destruct 4%nat sfP_ as SYO FOK DAT SEP | sf_fb; destruct sfP_ as (SYO & FOK & DAT & SEP) ]. unfold sync_data in DAT. rewrite Hd in DAT. first [ sf_destruct 5%nat DAT as Dpos ARR LEN PRE LE | sf_fb; destruct DAT as (Dpos & ARR & LEN & PRE & LE) ].
destruct (SYBLK ltac:(rewrite Hd; discriminate)) as [(_ & _ & _ & B4 & B5) GE4]. unfold alloc_ceiling in B4.
destruct (u8arr_window _ _ _ (sy_fill (h_oy h)) nb ARR ltac:(lia) ltac:(lia) ltac:(lia)) as (W1 & WIN & W3).
assert (SRC : bytes_at rsegs m (x_P c) (to_bytes (ztake nb (x_payload c)))).
{ unfold ztake. rewrite to_bytes_firstn. eapply bytes_at_prefix. rewrite firstn_skipn. exact PAY. }

pose proof (sync_call_P RBD RBR c x h st m CX HP ND PERM ltac:(intros E; rewrite Hd in E; discriminate E)) as OWNP.
assert (APP : zlength (x_payload c) = 0 \/ a_D x + sy_storage (h_oy h) <= x_P c \/ x_P c + zlength (x_payload c) <= a_D x).
{ destruct PIN as [[NE IN]|[E _]]; [| left; rewrite E; reflexivity]. right.
pose proof (blocks_apart RBD st (a_LB x) m (owned_pre x h) (q, a_D x, sy_storage (h_oy h)) (x_LB0 c) (x_pb c, x_P c, zlength (x_payload c)) HP ND) as BA.
cbn [blk_addr blk_size fst snd] in BA. apply BA; [| apply in_app_iff; right; exact IN].
rewrite owned_split, Hd, <- app_assoc in PERM. exact PERM. }
pose proof (munch_refl [(a_D x + sy_fill (h_oy h), a_D x + sy_fill (h_oy h) + nb)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
change (id (u8arr rsegs m (a_D x) (a_sybytes x))) in ARR. change (id (sync_rep m (aOY c) (a_D x) (h_oy h) (a_sybytes x))) in SY.
change (id (bytes_at rsegs m (x_P c) (to_bytes (x_payload c)))) in PAY. change (id (rw_cells rsegs m RERRNO [C4 errv])) in ERR.
clear W1 W3.
zstep. callx (eapply (memcpy_callv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (a_D x + sy_fill (h_oy h)) (x_P c) nb (to_bytes (ztake nb (x_payload c))));
[exact SRC| rewrite to_bytes_length; unfold ztake; rewrite firstn_length_le by (unfold zlength in *; (clear - BUD BRR Hnb3 Hnb1 nb h c RCEIL; lia)); reflexivity| (clear - Hnb1 nb h; lia)| (clear - B4 Hroom x nb h RCEIL; lia)| unfold zlength in *; (clear - GE4 B4 PLT BRR PRANGE P0 Hnb3 Hnb1 x nb h c RCEIL; lia)| exact WIN| unfold zlength in *; (clear - APP I1 BUD P0 Hroom Hnb1 x nb h c RCEIL; lia)| exact MI]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (mW := mx) in * end.
lazymatch goal with H : rw_cells rsegs mW (a_D x + sy_fill (h_oy h)) [CB (Z.to_nat nb) _] |- _ => rename H into WIN' end.
lazymatch goal with H : bytes_at rsegs mW (x_P c) (to_bytes (ztake nb _)) |- _ => rename H into SRC' end.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG. unfold id in ARR, SY, PAY, ERR.

assert (OWNW : forall b2, In b2 (owned_pre x h ++ x_LB0 c) -> forall a, blk_addr b2 <= a < blk_addr b2 + blk_size b2 ->
outside [(a_D x + sy_fill (h_oy h), a_D x + sy_fill (h_oy h) + nb)] a).
{ intros b2 Hb2 a Ha. destruct (OWNP b2 Hb2 a Ha) as [_ O]. cbn in O |- *. lia. }
eapply (pay_keep c _ _ _ CX AG) in PAY; [| intros NE IN a Ha; cbn; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in ERR; [| side1].
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| side1|].
2:{ intros a Ha. apply (OWNW (sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h))); [| cbn; exact Ha]. unfold owned_pre. rewrite !in_app_iff. cbn. clear. tauto. }
eapply (os_piece_agree2 _ _ _ _ _ _ AG) in OSP; [| side1|].
2:{ intros a (bb & Hbb & Ra). apply (OWNW bb); [| exact Ra]. unfold stream_blks in Hbb. unfold owned_pre. rewrite !in_app_iff in Hbb. rewrite !in_app_iff. clear - Hbb. tauto. }
eapply (dec_piece_agree2 _ _ _ _ _ _ _ DRF AG) in DEC.
2:{ intros a (bb & Hbb & Ra). apply (OWNW bb); [| exact Ra]. unfold owned_pre. rewrite !in_app_iff.
unfold dec_piece in DEC. destruct (h_st h); [left; left; exact Hbb| destruct DEC as [_ E0]; rewrite E0 in Hbb; destruct Hbb]. }
eapply (rtables_pristine_agree _ _ _ AG) in TP; [| side1]. eapply (stderr_wfile_agree _ _ _ AG) in SEW; [| side1].
assert (HP' : RHEAP st (a_LB x) mW).
{ eapply RHF; [exact HP| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil]. right; right.
exists (q, a_D x, sy_storage (h_oy h)). split; [| cbn; lia]. eapply Permutation_in; [apply Permutation_sym; exact PERM|].
unfold owned. rewrite Hd. rewrite !in_app_iff. cbn. clear. tauto. }
assert (AUX' : rauxv_ok mW (x_AB c)).
{ eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; (clear - GE4 B5 B4 LE I1 BUD PCR PRANGE CEIL' LO SPAB P0 Hroom RET0 Hnb1 x nb h c RCEIL; lia)| apply Forall_nil]. }
assert (PE' : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) mW).
{ eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP); [exact HL0| exact PE| exact AG|].
intros a Hc Hout Hx. destruct Hc as [Hc|[Hc|(bb & Hbb & Rbb)]]; [cbn; (clear - Hout Hc a GE4 B4 LE BUD PCR PRANGE CEIL' LO P0 Hroom RET0 Hnb1 x nb h c RCEIL; lia)| cbn; unfold ralloc_static, RLIBC, RCTX in Hc; (clear - Hc a B5 I1 BUD Hroom Hnb3 Hnb1 x nb h c RCEIL; lia)|].
apply (OWNW bb); [apply in_app_iff; right; exact Hbb| exact Rbb]. }

destruct (u8arr_window _ _ _ (sy_fill (h_oy h)) nb ARR ltac:(lia) ltac:(lia) ltac:(lia)) as (W1 & _ & W3).
eapply (u8arr_agree _ _ _ _ _ AG) in W1; [| rewrite firstn_length_le by (clear - GE4 LE LEN Dpos BUD BRR PCR Hroom RET0 Hnb1 x nb h c RCEIL; lia); cbn; intros; (clear - H a I1 BUD Hnb3 Hnb1 x nb h c RCEIL; lia)].
eapply (u8arr_agree _ _ _ _ _ AG) in W3; [| rewrite skipn_length; cbn; intros; lia].
destruct (u8arr_unwindow mW (a_D x) _ nb _ _ (sy_fill (h_oy h)) W1 ltac:(rewrite firstn_length_le by (clear - GE4 LE LEN Dpos BUD BRR PCR Hroom RET0 Hnb1 x nb h c RCEIL; lia); (clear - I1 h; lia)) WIN' ltac:((clear - Hnb1 nb h; lia)) W3) as [ARR' LEN'].
rewrite skipn_length in LEN'.
assert (LSRC : Z.of_nat (length (to_bytes (ztake nb (x_payload c)))) = nb).
{ rewrite to_bytes_length. unfold ztake. rewrite firstn_length_le by (unfold zlength in *; lia). lia. }
pose proof (sync_rep_write m mW (aOY c) (a_D x) (h_oy h) (a_sybytes x) q nb _ SY SYI Hd ltac:(lia) Hroom LSRC SYO ARR') as SY'.
unfold ubytes in SY'. rewrite map_unsigned_to_bytes in SY' by (apply X1r1.Forall_ztake; exact PF).
clear ARR SY W1 W3 WIN' AG MU WM OWNW OWNP HP AUX PE.
set (oyw := sync_write (h_oy h) (sy_fill (h_oy h)) (ztake nb (x_payload c))) in SY'.
set (bytes'' := take (Z.to_nat (sy_fill (h_oy h))) (a_sybytes x) ++ to_bytes (ztake nb (x_payload c)) ++ drop (Z.to_nat (sy_fill (h_oy h) + nb)) (a_sybytes x)) in *.
set (h' := set_ogg h oyw (h_os h)). set (x' := hax_sync x (a_LB x) (a_D x) bytes'').
apply evt_done. lazymatch goal with |- impl _ _ _ _ (MS ?R ?F' ?pc' ?fc' _ ?m' ?rom) =>
change (implM rsegs (chunk_tail3 fuel h' nb) st POSTQ (MS R F' pc' fc' None m' rom)) end.
apply WROTE; [| reflexivity].
pose proof (sync_write_inv2 (h_oy h) (ztake nb (x_payload c)) SYI2 (X1r1.Forall_ztake _ _ _ PF)) as SWI2.
pose proof (sync_write_inv (h_oy h) (ztake nb (x_payload c)) SYI (X1r1.Forall_ztake _ _ _ PF)) as sfP_; first [ sf_destruct 5%nat sfP_ as SWI SWL SWF SWR SWS | sf_fb; destruct sfP_ as (SWI & SWL & SWF & SWR & SWS) ].
fold oyw in SWI2, SWI, SWL, SWF, SWR, SWS. rewrite zlength_ztake in SWL by (unfold zlength in *; lia).
assert (SWD : sy_data oyw = sy_data (h_oy h)) by reflexivity.
assert (PERM' : Permutation (a_LB x') (owned x' h' ++ x_LB0 c)) by exact PERM.
clearbody oyw.
pose proof FOK as (Fs & _). unfold int31 in Fs.
unfold CUTC4. sf_eexists 16%nat. first [ unshelve sf_eexists 8%nat; [ exact (F) | exact (fc) | exact (mW) | exact (x') | exact (jn) | exact (jb) | exact (s3w) | exact (s8w) | ] | sf_fb; exists F, fc, mW, x', jn, jb, s3w, s8w ]. split; [reflexivity|]. split; [exact FRM|].
split.
{ unfold hrep. split; [exists j16, jsk, lk; split; [unfold low_cells, wz; exact LOW| exact LKOK]|]. split; [reflexivity|]. split; [reflexivity|].
split; [exists stb; exact STB|]. split; [exact OSP|]. split; [exists opj; exact OPK|]. split; [exists ogj; exact OGJ|].
split; [exact SY'|]. split; [exact BI|]. split; [exists pad; exact FSZ|]. split; [exists outb; split; [exact OUT| exact LOUT]|].
split; [exists hij; exact HI|]. split; [exact SAV|]. split; [exact DEC|].
split. { split; [exact HP'|]. split; [exact PERM'|]. split; [exact PAY|]. split; [exact TP|]. split; [exact SEW|].
split; [exists errv; exact ERR|]. split; [exact AUX'|]. split; [assumption|]. split; [exact ST|]. split; [exact PE'| exact SO]. }
unfold hpure. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os h' set_ogg a_D a_sybytes a_Dc x' hax_sync].
split. { split; [exact SWI2|]. rewrite SWS, SWD. split; [exact SYST| exact SYNUL]. }
split; [exact BOK|]. split; [exact OWN|]. split; [rewrite SWS, SWD; exact SYBLK|].
split; [rewrite SWS; (clear - LSRC LEN' GE4 LE LEN I1 BRR P0 Hroom Hnb1 x nb h c RCEIL; lia)|].
repeat (split; [assumption|]). unfold hbudget, hconsumed, hpend in BUD |- *. cbn [h_packet_count h_oy h_os h_bytes_remaining h' set_ogg]. rewrite SWF, SWR. exact BUD. }
cbn [h_oy h_bytes_remaining set_ogg h']. rewrite SWL, SWF, SWR. repeat split; (clear - LEN' Hnb1 x nb h c Hnb2 Hnb3 LE BUD PCR PL RET0 RCEIL; lia).
-
cbn in SEG. destruct SEG as [-> ->].
assert (SRC : bytes_at rsegs m (x_P c) (to_bytes (ztake 0 (x_payload c)))) by (cbn; apply bytes_at_nil; lia).
pose proof (rw_cells_CB0 m 0 ltac:(lia)) as DST.
pose proof (munch_refl [(0, 0 + 0)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
change (id (sync_rep m (aOY c) (a_D x) (h_oy h) (a_sybytes x))) in SY.
change (id (bytes_at rsegs m (x_P c) (to_bytes (x_payload c)))) in PAY. change (id (rw_cells rsegs m RERRNO [C4 errv])) in ERR.
zstep. callx (eapply (memcpy_callv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m 0 (x_P c) 0 (to_bytes (ztake 0 (x_payload c))) []);
[exact SRC| reflexivity| lia| lia| unfold zlength in *; lia| exact DST| lia| exact MI]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (mW := mx) in * end.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG. unfold id in SY, PAY, ERR.
eapply (pay_keep c _ _ _ CX AG) in PAY; [| intros NE IN a Ha; cbn; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in ERR; [| side1].
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| side1| intros a Ha; cbn; lia].
eapply (os_piece_agree2 _ _ _ _ _ _ AG) in OSP; [| side1| intros a _; cbn; lia].
eapply (dec_piece_agree2 _ _ _ _ _ _ _ DRF AG) in DEC; [| intros a _; cbn; lia].
eapply (sync_rep_agree _ _ _ _ _ _ _ AG) in SY; [| side1| intros a _; cbn; lia].
eapply (rtables_pristine_agree _ _ _ AG) in TP; [| side1]. eapply (stderr_wfile_agree _ _ _ AG) in SEW; [| side1].
assert (HP' : RHEAP st (a_LB x) mW).
{ assert (MU0 : munch [] m mW) by (eapply (munch_weaken [(0, 0 + 0)] [] m mW); [unfold sub_fp, outside; intros; split; [lia| exact I]| exact MU]).
eapply RHF; [exact HP| exact MU0| exact WM| apply Forall_nil]. }
assert (AUX' : rauxv_ok mW (x_AB c)).
{ eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia| apply Forall_nil]. }
assert (PE' : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) mW).
{ eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP); [exact HL0| exact PE| exact AG|]. intros a _ _ _. cbn. lia. }
clear AG MU WM HP AUX PE.
apply evt_done. lazymatch goal with |- impl _ _ _ _ (MS ?R ?F' ?pc' ?fc' _ ?m' ?rom) =>
change (implM rsegs (chunk_tail3 fuel h 0) st POSTQ (MS R F' pc' fc' None m' rom)) end.
apply WROTE; [| reflexivity].
pose proof SY as (_ & FOK & _). pose proof FOK as (Fs & Ff & _). unfold int31 in Fs, Ff.
unfold CUTC4. sf_eexists 16%nat. first [ unshelve sf_eexists 8%nat; [ exact (F) | exact (fc) | exact (mW) | exact (x) | exact (jn) | exact (jb) | exact (s3w) | exact (s8w) | ] | sf_fb; exists F, fc, mW, x, jn, jb, s3w, s8w ]. split; [reflexivity|]. split; [exact FRM|].
split.
{ unfold hrep. split; [exists j16, jsk, lk; split; [unfold low_cells, wz; exact LOW| exact LKOK]|]. split; [reflexivity|]. split; [reflexivity|].
split; [exists stb; exact STB|]. split; [exact OSP|]. split; [exists opj; exact OPK|]. split; [exists ogj; exact OGJ|].
split; [exact SY|]. split; [exact BI|]. split; [exists pad; exact FSZ|]. split; [exists outb; split; [exact OUT| exact LOUT]|].
split; [exists hij; exact HI|]. split; [exact SAV|]. split; [exact DEC|].
split. { split; [exact HP'|]. split; [exact PERM|]. split; [exact PAY|]. split; [exact TP|]. split; [exact SEW|].
split; [exists errv; exact ERR|]. split; [exact AUX'|]. split; [assumption|]. split; [exact ST|]. split; [exact PE'| exact SO]. }
exact PURE. }
repeat split; lia.
Qed.
End CHUNK.

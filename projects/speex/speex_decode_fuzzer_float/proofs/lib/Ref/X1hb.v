(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1bq X1br X1c0.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0qb X0pt.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1m2 X1m3 X1m5 X1fl X1ea X1fr X1h7 X1kd X1k9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1ik X1ij X1ii X1il X1im X1ip X1in X1ja X1iu X1j8 X1j4 X1j9 X1it.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1g3 X1g1 X1g6 X1g5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1go X1hk X1hl X1h9 X1gy X1hg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require X1ff X1fd.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma u8arr_nil : forall m A, 0 <= A <= 2^64 -> u8arr rsegs m A [].
Proof. intros m A HA. split; (split; [lia|]; split; [cbn; lia|]); cbn; intros; lia. Qed.

Section PAGE1.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).

#[using="DRF RHF RBR RND RBD CX"] Lemma pageout_call : forall (ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (x : hax) (h : hstate bptr) (st : PState) (nbr brem0 : Z),
hrep dec_rep c x h st m (C8 (wz nbr)) (C8 (wz brem0)) ->
evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem)
(r : Z) (oog : option page) (oy' : sync_st bptr) (j0 j1 j2 j3 opj : list byte),
ms' = MS (mkR ra (wz (hsp c)) (x_gp c) tpv t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ ogg_sync_pageout (h_oy h) = Some ((r, oog), oy')
/\ hrepx dec_rep c x (set_ogg h oy' (h_os h)) st m' (C8 (wz nbr)) (C8 (wz brem0))
(og_cells (a_D x) oog [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3]) [CB 48 opj]
/\ hpend (set_ogg h oy' (h_os h)) <= hpend h
/\ match oog with
| Some og => r = 1 /\ page_ok oy' og /\ sy_data oy' <> None /\ page_budget c (set_ogg h oy' (h_os h)) og
/\ hpend (set_ogg h oy' (h_os h)) + 27 <= hpend h
| None => r <> 1
end)
(MS (mkR ra (wz (hsp c)) (x_gp c) tpv t0 t1 t2 s0 s1 (wz (aOY c)) (wz (aOG c)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz A_ogg_sync_pageout) fc None m (seg_rom rsegs)).
Proof.
intros until brem0. intros HR.
first [ sf_destruct 16%nat HR as (j16 & lk & LOW) _ _ (stb & STB) OSP (opj & OPK) (ogj & OGJ) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG PURE | sf_fb; destruct HR as ((j16 & lk & LOW) & _ & _ & (stb & STB) & OSP & (opj & OPK) & (ogj & OGJ) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
unfold hbudget, hconsumed, hpend in BUD.
pose proof SYOK as (SYI2 & SYST & SYNUL). pose proof SYI2 as [SYI _].
pose proof (RND _ _ _ HP) as ND.
assert (HL0 : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
pose proof (pay_range RBR c _ _ _ CX HP HL0) as PRANGE.
assert (NUL : sy_data (h_oy h) = None -> a_D x = 0 /\ sy_storage (h_oy h) = 0).
{ intros ED. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT. rewrite ED in DAT. first [ sf_destruct 4%nat DAT as -> _ _ -> | sf_fb; destruct DAT as (-> & _ & _ & ->) ]. auto. }
assert (SYR : a_D x + sy_storage (h_oy h) <= alloc_ceiling /\ 0 <= a_D x /\ (a_D x + sy_storage (h_oy h) <= 0x10000 \/ 0x67000 <= a_D x)).
{ destruct (sy_data (h_oy h)) eqn:ED.
- destruct (SYBLK ltac:(congruence)) as [(B1 & _ & _ & B4 & B5) _]. lia.
- destruct (NUL eq_refl) as [-> ->]. unfold alloc_ceiling. lia. }
destruct SYR as (SYR & D0 & SYRR).
pose proof SY as sfP_; first [ sf_destruct 4%nat sfP_ as SYC SYF DAT SYSEP | sf_fb; destruct sfP_ as (SYC & SYF & DAT & SYSEP) ].

assert (ARR : u8arr rsegs m (a_D x) (a_sybytes x) /\ buf_pre (sy_buf (h_oy h)) (a_sybytes x)).
{ unfold sync_data in DAT. destruct (sy_data (h_oy h)).
- first [ sf_destruct 5%nat DAT as D1 AR D3 D4 D5 | sf_fb; destruct DAT as (D1 & AR & D3 & D4 & D5) ]. split; [exact AR| split; [exact D4| exact D5]].
- first [ sf_destruct 4%nat DAT as -> -> E3 _ | sf_fb; destruct DAT as (-> & -> & E3 & _) ]. split; [apply u8arr_nil; lia|]. rewrite E3. split; [reflexivity| cbn; lia]. }
destruct ARR as [ARR PRE].

destruct (ogg_sync_pageout (h_oy h)) as [[[r oog] oy']|] eqn:EPO.
2:{ exfalso. exact (ogg_sync_pageout_total _ SYI EPO). }
pose proof (ogg_sync_pageout_frame _ _ _ _ SYI EPO) as sfP_; first [ sf_destruct 7%nat sfP_ as SYI' EF EB ED ES RMONO PGF | sf_fb; destruct sfP_ as (SYI' & EF & EB & ED & ES & RMONO & PGF) ].
pose proof (ogg_sync_pageout_inv2 _ _ _ _ SYI2 EPO) as [SYI2' PGI]. pose proof SYI' as (SYRF & _). pose proof SYI as (SYRF0 & _).

apply (rw_cells_split_CB _ _ _ [] _ _ [] [8; 8; 8; 8]%nat) in OGJ; [| reflexivity]. cbn [mk_CB_cells app] in OGJ.
eapply evt_mono.
{ eapply (ogg_sync_pageout_spec (aOY c) (aOG c) (a_D x) (x_lo c) (a_sybytes x) (h_oy h));
rewrite ?(unsigned_lit (aLOW c)) by (clear - SYSEP SYRR D0 SYR SYST LO CEIL ABB SPAB h x c RCEIL; lia);
first [ exact SYF | exact SYI2 | exact PRE | exact SYLEN | exact ST | exact MI | exact SYC | exact ARR | exact OGJ | exact EPO | reflexivity | (clear - D0 x SYSEP SYRR SYR SYST SYLEN LO CEIL ABB SPAB h c RCEIL CEIL'; lia) ]. }
cbv beta. intros ms' PO.
first [ sf_destruct 24%nat PO as y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 m' -> MU WM MI' ST' SYC' SYF' ARR' OG' | sf_fb; destruct PO as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m' & -> & MU & WM & MI' & ST' & SYC' & SYF' & ARR' & OG') ].
rewrite ?(unsigned_lit (aLOW c)) in MU by lia. rewrite ?(unsigned_lit (aLOW c)) in ST' by lia. rewrite SYLEN in MU.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG.

pose proof (sync_call_P RBD RBR c x h st m CX HP ND PERM NUL) as OWNP.
assert (OWNW : forall bb, In bb (owned_pre x h ++ x_LB0 c) -> forall a, blk_addr bb <= a < blk_addr bb + blk_size bb ->
outside [(aLOW c - 160, aLOW c); (aOY c, aOY c + 32); (aOG c, aOG c + 32); (a_D x, a_D x + sy_storage (h_oy h))] a).
{ intros bb Hbb a Ha. destruct (OWNP bb Hbb a Ha) as [_ OUTa]. cbn [outside fst snd] in OUTa |- *.
assert (I2 : In bb (a_LB x)).
{ eapply Permutation_in; [apply Permutation_sym; exact PERM|]. rewrite owned_split, <- app_assoc. apply in_app_iff in Hbb.
rewrite !in_app_iff. destruct Hbb; [left; assumption| right; right; assumption]. }
pose proof (RBR _ _ _ _ HP I2) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4. lia. }
clear SYC ST MI ARR OGJ.
eapply (os_piece_agree2 _ _ _ _ _ _ AG) in OSP; [| side1|].
2:{ intros a (bb & Hbb & Ra). apply (OWNW bb); [| exact Ra]. unfold stream_blks in Hbb. unfold owned_pre.
rewrite !in_app_iff in Hbb. rewrite !in_app_iff. clear -Hbb. tauto. }
eapply (dec_piece_agree2 _ _ _ _ _ _ _ DRF AG) in DEC.
2:{ intros a (bb & Hbb & Ra). apply (OWNW bb); [| exact Ra]. unfold owned_pre. rewrite !in_app_iff.
unfold dec_piece in DEC. destruct (h_st h); [left; left; exact Hbb| destruct DEC as [_ E0]; rewrite E0 in Hbb; destruct Hbb]. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| side1|].
2:{ intros a Ha. apply (OWNW (sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h))); [| cbn; exact Ha].
unfold owned_pre. rewrite !in_app_iff. cbn. clear. tauto. }
eapply (pay_keep c _ _ _ CX AG) in PAY.
2:{ intros NE IN a Ha. apply (OWNW (x_pb c, x_P c, zlength (x_payload c))); [apply in_app_iff; right; exact IN| cbn; exact Ha]. }
clear SY.   xport AG side1.
assert (HP' : RHEAP st (a_LB x) m').
{ destruct (sy_data (h_oy h)) as [p|] eqn:EDD.
- eapply RHF; [exact HP| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|].
apply Forall_cons; [| apply Forall_nil]. right; right. exists (p, a_D x, sy_storage (h_oy h)). split; [| cbn; lia].
eapply Permutation_in; [apply Permutation_sym; exact PERM|]. unfold owned. rewrite ?EDD. cbn [opt_blk]. rewrite !in_app_iff. cbn. clear. tauto.
- destruct (NUL eq_refl) as [DZ SZ].
eapply (RHF st (a_LB x) m m' [(aLOW c - 160, aLOW c); (aOY c, aOY c + 32); (aOG c, aOG c + 32)]); [exact HP| | exact WM|].
+ eapply munch_weaken; [| exact MU]. intros q Hq. cbn [outside fst snd] in Hq |- *. rewrite DZ, SZ. lia.
+ apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
assert (AUX' : rauxv_ok m' (x_AB c)).
{ eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL.
apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
assert (PE' : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m').
{ eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP); [exact HL0| exact PE| exact AG|].
intros a Hc Hout Hx. cbn beta. destruct Hc as [Hc|[Hc|(bb & Hbb & Rbb)]].
- cbn [outside fst snd]. lia.
- cbn [outside fst snd]. unfold ralloc_static, RLIBC, RCTX in Hc. (clear - Hc a SYRR SYLEN CEIL' LO h x c RCEIL; lia).
- apply (OWNW bb); [apply in_app_iff; right; exact Hbb| exact Rbb]. }
clear HP AUX PE MU WM.

set (h1 := set_ogg h oy' (h_os h)).
assert (EPEND : hpend h1 <= hpend h /\ match oog with Some pg => hpend h1 + pg_header_len pg + pg_body_len pg <= hpend h | None => True end).
{ unfold hpend. cbn [h_oy h1 set_ogg]. rewrite EF. split; [lia|]. destruct oog as [pg|]; [| exact I]. lia. }
sf_eexists 22%nat. exists opj. split; [reflexivity|]. split; [reflexivity|].
split.
{
split; [exists j16, lk; exact LOW|]. split; [reflexivity|]. split; [reflexivity|]. split; [exists stb; exact STB|].
split; [exact OSP|]. split; [split; [exact OPK| reflexivity]|].
split; [split; [exact OG'| destruct oog; reflexivity]|].
split.
{ split; [exact SYC'|]. split; [exact SYF'|]. split; [| exact SYSEP].
unfold sync_data in DAT |- *. cbn [h_oy h1 set_ogg]. rewrite ED, ES, EB. destruct (sy_data (h_oy h)); [| exact DAT].
first [ sf_destruct 5%nat DAT as D1 _ D3 D4 D5 | sf_fb; destruct DAT as (D1 & _ & D3 & D4 & D5) ]. split; [exact D1|]. split; [exact ARR'|]. auto. }
split; [exact BI|]. split; [exists pad; exact FSZ|]. split; [exists outb; split; [exact OUT| exact LOUT]|]. split; [exists hij; exact HI|].
split; [exact SAV|]. split; [exact DEC|].
split.
{ split; [exact HP'|]. split.
{ unfold owned in PERM |- *. cbn [h_st h_bits h_os h_oy h1 set_ogg]. rewrite ED, ES. exact PERM. }
split; [exact PAY|]. split; [exact TP|]. split; [exact SEW|]. split; [exists errv; exact ERR|]. split; [exact AUX'|].
split; [exact MI'|]. split; [exact ST'|]. split; [exact PE'| exact SO]. }
unfold hpure. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os h1 set_ogg].
split. { split; [exact SYI2'|]. rewrite ES, ED. split; [exact SYST| exact SYNUL]. }
split; [exact BOK|]. split; [exact OWN|]. split; [rewrite ED, ES; exact SYBLK|]. split; [rewrite ES; exact SYLEN|].
split; [exact BBR|]. split; [exact BSZ|]. split; [exact FS|]. split; [exact GFS|]. split; [exact NFR|]. split; [exact CHR|].
split; [exact RTR|]. split; [exact EXR|]. split; [exact SSR|]. split; [exact PCR|]. split; [exact LGR|]. split; [exact SIR|].
split; [exact EOR|]. split; [exact BRR|]. split; [exact L4K|]. split; [exact STR|].
unfold hbudget, hconsumed, hpend in EPEND |- *. cbn [h_packet_count h_oy h_os h_bytes_remaining h1 set_ogg] in EPEND |- *. lia. }
split; [exact (proj1 EPEND)|].
destruct oog as [pg|]; [| exact PGI].
destruct PGI as [-> POK]. split; [reflexivity|]. split; [exact POK|].
pose proof POK as sfP_; first [ sf_destruct 7%nat sfP_ as Q0 Q1 Q2 Q3 Q4 Q5 Q6 | sf_fb; destruct sfP_ as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6) ].
split.
{ rewrite ED. intros EDN. unfold sync_data in DAT. rewrite EDN in DAT. first [ sf_destruct 4%nat DAT as _ _ EBUF _ | sf_fb; destruct DAT as (_ & _ & EBUF & _) ].
rewrite EB, EBUF in Q5. unfold zlength in Q5. cbn in Q5. lia. }
split.
{ exists (hconsumed c h). unfold hbudget, hconsumed, hpend in EPEND |- *. cbn [h_packet_count h_oy h_os h_bytes_remaining h1 set_ogg] in EPEND |- *. lia. }
unfold hpend in EPEND |- *. cbn [h_oy h1 set_ogg] in EPEND |- *. lia.
Qed.

#[using="Type"] Lemma pageout_ret : forall (sy sy' : sync_st bptr) r og,
ogg_sync_pageout sy = Some ((r, og), sy') -> r = 1 \/ r = 0 \/ r = -1.
Proof.
intros sy sy' r og E. unfold ogg_sync_pageout in E. destruct (ogg_sync_check sy). { inversion E. lia. }
revert E. generalize (pageout_fuel sy) as fuel. intros fuel. revert sy.
induction fuel as [|fuel IH]; intros sy E; [discriminate|]. cbn [pageout_loop] in E.
destruct (ogg_sync_pageseek sy) as [[r1 og1] sy1].
destruct (0 <? r1); [inversion E; lia|]. destruct (r1 =? 0); [inversion E; lia|].
destruct (sy_unsynced sy1 =? 0); [inversion E; lia|]. eapply IH. exact E.
Qed.

Notation PPOST := (PPOST dec_rep c).
Notation PGB := (PGB dec_rep c).

#[using="DRF RHF RBR RND RBD CX"] Lemma page_head1 : forall fuel' h st ms,
PG1 dec_rep c h st ms ->
(forall h1 og st1 ms1, PGB h1 og st1 ms1 -> h_bytes_remaining h1 = h_bytes_remaining h -> hpend h1 + 27 <= hpend h ->
implM rsegs (page_bodyP fuel' h1 og) st1 (PPOST (h_bytes_remaining h)) ms1) ->
implM rsegs (page_loopP (S fuel') h) st (PPOST (h_bytes_remaining h)) ms.
Proof.
intros fuel' h st ms PG K. rewrite page_loop_S.
first [ sf_destruct 27%nat PG as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x s0v nbr brem0 -> FRM HR LOK | sf_fb; destruct PG as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & s0v & nbr & brem0 & -> & FRM & HR & LOK) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HR as sfP_; first [ sf_destruct 16%nat sfP_ as _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_ & _ & _ & _ & _ & _ & _ & MI & _) PURE | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & MI & _) & PURE) ].
pose proof PURE as sfP_; first [ sf_destruct 18%nat sfP_ as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SIR _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SIR & _) ].
change (id (hrep dec_rep c x h st m (C8 (wz nbr)) (C8 (wz brem0)))) in HR.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold implM. iprefix. unfold hregs, A_PAGE1, wz.

zstep. zstep. zstep.
clear MU WM. unfold id in HR.
eapply evt_cut. { eapply pageout_call. exact HR. }
cbv beta. intros ms1 sfH_; first [ sf_destruct 28%nat sfH_ as y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 m' r oog oy' j0 j1 j2 j3 opj -> EPO HRX PEND CASE | sf_fb; destruct sfH_ as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m' & r & oog & oy' & j0 & j1 & j2 & j3 & opj & -> & EPO & HRX & PEND & CASE) ].
rewrite EPO. replace (ret_pc (Z_to_bv 64 0x1c02c)) with (Z_to_bv 64 0x1c02c) by (symmetry; rpc).
pose proof (pageout_ret _ _ _ _ EPO) as RR.
pose proof HRX as sfP_; first [ sf_destruct 16%nat sfP_ as _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_ & _ & _ & _ & _ & _ & _ & MI' & _) _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & MI' & _) & _) ].
pose proof (munch_refl [] m') as MU. pose proof (wmono_refl rsegs m') as WM.
unfold wz. zstep. if_cases K1; zify_cond K1.
-
assert (NE : r <> 1) by (intros ->; apply K1; reflexivity).
replace (negb (r =? 1)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NE).
clear CASE.
apply evt_done. apply implM_ret. apply evt_done. split; [| reflexivity].
unfold PGX. sf_eexists 16%nat. first [ unshelve sf_eexists 7%nat; [ exact (F) | exact (fc) | exact (m') | exact (x) | exact (s0v) | exact (nbr) | exact (brem0) | ] | sf_fb; exists F, fc, m', x, s0v, nbr, brem0 ]. split; [reflexivity|]. split; [exact FRM|].
split; [| exact LOK]. eapply hrepx_hrep. exact HRX.
-
destruct RR as [->|[->| ->]]; [| cbv in K1; discriminate| cbv in K1; discriminate]. cbn [Z.eqb negb].
destruct oog as [og|]; [| exfalso; exact (CASE eq_refl)].
first [ sf_destruct 5%nat CASE as _ POK NN PB P27 | sf_fb; destruct CASE as (_ & POK & NN & PB & P27) ].
zstep. apply evt_done. apply (K _ og); [| reflexivity| exact P27].
unfold X1hg.PGB. sf_eexists 15%nat. first [ unshelve sf_eexists 9%nat; [ exact (F) | exact (fc) | exact (m') | exact (x) | exact (s0v) | exact ((h_stream_init h)) | exact (nbr) | exact (brem0) | exact ([CB 48 opj]) | ] | sf_fb; exists F, fc, m', x, s0v, (h_stream_init h), nbr, brem0, [CB 48 opj] ].
split.
{ unfold hregs, wz. cbn [h_nframes h_last_granule h_packet_count h_speex_serialno h_channels h_eos h_stream_init set_ogg].
destruct SIR as [E|E]; rewrite E; reflexivity. }
split; [exact FRM|]. split; [exact HRX|]. split; [exact LOK|]. split; [exact POK|]. split; [exact NN| exact PB].
Qed.

#[using="DRF RHF RBR RND RBD CX"] Lemma page_headN : forall fuel' h st ms,
PGN dec_rep c h st ms ->
(forall h1 og st1 ms1, PGB h1 og st1 ms1 -> h_bytes_remaining h1 = h_bytes_remaining h -> hpend h1 + 27 <= hpend h ->
implM rsegs (page_bodyP fuel' h1 og) st1 (PPOST (h_bytes_remaining h)) ms1) ->
implM rsegs (page_loopP (S fuel') h) st (PPOST (h_bytes_remaining h)) ms.
Proof.
intros fuel' h st ms PG K. rewrite page_loop_S.
first [ sf_destruct 29%nat PG as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x s0v s5v nbr brem0 -> FRM SI1 HR LOK | sf_fb; destruct PG as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & s0v & s5v & nbr & brem0 & -> & FRM & SI1 & HR & LOK) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HR as sfP_; first [ sf_destruct 16%nat sfP_ as _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_ & _ & _ & _ & _ & _ & _ & MI & _) PURE | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & MI & _) & PURE) ].
change (id (hrep dec_rep c x h st m (C8 (wz nbr)) (C8 (wz brem0)))) in HR.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold implM. iprefix. unfold hregs, A_PAGEN, wz.

zstep. zstep. zstep.
clear MU WM. unfold id in HR.
eapply evt_cut. { eapply pageout_call. exact HR. }
cbv beta. intros ms1 sfH_; first [ sf_destruct 28%nat sfH_ as y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 m' r oog oy' j0 j1 j2 j3 opj -> EPO HRX PEND CASE | sf_fb; destruct sfH_ as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m' & r & oog & oy' & j0 & j1 & j2 & j3 & opj & -> & EPO & HRX & PEND & CASE) ].
rewrite EPO. replace (ret_pc (Z_to_bv 64 0x1c358)) with (Z_to_bv 64 0x1c358) by (symmetry; rpc).
pose proof (pageout_ret _ _ _ _ EPO) as RR.
pose proof HRX as sfP_; first [ sf_destruct 16%nat sfP_ as _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_ & _ & _ & _ & _ & _ & _ & MI' & _) _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & MI' & _) & _) ].
pose proof (munch_refl [] m') as MU. pose proof (wmono_refl rsegs m') as WM.

unfold wz. zstep. zstep. zstep. if_cases K1; zify_cond K1.
-
destruct RR as [->|[->| ->]]; [| cbv in K1; discriminate| cbv in K1; discriminate]. cbn [Z.eqb negb].
destruct oog as [og|]; [| exfalso; exact (CASE eq_refl)].
first [ sf_destruct 5%nat CASE as _ POK NN PB P27 | sf_fb; destruct CASE as (_ & POK & NN & PB & P27) ].
apply evt_done. apply (K _ og); [| reflexivity| exact P27].
unfold X1hg.PGB. sf_eexists 15%nat. first [ unshelve sf_eexists 9%nat; [ exact (F) | exact (fc) | exact (m') | exact (x) | exact (s0v) | exact (1) | exact (nbr) | exact (brem0) | exact ([CB 48 opj]) | ] | sf_fb; exists F, fc, m', x, s0v, 1, nbr, brem0, [CB 48 opj] ].
split.
{ unfold hregs, wz. cbn [h_nframes h_last_granule h_packet_count h_speex_serialno h_channels h_eos h_stream_init set_ogg].
rewrite SI1. reflexivity. }
split; [exact FRM|]. split; [exact HRX|]. split; [exact LOK|]. split; [exact POK|]. split; [exact NN| exact PB].
-
assert (NE : r <> 1) by (intros ->; apply K1; reflexivity).
replace (negb (r =? 1)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NE).
clear CASE.
apply evt_done. apply implM_ret. apply evt_done. split; [| reflexivity].
unfold PGX. sf_eexists 16%nat. first [ unshelve sf_eexists 7%nat; [ exact (F) | exact (fc) | exact (m') | exact (x) | exact (s0v) | exact (nbr) | exact (brem0) | ] | sf_fb; exists F, fc, m', x, s0v, nbr, brem0 ]. split.
{ unfold hregs, wz. cbn [h_nframes h_last_granule h_packet_count h_speex_serialno h_channels h_eos h_stream_init set_ogg].
rewrite SI1. reflexivity. }
split; [exact FRM|]. split; [| exact LOK]. eapply hrepx_hrep. exact HRX.
Qed.
End PAGE1.

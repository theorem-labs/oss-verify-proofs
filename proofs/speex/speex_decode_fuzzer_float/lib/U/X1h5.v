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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ij X1ii X1il.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g3 X1g1 X1g6 X1g5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gy X1hg X1hf X1hh X1hi X1hj X1gz X1gt X1gu X1h6 X1gx X1h3 X1h1 X1h2 X1h4.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Definition ph_fin (h : hstate bptr) (blk : bptr) (hd : spx_header) (st : dec_state bptr) (ch2 fs rate : Z) : M PState (option (hstate bptr)) :=
if INT_MAX - 1 <? hd_extra_headers hd
then X1qx.mbind (h_decoder_destroyP st) (fun _ => X1qx.mbind (raw_free blk) (fun _ => X1qx.mret None))
else X1qx.mbind (raw_free blk) (fun _ =>
let '(lookahead, st0) := speex_decoder_ctl st CtlGetLookahead in
X1qx.mret (Some (set_header h st0 (hd_frames_per_packet hd) ch2 rate (hd_extra_headers hd) fs))).

Definition hax_dec (x : hax) (S : Z) (LBD : list block) : hax :=
HAX (LBD ++ a_LB x) (a_D x) (a_sybytes x) (a_Bd x) (a_L x) (a_Gv x) (a_nB x) (a_nL x) (a_nG x) (a_hdr x) (a_lws x) (a_gws x) (a_body x) (a_Dc x) S LBD.

Definition hj_frame {RCEIL : RunCeiling} (c : hcx) (x : hax) (h : hstate bptr) (m : mem) (nbr brem0 fs rate : Z) : Prop :=
(exists j16 jsk lk, rw_cells rsegs m (aLOW c) [CB 16 j16; C8 (wz brem0); C8 (wz nbr); CB 16 jsk; C8 (wz (x_P c)); C8 (wz fs); C8 (wz (h_last_granule h)); CB 4 lk; C4 (wz rate)])
/\ (exists stb, rw_cells rsegs m (aSTEREO c) [CB 24 stb])
/\ stream_rep m c x h
/\ (exists opj, rw_cells rsegs m (aOP c) [CB 48 opj]) /\ (exists ogj, rw_cells rsegs m (aOG c) [CB 32 ogj])
/\ sync_rep m (aOY c) (a_D x) (h_oy h) (a_sybytes x)
/\ bits_rep rsegs m (aBITS c) (a_Dc x) (h_bits h)
/\ (exists pad, rw_cells rsegs m (aFSZ c) [CB 4 pad; C4 (wz fs)])
/\ (exists outb, u8arr rsegs m (aOUT c) outb /\ Z.of_nat (length outb) = 8000)
/\ (exists cbk, rw_cells rsegs m (aCBK c) cbk /\ cells_size cbk = 48%nat)
/\ rw_cells rsegs m (aSAV c) (sav_cells c).

Definition HJ {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (h : hstate bptr) (blk : bptr) (hd : spx_header) (d : dec_state bptr) (ch2 fs rate : Z) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (nbr brem0 HB S pno : Z) (LBD : list block) (s0w s3w s8w : word),
ms = MS (mkR x1 (wz (hsp c)) (x_gp c) (wz RATP) t0 t1 t2 s0w (wz pno) a0 a1 a2 a3 a4 a5 a6 a7
(wz S) s3w (wz (h_extra_headers h)) (wz 2147483647) (wz HB) (wz (h_packet_count h)) s8w (wz (hd_frames_per_packet hd))
(wz (h_speex_serialno h)) (wz ch2) t3 t4 t5 t6)
F (wz 0x1c6a0) fc None m (seg_rom rsegs)
/\ frm0 fc /\ hdr_pure c x h nbr brem0 /\ hj_frame c x h m nbr brem0 fs rate
/\ hglobX c x h st m (LBD ++ [(blk, HB, SIZEOF_SPEEX_HEADER_Z)])
/\ hdr_blk m HB hd /\ 0 <= pno <= h_packet_count h
/\ 0 < S < 2^63 /\ dec_rep (aSTEREO c) m S d LBD /\ (forall b, In b LBD -> rblock_range (blk_addr b) (blk_size b))
/\ 0 <= fs <= 640 /\ -2^31 <= rate < 2^31 /\ 1 <= hd_frames_per_packet hd <= 10 /\ (ch2 = 1 \/ ch2 = 2).

Section HDR6.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis DCTL : rspx_decoder_ctl_stmt dec_rep.
Hypothesis DDESTROY : rspx_decoder_destroy_stmt dec_rep.
Hypothesis RFREE : rfree_stmt.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).
Notation DESTROY_FREE_NONE st blk := (X1qx.mbind (h_decoder_destroyP st) (fun _ => X1qx.mbind (raw_free blk) (fun _ => X1qx.mret (@None (hstate bptr))))).
Notation PK := (PK dec_rep c).

#[using="DRF DCTL RHF RBR RND RBD CX"] Lemma hdr_chan : forall fuel' h blk hd d3 fs rate pn st ms (br0 : Z) (oy0 : sync_st bptr),
HC dec_rep c h blk hd d3 fs rate st ms ->
(forall dJ ch2 st' ms', HJ dec_rep c h blk hd dJ ch2 fs rate st' ms' ->
implM rsegs (X1qx.mbind (ph_fin h blk hd dJ ch2 fs rate) (hdr_tailK fuel' h pn)) st' (PKPOST dec_rep c br0 oy0) ms') ->
implM rsegs (X1qx.mbind (ph_after_rate h blk hd d3 fs rate) (hdr_tailK fuel' h pn)) st (PKPOST dec_rep c br0 oy0) ms.
Proof.
intros fuel' h blk hd d3 fs rate pn st ms br0 oy0 HCC KJ.
first [ sf_destruct 41%nat HCC as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 HB S pno LBD s0w s3w s8w -> FRM PU FR HG HBK PNO SB DR BRD FSOK RTR' FPOK | sf_fb; destruct HCC as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & HB & S & pno & LBD & s0w & s3w & s8w & -> & FRM & PU & FR & HG & HBK & PNO & SB & DR & BRD & FSOK & RTR' & FPOK) ].
pose proof PU as sfP_; first [ sf_destruct 9%nat sfP_ as SI1 EOS0 PC0 EST AS0 ALBD PURE LOK BUD' | sf_fb; destruct sfP_ as (SI1 & EOS0 & PC0 & EST & AS0 & ALBD & PURE & LOK & BUD') ].
pose proof FR as sfP_; first [ sf_destruct 11%nat sfP_ as (j16 & jsk & lk & LOW) (stb & STB) OSP (opj & OP) (ogj & OG) SY BI (pad & FSZ) (outb & OUT & LOUT) (cbj & CBK) SAV | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW) & (stb & STB) & OSP & (opj & OP) & (ogj & OG) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (cbj & CBK) & SAV) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof HBK as sfP_; first [ sf_destruct 9%nat sfP_ as (junk28 & w1 & w2 & w3 & r1 & r2 & HCELLS) HBR V1 V2 V3 V4 V5 V6 V7 | sf_fb; destruct sfP_ as ((junk28 & w1 & w2 & w3 & r1 & r2 & HCELLS) & HBR & V1 & V2 & V3 & V4 & V5 & V6 & V7) ].
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HBR as sfP_; first [ sf_destruct 5%nat sfP_ as HB1 _ _ HB4 HB5 | sf_fb; destruct sfP_ as (HB1 & _ & _ & HB4 & HB5) ]. unfold alloc_ceiling, SIZEOF_SPEEX_HEADER_Z in HB4, HB5. unfold SPEEX_NB_MODES in V3.
assert (EOSB : 0 <= h_eos h <= 1) by lia.
pose proof (RND _ _ _ HP) as ND.
set (LBX := (LBD ++ [(blk, HB, SIZEOF_SPEEX_HEADER_Z)]) ++ a_LB x) in *.
assert (HLo : forall b, In b (owned x h) -> In b LBX).
{ intros b Hb. subst LBX. apply in_app_iff. right. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. exact Hb. }
assert (HLD : forall b, In b LBD -> In b LBX) by (intros b Hb; subst LBX; apply in_app_iff; left; apply in_app_iff; left; exact Hb).
assert (HHB : In (blk, HB, SIZEOF_SPEEX_HEADER_Z) LBX) by (subst LBX; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
assert (APART : forall bb a, (In bb (owned x h) \/ bb = (blk, HB, SIZEOF_SPEEX_HEADER_Z)) -> blk_addr bb <= a < blk_addr bb + blk_size bb ->
outside (map (fun b : block => (blk_addr b, blk_addr b + blk_size b)) LBD) a).
{ intros bb a Hbb Ra. apply outside_blocks. intros b Hb.
assert (NE : blk_id b <> blk_id bb).
{ pose proof ND as ND'. subst LBX. rewrite <- app_assoc, map_app in ND'. intros E.
eapply (nodup_app_disj _ _ (blk_id b) ND'); [apply in_map; exact Hb|]. rewrite E, map_app. apply in_app_iff.
destruct Hbb as [Hbb| ->]; [right; apply in_map; eapply Permutation_in; [apply Permutation_sym; exact PERM|]; apply in_app_iff; left; exact Hbb| left; left; reflexivity]. }
assert (Hbb' : In bb LBX) by (destruct Hbb as [Hbb| ->]; [apply HLo; exact Hbb| exact HHB]).
pose proof (RBD _ _ _ _ _ HP (HLD _ Hb) Hbb' NE). lia. }
assert (OWF : forall P sz a, (aLOW c <= a < P \/ P + sz <= a < usp c) -> aLOW c <= P -> 0 <= sz ->
outside ((x_lo c, aLOW c) :: (P, P + sz) :: map (fun b : block => (blk_addr b, blk_addr b + blk_size b)) LBD) a).
{ intros P sz a Ha HPl Hsz. cbn [outside]. split; [lia|]. split; [lia|]. apply outside_blocks. intros b Hb.
pose proof (BRD b Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4. lia. }
assert (OWB : forall P sz bb a, (In bb (owned x h) \/ bb = (blk, HB, SIZEOF_SPEEX_HEADER_Z)) -> blk_addr bb <= a < blk_addr bb + blk_size bb -> aLOW c <= P -> 0 <= sz ->
outside ((x_lo c, aLOW c) :: (P, P + sz) :: map (fun b : block => (blk_addr b, blk_addr b + blk_size b)) LBD) a).
{ intros P sz bb a Hbb Ra HPl Hsz. assert (Hbb' : In bb LBX) by (destruct Hbb as [Hbb| ->]; [apply HLo; exact Hbb| exact HHB]).
pose proof (RBR _ _ _ _ HP Hbb') as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4.
cbn [outside]. split; [lia|]. split; [lia|]. apply (APART bb a Hbb Ra). }

unfold ph_after_rate. cbv zeta.
set (ch' := if h_channels h =? -1 then hd_nb_channels hd else h_channels h).
assert (CH'R : -2^31 <= ch' < 2^31) by (subst ch'; destruct (h_channels h =? -1); lia).

assert (JJ : forall dJ ch2 mJ (FJ : bvmap 5 word) fcJ cbk (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
frm0 fcJ -> (ch2 = 1 \/ ch2 = 2) ->
rw_cells rsegs mJ (aLOW c) [CB 16 j16; C8 (wz brem0); C8 (wz nbr); CB 16 jsk; C8 (wz (x_P c)); C8 (wz fs); C8 (wz (h_last_granule h)); CB 4 lk; C4 (wz rate)] ->
rw_cells rsegs mJ (aSTEREO c) [CB 24 stb] -> stream_rep mJ c x h -> rw_cells rsegs mJ (aOP c) [CB 48 opj] -> rw_cells rsegs mJ (aOG c) [CB 32 ogj] ->
sync_rep mJ (aOY c) (a_D x) (h_oy h) (a_sybytes x) -> bits_rep rsegs mJ (aBITS c) (a_Dc x) (h_bits h) ->
rw_cells rsegs mJ (aFSZ c) [CB 4 pad; C4 (wz fs)] -> u8arr rsegs mJ (aOUT c) outb -> rw_cells rsegs mJ (aCBK c) cbk -> cells_size cbk = 48%nat ->
rw_cells rsegs mJ (aSAV c) (sav_cells c) ->
rw_cells rsegs mJ HB (spx_header_cells junk28 hd w1 w2 w3 r1 r2) ->
hglobX c x h st mJ (LBD ++ [(blk, HB, SIZEOF_SPEEX_HEADER_Z)]) -> dec_rep (aSTEREO c) mJ S dJ LBD ->
evt rsegs (fun ms1 => impl rsegs (at_node rsegs) ((X1qx.mbind (ph_fin h blk hd dJ ch2 fs rate) (hdr_tailK fuel' h pn)) st)
(epost (fun p ms2 => PKPOST dec_rep c br0 oy0 (fst p) (snd p) ms2)) ms1)
(MS (mkR y1 (Z_to_bv 64 (aLOW c)) (x_gp c) (Z_to_bv 64 RATP) y5 y6 y7 s0w (Z_to_bv 64 pno) y10 y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 S) s3w (Z_to_bv 64 (h_extra_headers h)) (Z_to_bv 64 2147483647) (Z_to_bv 64 HB) (Z_to_bv 64 (h_packet_count h))
s8w (Z_to_bv 64 (hd_frames_per_packet hd)) (Z_to_bv 64 (h_speex_serialno h)) (Z_to_bv 64 ch2) y28 y29 y30 y31)
FJ (Z_to_bv 64 0x1c6a0) fcJ None mJ (seg_rom rsegs))).
{ intros. apply evt_done. apply KJ.
unfold HJ. sf_eexists 16%nat. first [ unshelve sf_eexists 13%nat; [ exact (FJ) | exact (fcJ) | exact (mJ) | exact (x) | exact (nbr) | exact (brem0) | exact (HB) | exact (S) | exact (pno) | exact (LBD) | exact (s0w) | exact (s3w) | exact (s8w) | ] | sf_fb; exists FJ, fcJ, mJ, x, nbr, brem0, HB, S, pno, LBD, s0w, s3w, s8w ].
split; [reflexivity|]. split; [assumption|]. split; [exact PU|].
split. { split; [exists j16, jsk, lk; assumption|]. split; [exists stb; assumption|]. split; [assumption|].
split; [exists opj; assumption|]. split; [exists ogj; assumption|]. split; [assumption|]. split; [assumption|].
split; [exists pad; assumption|]. split; [exists outb; split; [assumption| exact LOUT]|]. split; [exists cbk; split; assumption| assumption]. }
split; [assumption|]. split. { split; [first [ unshelve sf_eexists 6%nat; [ exact (junk28) | exact (w1) | exact (w2) | exact (w3) | exact (r1) | exact (r2) | ] | sf_fb; exists junk28, w1, w2, w3, r1, r2 ]; assumption|]. split; [exact HBR|]. unfold SPEEX_NB_MODES. repeat (split; [lia|]). lia. }
split; [exact PNO|].
split; [exact SB|]. split; [assumption|]. split; [exact BRD|]. split; [exact FSOK|]. split; [exact RTR'|]. split; [exact FPOK| assumption]. }

assert (J1 : forall (y10 : word),
evt rsegs (fun ms1 => impl rsegs (at_node rsegs)
((X1qx.mbind (let '(channels, st0) := (if negb (ch' =? 1) then let '(_, st0) := speex_decoder_ctl d3 CtlSetHandlerStereo in (2, st0) else (ch', d3)) in
ph_fin h blk hd st0 channels fs rate) (hdr_tailK fuel' h pn)) st)
(epost (fun p ms2 => PKPOST dec_rep c br0 oy0 (fst p) (snd p) ms2)) ms1)
(MS (mkR x1 (Z_to_bv 64 (aLOW c)) (x_gp c) (Z_to_bv 64 RATP) t0 t1 t2 s0w (Z_to_bv 64 pno) y10 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 S) s3w (Z_to_bv 64 (h_extra_headers h)) (Z_to_bv 64 2147483647) (Z_to_bv 64 HB) (Z_to_bv 64 (h_packet_count h))
s8w (Z_to_bv 64 (hd_frames_per_packet hd)) (Z_to_bv 64 (h_speex_serialno h)) (Z_to_bv 64 ch') t3 t4 t5 t6)
F (Z_to_bv 64 0x1c650) fc None m (seg_rom rsegs))).
{ intros y10.

zstep. zstep. zstep. if_cases B1; rewrite zbv_eqb_signed in B1 by lia.
-
first [apply (proj1 (Z.eqb_eq _ _)) in B1| apply Bool.negb_false_iff in B1; apply (proj1 (Z.eqb_eq _ _)) in B1].
rewrite B1. cbn [Z.eqb Pos.eqb negb].
eapply (JJ d3 1 m F fc [CB 48 cbj]); first [exact FRM| left; reflexivity| assumption| reflexivity].
-
assert (NE1 : ch' <> 1) by (first [apply (proj1 (Z.eqb_neq _ _)) in B1| apply Bool.negb_true_iff in B1; apply (proj1 (Z.eqb_neq _ _)) in B1]; exact B1).
replace (ch' =? 1) with false by (symmetry; apply Z.eqb_neq; exact NE1). cbn [negb].
destruct (speex_decoder_ctl d3 CtlSetHandlerStereo) as [v4 d4] eqn:E4. cbn iota.
pose proof (got_stereo_handler_cell m TP) as GOTC. unfold GOT_stereo_handler in GOTC. change X1ff.rsegs with X1gj.rsegs in GOTC.
pose proof (munch_refl [(aCBK c, aCBK c + 24)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold spx_header_cells in HCELLS. unfold wz in LOW, FSZ.

do 7 zstep. zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (m3 := mx) in * end.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
destruct (hglobX_munch RHF RBR RND RBD c x h st m m3 _ _ CX HG MU WM) as [HG3 _]; [assumption| assumption| apply Forall_cons; [left; cbn; lia| apply Forall_nil]|].
eapply (stream_rep_agree2 _ _ _ _ _ _ AG) in OSP; [| side1c| intros a (bb & Hbb & Ra); pose proof (RBR _ _ _ _ HP (HLo _ (in_owned_stream _ _ _ Hbb))) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]; unfold alloc_ceiling in B4; cbn [outside fst snd]; lia].
eapply (sync_rep_agree _ _ _ _ _ _ _ AG) in SY; [| side1c|].
2:{ intros a Ha. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT.
destruct (sy_data (h_oy h)) as [q|] eqn:ESD; [| first [ sf_destruct 4%nat DAT as _ _ _ ST0 | sf_fb; destruct DAT as (_ & _ & _ & ST0) ]; rewrite SYLEN, ST0 in Ha; lia].
pose proof (RBR _ _ _ _ HP (HLo _ (in_owned_sync _ _ _ ESD))) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. cbn in B4. unfold alloc_ceiling in B4. cbn [outside fst snd]. lia. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| side1c| intros a Ha; pose proof BBR as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]; unfold alloc_ceiling in B4; cbn [outside fst snd]; lia].
assert (DR3 : dec_rep (aSTEREO c) m3 S d3 LBD).
{ eapply DRF; [exact DR|]. intros a Ha (bb & Hbb & Ra). apply AG; [exact Ha|].
pose proof (BRD bb Hbb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4. cbn [outside fst snd]. lia. }
clear MU WM AG HG DR HP ST MI TP. rename HG3 into HG. rename DR3 into DR.
pose proof HG as sfP_; first [ sf_destruct 10%nat sfP_ as HP _ _ TP _ _ _ MI ST _ | sf_fb; destruct sfP_ as (HP & _ & _ & TP & _ & _ & _ & MI & ST & _) ]. clearbody m3.

lazymatch type of CBK with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5] =>
pose proof (proj1 (rw_cells_app rsegs m3 (aCBK c) [c1; c2; c3; c4] [c5]) CBK) as [CBA CBR] end.
cbn [cells_size csize Nat.add] in CBR. clear CBK.

do 6 zstep.
eapply evt_cut.
{ eapply DCTL with (STEREO := aSTEREO c) (S := S) (d := d3) (LBD := LBD) (code := SPEEX_SET_HANDLER) (P := aCBK c) (arg := ArgCallback) (req := CtlSetHandlerStereo) (lo := x_lo c);
rewrite ?(unsigned_lit (aLOW c)) by (clear - CEIL' SPB LO c RCEIL; lia);
first [ ctl_ptr_tac CX | exact DR | reflexivity | exact TP | exact BRD | exact ST | exact MI | exact FRM
| exact I
| eexists; unfold wz; exact CBA
| right; (clear - c; lia)
| intros b Hb; pose proof (BRD b Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]; unfold alloc_ceiling in B4; cbn [ctl_arg_size]; (clear - B4 b CEIL' LO c RCEIL; lia)
| unfold DEC_CTL_STACK, alloc_ceiling in *; (clear - CEIL' c RCEIL LO; lia) ]. }
cbv beta. intros ms4 PO.
first [ sf_destruct 29%nat PO as u0 u1 u2 g0 g1 g2 g3 g4 g5 g6 g7 u3 u4 u5 u6 F4 fc4 m4 req4 -> CRQ MU WM MI4 FRM4 ST4 EA0 DR4 AP4 | sf_fb; destruct PO as (u0 & u1 & u2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & u3 & u4 & u5 & u6 & F4 & fc4 & m4 & req4 & -> & CRQ & MU & WM & MI4 & FRM4 & ST4 & EA0 & DR4 & AP4) ].
cbn in CRQ. injection CRQ as <-. rewrite E4 in DR4. cbn [snd] in DR4. clear EA0.
cbn [ctl_arg_size] in MU. rewrite ?(unsigned_lit (aLOW c)) in MU by lia. rewrite ?(unsigned_lit (aLOW c)) in ST4 by lia.
replace (ret_pc (Z_to_bv 64 0x1c69c)) with (Z_to_bv 64 0x1c69c) by (symmetry; rpc).
destruct (hglobX_munch RHF RBR RND RBD c x h st m3 m4 _ _ CX HG MU WM MI4 ST4) as [HG4 AG].
{ apply (ctl_frame_ok c CX); [lia| intros b Hb; apply in_app_iff; left; exact Hb]. }
destruct AP4 as (pad4 & CBA4).
eapply (rw_cells_agree _ _ _ _ _ _ AG) in LOW; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in STB; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OP; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OG; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in FSZ; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (u8arr_agree _ _ _ _ _ AG) in OUT; [| intros a Ha; apply OWF; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in CBR; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in SAV; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in HCELLS; [| intros a Ha; eapply (OWB _ _ (blk, HB, SIZEOF_SPEEX_HEADER_Z)); [right; reflexivity| cbn in Ha |- *; unfold SIZEOF_SPEEX_HEADER_Z; lia| lia| lia]].
eapply (stream_rep_agree2 _ _ _ _ _ _ AG) in OSP; [| intros a Ha; apply OWF; lia| intros a (bb & Hbb & Ra); apply (OWB _ _ bb a); [left; apply in_owned_stream; exact Hbb| exact Ra| lia| lia]].
eapply (sync_rep_agree _ _ _ _ _ _ _ AG) in SY; [| intros a Ha; apply OWF; lia|].
2:{ intros a Ha. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT.
destruct (sy_data (h_oy h)) as [q|] eqn:ESD; [| first [ sf_destruct 4%nat DAT as _ _ _ ST0 | sf_fb; destruct DAT as (_ & _ & _ & ST0) ]; rewrite SYLEN, ST0 in Ha; lia].
apply (OWB _ _ (q, a_D x, sy_storage (h_oy h)) a); [left; apply in_owned_sync; exact ESD| cbn; rewrite <- SYLEN; lia| lia| lia]. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| intros a Ha; apply OWF; lia| intros a Ha; apply (OWB _ _ _ a (or_introl (in_owned_bits x h))); [cbn; lia| lia| lia]].
assert (CBK4 : rw_cells rsegs m4 (aCBK c) ([C4 (wz SPEEX_INBAND_STEREO); CB 4 pad4; C8 (wz A_speex_std_stereo_request_handler); C8 (wz (aSTEREO c))] ++ [CB 24 (drop 8 (drop 12 (drop 4 cbj)))])).
{ apply (proj2 (rw_cells_app rsegs m4 (aCBK c) _ _)). split; [exact CBA4|]. cbn [cells_size csize Nat.add]. exact CBR. }
cbn [app] in CBK4.

zstep.
eapply (JJ d4 2 m4 F4 fc4); first [exact FRM4| right; reflexivity| exact HG4| exact DR4| assumption| reflexivity| exact CBK4]. }

unfold wz in LOW. unfold spx_header_cells in HCELLS.
unfold implM. iprefix. unfold wz.
zstep. zstep. if_cases B0; rewrite zbv_eqb_signed in B0 by lia.
+
assert (EC : ch' = h_channels h).
{ subst ch'. replace (h_channels h =? -1) with false; [reflexivity|]. symmetry. first [exact B0| apply Bool.negb_true_iff; exact B0]. }
rewrite <- EC. apply J1.
+
assert (EC : ch' = hd_nb_channels hd).
{ subst ch'. replace (h_channels h =? -1) with true; [reflexivity|]. symmetry. first [exact B0| apply Bool.negb_false_iff in B0; exact B0]. }
zstep. rewrite sx32_signed_small by lia. rewrite <- EC. apply J1.
Qed.

#[using="DRF DCTL DDESTROY RFREE RHF RBR RND RBD CX"] Lemma hdr_fin : forall fuel' h blk hd dJ ch2 fs rate pn st ms (br0 : Z) (oy0 : sync_st bptr),
HJ dec_rep c h blk hd dJ ch2 fs rate st ms -> h_oy h = oy0 -> h_bytes_remaining h = br0 ->
(forall h' pn' st' ms', PK h' st' ms' -> h_oy h' = oy0 -> h_bytes_remaining h' = br0 ->
os_lacing_fill (h_os h') - os_lacing_returned (h_os h') <= os_lacing_fill (h_os h) - os_lacing_returned (h_os h) ->
implM rsegs (packet_loopP fuel' h' pn') st' (PKPOST dec_rep c br0 oy0) ms') ->
implM rsegs (X1qx.mbind (ph_fin h blk hd dJ ch2 fs rate) (hdr_tailK fuel' h pn)) st (PKPOST dec_rep c br0 oy0) ms.
Proof.
intros fuel' h blk hd dJ ch2 fs rate pn st ms br0 oy0 HJC EOY EBR K.
first [ sf_destruct 43%nat HJC as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 HB S pno LBD s0w s3w s8w -> FRM PU FR HG HBK PNO SB DR BRD FSOK RTR' FPOK CH2 | sf_fb; destruct HJC as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & HB & S & pno & LBD & s0w & s3w & s8w & -> & FRM & PU & FR & HG & HBK & PNO & SB & DR & BRD & FSOK & RTR' & FPOK & CH2) ].
pose proof PU as sfP_; first [ sf_destruct 9%nat sfP_ as SI1 EOS0 PC0 EST AS0 ALBD PURE LOK BUD' | sf_fb; destruct sfP_ as (SI1 & EOS0 & PC0 & EST & AS0 & ALBD & PURE & LOK & BUD') ].
pose proof FR as sfP_; first [ sf_destruct 11%nat sfP_ as (j16 & jsk & lk & LOW) (stb & STB) OSP (opj & OP) (ogj & OG) SY BI (pad & FSZ) (outb & OUT & LOUT) (cbk & CBK & CBS) SAV | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW) & (stb & STB) & OSP & (opj & OP) & (ogj & OG) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (cbk & CBK & CBS) & SAV) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof HBK as sfP_; first [ sf_destruct 9%nat sfP_ as (junk28 & w1 & w2 & w3 & r1 & r2 & HCELLS) HBR V1 V2 V3 V4 V5 V6 V7 | sf_fb; destruct sfP_ as ((junk28 & w1 & w2 & w3 & r1 & r2 & HCELLS) & HBR & V1 & V2 & V3 & V4 & V5 & V6 & V7) ].
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HBR as sfP_; first [ sf_destruct 5%nat sfP_ as HB1 _ _ HB4 HB5 | sf_fb; destruct sfP_ as (HB1 & _ & _ & HB4 & HB5) ]. unfold alloc_ceiling, SIZEOF_SPEEX_HEADER_Z in HB4, HB5. unfold SPEEX_NB_MODES in V3.
assert (EOSB : 0 <= h_eos h <= 1) by lia. assert (CH2R : -2^31 <= ch2 < 2^31) by lia.
pose proof (RND _ _ _ HP) as ND.
set (LBX := (LBD ++ [(blk, HB, SIZEOF_SPEEX_HEADER_Z)]) ++ a_LB x) in *.
assert (HLo : forall b, In b (owned x h) -> In b LBX).
{ intros b Hb. subst LBX. apply in_app_iff. right. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. exact Hb. }
assert (HLD : forall b, In b LBD -> In b LBX) by (intros b Hb; subst LBX; apply in_app_iff; left; apply in_app_iff; left; exact Hb).
assert (HHB : In (blk, HB, SIZEOF_SPEEX_HEADER_Z) LBX) by (subst LBX; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
assert (HL0 : forall b, In b (x_LB0 c) -> In b LBX).
{ intros b Hb. subst LBX. apply in_app_iff. right. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
assert (APART : forall bb a, (In bb (owned x h) \/ bb = (blk, HB, SIZEOF_SPEEX_HEADER_Z)) -> blk_addr bb <= a < blk_addr bb + blk_size bb ->
outside (map (fun b : block => (blk_addr b, blk_addr b + blk_size b)) LBD) a).
{ intros bb a Hbb Ra. apply outside_blocks. intros b Hb.
assert (NE : blk_id b <> blk_id bb).
{ pose proof ND as ND'. subst LBX. rewrite <- app_assoc, map_app in ND'. intros E.
eapply (nodup_app_disj _ _ (blk_id b) ND'); [apply in_map; exact Hb|]. rewrite E, map_app. apply in_app_iff.
destruct Hbb as [Hbb| ->]; [right; apply in_map; eapply Permutation_in; [apply Permutation_sym; exact PERM|]; apply in_app_iff; left; exact Hbb| left; left; reflexivity]. }
assert (Hbb' : In bb LBX) by (destruct Hbb as [Hbb| ->]; [apply HLo; exact Hbb| exact HHB]).
pose proof (RBD _ _ _ _ _ HP (HLD _ Hb) Hbb' NE). lia. }
assert (OWF : forall P sz a, (aLOW c <= a < P \/ P + sz <= a < usp c) -> aLOW c <= P -> 0 <= sz ->
outside ((x_lo c, aLOW c) :: (P, P + sz) :: map (fun b : block => (blk_addr b, blk_addr b + blk_size b)) LBD) a).
{ intros P sz a Ha HPl Hsz. cbn [outside]. split; [lia|]. split; [lia|]. apply outside_blocks. intros b Hb.
pose proof (BRD b Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4. lia. }
assert (OWB : forall P sz bb a, (In bb (owned x h) \/ bb = (blk, HB, SIZEOF_SPEEX_HEADER_Z)) -> blk_addr bb <= a < blk_addr bb + blk_size bb -> aLOW c <= P -> 0 <= sz ->
outside ((x_lo c, aLOW c) :: (P, P + sz) :: map (fun b : block => (blk_addr b, blk_addr b + blk_size b)) LBD) a).
{ intros P sz bb a Hbb Ra HPl Hsz. assert (Hbb' : In bb LBX) by (destruct Hbb as [Hbb| ->]; [apply HLo; exact Hbb| exact HHB]).
pose proof (RBR _ _ _ _ HP Hbb') as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4.
cbn [outside]. split; [lia|]. split; [lia|]. apply (APART bb a Hbb Ra). }
unfold ph_fin. destruct (speex_decoder_ctl dJ CtlGetLookahead) as [la d5] eqn:E5.
unfold spx_header_cells in HCELLS. unfold wz in LOW, FSZ.
unfold implM. iprefix. unfold wz.

zstep. rewrite sx32_signed_small by lia.
rename m into m1. rename errv into errv1.

zstep. if_cases BE; rewrite zbv_eqb_signed in BE by lia.
-
assert (EE : hd_extra_headers hd = 2147483647) by (first [apply (proj1 (Z.eqb_eq _ _)) in BE| apply Bool.negb_false_iff in BE; apply (proj1 (Z.eqb_eq _ _)) in BE]; exact BE).
replace (INT_MAX - 1 <? hd_extra_headers hd) with true by (symmetry; apply Z.ltb_lt; unfold INT_MAX; lia).
apply evt_done. apply (hdr_f28c dec_rep DDESTROY RFREE RBR RND c CX).
unfold F28c. sf_eexists 26%nat. first [ unshelve sf_eexists 9%nat; [ exact (F) | exact (fc) | exact (m1) | exact (x) | exact (nbr) | exact (brem0) | exact (HB) | exact (S) | exact (LBD) | ] | sf_fb; exists F, fc, m1, x, nbr, brem0, HB, S, LBD ].
split; [reflexivity|]. split; [exact FRM|]. split; [exact PU|].
split; [eapply (junkframe_of c x h m1); [exact LOW| reflexivity| exact STB| exact OSP| exact OP| exact OG| exact SY| exact BI| exact FSZ| reflexivity| exact OUT| exact LOUT| exact CBK| exact CBS| exact SAV]|].
split; [exact HG|]. split; [lia|]. split; [exact DR| exact BRD].
- assert (NE : hd_extra_headers hd <> 2147483647) by (first [apply (proj1 (Z.eqb_neq _ _)) in BE| apply Bool.negb_true_iff in BE; apply (proj1 (Z.eqb_neq _ _)) in BE]; exact BE).
replace (INT_MAX - 1 <? hd_extra_headers hd) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).

zstep. zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st (PKPOST dec_rep c br0 oy0) msx) end.
apply implM_bind_assoc. eapply implM_bind.
{ eapply RFREE with (LB := LBX) (lo := x_lo c) (B := x_AB c);
rewrite ?(unsigned_lit (aLOW c)) by (clear - CEIL' SPB LO c RCEIL; lia);
first [ exact HP | exact HHB | exact AUX | exact ST | exact MI | reflexivity | (clear - SPAB c CEIL RCEIL; lia)
| unfold RATP; rewrite unsigned_lit by lia; exact ERR
| unfold RFREE_STACK; (clear - LO c; lia) ]. }
cbv beta. intros [] st2 ms2 PO.
first [ sf_destruct 25%nat PO as y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 m2 -> MI2 ST2 ERR2 AUX2 HPR EFA ESO HP2 | sf_fb; destruct PO as (y0 & y1 & y2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & EFA & ESO & HP2) ].
assert (NIB : forall b, In b (LBD ++ a_LB x) -> blk_id b <> blk).
{ pose proof ND as NDx. subst LBX. rewrite !map_app in NDx. cbn [map blk_id fst] in NDx.
intros b Hb E. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
- pose proof (NoDup_app_remove_r _ _ NDx) as N1. eapply (nodup_app_disj _ _ blk N1); [rewrite <- E; apply in_map; exact Hb| left; reflexivity].
- rewrite <- app_assoc in NDx. apply NoDup_app_remove_l in NDx. cbn [app] in NDx. apply (proj1 (List.NoDup_cons_iff _ _)) in NDx. destruct NDx as [NI _].
apply NI. rewrite <- E. apply in_map. exact Hb. }
assert (ELB : lb_remove blk LBX = LBD ++ a_LB x).
{ subst LBX. rewrite !lb_remove_app, lb_remove_self. rewrite !lb_remove_other; [rewrite app_nil_r; reflexivity| |];
intros b Hb; apply NIB; apply in_app_iff; first [left; exact Hb| right; exact Hb]. }
rewrite ELB in HPR, HP2.
rewrite ?(unsigned_lit (aLOW c)) in ST2 by lia. rewrite ?(unsigned_lit (aLOW c)) in HPR by lia.
unfold RATP in ERR2. rewrite ?unsigned_lit in ERR2 by lia. change (0x4d450 + -164) with RERRNO in ERR2.
replace (ret_pc (Z_to_bv 64 0x1c6b4)) with (Z_to_bv 64 0x1c6b4) by (symmetry; rpc).
pose proof (agree_of_rheap_pres _ _ _ _ HPR) as AG.
assert (PFR : forall a, aLOW c <= a -> rclient_addr (LBD ++ a_LB x) (aLOW c) a) by (intros a Ha; left; lia).
assert (PBL : forall bb a, (In bb (owned x h) \/ In bb LBD) -> blk_addr bb <= a < blk_addr bb + blk_size bb -> rclient_addr (LBD ++ a_LB x) (aLOW c) a).
{ intros bb a Hbb Ra. right; right. exists bb. split; [| exact Ra]. apply in_app_iff.
destruct Hbb as [Hbb|Hbb]; [right; eapply Permutation_in; [apply Permutation_sym; exact PERM|]; apply in_app_iff; left; exact Hbb| left; exact Hbb]. }
eapply (rw_cells_agree _ _ _ _ _ _ AG) in LOW; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in STB; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OP; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OG; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in FSZ; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (u8arr_agree _ _ _ _ _ AG) in OUT; [| intros a Ha; apply PFR; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in CBK; [| intros a Ha; apply PFR; rewrite CBS in Ha; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in SAV; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (stream_rep_agree2 _ _ _ _ _ _ AG) in OSP; [| intros a Ha; apply PFR; lia| intros a (bb & Hbb & Ra); apply (PBL bb a); [left; apply in_owned_stream; exact Hbb| exact Ra]].
eapply (sync_rep_agree _ _ _ _ _ _ _ AG) in SY; [| intros a Ha; apply PFR; lia|].
2:{ intros a Ha. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT.
destruct (sy_data (h_oy h)) as [q|] eqn:ESD; [| first [ sf_destruct 4%nat DAT as _ _ _ ST0 | sf_fb; destruct DAT as (_ & _ & _ & ST0) ]; rewrite SYLEN, ST0 in Ha; lia].
apply (PBL (q, a_D x, sy_storage (h_oy h)) a); [left; apply in_owned_sync; exact ESD| cbn; rewrite <- SYLEN; lia]. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| intros a Ha; apply PFR; lia| intros a Ha; apply (PBL _ a (or_introl (in_owned_bits x h))); cbn; lia].
assert (DR2 : dec_rep (aSTEREO c) m2 S dJ LBD).
{ eapply DRF; [exact DR|]. intros a Ha (bb & Hbb & Ra). apply AG; [exact Ha|]. apply (PBL bb a); [right; exact Hbb| exact Ra]. }
assert (HG2 : hglobX c x h st2 m2 LBD).
{ eapply (hglobX_agree2 RBR c x h st st2 m1 m2 _ _ _ errv1 CX HG AG HP2 MI2 ST2); [| exact ERR2| exact AUX2| exact ESO|].
- eapply stderr_wfile_agree; [exact AG| | exact SEW]. intros a Ha. right; left. unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
- intros a [Ha|[(Ha & Hs & Hx)|(bb & Hbb & Rbb)]]; [apply PFR; lia| right; left; split; [exact Ha| exact Hs]| right; right; exists bb; split; [apply in_app_iff; right; eapply Permutation_in; [apply Permutation_sym; exact PERM|]; apply in_app_iff; right; exact Hbb| exact Rbb]]. }
clear AG HPR HG HP ST MI TP SEW ERR AUX PE PAY DR HCELLS. rename HG2 into HG. rename DR2 into DR. rename MI2 into MI. rename ST2 into ST.
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP _ PAY TP SEW _ AUX _ _ PE SO2 | sf_fb; destruct sfP_ as (HP & _ & PAY & TP & SEW & _ & AUX & _ & _ & PE & SO2) ].
pose proof (RND _ _ _ HP) as ND2.

pose proof (proj1 (rw_cells_app rsegs m2 (aLOW c) [CB 16 j16; C8 (Z_to_bv 64 brem0); C8 (Z_to_bv 64 nbr); CB 16 jsk; C8 (Z_to_bv 64 (x_P c)); C8 (Z_to_bv 64 fs); C8 (Z_to_bv 64 (h_last_granule h))] [CB 4 lk; C4 (Z_to_bv 64 rate)]) LOW) as [LOWA LOWB].
cbn [cells_size csize Nat.add] in LOWB. replace (aLOW c + Z.of_nat 72) with (usp c + -8760) in LOWB by lia.
pose proof (proj1 (rw_cells_app rsegs m2 (usp c + -8760) [CB 4 lk] [C4 (Z_to_bv 64 rate)]) LOWB) as [LKC RTC].
cbn [cells_size csize Nat.add] in RTC. replace (usp c + -8760 + Z.of_nat 4) with (usp c + -8756) in RTC by lia. clear LOW LOWB.

unfold implM. iprefix. do 4 zstep.
eapply evt_cut.
{ eapply DCTL with (STEREO := aSTEREO c) (S := S) (d := dJ) (LBD := LBD) (code := SPEEX_GET_LOOKAHEAD) (P := usp c + -8760) (arg := ArgIntOut) (req := CtlGetLookahead) (lo := x_lo c);
rewrite ?(unsigned_lit (aLOW c)) by (clear - CEIL' SPB LO c RCEIL; lia);
first [ ctl_ptr_tac CX | exact DR | reflexivity | exact TP | exact BRD | exact ST | exact MI | exact FRM
| exact I
| eexists; exact LKC
| right; (clear - c; lia)
| intros b Hb; pose proof (BRD b Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]; unfold alloc_ceiling in B4; cbn [ctl_arg_size]; (clear - B4 b CEIL' LO c RCEIL; lia)
| unfold DEC_CTL_STACK, alloc_ceiling in *; (clear - CEIL' c RCEIL LO; lia) ]. }
cbv beta. intros ms5 PO.
first [ sf_destruct 29%nat PO as u0 u1 u2 g0 g1 g2 g3 g4 g5 g6 g7 u3 u4 u5 u6 F5 fc5 m5 req5 -> CRQ MU WM MI5 FRM5 ST5 EA0 DR5 AP5 | sf_fb; destruct PO as (u0 & u1 & u2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & u3 & u4 & u5 & u6 & F5 & fc5 & m5 & req5 & -> & CRQ & MU & WM & MI5 & FRM5 & ST5 & EA0 & DR5 & AP5) ].
cbn in CRQ. injection CRQ as <-. rewrite E5 in DR5, AP5. cbn [fst snd] in DR5, AP5. clear EA0.
cbn [ctl_arg_size] in MU. rewrite ?(unsigned_lit (aLOW c)) in MU by lia. rewrite ?(unsigned_lit (aLOW c)) in ST5 by lia.
replace (ret_pc (Z_to_bv 64 0x1c6c4)) with (Z_to_bv 64 0x1c6c4) by (symmetry; rpc).
destruct (hglobX_munch RHF RBR RND RBD c x h st2 m2 m5 _ _ CX HG MU WM MI5 ST5) as [HG5 AG].
{ apply (ctl_frame_ok c CX); [lia| intros b Hb; exact Hb]. }
destruct AP5 as [LKC5 LAR].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in LOWA; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in RTC; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in STB; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OP; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OG; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in FSZ; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (u8arr_agree _ _ _ _ _ AG) in OUT; [| intros a Ha; apply OWF; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in CBK; [| intros a Ha; apply OWF; rewrite CBS in Ha; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in SAV; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (stream_rep_agree2 _ _ _ _ _ _ AG) in OSP; [| intros a Ha; apply OWF; lia| intros a (bb & Hbb & Ra); apply (OWB _ _ bb a); [left; apply in_owned_stream; exact Hbb| exact Ra| lia| lia]].
eapply (sync_rep_agree _ _ _ _ _ _ _ AG) in SY; [| intros a Ha; apply OWF; lia|].
2:{ intros a Ha. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT.
destruct (sy_data (h_oy h)) as [q|] eqn:ESD; [| first [ sf_destruct 4%nat DAT as _ _ _ ST0 | sf_fb; destruct DAT as (_ & _ & _ & ST0) ]; rewrite SYLEN, ST0 in Ha; lia].
apply (OWB _ _ (q, a_D x, sy_storage (h_oy h)) a); [left; apply in_owned_sync; exact ESD| cbn; rewrite <- SYLEN; lia| lia| lia]. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| intros a Ha; apply OWF; lia| intros a Ha; apply (OWB _ _ _ a (or_introl (in_owned_bits x h))); [cbn; lia| lia| lia]].
apply (rw_cells_C4_CB4 m5 _ [] _ []) in LKC5. cbn [app] in LKC5.
assert (LOW : rw_cells rsegs m5 (aLOW c) [CB 16 j16; C8 (Z_to_bv 64 brem0); C8 (Z_to_bv 64 nbr); CB 16 jsk; C8 (Z_to_bv 64 (x_P c)); C8 (Z_to_bv 64 fs); C8 (Z_to_bv 64 (h_last_granule h)); CB 4 (le4 (Z_to_bv 64 la)); C4 (Z_to_bv 64 rate)]).
{ apply (proj2 (rw_cells_app rsegs m5 (aLOW c) [CB 16 j16; C8 (Z_to_bv 64 brem0); C8 (Z_to_bv 64 nbr); CB 16 jsk; C8 (Z_to_bv 64 (x_P c)); C8 (Z_to_bv 64 fs); C8 (Z_to_bv 64 (h_last_granule h))] [CB 4 (le4 (Z_to_bv 64 la)); C4 (Z_to_bv 64 rate)])).
split; [exact LOWA|]. lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (usp c + -8760) by (cbn; lia) end.
apply (proj2 (rw_cells_app rsegs m5 (usp c + -8760) [CB 4 (le4 (Z_to_bv 64 la))] [C4 (Z_to_bv 64 rate)])). split; [exact LKC5|].
lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (usp c + -8756) by (cbn; lia) end. exact RTC. }
clear MU WM AG HG DR HP ST MI TP LKC LKC5 LOWA RTC. rename HG5 into HG. rename DR5 into DR. rename MI5 into MI. rename ST5 into ST.
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP _ PAY5 TP SEW5 ERR5 AUX5 _ _ PE5 SO5 | sf_fb; destruct sfP_ as (HP & _ & PAY5 & TP & SEW5 & ERR5 & AUX5 & _ & _ & PE5 & SO5) ].

zstep. zstep. first [rewrite swrap32_small by lia| rewrite swrap32_u64_plus1 by lia].
zstep. replace (bv_lts (Z_to_bv 64 (h_packet_count h + 1)) (Z_to_bv 64 (h_packet_count h))) with false by (rewrite PC0; vm_compute; reflexivity). cbv iota.
zstep. zstep. zstep. if_true_z.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st2 (PKPOST dec_rep c br0 oy0) msx) end.
cbn iota. apply implM_retb. unfold hdr_tailK. cbn iota. apply implM_retb. cbn iota.
set (h3 := set_header h d5 (hd_frames_per_packet hd) ch2 rate (hd_extra_headers hd) fs).
set (x'' := hax_dec x S LBD).
pose proof OSP as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ (I1 & I2 & _) _ | sf_fb; destruct sfP_ as (_ & _ & _ & (I1 & I2 & _) & _) ].
apply (K (incr_packet_count h3) pn st2); [| subst h3; exact EOY| subst h3; exact EBR| subst h3; cbn [h_os incr_packet_count set_header]; lia].
unfold X1hg.PK. sf_eexists 16%nat. first [ unshelve sf_eexists 11%nat; [ exact (F5) | exact (fc5) | exact (m5) | exact (x'') | exact (nbr) | exact (brem0) | exact (pno) | exact (s0w) | exact (Z_to_bv 64 (h_speex_serialno h)) | exact (Z_to_bv 64 2147483647) | exact (s8w) | ] | sf_fb; exists F5, fc5, m5, x'', nbr, brem0, pno, s0w, (Z_to_bv 64 (h_speex_serialno h)), (Z_to_bv 64 2147483647), s8w ].
split. { unfold hregs, wz. subst h3 x''. cbn [h_nframes h_last_granule h_packet_count h_speex_serialno h_channels h_eos h_stream_init h_extra_headers incr_packet_count set_header hax_dec a_S].
rewrite ?PC0, ?EOS0. replace (hd_frames_per_packet hd =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Z.add Pos.add]. reflexivity. }
split; [exact FRM5|]. split; [exact SI1|]. split; [exact EOS0|].
split.
{
split. { exists j16, jsk, (le4 (Z_to_bv 64 la)). split.
- subst h3 x''. unfold low_cells, wz. cbn [h_extra_headers h_granule_frame_size h_last_granule h_rate incr_packet_count set_header]. exact LOW.
- unfold lk_ok. intros _. exists la. split; [reflexivity|]. pose proof (lookahead_range dJ) as LRR. rewrite E5 in LRR. cbn [fst] in LRR. apply LRR. exact LAR. }
split; [reflexivity|]. split; [reflexivity|]. split; [exists stb; exact STB|].
split. { unfold os_piece. subst h3 x''. cbn [h_stream_init incr_packet_count set_header]. rewrite SI1. cbn [Z.eqb]. exact OSP. }
split; [exists opj; exact OP|]. split; [exists ogj; exact OG|]. split; [exact SY|]. split; [exact BI|].
split; [exists pad; subst h3; unfold fsz_cells, wz; cbn [h_frame_size incr_packet_count set_header]; exact FSZ|].
split; [exists outb; split; [exact OUT| exact LOUT]|].
split; [apply rw_cells_forget in CBK; rewrite CBS in CBK; destruct CBK as [hij CBK]; exists hij; exact CBK|].
split; [exact SAV|].
split. { unfold dec_piece. subst h3 x''. cbn [h_st incr_packet_count set_header a_S a_LBD hax_dec]. split; [exact DR|]. split; [exact SB| exact BRD]. }
split. { pose proof HG as (HP' & PERM' & REST). split; [exact HP'|]. split; [| exact REST].
subst h3 x''. unfold owned. cbn [h_st h_bits h_os h_oy incr_packet_count set_header a_LB a_LBD a_Dc a_Bd a_nB a_L a_nL a_Gv a_nG a_D hax_dec].
unfold owned in PERM'. rewrite EST in PERM'. cbn [app] in PERM'. rewrite <- app_assoc. apply Permutation_app_head. cbn [app]. exact PERM'. }
unfold hpure. subst h3 x''. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os incr_packet_count set_header a_D a_sybytes a_Dc hax_dec].
replace (hd_frames_per_packet hd =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
split; [exact SYOK|]. split; [exact BOK|]. split; [exact OWN|]. split; [exact SYBLK|]. split; [exact SYLEN|]. split; [exact BBR|]. split; [exact BSZ|].
split; [exact FSOK|]. split; [reflexivity|]. split; [exact FPOK|]. split; [lia|]. split; [exact RTR'|]. split; [lia|]. split; [exact SSR|].
split; [rewrite PC0; lia|]. split; [exact LGR|]. split; [exact SIR|]. split; [exact EOR|]. split; [exact BRR|]. split; [exact L4K|]. split; [rewrite PC0; lia|].
unfold hbudget, hconsumed, hpend in BUD, BUD' |- *. cbn [h_packet_count h_oy h_os h_bytes_remaining incr_packet_count set_header]. rewrite PC0 in *. lia. }
split. { unfold low_ok in LOK |- *. subst h3. cbn [h_bytes_remaining incr_packet_count set_header]. exact LOK. }
subst h3. cbn [h_packet_count incr_packet_count set_header]. rewrite ?PC0. split; [lia| intros HZ; exfalso; lia].
Qed.
End HDR6.

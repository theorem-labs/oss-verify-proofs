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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gy X1hg X1hf X1hh X1hi X1hj X1gz X1gt X1gu X1h6 X1gx X1h3 X1h1 X1h2.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma fpp_test : forall f, -2^31 <= f < 2^31 ->
((bv_swrap 32 (f + -11)) mod 2^64 <? 18446744073709551606) = ((f <? 1) || (10 <? f)).
Proof.
intros f Hf. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
destruct (Z.lt_ge_cases f (-2^31 + 11)) as [LO|HI].
- rewrite <- (Z.mod_unique_pos (f + -11 + 2^31) (2^32) (-1) (f + -11 + 2^31 + 2^32)) by lia.
rewrite Z.mod_small by lia.
replace (f <? 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [orb]. apply Z.ltb_lt. lia.
- rewrite (Z.mod_small (f + -11 + 2^31)) by lia.
replace (f + -11 + 2 ^ 31 - 2 ^ 31) with (f - 11) by lia.
rewrite mod64_of_int by lia.
destruct (Z.ltb_spec (f - 11) 0); destruct (Z.ltb_spec f 1); destruct (Z.ltb_spec 10 f); cbn [orb];
first [apply Z.ltb_lt; lia| apply Z.ltb_ge; lia].
Qed.

Section HDR5.
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

#[using="DCTL DDESTROY RFREE RHF RBR RND RBD CX"] Lemma hdr_ctls2 : forall fuel' h blk hd d2 fs rate pn st ms (br0 : Z) (oy0 : sync_st bptr),
HR dec_rep c h blk hd d2 fs rate st ms ->
(forall d3 st' ms', HC dec_rep c h blk hd d3 fs rate st' ms' ->
implM rsegs (X1qx.mbind (ph_after_rate h blk hd d3 fs rate) (hdr_tailK fuel' h pn)) st' (PKPOST dec_rep c br0 oy0) ms') ->
implM rsegs (X1qx.mbind (ph_from_rate h blk hd d2 fs rate) (hdr_tailK fuel' h pn)) st (PKPOST dec_rep c br0 oy0) ms.
Proof.
intros fuel' h blk hd d2 fs rate pn st ms br0 oy0 HRC KC.
first [ sf_destruct 41%nat HRC as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 HB S pno LBD s0w s3w s8w -> FRM PU FR HG HBK PNO SB DR BRD FSOK RTR' _ | sf_fb; destruct HRC as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & HB & S & pno & LBD & s0w & s3w & s8w & -> & FRM & PU & FR & HG & HBK & PNO & SB & DR & BRD & FSOK & RTR' & _) ].
pose proof PU as sfP_; first [ sf_destruct 9%nat sfP_ as SI1 EOS0 PC0 EST AS0 ALBD PURE LOK BUD' | sf_fb; destruct sfP_ as (SI1 & EOS0 & PC0 & EST & AS0 & ALBD & PURE & LOK & BUD') ].
pose proof FR as sfP_; first [ sf_destruct 11%nat sfP_ as (j16 & jsk & lk & LOW) (stb & STB) OSP (opj & OP) (ogj & OG) SY BI (pad & FSZ) (outb & OUT & LOUT) (cbj & CBK) SAV | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW) & (stb & STB) & OSP & (opj & OP) & (ogj & OG) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (cbj & CBK) & SAV) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof HBK as sfP_; first [ sf_destruct 9%nat sfP_ as (junk28 & w1 & w2 & w3 & r1 & r2 & HCELLS) HBR V1 V2 V3 V4 V5 V6 V7 | sf_fb; destruct sfP_ as ((junk28 & w1 & w2 & w3 & r1 & r2 & HCELLS) & HBR & V1 & V2 & V3 & V4 & V5 & V6 & V7) ].
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HBR as sfP_; first [ sf_destruct 5%nat sfP_ as HB1 _ _ HB4 HB5 | sf_fb; destruct sfP_ as (HB1 & _ & _ & HB4 & HB5) ]. unfold alloc_ceiling, SIZEOF_SPEEX_HEADER_Z in HB4, HB5. unfold SPEEX_NB_MODES in V3.
assert (EOSB : 0 <= h_eos h <= 1) by lia.
unfold ph_from_rate. destruct (speex_decoder_ctl d2 (CtlSetSamplingRate rate)) as [v3 d3] eqn:E3.
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
assert (FAILX : forall dX mX stX (FX : bvmap 5 word) fcX (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
frm0 fcX -> hdr_junkframe c x h mX -> hglobX c x h stX mX (LBD ++ [(blk, HB, SIZEOF_SPEEX_HEADER_Z)]) -> dec_rep (aSTEREO c) mX S dX LBD ->
evt rsegs (fun ms1 => impl rsegs (at_node rsegs) ((X1qx.mbind (DESTROY_FREE_NONE dX blk) (hdr_tailK fuel' h pn)) stX)
(epost (fun p ms2 => PKPOST dec_rep c br0 oy0 (fst p) (snd p) ms2)) ms1)
(MS (mkR y1 (Z_to_bv 64 (aLOW c)) (x_gp c) (Z_to_bv 64 RATP) y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 S) y19 y20 y21 (Z_to_bv 64 HB)
y23 y24 y25 y26 y27 y28 y29 y30 y31) FX (Z_to_bv 64 0x1c74c) fcX None mX (seg_rom rsegs))).
{ intros. apply evt_done. apply (hdr_f28c dec_rep DDESTROY RFREE RBR RND c CX).
unfold F28c. sf_eexists 26%nat. first [ unshelve sf_eexists 9%nat; [ exact (FX) | exact (fcX) | exact (mX) | exact (x) | exact (nbr) | exact (brem0) | exact (HB) | exact (S) | exact (LBD) | ] | sf_fb; exists FX, fcX, mX, x, nbr, brem0, HB, S, LBD ].
split; [reflexivity|]. split; [assumption|]. split; [exact PU|]. split; [assumption|]. split; [assumption|].
split; [lia|]. split; [assumption| exact BRD]. }

pose proof (proj1 (rw_cells_app rsegs m (aLOW c) [CB 16 j16; C8 (wz brem0); C8 (wz nbr); CB 16 jsk; C8 (wz (x_P c)); C8 (wz fs); C8 (wz (h_last_granule h)); CB 4 lk] [C4 (wz rate)]) LOW) as [LOW1 RTC].
cbn [cells_size csize Nat.add] in RTC. replace (aLOW c + Z.of_nat 76) with (usp c + -8756) in RTC by lia. clear LOW.
unfold spx_header_cells in HCELLS. unfold wz in RTC, LOW1.
unfold implM. iprefix. unfold wz.

do 4 zstep.
eapply evt_cut.
{ eapply DCTL with (STEREO := aSTEREO c) (S := S) (d := d2) (LBD := LBD) (code := SPEEX_SET_SAMPLING_RATE) (P := usp c + -8756) (arg := ArgIntIn rate) (req := CtlSetSamplingRate rate) (lo := x_lo c);
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ ctl_ptr_tac CX | exact DR | reflexivity | exact TP | exact BRD | exact ST | exact MI | exact FRM
| exact I
| exists (Z_to_bv 64 rate); split; [exact RTC| split; [rewrite Z_to_bv_unsigned; apply mod64_mod32| lia]]
| right; lia
| intros b Hb; pose proof (BRD b Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]; unfold alloc_ceiling in B4; cbn [ctl_arg_size]; lia
| unfold DEC_CTL_STACK, alloc_ceiling in *; lia ]. }
cbv beta. intros ms1 PO.
first [ sf_destruct 29%nat PO as y0 y1 y2 e0 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 F1 fc1 m1 req1 -> CRQ MU WM MI1 FRM1 ST1 EA0 DR1 AP1 | sf_fb; destruct PO as (y0 & y1 & y2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & F1 & fc1 & m1 & req1 & -> & CRQ & MU & WM & MI1 & FRM1 & ST1 & EA0 & DR1 & AP1) ].
cbn in CRQ. injection CRQ as <-. rewrite E3 in DR1. cbn [snd] in DR1. clear EA0.
cbn [ctl_arg_size] in MU. rewrite ?(unsigned_lit (aLOW c)) in MU by lia. rewrite ?(unsigned_lit (aLOW c)) in ST1 by lia.
replace (ret_pc (Z_to_bv 64 0x1c634)) with (Z_to_bv 64 0x1c634) by (symmetry; rpc).
destruct (hglobX_munch RHF RBR RND RBD c x h st m m1 _ _ CX HG MU WM MI1 ST1) as [HG1 AG].
{ apply (ctl_frame_ok c CX); [lia| intros b Hb; apply in_app_iff; left; exact Hb]. }
destruct AP1 as (wr & RTC1 & RMOD).
eapply (rw_cells_agree _ _ _ _ _ _ AG) in LOW1; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in STB; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OP; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OG; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in FSZ; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (u8arr_agree _ _ _ _ _ AG) in OUT; [| intros a Ha; apply OWF; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in CBK; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in SAV; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in HCELLS; [| intros a Ha; eapply (OWB _ _ (blk, HB, SIZEOF_SPEEX_HEADER_Z)); [right; reflexivity| cbn in Ha |- *; unfold SIZEOF_SPEEX_HEADER_Z; lia| lia| lia]].
eapply (stream_rep_agree2 _ _ _ _ _ _ AG) in OSP; [| intros a Ha; apply OWF; lia| intros a (bb & Hbb & Ra); apply (OWB _ _ bb a); [left; apply in_owned_stream; exact Hbb| exact Ra| lia| lia]].
eapply (sync_rep_agree _ _ _ _ _ _ _ AG) in SY; [| intros a Ha; apply OWF; lia|].
2:{ intros a Ha. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT.
destruct (sy_data (h_oy h)) as [q|] eqn:ESD; [| first [ sf_destruct 4%nat DAT as _ _ _ ST0 | sf_fb; destruct DAT as (_ & _ & _ & ST0) ]; rewrite SYLEN, ST0 in Ha; lia].
apply (OWB _ _ (q, a_D x, sy_storage (h_oy h)) a); [left; apply in_owned_sync; exact ESD| cbn; rewrite <- SYLEN; lia| lia| lia]. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| intros a Ha; apply OWF; lia| intros a Ha; apply (OWB _ _ _ a (or_introl (in_owned_bits x h))); [cbn; lia| lia| lia]].

apply (rw_cells_C4_eqm m1 _ [] wr rate []) in RTC1; [| exact RMOD]. cbn [app] in RTC1.
assert (LOW : rw_cells rsegs m1 (aLOW c) [CB 16 j16; C8 (Z_to_bv 64 brem0); C8 (Z_to_bv 64 nbr); CB 16 jsk; C8 (Z_to_bv 64 (x_P c)); C8 (Z_to_bv 64 fs); C8 (Z_to_bv 64 (h_last_granule h)); CB 4 lk; C4 (Z_to_bv 64 rate)]).
{ apply (proj2 (rw_cells_app rsegs m1 (aLOW c) [CB 16 j16; C8 (Z_to_bv 64 brem0); C8 (Z_to_bv 64 nbr); CB 16 jsk; C8 (Z_to_bv 64 (x_P c)); C8 (Z_to_bv 64 fs); C8 (Z_to_bv 64 (h_last_granule h)); CB 4 lk] [C4 (Z_to_bv 64 rate)])).
split; [exact LOW1|]. lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (usp c + -8756) by (cbn; lia) end. exact RTC1. }
clear MU WM AG HG ST MI HP RTC RTC1 LOW1.
pose proof HG1 as sfP_; first [ sf_destruct 10%nat sfP_ as HP _ _ TP1 _ _ _ _ ST _ | sf_fb; destruct sfP_ as (HP & _ & _ & TP1 & _ & _ & _ & _ & ST & _) ]. clear TP. rename TP1 into TP. rename HG1 into HG. rename MI1 into MI.
clear FRM. rename FRM1 into FRM. clear DR. rename DR1 into DR.
assert (JF1 : hdr_junkframe c x h m1).
{ eapply (junkframe_of c x h m1); [exact LOW| reflexivity| exact STB| exact OSP| exact OP| exact OG| exact SY| exact BI| exact FSZ| reflexivity| exact OUT| exact LOUT| exact CBK| reflexivity| exact SAV]. }

zstep. rewrite sx32_signed_small by lia. zstep. zstep.
rewrite land_ones64, X1nj.swrap32_mod64_plus.
zstep. if_cases BP; unfold bv_ltu in BP; rewrite !Z_to_bv_unsigned in BP; change (bv_wrap 64 (-10)) with 18446744073709551606 in BP;
change (bv_wrap 64 (bv_swrap 32 (hd_frames_per_packet hd + -11))) with ((bv_swrap 32 (hd_frames_per_packet hd + -11)) mod 2^64) in BP;
rewrite fpp_test in BP by lia; rewrite BP.
-
apply (FAILX d3 m1 st F1 fc1); [exact FRM| exact JF1| exact HG| exact DR].
-
assert (FPOK : 1 <= hd_frames_per_packet hd <= 10).
{ destruct (Z.ltb_spec (hd_frames_per_packet hd) 1); destruct (Z.ltb_spec 10 (hd_frames_per_packet hd)); cbn in BP; try discriminate; lia. }
apply evt_done. apply KC.
unfold HCG. sf_eexists 16%nat. first [ unshelve sf_eexists 13%nat; [ exact (F1) | exact (fc1) | exact (m1) | exact (x) | exact (nbr) | exact (brem0) | exact (HB) | exact (S) | exact (pno) | exact (LBD) | exact (s0w) | exact (s3w) | exact (s8w) | ] | sf_fb; exists F1, fc1, m1, x, nbr, brem0, HB, S, pno, LBD, s0w, s3w, s8w ].
split; [reflexivity|]. split; [exact FRM|]. split; [exact PU|].
split. { split; [exists j16, jsk, lk; unfold wz; exact LOW|]. split; [exists stb; exact STB|]. split; [exact OSP|].
split; [exists opj; exact OP|]. split; [exists ogj; exact OG|]. split; [exact SY|]. split; [exact BI|].
split; [exists pad; unfold wz; exact FSZ|]. split; [exists outb; split; [exact OUT| exact LOUT]|]. split; [exists cbj; exact CBK| exact SAV]. }
split; [exact HG|]. split. { split; [first [ unshelve sf_eexists 6%nat; [ exact (junk28) | exact (w1) | exact (w2) | exact (w3) | exact (r1) | exact (r2) | ] | sf_fb; exists junk28, w1, w2, w3, r1, r2 ]; unfold spx_header_cells; exact HCELLS|]. split; [exact HBR|]. unfold SPEEX_NB_MODES. repeat (split; [lia|]). lia. }
split; [exact PNO|]. split; [exact SB|]. split; [exact DR|]. split; [exact BRD|]. split; [exact FSOK|]. split; [exact RTR'| exact FPOK].
Qed.
End HDR5.

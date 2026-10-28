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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gy X1hg X1hf X1hh X1hi X1hj X1gz X1gt X1gu X1h6 X1gx X1h3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma lib_get_mode_some : forall i, 0 <= i < SPEEX_NB_MODES -> speex_lib_get_mode i = Some (mode_of_id i).
Proof.
intros i Hi. unfold speex_lib_get_mode, mode_of_id, SPEEX_NB_MODES in *.
replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia). replace (3 <=? i) with false by (symmetry; apply Z.leb_gt; lia). cbn [orb].
destruct (i =? 0); [reflexivity|]. destruct (i =? 1); reflexivity.
Qed.

Lemma mode_bsv_cell : forall m mo, rtables_pristine m -> rw_cells rsegs m (mode_addr mo + 28) [C4 (Z_to_bv 64 (mode_bitstream_version mo))].
Proof.
intros m mo TP. destruct mo; cbn [mode_addr mode_bitstream_version];
(apply rw_cells_of_pristine; [exact TP| cbn; tauto| unfold RTABLES_LO, A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode; lia
| unfold RTABLES_HI, A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode; cbn; lia| vm_compute; reflexivity]).
Qed.

Lemma mode_addr_ok : forall mo, 0 < mode_addr mo < 2^32 /\ mode_addr mo mod 8 = 0.
Proof. intros []; unfold mode_addr, A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode; (split; [lia| reflexivity]). Qed.
Lemma mode_addr_nz : forall mo, bv_eqb (Z_to_bv 64 (mode_addr mo)) (Z_to_bv 64 0) = false.
Proof. intros []; reflexivity. Qed.
Lemma mode_addr_land7 : forall mo, Z.land (mode_addr mo) 7 = 0.
Proof. intros []; reflexivity. Qed.
Lemma land3_of_mod16 : forall a, a mod 16 = 0 -> Z.land a 3 = 0.
Proof.
intros a H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
rewrite (Znumtheory.Zmod_div_mod 4 16 a) by (lia || (exists 4; reflexivity)). rewrite H. reflexivity.
Qed.

Section HDR2.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis DINIT : rspx_decoder_init_stmt dec_rep.
Hypothesis DDESTROY : rspx_decoder_destroy_stmt dec_rep.
Hypothesis RFREE : rfree_stmt.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).
Notation FREE_NONE blk := (X1qx.mbind (raw_free blk) (fun _ => X1qx.mret (@None (hstate bptr)))).

#[using="DINIT RFREE RBR RND CX"] Lemma hdr_checks : forall fuel' h blk hd pn st ms (br0 : Z) (oy0 : sync_st bptr),
HM c h blk hd st ms ->
(forall d st' ms', HS dec_rep c h blk hd d st' ms' -> dec_mode d = mode_of_id (hd_mode hd) ->
hd_speex_version_id hd <= 1 -> hd_mode_bitstream_version hd = mode_bitstream_version (mode_of_id (hd_mode hd)) ->
implM rsegs (X1qx.mbind (ph_after_init h blk hd d) (hdr_tailK fuel' h pn)) st' (PKPOST dec_rep c br0 oy0) ms') ->
implM rsegs (X1qx.mbind (ph_after_p2h h blk hd) (hdr_tailK fuel' h pn)) st (PKPOST dec_rep c br0 oy0) ms.
Proof.
intros fuel' h blk hd pn st ms br0 oy0 HMC KS.
first [ sf_destruct 33%nat HMC as x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 HB pno s0w s3w s8w -> FRM PU FR HG HBK PNO | sf_fb; destruct HMC as (x1 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & HB & pno & s0w & s3w & s8w & -> & FRM & PU & FR & HG & HBK & PNO) ].
pose proof PU as sfP_; first [ sf_destruct 9%nat sfP_ as SI1 EOS0 PC0 EST AS0 ALBD PURE LOK BUD' | sf_fb; destruct sfP_ as (SI1 & EOS0 & PC0 & EST & AS0 & ALBD & PURE & LOK & BUD') ].
pose proof FR as sfP_; first [ sf_destruct 11%nat sfP_ as (j16 & jsk & lk & LOW & LKOK) (stb & STB) OSP (opj & OP) (ogj & OG) SY BI (pad & FSZ) (outb & OUT & LOUT) (cbj & CBK) SAV | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW & LKOK) & (stb & STB) & OSP & (opj & OP) & (ogj & OG) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (cbj & CBK) & SAV) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof HBK as sfP_; first [ sf_destruct 9%nat sfP_ as (junk28 & w1 & w2 & w3 & r1 & r2 & HCELLS) HBR V1 V2 V3 V4 V5 V6 V7 | sf_fb; destruct sfP_ as ((junk28 & w1 & w2 & w3 & r1 & r2 & HCELLS) & HBR & V1 & V2 & V3 & V4 & V5 & V6 & V7) ].
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HBR as sfP_; first [ sf_destruct 5%nat sfP_ as HB1 HB2 _ HB4 HB5 | sf_fb; destruct sfP_ as (HB1 & HB2 & _ & HB4 & HB5) ]. unfold alloc_ceiling, SIZEOF_SPEEX_HEADER_Z in HB4, HB5. unfold SPEEX_NB_MODES in V3.
pose proof (RND _ _ _ HP) as ND.
assert (HLo : forall b, In b (owned x h) -> In b ([(blk, HB, SIZEOF_SPEEX_HEADER_Z)] ++ a_LB x)).
{ intros b Hb. right. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. exact Hb. }
assert (HL0 : forall b, In b (x_LB0 c) -> In b ([(blk, HB, SIZEOF_SPEEX_HEADER_Z)] ++ a_LB x)).
{ intros b Hb. right. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
assert (EOSB : 0 <= h_eos h <= 1) by lia.
set (mo := mode_of_id (hd_mode hd)).
pose proof (mode_bsv_cell m mo TP) as BSV. pose proof (mode_addr_ok mo) as (MAO & MA8).

assert (FAIL : forall (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
evt rsegs (fun ms1 => impl rsegs (at_node rsegs) ((X1qx.mbind (FREE_NONE blk) (hdr_tailK fuel' h pn)) st)
(epost (fun p ms2 => PKPOST dec_rep c br0 oy0 (fst p) (snd p) ms2)) ms1)
(MS (mkR y1 (Z_to_bv 64 (aLOW c)) (x_gp c) (Z_to_bv 64 RATP) y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 (Z_to_bv 64 HB)
y23 y24 y25 y26 y27 y28 y29 y30 y31) F (Z_to_bv 64 0x1c754) fc None m (seg_rom rsegs))).
{ intros. apply evt_done. apply (hdr_f294 dec_rep RFREE RBR RND c CX).
unfold F294. sf_eexists 27%nat. first [ unshelve sf_eexists 7%nat; [ exact (F) | exact (fc) | exact (m) | exact (x) | exact (nbr) | exact (brem0) | exact (HB) | ] | sf_fb; exists F, fc, m, x, nbr, brem0, HB ].
split; [reflexivity|]. split; [exact FRM|]. split; [exact PU|]. split; [apply (hdr_frame_junk _ _ _ _ _ _ FR)| exact HG]. }
unfold spx_header_cells in HCELLS.
unfold implM. iprefix. unfold hregs, wz.

zstep. zstep. rewrite (land3_of_mod16 HB HB2). zstep. if_false_z.
zstep. rewrite sx32_small by (unfold X1nj.int31; lia).
zstep. zstep. if_cases B1; scond B1; [exfalso; lia|].
unfold ph_after_p2h.
replace ((SPEEX_NB_MODES <=? hd_mode hd) || (hd_mode hd <? 0)) with false.
2:{ symmetry. unfold SPEEX_NB_MODES. replace (3 <=? hd_mode hd) with false by (symmetry; apply Z.leb_gt; lia). replace (hd_mode hd <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
cbv zeta. rewrite (lib_get_mode_some (hd_mode hd)) by (unfold SPEEX_NB_MODES; lia). fold mo.

assert (JOIN : forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
evt rsegs (fun ms1 => impl rsegs (at_node rsegs)
((X1qx.mbind (if 1 <? hd_speex_version_id hd then FREE_NONE blk
else if mode_bitstream_version mo <? hd_mode_bitstream_version hd then FREE_NONE blk
else if hd_mode_bitstream_version hd <? mode_bitstream_version mo then FREE_NONE blk
else X1qx.mbind (h_decoder_initP mo) (fun ost => match ost with None => FREE_NONE blk | Some st0 => ph_after_init h blk hd st0 end))
(hdr_tailK fuel' h pn)) st)
(epost (fun p ms2 => PKPOST dec_rep c br0 oy0 (fst p) (snd p) ms2)) ms1)
(MS (mkR y1 (Z_to_bv 64 (aLOW c)) (x_gp c) (Z_to_bv 64 RATP) y5 y6 y7 s0w (Z_to_bv 64 pno) (Z_to_bv 64 (mode_addr mo)) y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 (a_S x)) s3w (Z_to_bv 64 (h_extra_headers h)) (Z_to_bv 64 2147483647) (Z_to_bv 64 HB) (Z_to_bv 64 (h_packet_count h))
s8w (Z_to_bv 64 (h_nframes h)) (Z_to_bv 64 (h_speex_serialno h)) (Z_to_bv 64 (h_channels h)) y28 y29 y30 y31)
F (Z_to_bv 64 0x1c5ac) fc None m (seg_rom rsegs))).
{ intros.

zstep. rewrite sx32_signed_small by lia. zstep. zstep. if_cases B2; scond B2.
- replace (1 <? hd_speex_version_id hd) with true by (symmetry; apply Z.ltb_lt; lia). apply FAIL.
- replace (1 <? hd_speex_version_id hd) with false by (symmetry; apply Z.ltb_ge; lia).

zstep. rewrite mode_addr_nz. cbv iota. zstep. rewrite mode_addr_land7. zstep. if_false_z.
zstep. rewrite sx32_small by (unfold X1nj.int31, mode_bitstream_version; lia).
zstep. rewrite sx32_signed_small by lia.
zstep. if_cases B3; rewrite zbv_eqb_signed in B3 by (unfold mode_bitstream_version; lia).
+
assert (NE : mode_bitstream_version mo <> hd_mode_bitstream_version hd).
{ first [apply Bool.negb_true_iff in B3| idtac]. apply (proj1 (Z.eqb_neq _ _)) in B3. exact B3. }
destruct (Z.lt_ge_cases (mode_bitstream_version mo) (hd_mode_bitstream_version hd)) as [LT|GE].
* replace (mode_bitstream_version mo <? hd_mode_bitstream_version hd) with true by (symmetry; apply Z.ltb_lt; lia). apply FAIL.
* replace (mode_bitstream_version mo <? hd_mode_bitstream_version hd) with false by (symmetry; apply Z.ltb_ge; lia).
replace (hd_mode_bitstream_version hd <? mode_bitstream_version mo) with true by (symmetry; apply Z.ltb_lt; lia). apply FAIL.
+ assert (EQV : mode_bitstream_version mo = hd_mode_bitstream_version hd).
{ first [apply Bool.negb_false_iff in B3| idtac]. apply (proj1 (Z.eqb_eq _ _)) in B3. exact B3. }
replace (mode_bitstream_version mo <? hd_mode_bitstream_version hd) with false by (symmetry; apply Z.ltb_ge; lia).
replace (hd_mode_bitstream_version hd <? mode_bitstream_version mo) with false by (symmetry; apply Z.ltb_ge; lia).

zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st (PKPOST dec_rep c br0 oy0) msx) end.
apply implM_bind_assoc. eapply implM_bind.
{ eapply DINIT with (LB := [(blk, HB, SIZEOF_SPEEX_HEADER_Z)] ++ a_LB x) (mo := mo) (AB := x_AB c) (lo := x_lo c);
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ exact HP | exact TP | exact AUX | exact ST | exact MI | exact FRM | reflexivity
| unfold DEC_INIT_STACK, alloc_ceiling in *; lia
| unfold RATP; rewrite unsigned_lit by lia; exact ERR
| clear - SP16; Z.div_mod_to_equations; lia ]. }
cbv beta. intros ost st1 ms1 PO.
first [ sf_destruct 28%nat PO as z0 z1 z2 e0 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 F1 fc1 m1 errv1 -> FRM1 MI1 ST1 ERR1 AUX1 HPR ESO RES | sf_fb; destruct PO as (z0 & z1 & z2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z3 & z4 & z5 & z6 & F1 & fc1 & m1 & errv1 & -> & FRM1 & MI1 & ST1 & ERR1 & AUX1 & HPR & ESO & RES) ].
rewrite ?(unsigned_lit (aLOW c)) in ST1 by lia. rewrite ?(unsigned_lit (aLOW c)) in HPR by lia.
unfold RATP in ERR1. rewrite ?unsigned_lit in ERR1 by lia. change (0x4d450 + -164) with RERRNO in ERR1.
replace (ret_pc (Z_to_bv 64 0x1c5d4)) with (Z_to_bv 64 0x1c5d4) by (symmetry; rpc).
pose proof (agree_of_rheap_pres _ _ _ _ HPR) as AG.

assert (PFR : forall a, aLOW c <= a -> rclient_addr ([(blk, HB, SIZEOF_SPEEX_HEADER_Z)] ++ a_LB x) (aLOW c) a) by (intros a Ha; left; lia).
assert (PBL : forall bb a, In bb (owned x h) -> blk_addr bb <= a < blk_addr bb + blk_size bb -> rclient_addr ([(blk, HB, SIZEOF_SPEEX_HEADER_Z)] ++ a_LB x) (aLOW c) a).
{ intros bb a Hbb Ra. right; right. exists bb. split; [apply HLo; exact Hbb| exact Ra]. }
eapply (rw_cells_agree _ _ _ _ _ _ AG) in LOW; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in STB; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OP; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OG; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in FSZ; [| intros a Ha; apply PFR; unfold fsz_cells in Ha; cbn in Ha; lia].
eapply (u8arr_agree _ _ _ _ _ AG) in OUT; [| intros a Ha; apply PFR; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in CBK; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in SAV; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in HCELLS; [| intros a Ha; right; right; exists (blk, HB, SIZEOF_SPEEX_HEADER_Z); split; [left; reflexivity| cbn in Ha |- *; unfold SIZEOF_SPEEX_HEADER_Z; lia]].
eapply (stream_rep_agree2 _ _ _ _ _ _ AG) in OSP; [| intros a Ha; apply PFR; lia| intros a (bb & Hbb & Ra); apply (PBL bb a); [apply in_owned_stream; exact Hbb| exact Ra]].
eapply (sync_rep_agree _ _ _ _ _ _ _ AG) in SY; [| intros a Ha; apply PFR; lia|].
2:{ intros a Ha. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT.
destruct (sy_data (h_oy h)) as [q|] eqn:ESD; [| first [ sf_destruct 4%nat DAT as _ _ _ ST0 | sf_fb; destruct DAT as (_ & _ & _ & ST0) ]; rewrite SYLEN, ST0 in Ha; lia].
apply (PBL (q, a_D x, sy_storage (h_oy h)) a); [apply in_owned_sync; exact ESD| cbn; rewrite <- SYLEN; lia]. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| intros a Ha; apply PFR; lia| intros a Ha; apply (PBL _ a (in_owned_bits x h)); cbn; lia].
assert (FRAME1 : hdr_frame c x h m1 nbr brem0).
{ split; [exists j16, jsk, lk; split; [exact LOW| exact LKOK]|]. split; [exists stb; exact STB|]. split; [exact OSP|].
split; [exists opj; exact OP|]. split; [exists ogj; exact OG|]. split; [exact SY|]. split; [exact BI|].
split; [exists pad; exact FSZ|]. split; [exists outb; split; [exact OUT| exact LOUT]|]. split; [exists cbj; exact CBK| exact SAV]. }
assert (HBK1 : hdr_blk m1 HB hd).
{ split; [first [ unshelve sf_eexists 6%nat; [ exact (junk28) | exact (w1) | exact (w2) | exact (w3) | exact (r1) | exact (r2) | ] | sf_fb; exists junk28, w1, w2, w3, r1, r2 ]; exact HCELLS|]. split; [exact HBR|]. unfold SPEEX_NB_MODES. repeat (split; [lia|]). lia. }
assert (HGX : forall st' extra, RHEAP st' (extra ++ a_LB x) m1 -> ps_so st' = ps_so st -> hglobX c x h st' m1 extra).
{ intros st' extra HPe SOe. eapply (hglobX_agree2 RBR c x h st st' m m1 _ extra _ errv1 CX HG AG HPe MI1 ST1); [| exact ERR1| exact AUX1| exact SOe|].
- eapply stderr_wfile_agree; [exact AG| | exact SEW]. intros a Ha. right; left. unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
- intros a [Ha|[(Ha & Hs & Hx)|(bb & Hbb & Rbb)]]; [apply PFR; lia| right; left; split; [exact Ha| exact Hs]| right; right; exists bb; split; [apply HL0; exact Hbb| exact Rbb]]. }
clear AG HPR LOW STB OP OG FSZ OUT CBK OSP SY BI.
destruct ost as [d|].
*
first [ sf_destruct 7%nat RES as S LBD -> SB HP2 DR DM | sf_fb; destruct RES as (S & LBD & -> & SB & HP2 & DR & DM) ].
unfold implM. iprefix. zstep. if_cases BZ; scond BZ; [exfalso; lia|].
apply evt_done. apply (KS d st1); [| exact DM| lia| symmetry; exact EQV].
unfold HS. sf_eexists 15%nat. first [ unshelve sf_eexists 13%nat; [ exact (F1) | exact (fc1) | exact (m1) | exact (x) | exact (nbr) | exact (brem0) | exact (HB) | exact (S) | exact (pno) | exact (LBD) | exact (s0w) | exact (s3w) | exact (s8w) | ] | sf_fb; exists F1, fc1, m1, x, nbr, brem0, HB, S, pno, LBD, s0w, s3w, s8w ].
split; [reflexivity|]. split; [exact FRM1|]. split; [exact PU|]. split; [exact FRAME1|].
split; [apply HGX; [rewrite <- app_assoc; exact HP2| exact ESO]|].
split; [exact HBK1|]. split; [exact PNO|]. split; [lia|]. split; [exact DR|].
intros b Hb. apply (RBR _ _ _ _ HP2). apply in_app_iff. left. exact Hb.
*
destruct RES as [-> HP2].
unfold implM. iprefix. zstep. if_cases BZ; scond BZ; [| exfalso; apply BZ; reflexivity].
apply evt_done. apply (hdr_f294 dec_rep RFREE RBR RND c CX).
unfold F294. sf_eexists 27%nat. first [ unshelve sf_eexists 7%nat; [ exact (F1) | exact (fc1) | exact (m1) | exact (x) | exact (nbr) | exact (brem0) | exact (HB) | ] | sf_fb; exists F1, fc1, m1, x, nbr, brem0, HB ].
split; [reflexivity|]. split; [exact FRM1|]. split; [exact PU|]. split; [apply (hdr_frame_junk _ _ _ _ _ _ FRAME1)|].
apply HGX; [cbn [app]; exact HP2| exact ESO]. }

zstep. if_cases BM; scond BM.
-
pose proof (got_nb_mode_cell m TP) as GOTC. unfold GOT_speex_nb_mode in GOTC. change X1ff.rsegs with X1gj.rsegs in GOTC.
zstep. zstep.
replace A_speex_nb_mode with (mode_addr mo) by (subst mo; unfold mode_of_id; rewrite BM; reflexivity).
apply JOIN.
-
zstep.
eapply evt_cut; [eapply (speex_lib_get_mode_spec (hd_mode hd)); [exact TP| exact MI| lia]|].
cbv beta. intros ms2 PO. first [ sf_destruct 15%nat PO as u0 u1 u2 g1 g2 g3 g4 g5 g6 g7 u3 u4 u5 u6 -> | sf_fb; destruct PO as (u0 & u1 & u2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & u3 & u4 & u5 & u6 & ->) ].
replace (ret_pc (Z_to_bv 64 0x1c5a0)) with (Z_to_bv 64 0x1c5a0) by (symmetry; rpc).
fold mo. unfold wz. zstep. apply JOIN.
Qed.
End HDR2.

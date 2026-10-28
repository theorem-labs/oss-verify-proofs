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

Section HDR1.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis P2H : rspx_packet_to_header_stmt.
Hypothesis RFREE : rfree_stmt.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).

#[using="P2H RFREE RHF RBR RND CX"] Lemma hdr_p2h : forall fuel' h op pn st ms (br0 : Z) (oy0 : sync_st bptr),
PKH dec_rep c h op st ms -> h_oy h = oy0 -> h_bytes_remaining h = br0 ->
h_packet_count h + 1 + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * hconsumed c h ->
(forall blk hd st' ms', HM c h blk hd st' ms' ->
implM rsegs (X1qx.mbind (ph_after_p2h h blk hd) (hdr_tailK fuel' h pn)) st' (PKPOST dec_rep c br0 oy0) ms') ->
implM rsegs (pkt_bodyP fuel' h op (packet_data (h_os h) op) pn) st (PKPOST dec_rep c br0 oy0) ms.
Proof.
intros fuel' h op pn st ms br0 oy0 PB EOY EBR BUD' KM.
first [ sf_destruct 44%nat PB as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 ogj gw pno s0w s3w -> FRM SI1 EOS0 SSE SNM1 HRX LOK OF1 OF2 OF3 OF4 BDNZ EOSR PNO _ PC0 | sf_fb; destruct PB as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & ogj & gw & pno & s0w & s3w & -> & FRM & SI1 & EOS0 & SSE & SNM1 & HRX & LOK & OF1 & OF2 & OF3 & OF4 & BDNZ & EOSR & PNO & _ & PC0) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HRX as sfP_; first [ sf_destruct 16%nat sfP_ as (j16 & jsk & lk & LOW & LKOK) _ _ (stb & STB) OSP (OPK & OPS) (OG & OGS) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG PURE | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW & LKOK) & _ & _ & (stb & STB) & OSP & (OPK & OPS) & (OG & OGS) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
unfold os_piece in OSP. rewrite SI1 in OSP. cbn [Z.eqb] in OSP.
pose proof OSP as sfP_; first [ sf_destruct 34%nat sfP_ as OS LH FOK SINV BINV LOK' GOK UL UG UB W1 L1 L2 L3 PB1 PB2 N1 N2 N3 Z1 Z2 Z3 R1 R2 R3 C1 C2 C3 E1 E2 E3 G1 G2 G3 | sf_fb; destruct sfP_ as (OS & LH & FOK & SINV & BINV & LOK' & GOK & UL & UG & UB & W1 & L1 & L2 & L3 & PB1 & PB2 & N1 & N2 & N3 & Z1 & Z2 & Z3 & R1 & R2 & R3 & C1 & C2 & C3 & E1 & E2 & E3 & G1 & G2 & G3) ].
pose proof BINV as (BL & _).
pose proof (RND _ _ _ HP) as ND.
unfold hbudget, hconsumed, hpend in BUD. pose proof L4K as L4K'. unfold MAX_FUZZ_SIZE in L4K'.
destruct PC0 as [PC0 PKO0].
rewrite PC0 in STR. destruct (h_st h) as [d|] eqn:EST; [exfalso; exact (STR eq_refl)|]. clear STR.
unfold dec_piece in DEC. rewrite EST in DEC. destruct DEC as [AS0 ALBD].
destruct (os_body_data (h_os h)) as [pbody|] eqn:EBD; [| exfalso; exact (BDNZ eq_refl)]. clear BDNZ.
specialize (R1 ltac:(discriminate)).

unfold pkt_bodyP. rewrite PC0. cbn [Z.eqb]. rewrite process_header_eq.
apply implM_bind_assoc. apply implM_bind_assoc.

set (pb := firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) (a_body x))).
assert (LENB : (Z.to_nat (pk_off op) + Z.to_nat (pk_bytes op) <= length (a_body x))%nat) by (unfold zlength in BL; lia).
assert (LPB : length pb = Z.to_nat (pk_bytes op)) by (subst pb; rewrite length_firstn, length_skipn; lia).
pose proof (bytes_at_sub m (a_Bd x) (a_body x) (Z.to_nat (pk_off op)) (Z.to_nat (pk_bytes op)) (proj1 UB) LENB) as SRC.
rewrite Z2Nat.id in SRC by lia. fold pb in SRC.
assert (PDE : packet_data (h_os h) op = ubytes pb) by (subst pb; apply packet_bytes_eq; [exact PB1| exact BL| lia| lia| lia]).
rewrite PDE.
assert (HLo : forall b, In b (owned x h) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. exact Hb. }
assert (HL0 : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
assert (INBODY : In (pbody, a_Bd x, a_nB x) (a_LB x)).
{ apply HLo. apply in_owned_stream. unfold stream_blks. rewrite EBD. apply in_app_iff; left. left. reflexivity. }
pose proof (rheap_ssp0 _ _ _ HP) as SSP.
unfold low_cells, wz in LOW. unfold fsz_cells in FSZ.
pose proof (munch_refl [(aCBK c, aCBK c + 48)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
change (id (rw_cells rsegs m RERRNO [C4 errv])) in ERR. change (id (bytes_at rsegs m (x_P c) (to_bytes (x_payload c)))) in PAY.
unfold implM. iprefix. unfold hregs, wz.

zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite Z.add_0_r. rewrite swrap32_small by lia.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (mA := mx) in * end.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG. unfold id in ERR, PAY.
assert (HG1 : hglob c x h st mA).
{ eapply (hglob_frame RHF RBR c x h st m mA); [exact CX| exact HG| exact MU| exact WM| | assumption| assumption].
unfold in_frame. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
eapply (stream_rep_agree2 _ _ _ _ _ _ AG) in OSP; [| side1c| intros a (bb & Hbb & Ra); pose proof (RBR _ _ _ _ HP (HLo _ (in_owned_stream _ _ _ Hbb))) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]; unfold alloc_ceiling in B4; cbn [outside fst snd]; lia].
eapply (sync_rep_agree _ _ _ _ _ _ _ AG) in SY; [| side1c| intros a Ha; pose proof SYBLK; unfold rblock_range, alloc_ceiling in *; cbn [outside fst snd];
destruct (sy_data (h_oy h)) eqn:ESD; [pose proof (SYBLK ltac:(discriminate)); lia| first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]; unfold sync_data in DAT; rewrite ESD in DAT; first [ sf_destruct 4%nat DAT as _ _ _ ST0 | sf_fb; destruct DAT as (_ & _ & _ & ST0) ]; rewrite SYLEN, ST0 in Ha; lia]].
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| side1c| intros a Ha; pose proof BBR as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]; unfold alloc_ceiling in B4; cbn [outside fst snd]; lia].
pose proof HG1 as sfP_; first [ sf_destruct 11%nat sfP_ as HP1 _ PAY1 TP1 SEW1 (errv1 & ERR1) AUX1 MIA STA PE1 _ | sf_fb; destruct sfP_ as (HP1 & _ & PAY1 & TP1 & SEW1 & (errv1 & ERR1) & AUX1 & MIA & STA & PE1 & _) ].
pose proof (rheap_ssp0 _ _ _ HP1) as SSP1.
clearbody mA. clear MU WM AG HG HP PAY TP SEW ERR AUX MI ST PE SSP.

zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st (PKPOST dec_rep c br0 oy0) msx) end.
eapply implM_bind.
{ eapply P2H with (LB := a_LB x) (pblk := (pbody, a_Bd x, a_nB x)) (P := a_Bd x + pk_off op) (size := pk_bytes op) (pbytes := pb)
(AB := x_AB c) (lo := x_lo c) (canary := run_canary);
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ exact HP1 | exact INBODY | exact SRC | exact TP1 | exact SEW1 | exact SSP1 | exact AUX1 | exact STA | exact MIA | exact FRM | reflexivity
| unfold PKT2HDR_STACK, alloc_ceiling in *; cbn [blk_addr blk_size fst snd]; lia
| unfold RATP; rewrite unsigned_lit by lia; exact ERR1
| rewrite PKO0, Z.add_0_r; rewrite (Znumtheory.Zmod_div_mod 4 16) by (lia || (exists 4; reflexivity)); rewrite (proj1 (proj2 R1)); reflexivity ]. }
cbv beta. intros r st1 ms1 PO.
first [ sf_destruct 30%nat PO as y0 y1 y2 e0 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 Ft fc1 m1 errv2 -> FRM1 MI1 ST1 ERR2 AUX2 PEX SEW2 SSP2 ESO RES | sf_fb; destruct PO as (y0 & y1 & y2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & Ft & fc1 & m1 & errv2 & -> & FRM1 & MI1 & ST1 & ERR2 & AUX2 & PEX & SEW2 & SSP2 & ESO & RES) ].
rewrite ?(unsigned_lit (aLOW c)) in ST1 by lia. rewrite ?(unsigned_lit (aLOW c)) in PEX by lia.
unfold RATP in ERR2. rewrite ?unsigned_lit in ERR2 by lia. change (0x4d450 + -164) with RERRNO in ERR2.
replace (ret_pc (Z_to_bv 64 0x1c57c)) with (Z_to_bv 64 0x1c57c) by (symmetry; rpc).
pose proof (agree_of_pres_except _ _ _ _ PEX) as AG.

assert (PFR : forall a, aLOW c <= a < usp c -> rclient_addr (a_LB x) (aLOW c) a /\ ~ in_ivs [(250128, 250128 + 232)] a).
{ intros a Ha. split; [left; lia| cbn [in_ivs fst snd]; lia]. }
assert (PBL : forall bb a, In bb (owned x h) -> blk_addr bb <= a < blk_addr bb + blk_size bb -> rclient_addr (a_LB x) (aLOW c) a /\ ~ in_ivs [(250128, 250128 + 232)] a).
{ intros bb a Hbb Ra. pose proof (RBR _ _ _ _ HP1 (HLo _ Hbb)) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 B5 | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & B5) ]. unfold alloc_ceiling in B4.
split; [right; right; exists bb; split; [apply HLo; exact Hbb| exact Ra]| cbn [in_ivs fst snd]; lia]. }
eapply (rw_cells_agree _ _ _ _ _ _ AG) in LOW; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in STB; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OPK; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OG; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in FSZ; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (u8arr_agree _ _ _ _ _ AG) in OUT; [| intros a Ha; apply PFR; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in HI; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in SAV; [| intros a Ha; apply PFR; cbn in Ha; lia].
eapply (stream_rep_agree2 _ _ _ _ _ _ AG) in OSP; [| intros a Ha; apply PFR; lia| intros a (bb & Hbb & Ra); apply (PBL bb a); [apply in_owned_stream; exact Hbb| exact Ra]].
eapply (sync_rep_agree _ _ _ _ _ _ _ AG) in SY; [| intros a Ha; apply PFR; lia|].
2:{ intros a Ha. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT.
destruct (sy_data (h_oy h)) as [q|] eqn:ESD; [| first [ sf_destruct 4%nat DAT as _ _ _ ST0 | sf_fb; destruct DAT as (_ & _ & _ & ST0) ]; rewrite SYLEN, ST0 in Ha; lia].
apply (PBL (q, a_D x, sy_storage (h_oy h)) a); [apply in_owned_sync; exact ESD| cbn; rewrite <- SYLEN; lia]. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| intros a Ha; apply PFR; lia| intros a Ha; apply (PBL _ a (in_owned_bits x h)); cbn; lia].
destruct (rw_cells_forget _ _ _ _ OPK) as [opj' OP']. cbn [cells_size csize Nat.add] in OP'.
assert (FRAME1 : hdr_frame c x h m1 nbr brem0).
{ split; [exists j16, jsk, lk; split; [unfold low_cells, wz; exact LOW| exact LKOK]|]. split; [exists stb; exact STB|]. split; [exact OSP|].
split; [exists opj'; exact OP'|]. split; [exists ogj; exact OG|]. split; [exact SY|]. split; [exact BI|].
split; [exists pad; unfold fsz_cells; exact FSZ|]. split; [exists outb; split; [exact OUT| exact LOUT]|]. split; [exists (take 44 hij); exact HI| exact SAV]. }
assert (PUREX : hdr_pure c x h nbr brem0).
{ split; [exact SI1|]. split; [exact EOS0|]. split; [exact PC0|]. split; [exact EST|]. split; [exact AS0|]. split; [exact ALBD|].
split; [exact PURE|]. split; [exact LOK|]. rewrite PC0 in BUD'. unfold hconsumed, hpend in BUD' |- *. lia. }
assert (HGX : forall extra, RHEAP st1 (extra ++ a_LB x) m1 -> hglobX c x h st1 m1 extra).
{ intros extra HPe. eapply (hglobX_agree2 RBR c x h st st1 mA m1 [] extra _ errv2 CX); [apply hglobX_nil; exact HG1| exact AG| exact HPe| exact MI1| exact ST1| exact SEW2| exact ERR2| exact AUX2| exact ESO|].
intros a [Ha|[(Ha & Hs & Hx)|(bb & Hbb & Rbb)]]; cbv beta; [split; [left; lia| cbn [in_ivs fst snd]; lia]| | ].
- split; [right; left; split; [exact Ha| exact Hs]| cbn [in_ivs fst snd]; lia].
- pose proof (RBR _ _ _ _ HP1 (HL0 _ Hbb)) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 B5 | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & B5) ]. unfold alloc_ceiling in B4.
split; [right; right; exists bb; split; [apply HL0; exact Hbb| exact Rbb]| cbn [in_ivs fst snd]; lia]. }
clear AG PEX LOW STB OSP OP' OG SY BI FSZ OUT HI OPK.

destruct r as [[blk hd]|].
-
first [ sf_destruct 18%nat RES as HB junk28 w1 w2 w3 r1 r2 -> HBR HP2 HCELLS V1 V2 V3 V4 V5 V6 V7 | sf_fb; destruct RES as (HB & junk28 & w1 & w2 & w3 & r1 & r2 & -> & HBR & HP2 & HCELLS & V1 & V2 & V3 & V4 & V5 & V6 & V7) ].
pose proof HBR as sfP_; first [ sf_destruct 5%nat sfP_ as HB1 _ _ HB4 _ | sf_fb; destruct sfP_ as (HB1 & _ & _ & HB4 & _) ]. unfold alloc_ceiling, SIZEOF_SPEEX_HEADER_Z in HB4.
unfold implM. iprefix. zstep. if_cases BZ; scond BZ; [exfalso; lia|].
apply evt_done. apply KM.
unfold HM. sf_eexists 15%nat. first [ unshelve sf_eexists 11%nat; [ exact (Ft) | exact (fc1) | exact (m1) | exact (x) | exact (nbr) | exact (brem0) | exact (HB) | exact (pno) | exact (s0w) | exact (s3w) | exact (Z_to_bv 64 (pk_bytes op)) | ] | sf_fb; exists Ft, fc1, m1, x, nbr, brem0, HB, pno, s0w, s3w, (Z_to_bv 64 (pk_bytes op)) ].
split; [unfold hregs; reflexivity|].
split; [exact FRM1|]. split; [exact PUREX|]. split; [exact FRAME1|].
split; [apply HGX; cbn [app]; exact HP2|].
split; [| exact PNO]. split; [first [ unshelve sf_eexists 6%nat; [ exact (junk28) | exact (w1) | exact (w2) | exact (w3) | exact (r1) | exact (r2) | ] | sf_fb; exists junk28, w1, w2, w3, r1, r2 ]; exact HCELLS|]. split; [exact HBR|]. repeat (split; [assumption|]). assumption.
-
destruct RES as [-> HP2].
unfold implM. iprefix. zstep. if_cases BZ; scond BZ; [| exfalso; apply BZ; reflexivity].
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st1 (PKPOST dec_rep c br0 oy0) msx) end.
apply implM_retb. unfold hdr_tailK. apply implM_bind_assoc.
eapply (clean_inl_k RFREE RBR RND c CX); [| intros st' ms' HF; apply implM_retb; apply implM_ret; apply evt_done; exact HF].
pose proof (HGX [] HP2) as HG2. apply hglobX_nil in HG2.
pose proof HG2 as sfP_; first [ sf_destruct 11%nat sfP_ as HP3 PERM3 _ _ SEW3 ERR3 AUX3 MI3 ST3 PE3 SO3 | sf_fb; destruct sfP_ as (HP3 & PERM3 & _ & _ & SEW3 & ERR3 & AUX3 & MI3 & ST3 & PE3 & SO3) ].
pose proof (hdr_frame_junk _ _ _ _ _ _ FRAME1) as sfP_; first [ sf_destruct 5%nat sfP_ as OSP2 SY2 BI2 JK2 SAV2 | sf_fb; destruct sfP_ as (OSP2 & SY2 & BI2 & JK2 & SAV2) ].
unfold CLI. sf_eexists 28%nat. first [ unshelve sf_eexists 4%nat; [ exact (Ft) | exact (fc1) | exact (m1) | exact ((a_LB x)) | ] | sf_fb; exists Ft, fc1, m1, (a_LB x) ].
split; [rewrite PC0, ?EOS0; reflexivity|]. split; [exact FRM1|]. split; [exact EST|]. split; [exact SI1|]. split; [exact ST3|].
split; [exact HP3|]. split; [exact (RND _ _ _ HP3)|].
split. { unfold stream_blks. rewrite <- !app_assoc. unfold owned in PERM3. rewrite EST in PERM3. rewrite <- !app_assoc in PERM3. cbn [app] in PERM3. exact PERM3. }
split; [exact BI2|]. split; [exact BOK|]. split; [exact OWN|]. split; [exact BBR|]. split; [exact OSP2|].
split; [exact SY2|]. split; [exact SYOK|]. split; [intros NE; exact (proj1 (SYBLK NE))|]. split; [exact JK2|]. split; [exact SAV2|].
split; [exact SEW3|]. split; [exact ERR3|]. split; [exact AUX3|]. split; [exact MI3|]. split; [exact PE3| exact SO3].
Qed.
End HDR1.

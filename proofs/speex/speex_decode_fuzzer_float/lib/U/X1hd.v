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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h9 X1gy X1hg X1hc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma stream_rep_reset {RCEIL : RunCeiling} : forall m m' c x h (oy : sync_st bptr) sn r os',
stream_rep m c x h -> -2^31 <= sn < 2^31 ->
ogg_stream_reset_serialno (h_os h) sn = (r, os') ->
rw_cells rsegs m' (aOS c) (stream_cells (a_Bd x) (a_L x) (a_Gv x) (a_hdr x) os') -> stream_fields_ok os' ->
u32arr rsegs m' (a_L x) (a_lws x) -> u64arr rsegs m' (a_Gv x) (a_gws x) -> u8arr rsegs m' (a_Bd x) (a_body x) ->
stream_rep m' c x (set_ogg h oy os')
/\ os_lacing_fill os' <= os_lacing_fill (h_os h) /\ os_body_fill os' <= os_body_fill (h_os h)
/\ os_lacing_storage os' = os_lacing_storage (h_os h) /\ os_body_storage os' = os_body_storage (h_os h)
/\ os_body_data os' = os_body_data (h_os h) /\ os_lacing_vals os' = os_lacing_vals (h_os h) /\ os_granule_vals os' = os_granule_vals (h_os h)
/\ os_lacing_fill os' - os_lacing_returned os' <= os_lacing_fill (h_os h) - os_lacing_returned (h_os h).
Proof.
intros m m' c x h oy sn r os' SR SN RES OS' FOK' AL AG AB.
first [ sf_destruct 34%nat SR as OS LH F1 SINV BINV LOK GOK UL UG UB W1 L1 L2 L3 PB1 PB2 N1 N2 N3 Z1 Z2 Z3 R1 R2 R3 C1 C2 C3 E1 E2 E3 G1 G2 G3 | sf_fb; destruct SR as (OS & LH & F1 & SINV & BINV & LOK & GOK & UL & UG & UB & W1 & L1 & L2 & L3 & PB1 & PB2 & N1 & N2 & N3 & Z1 & Z2 & Z3 & R1 & R2 & R3 & C1 & C2 & C3 & E1 & E2 & E3 & G1 & G2 & G3) ].
pose proof (ogg_stream_reset_serialno_inv _ _ _ _ SINV RES) as SINV'.
pose proof (ogg_stream_reset_serialno_body_inv _ _ _ _ BINV RES) as BINV'.
pose proof SINV as sfP_; first [ sf_destruct 5%nat sfP_ as I1 I2 I3 I4 I5 | sf_fb; destruct sfP_ as (I1 & I2 & I3 & I4 & I5) ]. pose proof (body_inv_fill_nonneg _ BINV) as BF0. unfold zlength in I3, I4.
unfold ogg_stream_reset_serialno in RES.
destruct (ogg_stream_check (h_os h)) eqn:ECK.
-
inversion RES; subst. split.
{ unfold stream_rep. cbn [h_os set_ogg]. repeat (split; [assumption|]). exact G3. }
repeat split; first [lia| reflexivity].
- inversion RES; subst. split; [| cbn; repeat split; first [lia| reflexivity]].
unfold stream_rep, ogg_stream_reset. cbn -[Z.add Z.mul Z.le Z.lt alloc_ceiling Z.of_nat rblock_range stream_zero].
split; [exact OS'|]. split; [exact LH|]. split; [exact FOK'|]. split; [exact SINV'|]. split; [exact BINV'|].
split; [apply Forall_nil|]. split; [apply Forall_nil|]. split; [exact AL|]. split; [exact AG|]. split; [exact AB|].
split; [unfold wpre; cbn; split; [reflexivity| lia]|].
split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [reflexivity|]. split; [cbn; lia|].
repeat (split; [assumption|]).
destruct G3 as [G|G]; [left; exact G| right]. exfalso. rewrite G in ECK. cbv in ECK. discriminate.
Qed.

Section PAGE3.
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
Notation PGS := (PGS dec_rep c).

Definition PGP (h : hstate bptr) (og : page) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (nbr brem0 : Z) (s3w s5w s8w : word) (OP : list cell),
ms = MS (hregs c h (a_S x) (wz (h_last_granule h)) (wz brem0) s3w s5w s8w (wz (h_speex_serialno h)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz 0x1c284) fc None m (seg_rom rsegs)
/\ frm0 fc /\ h_stream_init h = 1
/\ hrepx dec_rep c x h st m (C8 (wz nbr)) (C8 (wz brem0)) (page_cells (a_D x) og) OP /\ low_ok h nbr brem0
/\ page_ok (h_oy h) og /\ sy_data (h_oy h) <> None /\ page_budget c h og.

#[using="DRF RHF RBR CX"] Lemma page_serial : forall (Q : outcome bptr -> PState -> machine_state -> Prop) fuel' h og st ms,
PGS h og st ms ->
(forall h2 st2 ms2, PGP h2 og st2 ms2 -> h_oy h2 = h_oy h -> h_bytes_remaining h2 = h_bytes_remaining h ->
h2 = (let serial := ogg_page_serialno (page_header (h_oy h) og) in
if negb (serial =? os_serialno (h_os h))
then let '(r, os) := ogg_stream_reset_serialno (h_os h) serial in set_ogg h (h_oy h) os else h) ->
implM rsegs (X1qx.mbind (ogg_stream_pagein raw_realloc raw_free (h_os h2) (page_header (h_oy h) og) (page_body (h_oy h) og))
(fun x => let '(r, os) := x in page_restP fuel' (page_header (h_oy h) og) (set_ogg h2 (h_oy h2) os))) st2 Q ms2) ->
implM rsegs (page_rest2P fuel' (h_oy h) og h) st Q ms.
Proof.
intros Q fuel' h og st ms PG K.
first [ sf_destruct 34%nat PG as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 s3w s5w s8w OP -> FRM SI1 HRX LOK POK NN PB | sf_fb; destruct PG as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & s3w & s5w & s8w & OP & -> & FRM & SI1 & HRX & LOK & POK & NN & PB) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HRX as sfP_; first [ sf_destruct 16%nat sfP_ as (j16 & jsk & lk & LOW & LKO) _ _ (stb & STB) OSP (OPK & OPS) (OG & OGS) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG PURE | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW & LKO) & _ & _ & (stb & STB) & OSP & (OPK & OPS) & (OG & OGS) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
pose proof SYOK as (SYI2 & SYST & SYNUL). pose proof SYI2 as [SYI _].
assert (HL0 : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
pose proof (pay_range RBR c _ _ _ CX HP HL0) as PRANGE.
assert (NUL : sy_data (h_oy h) = None -> a_D x = 0 /\ sy_storage (h_oy h) = 0).
{ intros ED. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT. rewrite ED in DAT. first [ sf_destruct 4%nat DAT as -> _ _ -> | sf_fb; destruct DAT as (-> & _ & _ & ->) ]. auto. }
assert (SYR : a_D x + sy_storage (h_oy h) <= alloc_ceiling).
{ destruct (sy_data (h_oy h)) eqn:ED.
- destruct (SYBLK ltac:(congruence)) as [(_ & _ & _ & B4 & _) _]. exact B4.
- destruct (NUL eq_refl) as [-> ->]. unfold alloc_ceiling. lia. }
pose proof (page_hs _ _ _ _ _ _ SY SYI POK NN) as sfP_; first [ sf_destruct 11%nat sfP_ as HS HBS LHS LBS EHS EBS HL27 NSEG PG0 PGE BL0 | sf_fb; destruct sfP_ as (HS & HBS & LHS & LBS & EHS & EBS & HL27 & NSEG & PG0 & PGE & BL0) ].
set (hs := firstn (Z.to_nat (pg_header_len og)) (skipn (Z.to_nat (pg_hdr og)) (a_sybytes x))) in *.
pose proof (s32_range (le32_at (page_header (h_oy h) og) 14)) as SERR.
change (s32 (le32_at (page_header (h_oy h) og) 14)) with (ogg_page_serialno (page_header (h_oy h) og)) in SERR.
set (serial := ogg_page_serialno (page_header (h_oy h) og)) in *.
unfold os_piece in OSP. rewrite SI1 in OSP. cbn [Z.eqb] in OSP.
pose proof OSP as sfP_; first [ sf_destruct 34%nat sfP_ as OS LH FOK SINV BINV LOK' GOK UL UG UB W1 L1 L2 L3 PB1 PB2 N1 N2 N3 Z1 Z2 Z3 R1 R2 R3 C1 C2 C3 E1 E2 E3 G1 G2 G3 | sf_fb; destruct sfP_ as (OS & LH & FOK & SINV & BINV & LOK' & GOK & UL & UG & UB & W1 & L1 & L2 & L3 & PB1 & PB2 & N1 & N2 & N3 & Z1 & Z2 & Z3 & R1 & R2 & R3 & C1 & C2 & C3 & E1 & E2 & E3 & G1 & G2 & G3) ].
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as Fa Fb Fc Fd Fe Ff Fg Fh Fi Fj Fk Fl | sf_fb; destruct sfP_ as (Fa & Fb & Fc & Fd & Fe & Ff & Fg & Fh & Fi & Fj & Fk & Fl) ]. unfold int31 in Fd, Fe, Ff, Fg, Fh, Fi, Fj.
unfold page_rest2P. cbv zeta. fold serial.
unfold low_cells, wz in LOW. pose proof OS as OS0. unfold stream_cells, wz in OS.
pose proof (u8arr_bound _ _ _ _ UB) as BDB.
pose proof (munch_refl [(aOS c, aOS c + 408)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
change (id (rw_cells rsegs m RERRNO [C4 errv])) in ERR. change (id (bytes_at rsegs m (x_P c) (to_bytes (x_payload c)))) in PAY.
unfold implM. iprefix. unfold hregs, wz.

zstep. zstep.
callx (eapply ogg_page_serialno_spec with (G := aOG c) (D := a_D x) (og := og) (hs := hs); [reflexivity| exact OG| exact HS| lia| exact MI]).
rewrite EHS in POST. fold serial in POST. lazymatch type of POST with ?v = _ => subst v end. unfold wz.

zstep. zstep. if_cases K1; zify_cond K1.
-
apply land64_inj_signed in K1; [| lia| lia].
replace (negb (serial =? os_serialno (h_os h))) with false by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; lia).
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st Q msx) end.
apply (K h); [| reflexivity| reflexivity|].
2:{ cbv zeta. fold serial. replace (negb (serial =? os_serialno (h_os h))) with false by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; lia). reflexivity. }
unfold PGP. do 16 eexists. exists F, fc, m, x, nbr, brem0. do 3 eexists. exists OP.
split; [unfold hregs, wz; reflexivity|]. split; [exact FRM|]. split; [exact SI1|]. split; [exact HRX|].
split; [exact LOK|]. split; [exact POK|]. split; [exact NN| exact PB].
-
assert (NE : serial <> os_serialno (h_os h)) by (intros E; apply K1; rewrite E; reflexivity).
replace (negb (serial =? os_serialno (h_os h))) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NE).
destruct (ogg_stream_reset_serialno (h_os h) serial) as [rr os'] eqn:ERES.

zstep. zstep.
callx (eapply ogg_page_serialno_spec with (G := aOG c) (D := a_D x) (og := og) (hs := hs); [reflexivity| exact OG| exact HS| lia| exact MI]).
rewrite EHS in POST. fold serial in POST. lazymatch type of POST with ?v = _ => subst v end. unfold wz.
zstep. zstep. zstep.
clear OS.
callx (eapply ogg_stream_reset_serialno_spec with (A := aOS c) (Bd := a_Bd x) (L := a_L x) (Gv := a_Gv x) (hdr := a_hdr x) (os := h_os h) (serialno := serial);
[exact LH| exact FOK| lia| lia| exact SERR| exact Z1| exact MI| exact OS0| exact ERES| reflexivity| reflexivity]).
rename PC into OS2. rename POST into FOK2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (m2 := mx) in * end.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG. unfold id in ERR, PAY.
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| side1| side1].
eapply (dec_piece_agree2 _ _ _ _ _ _ _ DRF AG) in DEC.
2:{ intros a (bb & Hbb & Ra). unfold dec_piece in DEC. destruct (h_st h); [| destruct DEC as [_ E']; rewrite E' in Hbb; destruct Hbb].
destruct DEC as (_ & _ & BRD). pose proof (BRD bb Hbb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4. cbn [outside fst snd]. lia. }
xport AG side1.
assert (HP2 : RHEAP st (a_LB x) m2).
{ eapply RHF; [exact HP| exact MU| exact WM|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
assert (AUX2 : rauxv_ok m2 (x_AB c)).
{ eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
assert (PE2 : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m2).
{ eapply (pres_except_frame RBR c _ _ _ _ _ _ CX HP); [exact HL0| exact PE| exact AG|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
first [ pose proof (stream_rep_reset m m2 c x h (h_oy h) serial rr os' OSP SERR ERES OS2 FOK2 UL UG UB) as sfP_; sf_destruct 9%nat sfP_ as SR2 FL2 FB2 ELS EBST EBD ELV EGV FLR2 | sf_fb; destruct (stream_rep_reset m m2 c x h (h_oy h) serial rr os' OSP SERR ERES OS2 FOK2 UL UG UB) as (SR2 & FL2 & FB2 & ELS & EBST & EBD & ELV & EGV & FLR2) ].
lazymatch goal with MIx : mem_inv rsegs m2 |- _ => rename MIx into MI2 end.
clearbody m2. clear MU WM AG HP AUX PE.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st Q msx) end.
set (h2 := set_ogg h (h_oy h) os').
apply (K h2); [| reflexivity| reflexivity|].
2:{ cbv zeta. fold serial. replace (negb (serial =? os_serialno (h_os h))) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NE).
rewrite ERES. reflexivity. }
unfold PGP. do 16 eexists. exists F, fc, m2, x, nbr, brem0. do 3 eexists. exists OP.
split; [unfold hregs, wz; reflexivity|]. split; [exact FRM|]. split; [exact SI1|].
split.
{ split; [exists j16, jsk, lk; split; [exact LOW| exact LKO]|]. split; [reflexivity|]. split; [reflexivity|]. split; [exists stb; exact STB|].
split; [unfold os_piece; cbn [h_stream_init h2 set_ogg]; rewrite SI1; cbn [Z.eqb]; exact SR2|].
split; [split; [exact OPK| exact OPS]|]. split; [split; [exact OG| exact OGS]|].
split; [exact SY|]. split; [exact BI|]. split; [exists pad; exact FSZ|]. split; [exists outb; split; [exact OUT| exact LOUT]|].
split; [exists hij; exact HI|]. split; [exact SAV|]. split; [exact DEC|].
split.
{ split; [exact HP2|]. split.
{ unfold owned in PERM |- *. cbn [h_st h_bits h_os h_oy h2 set_ogg]. rewrite EBD, ELV, EGV. exact PERM. }
split; [exact PAY|]. split; [exact TP|]. split; [exact SEW|]. split; [exists errv; exact ERR|]. split; [exact AUX2|].
split; [exact MI2|]. split; [assumption|]. split; [exact PE2| exact SO]. }
unfold hpure. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os h2 set_ogg].
repeat (split; [assumption|]).
unfold hbudget, hconsumed, hpend in BUD |- *. cbn [h_packet_count h_oy h_os h_bytes_remaining h2 set_ogg]. rewrite ELS, EBST. lia. }
split; [exact LOK|]. split; [exact POK|]. split; [exact NN|].
destruct PB as (cold & PB'). exists cold. unfold hconsumed, hpend in PB' |- *.
cbn [h_packet_count h_oy h_os h_bytes_remaining h2 set_ogg] in PB' |- *. rewrite ELS, EBST. lia.
Qed.
End PAGE3.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0om X0qn X0px X0qc X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fd X1fe X1m2 X1m3 X1m5 X1m6 X1ik X1ii X1ij X1iu X1it X1im X1ip X1iq X1ix X1iy X1iz X1j0 X1j1 X1j2 X1j3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1qx X1r3 X1r4 X1qz X1r0 X1nv X1r1.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section PAGEIN.
Context {RCEIL : RunCeiling}.
Variable rhdr_known : PState -> bptr -> Prop.
Hypothesis rhdr_known_indep : forall s s' p, rhdr_known s p -> rhdr_known s' p.
Hypothesis HR : ogg_realloc_stmt rhdr_known.
Hypothesis HF : rfree_stmt.

Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Variables (s : PState) (LB : list block) (os : stream_st bptr) (pb pl pg psy : bptr).
Variables (A G Dsy nsy Bd L Gv lo B : Z) (og : page) (shdr hs bs bodybytes : list byte) (lws gws : list word) (errv : word).

Hypothesis HP : RHEAP s LB m.
Hypothesis SB : stream_blocks LB os Bd L Gv.
Hypothesis Hpb : os_body_data os = Some pb.
Hypothesis Hpl : os_lacing_vals os = Some pl.
Hypothesis Hpg : os_granule_vals os = Some pg.
Hypothesis HINb : In (pb, Bd, os_body_storage os) LB.
Hypothesis HINl : In (pl, L, os_lacing_storage os * 4) LB.
Hypothesis HINg : In (pg, Gv, os_lacing_storage os * 8) LB.
Hypothesis HKb : rhdr_known s pb.
Hypothesis HKl : rhdr_known s pl.
Hypothesis HKg : rhdr_known s pg.
Hypothesis HINsy : In (psy, Dsy, nsy) LB.
Hypothesis NEb : psy <> pb.
Hypothesis NEl : psy <> pl.
Hypothesis NEg : psy <> pg.

Hypothesis OS : rw_cells rsegs m A (stream_cells Bd L Gv shdr os).
Hypothesis HL : length shdr = 284%nat.
Hypothesis ARR : stream_arrays m os Bd L Gv bodybytes lws gws.
Hypothesis FOK : stream_fields_ok os.
Hypothesis SINV : stream_inv os.
Hypothesis BINV : body_inv os.
Hypothesis LOK : lacing_vals_ok (os_lacing os).

Hypothesis OG : rw_cells rsegs m G (page_cells Dsy og).
Hypothesis HS : bytes_at rsegs m (Dsy + pg_hdr og) hs.
Hypothesis HBS : bytes_at rsegs m (Dsy + pg_hdr og + pg_header_len og) bs.
Hypothesis LENH : length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat.
Hypothesis HLEN : Z.of_nat (length hs) = pg_header_len og.
Hypothesis BSLEN : Z.of_nat (length bs) = pg_body_len og.
Hypothesis Hsum : zsum (lacing_of (ubytes hs)) <= pg_body_len og.
Hypothesis Hpg0 : 0 <= pg_hdr og.
Hypothesis PGIN : pg_hdr og + pg_header_len og + pg_body_len og <= nsy.

Hypothesis HboundL : (os_lacing_storage os + znth (ubytes hs) 26 + 33) * 8 < MMAP_THRESHOLD.
Hypothesis HboundB : os_body_storage os + pg_body_len og + 1024 < MMAP_THRESHOLD.
Hypothesis HBIG : 1024 <= os_lacing_storage os.

Hypothesis AUX : rauxv_ok m B.
Hypothesis SPB : bv_unsigned sp <= B.
Hypothesis SPA : bv_unsigned sp <= A.
Hypothesis AB : A + 408 <= B.
Hypothesis SPG : bv_unsigned sp <= G.
Hypothesis SEP_AG : A + 408 <= G \/ G + 32 <= A.
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 176 - OGG_REALLOC_STACK.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
#[local] Set Default Proof Using "HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP rhdr_known_indep HR HF".

Local Notation hdr := (ubytes hs).
Local Notation nseg := (znth (ubytes hs) 26).
Local Notation H := (Dsy + pg_hdr og).
Local Notation POST := (X1j2.pagein_post rhdr_known ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB pb pl pg A G Dsy lo B og shdr hs bs m).
Local Notation kept := (lb_remove pg (lb_remove pl (lb_remove pb LB))).
Local Notation os1 := (pagein_returned os).
Local Notation W1 := [(bv_unsigned sp - 144, bv_unsigned sp); (A, A + 408); (Bd, Bd + os_body_storage os);
(L, L + 4 * os_lacing_storage os); (Gv, Gv + 8 * os_lacing_storage os)].
Local Notation FRAME mm loc := (rw_cells rsegs mm (bv_unsigned sp + -144)
(loc ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
Local Notation LOC j0 := [CB 8 j0; C8 (wz (ogg_page_granulepos hdr)); C8 (Z_to_bv 64 (znth hdr 18)); C8 (Z_to_bv 64 (znth hdr 21)); C8 (Z_to_bv 64 (znth hdr 5))].

Local Notation Wc := [(bv_unsigned sp + -144 - 32, bv_unsigned sp + -144); (A, A + 408)].
Local Open Scope mspec_scope.
Local Notation blen := (pg_body_len og).
Local Notation Bp := (Dsy + pg_hdr og + pg_header_len og).

Local Notation facts_proof := (X1j2.facts_proof rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation kept_ids := (X1j2.kept_ids rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation sync_kept := (X1j2.sync_kept rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation callee_keeps := (X1j2.callee_keeps rhdr_known rhdr_known_indep HR HF ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation cmod_callee := (X1j2.cmod_callee rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation pi_fail_zero := (X1j2.pi_fail_zero rhdr_known rhdr_known_indep HR HF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation pi_finish := (X1j2.pi_finish rhdr_known rhdr_known_indep HR HF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation pi_fail1 := (X1j2.pi_fail1 rhdr_known rhdr_known_indep HR HF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation sep_BL := (X1j2.sep_BL rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation sep_BG := (X1j2.sep_BG rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation sep_LG := (X1j2.sep_LG rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation sep_SB := (X1j2.sep_SB rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation sep_SL := (X1j2.sep_SL rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation sep_SG := (X1j2.sep_SG rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation HP_phase1 := (X1j2.HP_phase1 rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation AUX_phase1 := (X1j2.AUX_phase1 rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation ERR_phase1 := (X1j2.ERR_phase1 rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation HBS_phase1 := (X1j2.HBS_phase1 rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation cmod_phase1 := (X1j2.cmod_phase1 rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation sb_os1 := (X1j2.sb_os1 rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation cmod_phaseW := (X1j2.cmod_phaseW rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation phaseW_keeps := (X1j2.phaseW_keeps rhdr_known rhdr_known_indep HR HF sp tp m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).
Local Notation pi_rest := (X1j3.pi_rest rhdr_known rhdr_known_indep HR HF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB os pb pl pg psy A G Dsy nsy Bd L Gv lo B og shdr hs bs bodybytes lws gws errv HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP).

Theorem ogg_stream_pagein_spec : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
implM rsegs (ogg_stream_pagein raw_realloc raw_free os hdr (ubytes bs)) s POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_pagein) fc None m (seg_rom rsegs)).
Proof.
intros.
pose proof ARR as sfP_; first [ sf_destruct 8%nat sfP_ as BODY BLEN BPRE LAC LPRE LLEN GRA GLEN | sf_fb; destruct sfP_ as (BODY & BLEN & BPRE & LAC & LPRE & LLEN & GRA & GLEN) ].
pose proof facts_proof as FA. unfold facts in FA. pose proof CEIL as CE. unfold alloc_ceiling in CE.
pose proof LO as LO'. unfold OGG_REALLOC_STACK in LO'.
pose proof (pagein_returned_inv os SINV) as sfP_; first [ sf_destruct 9%nat sfP_ as SINV1 Hret1 Elv1 Egv1 Ebd1 Els1 Ebs1 Esn1 Epn1 | sf_fb; destruct sfP_ as (SINV1 & Hret1 & Elv1 & Egv1 & Ebd1 & Els1 & Ebs1 & Esn1 & Epn1) ].
pose proof (pagein_returned_body_inv os SINV BINV) as sfP_; first [ sf_destruct 4%nat sfP_ as BINV1 Hbr1 Hbf1 Hlf1 | sf_fb; destruct sfP_ as (BINV1 & Hbr1 & Hbf1 & Hlf1) ].
pose proof (fields_ok_returned os FOK SINV ltac:(lia)) as FOK1.
pose proof FOK1 as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in F4, F5, F6, F7, F8, F9, F10.
pose proof SINV1 as sfP_; first [ sf_destruct 5%nat sfP_ as I1 I2 I3 I4 I5 | sf_fb; destruct sfP_ as (I1 & I2 & I3 & I4 & I5) ]. unfold zlength in I3, I4.
unfold A_ogg_stream_pagein. unfold ogg_stream_pagein. unfold ogg_stream_check. rewrite Hpb.

eapply implM_evt.
{ eapply (pi_prologue A G Dsy Bd L Gv lo og shdr hs os ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc);
try eassumption; try reflexivity.
all: try (unfold zlength; (clear - FA gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL CE SPG LENH HL bs shdr G BSLEN og PGIN HLEN LO'; lia)).
1: pose proof sep_BL; lia.
1: pose proof sep_BG; lia.
1: pose proof sep_LG; lia.
1: pose proof sep_SB; (clear - H FA PGIN Hpg0 BSLEN HLEN LENH HL gws lws bodybytes bs hs shdr og B lo Gv L Bd nsy Dsy A os sp RCEIL; lia).
1: pose proof sep_SL; (clear - H FA PGIN Hpg0 BSLEN HLEN LENH HL gws lws bodybytes bs hs shdr og B lo Gv L Bd nsy Dsy A os sp RCEIL; lia).
1: pose proof sep_SG; lia. }
intros ms1 PP. first [ sf_destruct 40%nat PP as x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m1 j0 bodybytes1 lws1 gws1 -> MU1 WM1 MI1 OS1 BODY1 BLEN1 BPRE1 LAC1 LPRE1 LLEN1 GRA1 GLEN1 FR1 HS1 OG1 ST1 | sf_fb; destruct PP as (x1 & x5 & x6 & x7 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x22 & x28 & x29 & x30 & x31 & m1 & j0 & bodybytes1 & lws1 & gws1 & -> & MU1 & WM1 & MI1 & OS1 & BODY1 & BLEN1 & BPRE1 & LAC1 & LPRE1 & LLEN1 & GRA1 & GLEN1 & FR1 & HS1 & OG1 & ST1) ].
pose proof (wpre_length _ _ LPRE1) as LL1.
pose proof (rw_cells_bound _ _ _ _ OS1) as AB1. unfold stream_cells in AB1. cbn [cells_size csize Nat.add] in AB1.
unfold implM. iprefix.
pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
unfold stream_cells, wz in OS1.

zstep. zstep. if_cases CSER; zify_cond CSER.
{
assert (NE : ogg_page_serialno hdr <> os_serialno os1) by (intros E; apply CSER; rewrite E; reflexivity).
replace (ogg_page_serialno hdr =? os_serialno os1) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [negb]. cbv iota.
apply evt_done. apply implM_ret.
eapply pi_fail1; try eassumption. }
apply land64_inj_signed in CSER; [| lia| lia].
replace (ogg_page_serialno hdr =? os_serialno os1) with true by (symmetry; apply Z.eqb_eq; symmetry; exact CSER). cbn [negb]. cbv iota.

zstep. if_cases CVER; zify_cond CVER; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CVER by lia.
{
unfold ogg_page_version. replace (0 <? znth hdr 4) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
apply evt_done. apply implM_ret.
eapply pi_fail1; try eassumption. }
unfold ogg_page_version. replace (0 <? znth hdr 4) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.

zstep. zstep. zstep.
apply evt_done. eapply implM_bind.
{ eapply (X1iq.os_lacing_expand_spec rhdr_known rhdr_known_indep HR HF) with (s := s) (LB := LB) (os := os1) (pl := pl) (pg := pg)
(needed := nseg + 1) (A := A) (Bd := Bd) (L := L) (Gv := Gv) (lo := lo) (B := B) (hdr := shdr) (lws := lws1) (gws := gws1) (errv := errv).
all: lazymatch goal with
| |- RHEAP _ _ _ => apply HP_phase1; assumption
| |- stream_blocks _ _ _ _ _ => exact sb_os1
| |- length shdr = _ => exact HL
| |- os_lacing_vals _ = _ => rewrite Elv1; exact Hpl
| |- os_granule_vals _ = _ => rewrite Egv1; exact Hpg
| |- In _ _ => rewrite ?Els1; assumption
| |- rhdr_known _ _ => assumption
| |- u32arr _ _ _ _ => exact LAC1
| |- u64arr _ _ _ _ => exact GRA1
| |- Z.of_nat _ = _ => rewrite ?Els1; assumption
| |- rauxv_ok _ _ => apply AUX_phase1; assumption
| |- stk _ _ _ _ => rewrite unsigned_lit by (clear - gws1 lws1 bodybytes1 CE FA gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL; lia); exact ST1
| |- alloc_ceiling <= _ => exact CEIL
| |- rw_cells _ _ (bv_unsigned tp + -164) _ => rewrite TP, unsigned_lit by (unfold RATP; lia); unfold RATP; apply ERR_phase1; assumption
| |- rw_cells _ _ A _ => exact OS1
| |- mem_inv _ _ => exact MI1
| |- tp = _ => exact TP
| |- _ = Z_to_bv 64 _ => reflexivity
| |- _ -> _ => intros _; rewrite ?Els1; unfold MMAP_THRESHOLD in *; (clear - AB1 LL1 gws1 lws1 bodybytes1 FA HboundL LENH HL gws lws bodybytes bs hs shdr B lo Gv L Bd nsy Dsy A os sp RCEIL; lia)
| |- _ => rewrite ?unsigned_lit by (clear - gws1 lws1 bodybytes1 CE FA gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL; lia); rewrite ?Els1; unfold OGG_REALLOC_STACK; (clear - gws1 lws1 bodybytes1 FA gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL GLEN1 F4 Els1 F5 LL1 LLEN1 I3 AB1 HBIG LENH HL bs shdr LO'; lia)
end. }
intros [r os2] ps2 ms2 Q1. unfold lacing_expand_post in Q1.
first [ sf_destruct 24%nat Q1 as y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 errv2 -> MI2 ST2 ERR2 AUX2 FA2 SO2 CASES | sf_fb; destruct Q1 as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & FA2 & SO2 & CASES) ].
rewrite unsigned_lit in ST2 by lia. cbn [fst snd] in CASES.
replace (ret_pc (Z_to_bv 64 199096)) with (Z_to_bv 64 199096) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
destruct CASES as [(-> & ql & qg & L' & Gv' & ljunk & gjunk & LB2 & Eos2 & Hls2a & Hls2b & Hls2c & LENl2 & LENg2 & HP2 & KEPT2
& HINl2 & HINg2 & SB2 & HKl2 & HKg2 & FRESH2 & BRl2 & BRg2 & CM2 & OS2 & LAC2 & GRA2 & PERM2)
| (-> & -> & LB2 & HP2 & SUB2 & KEPT2 & CM2 & OS2 & ELB2)].
2:{
replace (negb (-1 =? 0)) with true by reflexivity. cbv iota. apply implM_ret.
rewrite unsigned_lit in CM2 by lia.
assert (KEPTk : forall b, In b kept -> In b LB2).
{ intros b Hb. first [ pose proof (kept_ids b Hb) as sfP_; sf_destruct 4%nat sfP_ as Hb0 N1 N2 N3 | sf_fb; destruct (kept_ids b Hb) as (Hb0 & N1 & N2 & N3) ]. apply KEPT2; [exact Hb0| rewrite Ebd1, Hpb; congruence| exact N2| exact N3]. }
first [ pose proof (callee_keeps m1 m2 LB2 j0 CM2 KEPTk) as sfP_; sf_destruct 4%nat sfP_ as TF TH TB TG | sf_fb; destruct (callee_keeps m1 m2 LB2 j0 CM2 KEPTk) as (TF & TH & TB & TG) ].
specialize (TF FR1). specialize (TH HS1). specialize (TB (HBS_phase1 _ MU1)). specialize (TG OG1).
pose proof (cmod_callee m1 m2 LB2 (cmod_phase1 _ MU1 WM1) CM2 KEPTk) as CMk.
clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl rsegs m2) as WM.

zstep. if_cases CR; zify_cond CR; rewrite ?unsigned_lit, ?land_ones64 in CR by lia.
2:{ exfalso. unfold wz in CR. rewrite ?Z_to_bv_unsigned in CR. revert CR. vm_compute. congruence. }
rewrite TP, unsigned_lit in ERR2 by (unfold RATP; lia). unfold RATP in ERR2.
eapply pi_fail_zero; try eassumption.

rewrite ELB2, Ebd1, Hpb. cbn [lb_remove_opt]. rewrite (lbr_comm pl pb), (lbr_comm pg pb). apply Permutation_refl. }

replace (negb (0 =? 0)) with false by reflexivity. cbv iota.
rewrite unsigned_lit in CM2 by lia.
assert (KEPTk : forall b, In b kept -> In b (lb_remove pg (lb_remove pl LB))).
{ intros b Hb. first [ pose proof (kept_ids b Hb) as sfP_; sf_destruct 4%nat sfP_ as Hb0 N1 N2 N3 | sf_fb; destruct (kept_ids b Hb) as (Hb0 & N1 & N2 & N3) ]. apply lb_remove_keep; [| exact N3]. apply lb_remove_keep; [exact Hb0| exact N2]. }
first [ pose proof (callee_keeps m1 m2 _ j0 CM2 KEPTk) as sfP_; sf_destruct 4%nat sfP_ as TF TH TB TG | sf_fb; destruct (callee_keeps m1 m2 _ j0 CM2 KEPTk) as (TF & TH & TB & TG) ].
specialize (TF FR1). specialize (TH HS1). specialize (TB (HBS_phase1 _ MU1)). specialize (TG OG1). rename TF into FR2. rename TH into HS2. rename TB into HBS2. rename TG into OG2.
pose proof (cmod_callee m1 m2 _ (cmod_phase1 _ MU1 WM1) CM2 KEPTk) as CMk2.
assert (HINb2' : In (pb, Bd, os_body_storage os) (lb_remove pg (lb_remove pl LB))).
{ pose proof SB as sfP_; first [ sf_destruct 6%nat sfP_ as _ _ _ D12 D13 _ | sf_fb; destruct sfP_ as (_ & _ & _ & D12 & D13 & _) ]. apply lb_remove_keep; [| cbn; eapply D13; eassumption]. apply lb_remove_keep; [exact HINb| cbn; eapply D12; eassumption]. }
pose proof (KEPT2 _ HINb2') as HINb2.
assert (BODY2 : u8arr rsegs m2 Bd bodybytes1).
{ eapply cmod_u8arr; [exact CM2| exact BODY1| eapply (rclient_range_block _ _ pb Bd (os_body_storage os)); [exact HINb2'| lia| lia]| cbn [disjoint_from]; lia]. }
clear KEPTk HINb2' CM2.

pose proof SB as sfP_; first [ sf_destruct 6%nat sfP_ as _ _ _ D12 D13 _ | sf_fb; destruct sfP_ as (_ & _ & _ & D12 & D13 & _) ].
destruct (FRESH2 _ HINb ltac:(cbn; eapply D12; eassumption) ltac:(cbn; eapply D13; eassumption)) as [NEbl2 NEbg2]. cbn [blk_id fst] in NEbl2, NEbg2.
destruct (FRESH2 _ HINsy ltac:(cbn; exact NEl) ltac:(cbn; exact NEg)) as [NEsl2 NEsg2]. cbn [blk_id fst] in NEsl2, NEsg2.
pose proof SB2 as sfP_; first [ sf_destruct 6%nat sfP_ as _ _ _ _ _ D23' | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & D23') ]. assert (NElg2 : ql <> qg) by (eapply D23'; rewrite Eos2; reflexivity).
pose proof (KEPT2 _ (lb_remove_keep _ _ _ (lb_remove_keep _ _ _ HINsy ltac:(cbn; exact NEl)) ltac:(cbn; exact NEg))) as HINsy2.
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP2 HINl2 HINg2 ltac:(cbn; exact NElg2)) as SEP_LG2. cbn [blk_addr blk_size fst snd] in SEP_LG2.
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP2 HINb2 HINl2 ltac:(cbn; exact NEbl2)) as SEP_BL2. cbn [blk_addr blk_size fst snd] in SEP_BL2.
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP2 HINb2 HINg2 ltac:(cbn; exact NEbg2)) as SEP_BG2. cbn [blk_addr blk_size fst snd] in SEP_BG2.
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP2 HINsy2 HINl2 ltac:(cbn; exact NEsl2)) as SEP_SL2. cbn [blk_addr blk_size fst snd] in SEP_SL2.
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP2 HINsy2 HINg2 ltac:(cbn; exact NEsg2)) as SEP_SG2. cbn [blk_addr blk_size fst snd] in SEP_SG2.
pose proof BRl2 as sfP_; first [ sf_destruct 5%nat sfP_ as Bl1 Bl2 Bl3 Bl4 Bl5 | sf_fb; destruct sfP_ as (Bl1 & Bl2 & Bl3 & Bl4 & Bl5) ]. pose proof BRg2 as sfP_; first [ sf_destruct 5%nat sfP_ as Bg1 Bg2 Bg3 Bg4 Bg5 | sf_fb; destruct sfP_ as (Bg1 & Bg2 & Bg3 & Bg4 & Bg5) ]. unfold alloc_ceiling in Bl4, Bg4.
hide SEP_LG2. hide SEP_BL2. hide SEP_BG2. hide SEP_SL2. hide SEP_SG2. hide Bl5. hide Bg5.

assert (E2 : os_lacing os2 = os_lacing os1 /\ os_lacing_fill os2 = os_lacing_fill os1 /\ os_lacing_packet os2 = os_lacing_packet os1 /\
os_lacing_returned os2 = 0 /\ os_body os2 = os_body os1 /\ os_body_fill os2 = os_body_fill os1 /\
os_body_returned os2 = os_body_returned os1 /\ os_body_storage os2 = os_body_storage os /\
os_body_data os2 = Some pb /\ os_lacing_vals os2 = Some ql /\ os_granule_vals os2 = Some qg /\
os_pageno os2 = os_pageno os1).
{ rewrite Eos2. unfold set_blocks. cbn. rewrite Hret1, Ebs1, Ebd1, Hpb. repeat split; reflexivity. }
first [ sf_destruct 12%nat E2 as E2l E2lf E2lp E2lr E2b E2bf E2br E2bs E2bd E2lv E2gv E2pn | sf_fb; destruct E2 as (E2l & E2lf & E2lp & E2lr & E2b & E2bf & E2br & E2bs & E2bd & E2lv & E2gv & E2pn) ].
assert (INT31 : os_lacing_storage os2 < 2^31) by (rewrite ?Els1 in Hls2c; unfold MMAP_THRESHOLD in Hls2c; (clear - Bg1 Bl1 Hls2c gjunk ljunk Gv' L' os2 gws1 lws1 F4 Els1 FA gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL; lia)).
assert (FOK2 : stream_fields_ok os2).
{ rewrite Eos2. apply fields_ok_set_blocks; [exact FOK1| rewrite Ebs1; (clear - BLEN1 bodybytes1 F1 Ebs1 os; lia)| unfold int31; split; [(clear - Bg3 Bg1 Bl1 Hls2b gjunk ljunk Gv' L' os2 gws1 lws1 I3 Hlf1 FA gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL; lia)| exact INT31]]. }
pose proof (set_blocks_inv os1 (os_body_data os1) (os_body_storage os1) (Some ql) (Some qg) (os_lacing_storage os2) SINV1) as [SINV2 Hret2].
rewrite <- Eos2 in SINV2, Hret2. rewrite Hret1 in Hret2.
pose proof (set_blocks_body_inv os1 (os_body_data os1) (os_body_storage os1) (Some ql) (Some qg) (os_lacing_storage os2) BINV1) as BINV2.
rewrite <- Eos2 in BINV2.
pose proof (lacing_vals_ok_returned os LOK) as LOK1.
assert (LOK2 : lacing_vals_ok (os_lacing os2)) by (rewrite E2l; exact LOK1).

clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
unfold implM. iprefix.
zstep. if_cases CR; zify_cond CR; rewrite ?unsigned_lit, ?land_ones64 in CR by lia.
{ exfalso. apply CR. reflexivity. }
clear CR.

eapply evt_cut.
{ eapply (pi_unroll A Bd L' Gv' H lo shdr hs os2 (lws1 ++ ljunk) (gws1 ++ gjunk) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc _ j0);
try eassumption.
all: try (rewrite ?E2l, ?E2lf, ?E2lp, ?E2lr, ?E2bf; unfold zlength; (clear - gjunk ljunk gws1 lws1 bodybytes1 FA gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL Hls2b os2 I3 I2 F6 Bg1 Bl1 Gv' L' AB1 LL1 Hpg0 LENH HL bs shdr og Bl4 Bg4 PGIN BSLEN HLEN LO' CE F2 Hbf1; lia)).
1: unfold hideP in SEP_LG2; lia.
1: unfold hideP in SEP_SL2; (clear - Bg1 Bl1 SEP_SL2 gjunk ljunk Gv' L' os2 AB1 LL1 gws1 lws1 bodybytes1 FA PGIN Hpg0 BSLEN HLEN LENH HL gws lws bodybytes bs hs shdr og B lo Gv L Bd nsy Dsy A os sp RCEIL; lia).
1: unfold hideP in SEP_SG2; (clear - Bg1 Bl1 SEP_SG2 gjunk ljunk Gv' L' os2 AB1 LL1 gws1 lws1 bodybytes1 FA PGIN Hpg0 BSLEN HLEN LENH HL gws lws bodybytes bs hs shdr og B lo Gv L Bd nsy Dsy A os sp RCEIL; lia).
rewrite E2l. apply wpre_app_junk. exact LPRE1. }
intros ms3 UP. unfold unroll_post in UP.
first [ sf_destruct 24%nat UP as y5' y6' y7' y11' y12' y13' y14' y15' y16' y17' y28' m3 lws3 -> MU3 WM3 MI3 OS3 LAC3 LPRE3 LLEN3 GRA3 FR3 HS3 | sf_fb; destruct UP as (y5' & y6' & y7' & y11' & y12' & y13' & y14' & y15' & y16' & y17' & y28' & m3 & lws3 & -> & MU3 & WM3 & MI3 & OS3 & LAC3 & LPRE3 & LLEN3 & GRA3 & FR3 & HS3) ].
pose proof (pagein_unroll_inv os2 (ogg_page_pageno hdr) SINV2 Hret2) as sfP_; first [ sf_destruct 8%nat sfP_ as SINV3 Hret3 Elv3 Egv3 Ebd3 Els3 Ebs3 Hlf3 | sf_fb; destruct sfP_ as (SINV3 & Hret3 & Elv3 & Egv3 & Ebd3 & Els3 & Ebs3 & Hlf3) ].
pose proof (pagein_unroll_body_inv os2 (ogg_page_pageno hdr) SINV2 Hret2 BINV2) as (BINV3 & Hbf3 & Hbr3).
pose proof (body_inv_fill_nonneg _ BINV3) as Hbf3'.
pose proof SINV3 as sfP_; first [ sf_destruct 5%nat sfP_ as J1 J2 J3 J4 J5 | sf_fb; destruct sfP_ as (J1 & J2 & J3 & J4 & J5) ]. unfold zlength in J3, J4.
assert (FOK3 : stream_fields_ok (pagein_unroll os2 (ogg_page_pageno hdr))) by (apply fields_ok_unroll; [exact FOK2| exact SINV2| lia| lia]).
pose proof (lacing_vals_ok_unroll os2 (ogg_page_pageno hdr) LOK2) as LOK3.
pose proof (wpre_length _ _ LPRE3) as LL3.
set (os3 := pagein_unroll os2 (ogg_page_pageno hdr)) in *.

rewrite TP, unsigned_lit in ERR2 by (unfold RATP; lia). unfold RATP in ERR2.
first [ pose proof (phaseW_keeps m2 m3 ps2 LB2 pb ql qg Bd L' Gv' (os_lacing_storage os2) (os_body_storage os) errv2 bodybytes1
HP2 HINb2 HINl2 HINg2 HINsy2 NEbl2 NEbg2 NEsl2 NEsg2 MU3 WM3) as sfP_; sf_destruct 7%nat sfP_ as Tst Tog Thbs Terr Taux HP3 Tbody | sf_fb; destruct (phaseW_keeps m2 m3 ps2 LB2 pb ql qg Bd L' Gv' (os_lacing_storage os2) (os_body_storage os) errv2 bodybytes1
HP2 HINb2 HINl2 HINg2 HINsy2 NEbl2 NEbg2 NEsl2 NEsg2 MU3 WM3) as (Tst & Tog & Thbs & Terr & Taux & HP3 & Tbody) ].
pose proof (Tst ST2) as ST3. pose proof (Tog OG2) as OG3. pose proof (Thbs HBS2) as HBS3. pose proof (Terr ERR2) as ERR3.
pose proof (Taux AUX2) as AUX3. pose proof (Tbody BLEN1 BODY2) as BODY3. clear Tst Tog Thbs Terr Taux Tbody.

eapply evt_cut.
{ eapply (pi_skip A Bd L' Gv' H (H + pg_header_len og) (pg_body_len og) shdr hs os3 lws3 m3 sp gp tp F fc);
try eassumption; try (unfold zlength; (clear - lws3 gjunk ljunk gws1 lws1 bodybytes1 FA gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL LL3 os3 Bg1 Bl1 Gv' L' AB1 LL1 Hpg0 HLEN LENH HL bs shdr og PGIN; lia)). }
intros ms4 SK. revert SK. destruct (pagein_skip os3 hdr) as [[bos' segptr] skipped] eqn:ESK. intros SK.
unfold skip_exit in SK. first [ sf_destruct 8%nat SK as z10 z11 z12 z13 -> Hsk Hseg Hbos | sf_fb; destruct SK as (z10 & z11 & z12 & z13 & -> & Hsk & Hseg & Hbos) ].
cbv iota. rewrite !zlength_ubytes, !BSLEN.
apply evt_done.
assert (K3 : forall b, In b kept -> In b LB2).
{ intros b Hb. first [ pose proof (kept_ids b Hb) as sfP_; sf_destruct 4%nat sfP_ as Hb0 N1 N2 N3 | sf_fb; destruct (kept_ids b Hb) as (Hb0 & N1 & N2 & N3) ]. apply KEPT2. apply lb_remove_keep; [| exact N3]. apply lb_remove_keep; [exact Hb0| exact N2]. }
assert (FRK : forall b, In b kept -> blk_id b <> ql /\ blk_id b <> qg).
{ intros b Hb. first [ pose proof (kept_ids b Hb) as sfP_; sf_destruct 4%nat sfP_ as Hb0 N1 N2 N3 | sf_fb; destruct (kept_ids b Hb) as (Hb0 & N1 & N2 & N3) ]. exact (FRESH2 b Hb0 N2 N3). }
assert (CMk3 : cmod [(A, A + 408)] kept (bv_unsigned sp) m m3).
{ eapply cmod_trans; [exact CMk2|]. eapply (cmod_phaseW m2 m3 ps2 LB2 ql qg); try eassumption. }
assert (BPRE3 : body_pre (os_body os3) bodybytes1).
{ destruct (unroll_body os2 (ogg_page_pageno hdr)) as [E|E]; fold os3 in E.
- rewrite E, E2b. exact BPRE1.
- rewrite E, E2b. pose proof BINV1 as (Xb & _). unfold zlength in Xb. apply body_pre_ztake; [exact BPRE1| lia| unfold zlength; lia]. }
assert (SB3 : stream_blocks LB2 os3 Bd L' Gv') by (unfold stream_blocks in *; rewrite Ebd3, Elv3, Egv3; exact SB2).
eapply (pi_rest m3 ps2 LB2 errv2 os3 ql qg L' Gv' bodybytes1 lws3 (gws1 ++ gjunk) j0 bos' segptr skipped); try eassumption.
all: try (rewrite ?Ebd3, ?Elv3, ?Egv3, ?Ebs3, ?Els3; first [eassumption | reflexivity]).
all: try (eapply rhdr_known_indep; eassumption).
all: try (clear - Ebs3 E2bs os2 BLEN1 bodybytes1 FA gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp LL3 Hlf3 Els3 lws3 E2lf Hls2b gjunk ljunk gws1 lws1 RCEIL; lia).
rewrite Ebs3, E2bs. exact HINb2.

rewrite Ebs3, E2bs, Els3. eapply Permutation_trans; [exact PERM2|].
rewrite (lbr_comm pl pb), (lbr_comm pg pb).
apply (Permutation_trans (l' := (ql, L', os_lacing_storage os2 * 4) :: (qg, Gv', os_lacing_storage os2 * 8)
:: (pb, Bd, os_body_storage os) :: lb_remove pb (lb_remove pg (lb_remove pl LB)))).
- apply perm_skip. apply perm_skip. apply perm_hd_lbr.
+ apply nodup_ids_lbr. apply nodup_ids_lbr. exact (RHEAP_blocks_nodup_proof _ _ _ HP).
+ apply lbr_in. split; [apply lbr_in; split; [exact HINb| cbn; eapply D12; eassumption]| cbn; eapply D13; eassumption].
- apply Permutation_sym. apply (Permutation_middle [_; _]).
Qed.

End PAGEIN.

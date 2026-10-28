(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0om X0qn X0px X0qc X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fd X1fe X1m2 X1m3 X1m5 X1m6 X1ik X1ii X1ij X1iu X1it X1im X1ip X1iq X1ix X1iy X1iz X1j0 X1j1 X1j2.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1qx X1r3 X1r4 X1qz X1r0 X1nv X1r1.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac wl_unf := try unfold alloc_ceiling in *.
Local Ltac lia ::= lean_lia ltac:(wl_unf).

Ltac sf_lean_nofat := lazymatch goal with | |- _ \/ _ \/ _ => first [ X1bw.disj_lia | wl_unf; first [ X1bw.disj_lia | X1bw.cllia ] ] | |- _ => first [ X1bw.llia | wl_unf; first [ X1bw.llia | X1bw.disj_lia | X1bw.cllia | X1bw.false_lia ] ] end.
Local Ltac slia ::= first [ exact I | sf_lean_nofat | split; [ sf_lean_nofat | exact I ] ].

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

Lemma pi_rest : forall m3 ps2 LB2 (errv2 : word) (os3 : stream_st bptr) (ql qg : bptr) (L' Gv' : Z)
(bodybytes1 : list byte) (lws3 gws3 : list word) (j0 : list byte) (bos' segptr skipped : Z)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x22 x27 x29 x30 x31 : word),
mem_inv rsegs m3 -> stk rsegs m3 lo (bv_unsigned sp + -144) -> rw_cells rsegs m3 (316496 + -164) [C4 errv2] -> rauxv_ok m3 B ->
ps_fa ps2 = ps_fa s -> ps_so ps2 = ps_so s -> RHEAP ps2 LB2 m3 -> (forall b, In b kept -> In b LB2) ->
(forall b, In b kept -> blk_id b <> ql /\ blk_id b <> qg) ->
cmod [(A, A + 408)] kept (bv_unsigned sp) m m3 ->
rw_cells rsegs m3 A (stream_cells Bd L' Gv' shdr os3) ->
u8arr rsegs m3 Bd bodybytes1 -> Z.of_nat (length bodybytes1) = os_body_storage os3 -> body_pre (os_body os3) bodybytes1 ->
u32arr rsegs m3 L' lws3 -> wpre (os_lacing os3) lws3 -> Z.of_nat (length lws3) = os_lacing_storage os3 ->
u64arr rsegs m3 Gv' gws3 -> Z.of_nat (length gws3) = os_lacing_storage os3 ->
FRAME m3 (LOC j0) -> bytes_at rsegs m3 H hs -> bytes_at rsegs m3 Bp bs -> rw_cells rsegs m3 G (page_cells Dsy og) ->
os_body_data os3 = Some pb -> os_lacing_vals os3 = Some ql -> os_granule_vals os3 = Some qg ->
In (pb, Bd, os_body_storage os3) LB2 -> In (ql, L', os_lacing_storage os3 * 4) LB2 -> In (qg, Gv', os_lacing_storage os3 * 8) LB2 ->
rhdr_known ps2 pb -> rhdr_known ps2 ql -> rhdr_known ps2 qg -> stream_blocks LB2 os3 Bd L' Gv' ->
Permutation LB2 ((pb, Bd, os_body_storage os3) :: (ql, L', os_lacing_storage os3 * 4) :: (qg, Gv', os_lacing_storage os3 * 8) :: kept) ->
psy <> ql -> psy <> qg ->
stream_fields_ok os3 -> stream_inv os3 -> os_lacing_returned os3 = 0 -> body_inv os3 -> lacing_vals_ok (os_lacing os3) ->
os_lacing_fill os3 + nseg + 1 <= os_lacing_storage os3 -> os_lacing_storage os3 < 2^31 ->
os_body_storage os3 = os_body_storage os ->
pagein_skip os3 hdr = (bos', segptr, skipped) -> 0 <= skipped <= zsum (lacing_of hdr) -> 0 <= segptr <= nseg ->
(bos' = 0 \/ bos' = Z.land (znth hdr 5) 2) ->
implM rsegs
(' (r, os0) <- (if negb (blen - skipped =? 0) then
' (r, os0) <- os_body_expand raw_realloc raw_free os3 (blen - skipped) ;;
if negb (r =? 0) then mret (r, os0) else mret (0, pagein_body os0 (ubytes bs) skipped (blen - skipped))
else mret (0, os3)) ;;
if negb (r =? 0) then mret (-1, os0) else mret (0, pagein_segments os0 hdr bos' segptr))
ps2 POST
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 (znth hdr 5)) x10
x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (-1)) (Z_to_bv 64 (blen - skipped)) (Z_to_bv 64 (Bp + skipped)) (Z_to_bv 64 H) x22 (Z_to_bv 64 segptr) (Z_to_bv 64 (ogg_page_pageno hdr)) (Z_to_bv 64 bos') (Z_to_bv 64 nseg) x27 x28 x29 x30 x31)
F (Z_to_bv 64 (if blen - skipped =? 0 then 0x30afc else 0x30ac8)) fc None m3 (seg_rom rsegs)).
Proof.
intros until x31.
intros MI3 ST3 ERR3 AUX3 FA2 SO2 HP3 K3 FRK CM3 OS3 BODY3 BLEN3 BPRE3 LAC3 LPRE3 LLEN3 GRA3 GLEN3 FR3 HS3 HBS3 OG3
Hpb3 Hql3 Hqg3 HINb3 HINl3 HINg3 HKb3 HKl3 HKg3 SB3 PERM3 NEsl NEsg FOK3 SINV3 Hret3 BINV3 LOK3 Hls3 INT31 Ebs3 ESK Hsk Hseg Hbos.
pose proof facts_proof as FA. unfold facts in FA. pose proof CEIL as CE. unfold alloc_ceiling in CE. pose proof LO as LO'. unfold OGG_REALLOC_STACK in LO'.
pose proof SINV3 as sfP_; first [ sf_destruct 5%nat sfP_ as J1 J2 J3 J4 J5 | sf_fb; destruct sfP_ as (J1 & J2 & J3 & J4 & J5) ]. unfold zlength in J3, J4.
pose proof FOK3 as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in F4, F5, F6, F7, F8, F9, F10.
pose proof BINV3 as sfP_; first [ sf_destruct 4%nat sfP_ as Bi1 Bi2 Bi3 Bi4 | sf_fb; destruct sfP_ as (Bi1 & Bi2 & Bi3 & Bi4) ]. unfold zlength in Bi1. pose proof BPRE3 as [BP1 BP2].
pose proof (wpre_length _ _ LPRE3) as LL3.
destruct (Z.eqb_spec (blen - skipped) 0) as [EZ|NZ]; cbn [negb]; cbv iota.
-
apply implM_retb. replace (negb (0 =? 0)) with false by reflexivity. cbv iota. apply implM_ret.
eapply (pi_finish m3 ps2 LB2 errv2 os3 pb ql qg Bd L' Gv' bodybytes1 lws3 gws3 j0 segptr bos'); try eassumption; try lia.
-
pose proof SB3 as sfP_; first [ sf_destruct 6%nat sfP_ as _ _ _ D12 D13 D23 | sf_fb; destruct sfP_ as (_ & _ & _ & D12 & D13 & D23) ].
assert (NEbl : pb <> ql) by (eapply D12; eassumption). assert (NEbg : pb <> qg) by (eapply D13; eassumption). assert (NElg : ql <> qg) by (eapply D23; eassumption).
unfold implM. iprefix.
pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
pose proof (rw_cells_bound _ _ _ _ OS3) as AB3. unfold stream_cells in AB3. cbn [cells_size csize Nat.add] in AB3.
unfold stream_cells, wz in OS3.

zstep. zstep. zstep.
apply evt_done. apply implM_bind_assoc. eapply implM_bind.
{ eapply (X1ip.os_body_expand_spec rhdr_known HR HF) with (s := ps2) (LB := LB2) (os := os3) (pb := pb)
(needed := blen - skipped) (A := A) (Bd := Bd) (L := L') (Gv := Gv') (lo := lo) (B := B) (hdr := shdr) (bodybytes := bodybytes1) (errv := errv2).
all: lazymatch goal with
| |- RHEAP _ _ _ => exact HP3
| |- stream_blocks _ _ _ _ _ => exact SB3
| |- length shdr = _ => exact HL
| |- os_body_data _ = _ => exact Hpb3
| |- In _ _ => exact HINb3
| |- rhdr_known _ _ => exact HKb3
| |- rw_cells _ _ Bd _ => replace (Z.to_nat (os_body_storage os3)) with (length bodybytes1) by (clear - BP2 FA BLEN3 bodybytes1 os3 gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp; lia); apply rw_cells_of_u8arr; exact BODY3
| |- rauxv_ok _ _ => exact AUX3
| |- stk _ _ _ _ => rewrite unsigned_lit by (clear - AB3 CE FA LENH gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL; lia); exact ST3
| |- alloc_ceiling <= _ => exact CEIL
| |- rw_cells _ _ (bv_unsigned tp + -164) _ => rewrite TP, unsigned_lit by (unfold RATP; lia); unfold RATP; exact ERR3
| |- rw_cells _ _ A _ => exact OS3
| |- mem_inv _ _ => exact MI3
| |- tp = _ => exact TP
| |- _ = Z_to_bv 64 _ => reflexivity
| |- _ -> _ => intros _; unfold MMAP_THRESHOLD in *; (clear - NZ BP2 FA Hsk Ebs3 skipped bodybytes1 os3 HboundB BSLEN gws lws bodybytes bs hs og B lo Gv L Bd nsy Dsy A os sp; lia)
| |- _ => rewrite ?unsigned_lit by (clear - AB3 CE FA LENH gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL; lia); unfold OGG_REALLOC_STACK; (clear - NZ FA Hsk skipped PGIN Hpg0 Hsum HLEN gws lws bodybytes bs hs og B lo Gv L Bd nsy Dsy A os sp BP2 F1 Ebs3 bodybytes1 os3 F2 Bi1 BLEN3 AB3 SPB LENH RCEIL SPA AB LO'; lia)
end. }
intros [r os3'] ps3 ms4 Q. unfold body_expand_post in Q.
first [ sf_destruct 24%nat Q as v5 v6 v7 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 m4 errv4 -> MI4 ST4 ERR4 AUX4 FA4 SO4 CASES | sf_fb; destruct Q as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m4 & errv4 & -> & MI4 & ST4 & ERR4 & AUX4 & FA4 & SO4 & CASES) ].
rewrite unsigned_lit in ST4 by lia. cbn [fst snd] in CASES.
replace (ret_pc (Z_to_bv 64 199380)) with (Z_to_bv 64 199380) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
rewrite TP, unsigned_lit in ERR4 by (unfold RATP; lia). unfold RATP in ERR4.
destruct CASES as [(-> & q & Bd' & junk & LB4 & Eos3' & Hbs4a & Hbs4b & HP4 & KEPT4 & HINb4 & SB4 & HKq & FRESH4 & BRb4 & CM4 & OS4 & BLK4 & PERM4)
| (-> & -> & HP4 & CM4 & OS4)].
2:{
cbv beta iota. replace (negb (-1 =? 0)) with true by reflexivity. cbv iota.
apply implM_retb. cbv beta iota. replace (negb (-1 =? 0)) with true by reflexivity. cbv iota. apply implM_ret.
rewrite unsigned_lit in CM4 by lia.
assert (K4 : forall b, In b kept -> In b (stream_clear_LB LB2 os3)).
{ intros b Hb. first [ pose proof (kept_ids b Hb) as sfP_; sf_destruct 4%nat sfP_ as Hb0 N1 N2 N3 | sf_fb; destruct (kept_ids b Hb) as (Hb0 & N1 & N2 & N3) ]. destruct (FRK b Hb) as [N4 N5].
unfold stream_clear_LB. rewrite Hqg3, Hql3, Hpb3. cbn [lb_remove_opt].
apply lb_remove_keep; [| exact N5]. apply lb_remove_keep; [| exact N4]. apply lb_remove_keep; [apply K3; exact Hb| exact N1]. }
first [ pose proof (callee_keeps m3 m4 _ j0 CM4 K4) as sfP_; sf_destruct 4%nat sfP_ as TF TH TB TG | sf_fb; destruct (callee_keeps m3 m4 _ j0 CM4 K4) as (TF & TH & TB & TG) ].
specialize (TF FR3). specialize (TH HS3). specialize (TB HBS3). specialize (TG OG3).
pose proof (cmod_callee m3 m4 _ CM3 CM4 K4) as CMk4.
clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl rsegs m4) as WM.
zstep. if_cases CR; zify_cond CR; rewrite ?unsigned_lit, ?land_ones64 in CR by lia.
2:{ exfalso. unfold wz in CR. rewrite ?Z_to_bv_unsigned in CR. revert CR. vm_compute. congruence. }
eapply pi_fail_zero; try eassumption.
all: try first [rewrite FA4; exact FA2 | rewrite SO4; exact SO2].

unfold stream_clear_LB. rewrite Hqg3, Hql3, Hpb3. cbn [lb_remove_opt].
eapply Permutation_trans; [apply perm_lbr; apply perm_lbr; apply perm_lbr; exact PERM3|].
rewrite (lbr_hd3 pb ql qg); [apply Permutation_refl| exact NEbl| exact NEbg| exact NElg
| intros b Hb; exact (proj1 (proj2 (kept_ids b Hb)))
| intros b Hb; exact (proj1 (FRK b Hb))
| intros b Hb; exact (proj2 (FRK b Hb))]. }

cbv beta iota. replace (negb (0 =? 0)) with false by reflexivity. cbv iota.
apply implM_retb. cbv beta iota. replace (negb (0 =? 0)) with false by reflexivity. cbv iota. apply implM_ret.
rewrite unsigned_lit in CM4 by lia.
set (os4 := pagein_body os3' (ubytes bs) skipped (blen - skipped)).
assert (E4 : os_body_fill os3' = os_body_fill os3 /\ os_body os3' = os_body os3 /\ os_body_data os3' = Some q /\
os_lacing_vals os3' = Some ql /\ os_granule_vals os3' = Some qg /\ os_lacing os3' = os_lacing os3 /\
os_lacing_storage os3' = os_lacing_storage os3 /\ os_lacing_fill os3' = os_lacing_fill os3 /\
os_lacing_packet os3' = os_lacing_packet os3 /\ os_lacing_returned os3' = 0 /\ os_body_returned os3' = os_body_returned os3).
{ rewrite Eos3'. unfold set_blocks. cbn. rewrite Hql3, Hqg3, Hret3. repeat split; reflexivity. }
first [ sf_destruct 11%nat E4 as E4bf E4b E4bd E4lv E4gv E4l E4ls E4lf E4lp E4lr E4br | sf_fb; destruct E4 as (E4bf & E4b & E4bd & E4lv & E4gv & E4l & E4ls & E4lf & E4lp & E4lr & E4br) ].
pose proof BRb4 as sfP_; first [ sf_destruct 5%nat sfP_ as Bq1 Bq2 Bq3 Bq4 Bq5 | sf_fb; destruct sfP_ as (Bq1 & Bq2 & Bq3 & Bq4 & Bq5) ]. unfold alloc_ceiling in Bq4.
assert (K4 : forall b, In b kept -> In b (lb_remove pb LB2)).
{ intros b Hb. first [ pose proof (kept_ids b Hb) as sfP_; sf_destruct 4%nat sfP_ as Hb0 N1 N2 N3 | sf_fb; destruct (kept_ids b Hb) as (Hb0 & N1 & N2 & N3) ]. apply lb_remove_keep; [apply K3; exact Hb| exact N1]. }
first [ pose proof (callee_keeps m3 m4 _ j0 CM4 K4) as sfP_; sf_destruct 4%nat sfP_ as TF TH TB TG | sf_fb; destruct (callee_keeps m3 m4 _ j0 CM4 K4) as (TF & TH & TB & TG) ].
specialize (TF FR3). specialize (TH HS3). specialize (TB HBS3). specialize (TG OG3). rename TF into FR4. rename TH into HS4. rename TB into HBS4. rename TG into OG4.
pose proof (cmod_callee m3 m4 _ CM3 CM4 K4) as CMk4.
pose proof (lb_remove_keep pb _ _ HINl3 ltac:(cbn; congruence)) as HINl3'. pose proof (lb_remove_keep pb _ _ HINg3 ltac:(cbn; congruence)) as HINg3'.
pose proof (RHEAP_block_range_proof _ _ _ _ HP3 HINl3) as BRl. cbn [blk_addr blk_size fst snd] in BRl. unfold rblock_range, alloc_ceiling in BRl. first [ sf_destruct 5%nat BRl as Bl1 Bl2 Bl3 Bl4 Bl5 | sf_fb; destruct BRl as (Bl1 & Bl2 & Bl3 & Bl4 & Bl5) ].
pose proof (RHEAP_block_range_proof _ _ _ _ HP3 HINg3) as BRg. cbn [blk_addr blk_size fst snd] in BRg. unfold rblock_range, alloc_ceiling in BRg. first [ sf_destruct 5%nat BRg as Bg1 Bg2 Bg3 Bg4 Bg5 | sf_fb; destruct BRg as (Bg1 & Bg2 & Bg3 & Bg4 & Bg5) ].
assert (LAC4 : u32arr rsegs m4 L' lws3).
{ eapply cmod_u32arr; [exact CM4| exact LAC3| eapply (rclient_range_block _ _ ql L' (os_lacing_storage os3 * 4)); [exact HINl3'| (clear - gws3 lws3 L' RCEIL; lia)| (clear - Bg1 Bl1 LL3 FA LLEN3 gws3 lws3 Gv' L' os3 LENH gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL; lia)]| cbn [disjoint_from]; (clear - Bl4 Bl1 AB3 LL3 CE FA LLEN3 gws3 lws3 L' os3 SPG LENH gws lws bodybytes hs B lo Gv L Bd nsy Dsy G A os sp RCEIL; lia)]. }
assert (GRA4 : u64arr rsegs m4 Gv' gws3).
{ eapply cmod_u64arr; [exact CM4| exact GRA3| eapply (rclient_range_block _ _ qg Gv' (os_lacing_storage os3 * 8)); [exact HINg3'| (clear - gws3 lws3 Gv' RCEIL; lia)| (clear - Bg1 Bl1 LL3 FA GLEN3 gws3 lws3 Gv' L' os3 LENH gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL; lia)]| cbn [disjoint_from]; (clear - Bg4 Bg1 AB3 CE FA GLEN3 gws3 lws3 Gv' os3 SPG LENH gws lws bodybytes hs B lo Gv L Bd nsy Dsy G A os sp RCEIL; lia)]. }
pose proof (KEPT4 _ HINl3') as HINl4. pose proof (KEPT4 _ HINg3') as HINg4.
pose proof (KEPT4 _ (lb_remove_keep pb _ _ (K3 _ sync_kept) ltac:(cbn; exact NEb))) as HINsy4.
pose proof (FRESH4 _ HINl3 ltac:(cbn; congruence)) as NEql. cbn [blk_id fst] in NEql.
pose proof (FRESH4 _ HINg3 ltac:(cbn; congruence)) as NEqg. cbn [blk_id fst] in NEqg.
pose proof (FRESH4 _ (K3 _ sync_kept) ltac:(cbn; exact NEb)) as NEqs. cbn [blk_id fst] in NEqs.
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP4 HINsy4 HINb4 ltac:(cbn; exact NEqs)) as SEP_SB4. cbn [blk_addr blk_size fst snd] in SEP_SB4.
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP4 HINb4 HINl4 ltac:(cbn; congruence)) as SEP_BL4. cbn [blk_addr blk_size fst snd] in SEP_BL4.
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP4 HINb4 HINg4 ltac:(cbn; congruence)) as SEP_BG4. cbn [blk_addr blk_size fst snd] in SEP_BG4.
hide SEP_SB4. hide SEP_BL4. hide SEP_BG4. hide Bq5. hide Bl5. hide Bg5.
hide HS4. hide HBS4. hide LAC4. hide GRA4. hide ERR4. hide OG4.
clear MU WM. pose proof (munch_refl [(Bd' + os_body_fill os3, Bd' + os_body_fill os3 + (blen - skipped)); (A, A + 408)] m4) as MU. pose proof (wmono_refl rsegs m4) as WM.
pose proof (rw_cells_bound _ _ _ _ OS4) as AB4. unfold stream_cells in AB4. cbn [cells_size csize Nat.add] in AB4.
unfold stream_cells, wz in OS4. rewrite E4bf in OS4.

zstep. if_cases CR; zify_cond CR; rewrite ?unsigned_lit, ?land_ones64 in CR by lia.
{ exfalso. apply CR. reflexivity. }
clear CR.

zstep. zstep. zstep. zstep. zstep.

pose proof BLK4 as [[LENL0 _] _]. cbn in LENL0. destruct LENL0 as [LENL0 _]. rewrite app_length in LENL0.
pose proof BLK4 as BLK4'.
replace (Z.to_nat (os_body_storage os3')) with
(Z.to_nat (os_body_fill os3) + Z.to_nat (blen - skipped) + (Z.to_nat (os_body_storage os3') - Z.to_nat (os_body_fill os3) - Z.to_nat (blen - skipped)))%nat in BLK4' by (clear - LENL0 Bq1 Hbs4b junk Bd' os3' NZ BP2 Bi1 FA Hsk skipped bodybytes1 os3 Hsum gws lws bodybytes bs hs og B lo Gv L Bd nsy Dsy A os sp RCEIL; lia).
destruct (body_split3 _ _ _ _ _ _ BLK4') as (C1 & C2 & C3). clear BLK4'.
replace (Bd' + Z.of_nat (Z.to_nat (os_body_fill os3))) with (Bd' + os_body_fill os3) in C2 by lia.
unfold hideP in HBS4.
pose proof (bytes_at_sub m4 Bp bs (Z.to_nat skipped) (Z.to_nat (blen - skipped)) HBS4 ltac:(lia)) as SRC.
replace (Bp + Z.of_nat (Z.to_nat skipped)) with (Bp + skipped) in SRC by (clear - LENL0 AB4 Hbs4b junk os3' AB3 NZ Bi1 FA Hsk skipped bodybytes1 os3 Hsum BSLEN LENH gws lws bodybytes bs hs og B lo Gv L Bd nsy Dsy A os sp RCEIL; lia).
hide HBS4.

zstep.
unfold hideP in SEP_SB4.
call (memcpy_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(Bd' + os_body_fill os3) (Bp + skipped) (blen - skipped)
(firstn (Z.to_nat (blen - skipped)) (skipn (Z.to_nat skipped) bs)) _).
all: try exact SRC. all: try exact C2. all: try (rewrite firstn_length_le by (rewrite skipn_length; lia); lia). all: try (clear - LENL0 Bq2 Bq1 junk Bd' os3' BP2 Bi1 FA bodybytes1 os3 gws lws bodybytes bs hs B lo Gv L Bd nsy Dsy A os sp RCEIL Bq4 Bq3 Hbs4b NZ skipped og AB4 AB3 Hsk Hpg0 Hsum BSLEN HLEN LENH PGIN SEP_SB4; lia). all: try assumption.
hide SEP_SB4.
try (lazymatch goal with H0 : mem_inv X1fd.rsegs ?mm |- _ => change X1fd.rsegs with rsegs in H0 end).
try (lazymatch goal with H0 : rw_cells X1fd.rsegs ?mm ?a ?b |- _ => change (rw_cells rsegs mm a b) in H0 end).
try (lazymatch goal with H0 : bytes_at X1fd.rsegs ?mm ?a ?b |- _ => change (bytes_at rsegs mm a b) in H0 end).
lazymatch goal with H0 : rw_cells _ ?mm (Bd' + os_body_fill os3) _ |- _ => rename H0 into DST5 end.
lazymatch goal with H0 : bytes_at _ ?mm (Bp + skipped) _ |- _ => rename H0 into SRC5 end.

replace (Bd' + os_body_fill os3) with (Bd' + Z.of_nat (Z.to_nat (os_body_fill os3))) in DST5 by lia.
lazymatch type of C3 with rw_cells _ ?mm _ _ =>
destruct (body_merge3 mm Bd' _ _ _ _ _ _ C1 DST5 C3) as [BODY5 BLEN5];
pose proof (munch_refl [(A, A + 408)] mm) as MUs; pose proof (wmono_refl rsegs mm) as WMs end.
set (bb5 := firstn (Z.to_nat (os_body_fill os3)) (bodybytes1 ++ junk) ++ firstn (Z.to_nat (blen - skipped)) (skipn (Z.to_nat skipped) bs) ++
firstn (Z.to_nat (os_body_storage os3') - Z.to_nat (os_body_fill os3) - Z.to_nat (blen - skipped)) (skipn (Z.to_nat (blen - skipped)) (skipn (Z.to_nat (os_body_fill os3)) (bodybytes1 ++ junk)))) in *.
clear C1 C3 DST5.
assert (Ea : firstn (Z.to_nat (os_body_fill os3)) (ubytes bodybytes1 ++ ubytes junk) = os_body os3).
{ rewrite firstn_app. replace (Z.to_nat (os_body_fill os3) - length (ubytes bodybytes1))%nat with 0%nat by (rewrite ubytes_length; lia).
cbn [firstn]. rewrite app_nil_r. rewrite <- Bi1, Nat2Z.id. exact BP1. }
assert (BPRE5 : body_pre (os_body os4) bb5).
{ unfold os4, pagein_body, set_body. cbn [os_body]. rewrite E4b. split.
- subst bb5. rewrite !ubytes_app, !ubytes_firstn, !ubytes_skipn, !ubytes_app. rewrite Ea. unfold zslice, ztake, zdrop.
rewrite app_assoc, firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. reflexivity.
- rewrite BLEN5, app_length. unfold zslice, ztake, zdrop. rewrite firstn_length_le by (rewrite skipn_length, ubytes_length; (clear - BLEN5 bb5 LENL0 Hbs4b junk os3' NZ Bi1 FA Hsk skipped bodybytes1 os3 Hsum BSLEN gws lws bodybytes bs hs og B lo Gv L Bd nsy Dsy A os sp RCEIL; lia)). lia. }
assert (BLEN5z : Z.of_nat (length bb5) = os_body_storage os3') by lia.
clear BLEN5 LENL0 Ea. clearbody bb5. hide BODY5.

zstep. zstep. lstep.
unfold hideP in BODY5.
lazymatch type of MUs with munch ?Ws ?ma ?mb =>
pose proof (u8arr_transport rsegs Ws ma mb Bd' bb5 BODY5 MUs WMs ltac:(cbn [disjoint_from]; lia)) as BODY6 end.
clear BODY5 MUs WMs.

unfold hideP in HS4, HBS4, LAC4, GRA4, ERR4, OG4.
lazymatch type of MU with munch ?W6 m4 ?m6 =>
pose proof (bytes_at_transport rsegs W6 m4 m6 _ hs HS4 MU ltac:(unfold hideP in SEP_SB4; cbn [disjoint_from]; (clear - bb5 AB4 SEP_SB4 Bq4 Bq1 Hbs4b Bd' os3' AB3 NZ BP2 Bi1 CE FA Hsk skipped bodybytes1 os3 SPG PGIN Hpg0 Hsum BSLEN HLEN LENH gws lws bodybytes bs hs og B lo Gv L Bd nsy Dsy G A os sp RCEIL; lia))) as HS6;
pose proof (bytes_at_transport rsegs W6 m4 m6 _ bs HBS4 MU ltac:(unfold hideP in SEP_SB4; cbn [disjoint_from]; (clear - bb5 AB4 SEP_SB4 Bq4 Bq1 Hbs4b Bd' os3' AB3 NZ BP2 Bi1 CE FA Hsk skipped bodybytes1 os3 SPG PGIN Hpg0 Hsum BSLEN HLEN LENH gws lws bodybytes bs hs og B lo Gv L Bd nsy Dsy G A os sp RCEIL; lia))) as HBS6;
pose proof (u32arr_transport rsegs W6 m4 m6 L' lws3 LAC4 MU WM ltac:(unfold hideP in SEP_BL4; cbn [disjoint_from]; (clear - bb5 AB4 SEP_BL4 Bl4 Bl2 Bl1 Bq4 Bq2 Bq1 E4ls Hbs4b Bd' os3' AB3 NZ LL3 BP2 Bi1 CE FA Hsk LLEN3 skipped gws3 lws3 bodybytes1 L' os3 SPG Hsum LENH gws lws bodybytes bs hs og B lo Gv L Bd nsy Dsy G A os sp RCEIL; lia))) as LAC6;
pose proof (u64arr_transport rsegs W6 m4 m6 Gv' gws3 GRA4 MU WM ltac:(unfold hideP in SEP_BG4; cbn [disjoint_from]; (clear - bb5 AB4 SEP_BG4 Bg4 Bg2 Bg1 Bq4 Bq2 Bq1 E4ls Hbs4b Bd' os3' AB3 NZ BP2 Bi1 CE FA Hsk GLEN3 skipped gws3 lws3 bodybytes1 Gv' os3 SPG Hsum LENH gws lws bodybytes bs hs og B lo Gv L Bd nsy Dsy G A os sp RCEIL; lia))) as GRA6;
pose proof (rw_cells_transport rsegs W6 m4 m6 _ _ ERR4 MU WM ltac:(unfold hideP in Bq5; cbn [disjoint_from cells_size csize Nat.add]; (clear - bb5 AB4 Bq5 Bq1 Hbs4b Bd' os3' AB3 BP2 Bi1 CE FA skipped bodybytes1 os3 SPG LENH gws lws bodybytes bs hs og B lo Gv L Bd nsy Dsy G A os sp RCEIL; lia))) as ERR6;
pose proof (rw_cells_transport rsegs W6 m4 m6 G _ OG4 MU WM ltac:(unfold page_cells; cbn [disjoint_from cells_size csize Nat.add]; (clear - bb5 AB4 Bq4 Bq1 Hbs4b Bd' os3' AB3 BP2 CE FA skipped bodybytes1 os3 SEP_AG SPG LENH gws lws bodybytes bs hs og B lo Gv L Bd nsy Dsy G A os sp RCEIL; lia))) as OG6;
assert (AUX6 : rauxv_ok m6 B) by (unfold hideP in Bq5; eapply rauxv_ok_frame; [exact AUX4| exact MU| exact WM|];
repeat (apply Forall_cons; [cbn; unfold RAUXV_CELL; (clear - bb5 AB4 Bq5 Bq4 Bq1 Hbs4b Bd' os3' AB3 BP2 Bi1 CE FA skipped bodybytes1 os3 SPG SPB LENH gws lws bodybytes bs hs og B lo Gv L Bd nsy Dsy G A os sp RCEIL AB; lia)|]); apply Forall_nil);
assert (HP6 : RHEAP ps3 LB4 m6) by (eapply RHEAP_frame_proof; [exact HP4| exact MU| exact WM|];
apply Forall_cons; [right; right; exists (q, Bd', os_body_storage os3'); split; [exact HINb4| cbn; (clear - bb5 Hbs4b Bd' os3' BP2 F2 FA skipped bodybytes1 os3 gws lws bodybytes bs hs og B lo Gv L Bd nsy Dsy A os sp RCEIL; lia)]|];
apply Forall_cons; [left; cbn; (clear - AB4 AB3 CE FA SPG LENH gws lws bodybytes hs B lo Gv L Bd nsy Dsy G A os sp RCEIL; lia)|]; apply Forall_nil);
assert (CM6 : cmod [(A, A + 408)] kept (bv_unsigned sp) m m6)
end.
{ eapply cmod_trans; [exact CMk4|].
pose proof (cmod_of_munch _ kept (bv_unsigned sp) _ _ MU WM) as C.
apply (cmod_weaken _ [(Bd' + os_body_fill os3, Bd' + os_body_fill os3 + (blen - skipped)); (A, A + 408)] kept kept (bv_unsigned sp) (bv_unsigned sp)) in C;
[| lia| auto| unfold sub_fp; cbn [outside]; intros; lia].
apply cmod_drop_iv in C; [exact C| lia| unfold hideP in Bq5; lia|].
intros b Hb. first [ pose proof (kept_ids b Hb) as sfP_; sf_destruct 4%nat sfP_ as Hb0 N1 N2 N3 | sf_fb; destruct (kept_ids b Hb) as (Hb0 & N1 & N2 & N3) ].
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP4 (KEPT4 _ (lb_remove_keep pb _ _ (K3 _ Hb) N1)) HINb4 (FRESH4 _ (K3 _ Hb) N1)) as X.
cbn [blk_addr blk_size fst snd] in X. lia. }
clear HS4 HBS4 LAC4 GRA4 ERR4 OG4 AUX4.

assert (FOK3' : stream_fields_ok os3').
{ rewrite Eos3'. apply fields_ok_set_blocks; [exact FOK3| lia| unfold int31; lia]. }
assert (FOK4 : stream_fields_ok os4) by (apply fields_ok_body; [exact FOK3'| rewrite E4bf; (clear - bb5 AB4 Bg1 Bl1 Bq1 Bd' AB3 NZ LL3 BP2 Bi1 FA Hsk Ebs3 BLEN3 skipped gws3 lws3 bodybytes1 Gv' L' os3 PGIN Hpg0 Hsum HLEN LENH gws lws bodybytes bs hs og B lo Gv L Bd nsy Dsy A os sp RCEIL; lia)]).
pose proof (set_blocks_inv os3 (Some q) (os_body_storage os3') (os_lacing_vals os3) (os_granule_vals os3) (os_lacing_storage os3) SINV3) as [SINV3' _].
rewrite <- Eos3' in SINV3'.
pose proof (pagein_body_inv os3' (ubytes bs) skipped (blen - skipped) SINV3') as [SINV4 Hret4]. fold os4 in SINV4, Hret4. rewrite E4lr in Hret4.
assert (SB4' : stream_blocks LB4 os4 Bd' L' Gv') by (unfold stream_blocks in SB4 |- *; exact SB4).
rewrite E4ls, E4lf, E4lp, E4lr, E4br in OS4.
eapply (pi_finish _ ps3 LB4 errv4 os4 q ql qg Bd' L' Gv' bb5 lws3 gws3 j0 segptr bos'); try eassumption.
all: try (rewrite FA4; exact FA2). all: try (rewrite SO4; exact SO2).
all: try (intros b Hb; exact (KEPT4 _ (K4 _ Hb))).
all: try (eapply rhdr_known_indep; eassumption).
all: subst os4; unfold pagein_body, set_body; cbn [os_body_data os_body os_body_storage os_body_fill os_body_returned os_lacing_vals os_lacing os_granule_vals os_granules
os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos];
rewrite ?E4l, ?E4ls, ?E4lf, ?E4bf; try eassumption; try lia.
unfold stream_cells, wz. cbn [os_body_data os_body os_body_storage os_body_fill os_body_returned os_lacing_vals os_lacing os_granule_vals os_granules
os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos].
rewrite ?E4bf, ?E4ls, ?E4lf, ?E4lp, ?E4lr, ?E4br. exact OS4.

eapply Permutation_trans; [exact PERM4|]. rewrite Eos3'. cbn [os_body_storage set_blocks]. apply perm_skip.
eapply Permutation_trans; [apply perm_lbr; exact PERM3|].
rewrite (lbr_hd1_of3 pb ql qg); [apply Permutation_refl| exact NEbl| exact NEbg| intros b Hb; exact (proj1 (proj2 (kept_ids b Hb)))].
Qed.

End PAGEIN.

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
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1ik X1ij X1ii X1il X1im X1is X1ip X1iq X1in X1ja X1iu X1j8 X1j4 X1j9 X1it X1j2 X1iv X1iw.
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

Lemma s64_range' : forall v, -2^63 <= s64 v < 2^63.
Proof. intros v. unfold s64. pose proof (Z.mod_pos_bound (v + 2^63) (2^64) ltac:(lia)). lia. Qed.

Lemma count_lt255_bound : forall l, 0 <= count_lt255 l <= zlength l.
Proof.
induction l as [|v l IH]; [unfold zlength; cbn; lia|]. cbn [count_lt255]. rewrite zlength_cons.
destruct (v <? 255); lia.
Qed.
Lemma ogg_page_packets_range : forall hdr, 0 <= znth hdr 26 <= 255 -> 0 <= ogg_page_packets hdr <= 255.
Proof.
intros hdr Hn. unfold ogg_page_packets. pose proof (count_lt255_bound (zslice 27 (znth hdr 26) hdr)).
unfold zslice in *. pose proof (zlength_ztake_le_n (znth hdr 26) (zdrop 27 hdr) ltac:(lia)). lia.
Qed.

Lemma sgn64_pos : forall p, -2^63 <= p < 2^63 ->
((0 <? Z.land p 18446744073709551615) && (Z.land p 18446744073709551615 <? 9223372036854775808) = true <-> 0 < p).
Proof.
intros p Hp. rewrite land_ones64.
destruct (Z_lt_le_dec p 0).
- rewrite <- (Z.mod_add p 1 (2^64)) by lia. rewrite Z.mod_small by lia.
split; [| lia]. intros H. apply andb_prop in H. destruct H as [_ H]. apply Z.ltb_lt in H. lia.
- rewrite Z.mod_small by lia. rewrite Bool.andb_true_iff, !Z.ltb_lt. lia.
Qed.
Lemma sgn64_pos_t : forall p, -2^63 <= p < 2^63 ->
(0 <? Z.land p 18446744073709551615) && (Z.land p 18446744073709551615 <? 9223372036854775808) = true -> 0 < p.
Proof. intros p Hp H. apply (proj1 (sgn64_pos p Hp) H). Qed.
Lemma sgn64_pos_f : forall p, -2^63 <= p < 2^63 ->
(0 <? Z.land p 18446744073709551615) && (Z.land p 18446744073709551615 <? 9223372036854775808) = false -> p <= 0.
Proof. intros p Hp H. destruct (Z_lt_le_dec 0 p); [| lia]. apply (proj2 (sgn64_pos p Hp)) in l. rewrite l in H. discriminate. Qed.

Lemma land64_of_signed : forall p, -2^63 <= p < 2^63 ->
(0 <= p -> Z.land p 18446744073709551615 = p) /\ (p < 0 -> Z.land p 18446744073709551615 = p + 2^64).
Proof.
intros p Hp. rewrite land_ones64. split; intros H.
- apply Z.mod_small. lia.
- rewrite <- (Z.mod_add p 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Ltac unsign p HP :=
let L := fresh "L" in pose proof (land64_of_signed p HP) as L;
first [ rewrite (proj1 L) in * by plia | rewrite (proj2 L) in * by plia
| let Hn := fresh "Hn" in let Hq := fresh "Hq" in
destruct (Z_lt_le_dec p 0) as [Hn|Hq]; [rewrite (proj2 L Hn) in * | rewrite (proj1 L Hq) in *] ];
clear L.

Definition C640 : Z := 14411518807585587.
Lemma c640_eq : C640 = Z.quot 9223372036854775807 640.
Proof. reflexivity. Qed.

Ltac scond K :=
unfold bv_lts, bv_ltu, bv_eqb in K;
rewrite ?zb_signed_small in K by plia;
rewrite ?unsigned_lit in K by plia;
lazymatch type of K with
| negb ?x = true => apply (proj1 (Bool.negb_true_iff x)) in K
| negb ?x = false => apply (proj1 (Bool.negb_false_iff x)) in K
| _ => idtac
end;
lazymatch type of K with
| (?a <? ?b) = true => apply (proj1 (Z.ltb_lt a b)) in K
| (?a <? ?b) = false => apply (proj1 (Z.ltb_ge a b)) in K
| (?a =? ?b) = true => apply (proj1 (Z.eqb_eq a b)) in K
| (?a =? ?b) = false => apply (proj1 (Z.eqb_neq a b)) in K
| (?a <=? ?b) = true => apply (proj1 (Z.leb_le a b)) in K
| (?a <=? ?b) = false => apply (proj1 (Z.leb_gt a b)) in K
| _ => idtac
end.

Lemma zbv_sub_land : forall x y, Z_to_bv 64 (x + - Z.land y 18446744073709551615) = Z_to_bv 64 (x - y).
Proof.
intros x y. apply Z_to_bv_eqm. rewrite land_ones64.
replace (x + - (y mod 2^64)) with (x - y mod 2^64) by lia. apply Zminus_mod_idemp_r.
Qed.
Lemma zbv_neg_land : forall y, Z_to_bv 64 (- Z.land y 18446744073709551615) = Z_to_bv 64 (- y).
Proof.
intros y. apply Z_to_bv_eqm. rewrite land_ones64.
replace (- (y mod 2^64)) with (0 - y mod 2^64) by lia. rewrite Zminus_mod_idemp_r. f_equal.
Qed.
Lemma zbv_eqb_signed : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
intros a b Ha Hb. rewrite bv_eqb_Z, !Z_to_bv_unsigned.
change (bv_wrap 64 a) with (a mod 2^64). change (bv_wrap 64 b) with (b mod 2^64).
destruct (Z.eqb_spec a b) as [->|NE]; [apply Z.eqb_refl|].
apply Z.eqb_neq. intros E. apply NE. rewrite <- !land_ones64 in E. apply land64_inj_signed in E; lia.
Qed.

Lemma v_div_small : forall x y, -2^63 <= x < 2^63 -> 0 < y < 2^63 ->
v_div (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.quot x y).
Proof.
intros x y Hx Hy. unfold v_div. rewrite unsigned_lit by lia.
replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). unfold zsig. rewrite !zb_signed_small by lia. reflexivity.
Qed.

Lemma swrap32_u64_plus1 : forall e, -2^31 <= e -> e + 1 < 2^31 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 e) + 1) = e + 1.
Proof.
intros e H1 H2. rewrite Z_to_bv_unsigned. change (bv_wrap 64 e) with (e mod 2^64).
rewrite X1nj.swrap32_mod64_plus. apply X1nj.swrap32_small. lia.
Qed.

Lemma swrap32_land64_plus1 : forall e, -2^31 <= e -> e + 1 < 2^31 -> bv_swrap 32 (Z.land e 18446744073709551615 + 1) = e + 1.
Proof.
intros e H1 H2. rewrite land_ones64. rewrite X1nj.swrap32_mod64_plus. apply X1nj.swrap32_small. lia.
Qed.

Lemma s32_range' : forall v, -2^31 <= s32 v < 2^31.
Proof. intros v. unfold s32. pose proof (Z.mod_pos_bound (v + 2^31) (2^32) ltac:(lia)). lia. Qed.

Section PAGE5.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).
Notation PGG := (PGG dec_rep c).
Notation PK := (PK dec_rep c).
Notation KREST fuel' := (fun o : outcome bptr => match o with
| Returned => X1qx.mret Returned
| Cont h5 => page_loopP fuel' h5 end).

#[using="CX"] Lemma page_granule : forall (Q : outcome bptr -> PState -> machine_state -> Prop) fuel' h og st ms,
PGG h og st ms ->
(forall h' st' ms', CLN dec_rep c h' st' ms' ->
implM rsegs (X1qx.mbind (cleanupP h') (fun _ => X1qx.mret Returned)) st' Q ms') ->
(forall h4 st4 ms4, PK h4 st4 ms4 -> h_oy h4 = h_oy h -> h_bytes_remaining h4 = h_bytes_remaining h ->
implM rsegs (X1qx.mbind (packet_loopP (packet_fuel (h_os h4)) h4 0) (KREST fuel')) st4 Q ms4) ->
(forall h4 st4 ms4, PGN dec_rep c h4 st4 ms4 -> h_oy h4 = h_oy h -> h_bytes_remaining h4 = h_bytes_remaining h ->
implM rsegs (page_loopP fuel' h4) st4 Q ms4) ->
implM rsegs (page_restP fuel' (page_header (h_oy h) og) h) st Q ms.
Proof.
intros Q fuel' h og st ms PG KC KP KN.
first [ sf_destruct 31%nat PG as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x s0v nbr brem0 OP -> FRM SI1 HRX LOK POK NN | sf_fb; destruct PG as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & s0v & nbr & brem0 & OP & -> & FRM & SI1 & HRX & LOK & POK & NN) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HRX as sfP_; first [ sf_destruct 16%nat sfP_ as (j16 & lk & LOW) _ _ (stb & STB) OSP (OPK & OPS) (OG & OGS) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG PURE | sf_fb; destruct sfP_ as ((j16 & lk & LOW) & _ & _ & (stb & STB) & OSP & (OPK & OPS) & (OG & OGS) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
pose proof SYOK as (SYI2 & SYST & SYNUL). pose proof SYI2 as [SYI _].
assert (EOSB : 0 <= h_eos h <= 1) by lia. assert (SIB : 0 <= h_stream_init h <= 1) by lia.
assert (NUL : sy_data (h_oy h) = None -> a_D x = 0 /\ sy_storage (h_oy h) = 0).
{ intros ED. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT. rewrite ED in DAT. first [ sf_destruct 4%nat DAT as -> _ _ -> | sf_fb; destruct DAT as (-> & _ & _ & ->) ]. auto. }
assert (SYR : a_D x + sy_storage (h_oy h) <= alloc_ceiling /\ 0 <= a_D x).
{ destruct (sy_data (h_oy h)) eqn:ED.
- destruct (SYBLK ltac:(congruence)) as [(B1 & _ & _ & B4 & _) _]. lia.
- destruct (NUL eq_refl) as [-> ->]. unfold alloc_ceiling. lia. }
destruct SYR as [SYR D0].
pose proof (page_hs _ _ _ _ _ _ SY SYI POK NN) as sfP_; first [ sf_destruct 11%nat sfP_ as HS HBS LHS LBS EHS EBS HL27 NSEG PG0 PGE BL0 | sf_fb; destruct sfP_ as (HS & HBS & LHS & LBS & EHS & EBS & HL27 & NSEG & PG0 & PGE & BL0) ].
set (hs := firstn (Z.to_nat (pg_header_len og)) (skipn (Z.to_nat (pg_hdr og)) (a_sybytes x))) in *.
unfold page_restP, granule_step.
remember (ogg_page_granulepos (page_header (h_oy h) og)) as pgr eqn:Epgr.
remember (ogg_page_packets (page_header (h_oy h) og)) as pnp eqn:Epnp.
remember (ogg_page_eos (page_header (h_oy h) og)) as peos eqn:Epeos.
assert (PGR : -2^63 <= pgr < 2^63) by (rewrite Epgr; apply s64_range').
assert (PNPR : 0 <= pnp <= 255) by (rewrite Epnp, <- EHS; apply ogg_page_packets_range; exact NSEG).
unfold low_cells, wz in LOW. unfold fsz_cells, wz in FSZ.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold implM. iprefix. unfold hregs, wz.

zstep. zstep.
callx (eapply ogg_page_granulepos_spec with (G := aOG c) (D := a_D x) (og := og) (hs := hs); [reflexivity| exact OG| exact HS| lia| exact MI]).
rewrite EHS, <- Epgr in POST. lazymatch type of POST with ?v = _ => subst v end. unfold wz.
zstep.

zstep. zstep.
callx (eapply ogg_page_packets_spec with (G := aOG c) (D := a_D x) (og := og) (hs := hs); [reflexivity| exact OG| exact HS| lia| lia| exact MI]).
rewrite EHS, <- Epnp in POST. lazymatch type of POST with ?v = _ => subst v end. unfold wz.

assert (CLJ : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (s3v s5v : Z),
evt rsegs (fun ms1 => impl rsegs (at_node rsegs) ((X1qx.mbind (cleanupP h) (fun _ => X1qx.mret Returned)) st)
(epost (fun p ms2 => Q (fst p) (snd p) ms2)) ms1)
(MS (mkR y1 (Z_to_bv 64 (aLOW c)) (x_gp c) (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (h_eos h)) (Z_to_bv 64 (h_channels h))
y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (a_S x)) (Z_to_bv 64 s3v) (Z_to_bv 64 (h_packet_count h)) (Z_to_bv 64 s5v)
(Z_to_bv 64 (-3)) (Z_to_bv 64 (h_speex_serialno h)) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 (h_nframes h)) (Z_to_bv 64 s0v) y28 y29 y30 y31)
F (Z_to_bv 64 0x1c38c) fc None m (seg_rom rsegs))).
{ intros. zstep. zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st Q msx) end.
apply KC. unfold CLN. sf_eexists 23%nat. first [ unshelve sf_eexists 6%nat; [ exact (F) | exact (fc) | exact (m) | exact (x) | exact ((C8 (Z_to_bv 64 nbr))) | exact ((C8 (Z_to_bv 64 brem0))) | ] | sf_fb; exists F, fc, m, x, (C8 (Z_to_bv 64 nbr)), (C8 (Z_to_bv 64 brem0)) ].
split; [rewrite SI1; reflexivity|]. split; [exact FRM|]. eapply hrepx_hrep. exact HRX. }

assert (JOIN : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (s5v skip : Z),
-1 <= pgr ->
evt rsegs (fun ms1 => impl rsegs (at_node rsegs)
((X1qx.mbind (packet_loopP (packet_fuel (h_os (set_granule h pgr skip))) (set_granule h pgr skip) 0) (KREST fuel')) st)
(epost (fun p ms2 => Q (fst p) (snd p) ms2)) ms1)
(MS (mkR y1 (Z_to_bv 64 (aLOW c)) (x_gp c) (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (h_eos h)) (Z_to_bv 64 (h_channels h))
y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (a_S x)) (Z_to_bv 64 pgr) (Z_to_bv 64 (h_packet_count h)) (Z_to_bv 64 s5v)
(Z_to_bv 64 (-3)) (Z_to_bv 64 (h_speex_serialno h)) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 (h_nframes h)) (Z_to_bv 64 s0v) y28 y29 y30 y31)
F (Z_to_bv 64 0x1c110) fc None m (seg_rom rsegs))).
{ intros until skip. intros PGE1. set (h4 := set_granule h pgr skip).
assert (HR4 : hrep dec_rep c x h4 st m (C8 (Z_to_bv 64 nbr)) (C8 (Z_to_bv 64 brem0))).
{ apply hrepx_hrep with (OG := page_cells (a_D x) og) (OP := OP).
first [ sf_destruct 16%nat HRX as L1 C1 C2 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 (G1 & G2 & G3) PU | sf_fb; destruct HRX as (L1 & C1 & C2 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & (G1 & G2 & G3) & PU) ].
split; [exact L1|]. split; [exact C1|]. split; [exact C2|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|].
split; [exact L6|]. split; [exact L7|]. split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact L11|]. split; [exact L12|].
split; [split; [exact G1| split; [exact G2| exact G3]]|].
unfold hpure in PU |- *. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os h4 set_granule].
first [ sf_destruct 22%nat PU as U1 U2 U3 U4 U5 U6 U7 U8 U9 U10 U11 U12 U13 U14 U15 U16 U17 U18 U19 U20 U21 U22 | sf_fb; destruct PU as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & U11 & U12 & U13 & U14 & U15 & U16 & U17 & U18 & U19 & U20 & U21 & U22) ].
repeat (split; [assumption|]). split; [lia|]. repeat (split; [assumption|]). exact U22. }
zstep. if_cases BJ; scond BJ.
-
assert (E1 : h_eos h = 1) by lia.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st Q msx) end.
unfold packet_fuel. cbn [packet_loop]. cbn [h_eos h4 set_granule]. rewrite E1. cbn [Z.eqb negb].
apply implM_retb. apply KN; [| reflexivity| reflexivity].
unfold PGN. sf_eexists 16%nat. first [ unshelve sf_eexists 8%nat; [ exact (F) | exact (fc) | exact (m) | exact (x) | exact (s0v) | exact (s5v) | exact (nbr) | exact (brem0) | ] | sf_fb; exists F, fc, m, x, s0v, s5v, nbr, brem0 ].
split; [unfold hregs, wz; cbn [h_nframes h_last_granule h_packet_count h_speex_serialno h_channels h_eos h_stream_init h4 set_granule]; rewrite E1; reflexivity|].
split; [exact FRM|]. split; [exact SI1|]. split; [exact HR4| exact LOK].
-
assert (E0 : h_eos h = 0) by lia.
zstep. zstep. first [rewrite swrap32_small by plia| rewrite swrap32_u64_plus1 by plia| rewrite swrap32_land64_plus1 by plia].
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st Q msx) end.
apply KP; [| reflexivity| reflexivity].
unfold X1hg.PK. sf_eexists 16%nat. first [ unshelve sf_eexists 8%nat; [ exact (F) | exact (fc) | exact (m) | exact (x) | exact (s5v) | exact (nbr) | exact (brem0) | exact (s0v) | ] | sf_fb; exists F, fc, m, x, s5v, nbr, brem0, s0v ].
split; [unfold hregs, wz; cbn [h_nframes h_last_granule h_packet_count h_speex_serialno h_channels h_eos h_stream_init h_extra_headers h4 set_granule]; rewrite ?E0; reflexivity|].
split; [exact FRM|]. split; [exact SI1|]. split; [exact E0|]. split; [exact HR4| exact LOK]. }

pose proof (ro_cells_image rsegs m 0x10740 [Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 51; Z_to_bv 8 0]
MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as ROC. cbn [length] in ROC.
assert (PB1 : 0 <= pnp * h_granule_frame_size h <= 163200).
{ rewrite GFS. split; [apply Z.mul_nonneg_nonneg; lia|]. change 163200 with (255 * 640). apply Z.mul_le_mono_nonneg; lia. }
assert (PB2 : 0 <= pnp * h_granule_frame_size h * h_nframes h <= 1632000).
{ split; [apply Z.mul_nonneg_nonneg; lia|]. change 1632000 with (163200 * 10). apply Z.mul_le_mono_nonneg; lia. }
assert (GBLK : forall (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
0 < pgr -> h_frame_size h <> 0 -> (0 < h_last_granule h \/ pgr < INT64_MAX + h_last_granule h) ->
evt rsegs (fun ms1 => impl rsegs (at_node rsegs)
((match (let a := pnp * h_granule_frame_size h * h_nframes h in
let b := pgr - h_last_granule h in
if (a <? b) || (INT64_MAX ÷ 640 - a <? - b) || (INT64_MAX ÷ 640 <? a - b) then None
else let skip := s32 (h_frame_size h * (a - b) ÷ h_granule_frame_size h) in
if skip =? INT_MIN then None else Some (if negb (peos =? 0) then - skip else skip))
with
| Some skip => X1qx.mbind (packet_loopP (packet_fuel (h_os (set_granule h pgr skip))) (set_granule h pgr skip) 0) (KREST fuel')
| None => X1qx.mbind (cleanupP h) (fun _ => X1qx.mret Returned)
end) st)
(epost (fun p ms2 => Q (fst p) (snd p) ms2)) ms1)
(MS (mkR y1 (Z_to_bv 64 (aLOW c)) (x_gp c) (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (h_eos h)) (Z_to_bv 64 (h_channels h))
(Z_to_bv 64 pnp) (Z_to_bv 64 (h_frame_size h)) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (a_S x)) (Z_to_bv 64 pgr) (Z_to_bv 64 (h_packet_count h)) (Z_to_bv 64 (h_last_granule h))
(Z_to_bv 64 (-3)) (Z_to_bv 64 (h_speex_serialno h)) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 (h_nframes h)) (Z_to_bv 64 s0v) y28 y29 y30 y31)
F (Z_to_bv 64 0x1c0b8) fc None m (seg_rom rsegs))).
{ intros until y31. intros PG1 FSNZ CND.
assert (BR : -2^63 < pgr - h_last_granule h < 2^63) by (unfold INT64_MAX in CND; lia).
cbv zeta.

zstep. zstep. rewrite swrap32_small by lia. rewrite ?land64 by lia. zstep. zstep. rewrite zbv_sub_land.
change (INT64_MAX ÷ 640) with 14411518807585587.
set (av := pnp * h_granule_frame_size h * h_nframes h) in *. set (bvv := pgr - h_last_granule h) in *.
zstep. if_cases BE; scond BE.
-
replace (av <? bvv) with true by (symmetry; apply Z.ltb_lt; exact BE). apply CLJ.
- replace (av <? bvv) with false by (symmetry; apply Z.ltb_ge; exact BE).

zstep. zstep. zstep. zstep. rewrite ?zbv_sub_land, ?zbv_neg_land. zstep. if_cases BG; scond BG.
+
replace (14411518807585587 - av <? - bvv) with true by (symmetry; apply Z.ltb_lt; lia). apply CLJ.
+ replace (14411518807585587 - av <? - bvv) with false by (symmetry; apply Z.ltb_ge; lia).
replace (14411518807585587 <? av - bvv) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
rewrite (Z.mul_comm (h_frame_size h) (av - bvv)).
assert (XB : 0 <= (av - bvv) * h_frame_size h <= 14411518807585587 * 640).
{ split; [apply Z.mul_nonneg_nonneg; lia|]. apply Z.mul_le_mono_nonneg; lia. }
assert (QB : 0 <= (av - bvv) * h_frame_size h ÷ h_granule_frame_size h < 2^63).
{ rewrite Z.quot_div_nonneg by lia. split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with (m := 1 * 2^63); [lia|]. apply Z.mul_le_mono_nonneg_r; lia. }

zstep. rewrite ?zbv_sub_land. zstep. rewrite ?land64 by lia. zstep. zstep.
rewrite v_div_small by lia. zstep. rewrite ?unsigned_lit by lia. rewrite ?Z.add_0_r, <- ?s32_swrap. zstep.
pose proof (s32_range' ((av - bvv) * h_frame_size h ÷ h_granule_frame_size h)) as SR.
zstep. if_cases BH; rewrite zbv_eqb_signed in BH by lia.
*
unfold INT_MIN. rewrite BH. apply CLJ.
* unfold INT_MIN. rewrite BH.

zstep. zstep.
callx (eapply ogg_page_eos_spec with (G := aOG c) (D := a_D x) (og := og) (hs := hs); [reflexivity| exact OG| exact HS| lia| exact MI]).
zstep. apply JOIN. lia. }

zstep. if_cases BA; scond BA.
-
replace (0 <? pgr) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].

zstep. zstep. if_cases BB; scond BB.
+
replace (pgr <? -1) with true by (symmetry; apply Z.ltb_lt; lia). apply CLJ.
+ replace (pgr <? -1) with false by (symmetry; apply Z.ltb_ge; lia). apply JOIN. lia.
-
replace (0 <? pgr) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].

zstep. rewrite sx32_small by (unfold X1nj.int31; lia). zstep. if_cases BC; scond BC.
+
replace (h_frame_size h =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb andb].
replace (pgr <? -1) with false by (symmetry; apply Z.ltb_ge; lia).

zstep. zstep. if_cases BB; scond BB; [exfalso; lia|]. apply JOIN. lia.
+ replace (h_frame_size h =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb].

zstep. if_cases BD; scond BD.
*
replace (0 <? h_last_granule h) with true by (symmetry; apply Z.ltb_lt; lia). cbn [orb].
apply GBLK; [lia| lia| left; lia].
* replace (0 <? h_last_granule h) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].

zstep. zstep. zstep. zstep. if_cases BF; scond BF.
--
unfold INT64_MAX. replace (pgr <? 9223372036854775807 + h_last_granule h) with false by (symmetry; apply Z.ltb_ge; lia).
replace (pgr <? -1) with false by (symmetry; apply Z.ltb_ge; lia). apply JOIN. lia.
-- unfold INT64_MAX. replace (pgr <? 9223372036854775807 + h_last_granule h) with true by (symmetry; apply Z.ltb_lt; lia).
apply GBLK; [lia| lia| right; unfold INT64_MAX; lia].
Qed.
End PAGE5.

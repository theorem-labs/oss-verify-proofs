(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1bq X1br X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0qb X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1fr X1no X1h7 X1kd X1k9.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ij X1ii X1il X1im X1is X1ip X1iq X1in X1ja X1iu X1j8 X1j4 X1j9 X1it X1j2 X1iv X1iw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g3 X1g1 X1g6 X1g5 X1g2.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h9 X1gy X1hg X1hf X1hh X1hi X1gz X1gx.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require UbDec.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac wl_unf := try unfold alloc_ceiling in *.
Local Ltac lia ::= lean_lia ltac:(wl_unf).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma packet_bytes_eq : forall (os : stream_st bptr) op (ab : list byte),
take (length (os_body os)) (ubytes ab) = os_body os -> zlength (os_body os) = os_body_fill os ->
0 <= pk_off op -> 0 <= pk_bytes op -> pk_off op + pk_bytes op <= os_body_fill os ->
packet_data os op = ubytes (firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) ab)).
Proof.
intros os op ab PB BL O1 O2 O3. unfold packet_data, zslice, ztake, zdrop. unfold zlength in BL.
rewrite <- PB. unfold ubytes. rewrite skipn_firstn_comm, firstn_firstn, <- firstn_map, <- skipn_map.
f_equal. f_equal. lia.
Qed.

Lemma read_from_leaf : forall (realloc : bptr -> Z -> M PState (option bptr)) (notify warning : list Z -> M PState unit)
(b r : bits_st bptr) (pkt : list Z) (len : Z) (s s' : PState),
in_leaves (speex_bits_read_from realloc notify warning b pkt len s) (Ok (r, s')) ->
sb_buf_size b <= sb_buf_size r /\ sb_owner r = sb_owner b.
Proof.
intros realloc notify warning b r pkt len s s' H. unfold speex_bits_read_from in H.
apply in_leaves_mbind in H. first [ sf_destruct 4%nat H as [b1 n1] s1 H1 H2 | sf_fb; destruct H as ([b1 n1] & s1 & H1 & H2) ]. apply in_leaves_mret in H2. inversion H2; subst. cbn.
destruct (sb_buf_size b <? len) eqn:LT.
- apply in_leaves_mbind in H1. first [ rename H1 into sfR_; sf_destruct 4%nat sfR_ as u s2 _ H1 | sf_fb; destruct H1 as (u & s2 & _ & H1) ].
destruct (negb (sb_owner b =? 0)).
+ apply in_leaves_mbind in H1. first [ rename H1 into sfR_; sf_destruct 4%nat sfR_ as tmp s3 _ H1 | sf_fb; destruct H1 as (tmp & s3 & _ & H1) ]. destruct tmp as [q|].
* apply in_leaves_mret in H1. inversion H1; subst. cbn. apply Z.ltb_lt in LT. lia.
* apply in_leaves_mbind in H1. first [ rename H1 into sfR_; sf_destruct 4%nat sfR_ as u' s4 _ H1 | sf_fb; destruct H1 as (u' & s4 & _ & H1) ]. apply in_leaves_mret in H1. inversion H1; subst. lia.
+ apply in_leaves_mbind in H1. first [ rename H1 into sfR_; sf_destruct 4%nat sfR_ as u' s4 _ H1 | sf_fb; destruct H1 as (u' & s4 & _ & H1) ]. apply in_leaves_mret in H1. inversion H1; subst. lia.
- apply in_leaves_mret in H1. inversion H1; subst. lia.
Qed.

Lemma got_stderr_cell : forall m, rtables_pristine m -> rw_cells rsegs m BITS_GOT_STDERR [C8 (Z_to_bv 64 BITS_STDERR_VAR)].
Proof. intros m TP. apply rw_cells_of_pristine; [exact TP| cbn; tauto| unfold RTABLES_LO, BITS_GOT_STDERR; lia| unfold BITS_GOT_STDERR, RTABLES_HI; cbn; lia| vm_compute; reflexivity]. Qed.
Lemma stderr_var_cell : forall m, rtables_pristine m -> rw_cells rsegs m BITS_STDERR_VAR [C8 (Z_to_bv 64 BITS_RSTDERR)].
Proof. intros m TP. apply rw_cells_of_pristine; [exact TP| cbn; tauto| unfold RTABLES_LO, BITS_STDERR_VAR; lia| unfold BITS_STDERR_VAR, RTABLES_HI; cbn; lia| vm_compute; reflexivity]. Qed.

Definition hax_bits (x : hax) (LB' : list block) (Dc' : Z) : hax :=
HAX LB' (a_D x) (a_sybytes x) (a_Bd x) (a_L x) (a_Gv x) (a_nB x) (a_nL x) (a_nG x) (a_hdr x) (a_lws x) (a_gws x) (a_body x) Dc' (a_S x) (a_LBD x).

Lemma flag_ok : forall (a : bool) skip, -2^63 <= skip < 2^63 ->
Z_to_bv 64 (Z.land (Z.b2z a) (Z.b2z (Z.lxor (bv_unsigned (Z_to_bv 64 skip)) 9223372036854775808 <? 9223372036854775808))) = Z_to_bv 64 0
\/ (Z_to_bv 64 (Z.land (Z.b2z a) (Z.b2z (Z.lxor (bv_unsigned (Z_to_bv 64 skip)) 9223372036854775808 <? 9223372036854775808))) = Z_to_bv 64 1 /\ skip < 0).
Proof.
intros a skip R. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
rewrite UbDec.lxor_sign_mod by lia.
destruct (Z.ltb_spec (skip + 9223372036854775808) 9223372036854775808) as [L|L].
- destruct a; cbn; [right; split; [reflexivity| lia]| left; reflexivity].
- destruct a; cbn; left; reflexivity.
Qed.

Lemma signed32_range : forall b : bv 32, -2^31 <= bv_signed b < 2^31.
Proof. intros b. pose proof (bv_signed_in_range 32 b ltac:(lia)) as R. unfold bv_half_modulus, bv_modulus in R. cbn in R. lia. Qed.

Section PKT3.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis DECODE : rspx_decode_stmt dec_rep.
Hypothesis DSTEREO : rspx_decode_stereo_stmt.
Hypothesis FWE : fwritex_stderr_stmt.
Hypothesis FLS : stdio_write_flush_stmt.
Hypothesis HRR : bits_realloc_stmt rtop_known.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Hypothesis RTK : rheap_top_known_stmt.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).
Notation PK := (PK dec_rep c).
Notation PKE := (PKE dec_rep c).
Notation decode_loopP := (decode_loop io_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M).

#[using="DRF DECODE DSTEREO RHF RBR RND RBD CX"] Lemma frame_loop : forall {B} (n : nat) g d st ms (KK : dec_state bptr * bits_st bptr -> M PState B) (Q : B -> PState -> machine_state -> Prop),
FR dec_rep c g (Z.of_nat n) st ms -> h_st g = Some d -> (1 <= n)%nat -> Z.of_nat n <= h_nframes g ->
(forall d' b' st' ms', PKE (set_bits_st g b' (Some d') (h_eos g)) st' ms' -> implM rsegs (KK (d', b')) st' Q ms') ->
implM rsegs (X1qx.mbind (decode_loopP n d (h_bits g)) KK) st Q ms.
Proof.
induction n as [|n IH]; intros g d st ms KK Q FX ESt N1 NF KEXIT; [lia|].
cbn [decode_loop]. apply implM_bind_assoc.
eapply implM_bind; [eapply (decode_call dec_rep DECODE RHF RBR RND RBD c CX); [exact FX| exact ESt]|].
cbv beta. intros [[ret d'] b'] st' ms' sfH_; first [ sf_destruct 5%nat sfH_ as -> RET ECH EBS FX' | sf_fb; destruct sfH_ as (-> & RET & ECH & EBS & FX') ].
replace (decode_loopP n d' b') with (decode_loopP (Z.to_nat (Z.of_nat (S n) - 1)) d' b') by (f_equal; lia).
eapply (frame_rest dec_rep DRF DSTEREO RHF RBR RND RBD c CX (set_bits_st g b' (Some d') (h_eos g)) (Z.of_nat (S n)) ret d' st ms' KK Q).
- exact FX'.
- reflexivity.
- exact RET.
- cbn [h_nframes set_bits_st]. lia.
- intros st2 ms2 PE. apply KEXIT. exact PE.
- intros ms2 FX2 J2. replace (Z.to_nat (Z.of_nat (S n) - 1)) with n by lia.
apply (IH (set_bits_st g b' (Some d') (h_eos g)) d' st ms2 KK Q).
+ replace (Z.of_nat n) with (Z.of_nat (S n) - 1) by lia. exact FX2.
+ reflexivity.
+ lia.
+ cbn [h_nframes set_bits_st]. lia.
+ intros d'' b'' st3 ms3 PE. apply KEXIT. exact PE.
Qed.

#[using="DRF DECODE DSTEREO FWE FLS HRR RHF RBR RND RBD RTK CX"] Lemma data_path : pkt_path_stmt dec_rep c (fun h op => PKD dec_rep c h op).
Proof.
intros fuel' h op pn st ms br0 oy0 PB EOY EBR BUD' K.
first [ sf_destruct 45%nat PB as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 ogj gw pno s0w s3w -> FRM SI1 EOS0 SSE SNM1 HRX LOK OF1 OF2 OF3 OF4 BDNZ EOSR PNO S3E PCNZ PC1 | sf_fb; destruct PB as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & ogj & gw & pno & s0w & s3w & -> & FRM & SI1 & EOS0 & SSE & SNM1 & HRX & LOK & OF1 & OF2 & OF3 & OF4 & BDNZ & EOSR & PNO & S3E & PCNZ & PC1) ].
cbv beta in S3E. subst s3w.
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HRX as sfP_; first [ sf_destruct 16%nat sfP_ as (j16 & jsk & lk & LOW & LKOK) _ _ (stb & STB) OSP (OPK & OPS) (OG & OGS) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG PURE | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW & LKOK) & _ & _ & (stb & STB) & OSP & (OPK & OPS) & (OG & OGS) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
unfold os_piece in OSP. rewrite SI1 in OSP. cbn [Z.eqb] in OSP.
pose proof OSP as sfP_; first [ sf_destruct 34%nat sfP_ as OS LH FOK SINV BINV LOK' GOK UL UG UB W1 L1 L2 L3 PB1 PB2 N1 N2 N3 Z1 Z2 Z3 R1 R2 R3 C1 C2 C3 E1 E2 E3 G1 G2 G3 | sf_fb; destruct sfP_ as (OS & LH & FOK & SINV & BINV & LOK' & GOK & UL & UG & UB & W1 & L1 & L2 & L3 & PB1 & PB2 & N1 & N2 & N3 & Z1 & Z2 & Z3 & R1 & R2 & R3 & C1 & C2 & C3 & E1 & E2 & E3 & G1 & G2 & G3) ].
pose proof SINV as sfP_; first [ sf_destruct 5%nat sfP_ as I1 I2 I3 I4 I5 | sf_fb; destruct sfP_ as (I1 & I2 & I3 & I4 & I5) ]. pose proof BINV as (BL & _).
pose proof (RND _ _ _ HP) as ND.
unfold hbudget, hconsumed, hpend in BUD. pose proof L4K as L4K'. unfold MAX_FUZZ_SIZE in L4K'.

destruct (h_st h) as [d|] eqn:ESt; [| exfalso; lia].

destruct (os_body_data (h_os h)) as [pbody|] eqn:EBD; [| exfalso; exact (BDNZ eq_refl)]. clear BDNZ.
specialize (R1 ltac:(discriminate)). specialize (G1 ltac:(discriminate)).

unfold pkt_bodyP.
replace (h_packet_count h =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (h_packet_count h <=? 1 + h_extra_headers h) with false by (symmetry; apply Z.leb_gt; lia).
rewrite ESt. rewrite <- SSE, Z.eqb_refl, Bool.andb_true_r, EOS0.
set (eos' := if negb (pk_e_o_s op =? 0) then 1 else 0).
apply implM_bind_assoc.

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
assert (INBITS : In (sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h)) (a_LB x)).
{ apply HLo. unfold owned. apply in_app_iff; right. apply in_app_iff; left. left. reflexivity. }
assert (INBODY : In (pbody, a_Bd x, a_nB x) (a_LB x)).
{ apply HLo. unfold owned. rewrite EBD. do 2 (apply in_app_iff; right). apply in_app_iff; left. left. reflexivity. }
assert (HK : rtop_known st (sb_chars (h_bits h))) by (eapply RTK; [exact HP| exact INBITS| unfold RBIG; lia]).
pose proof (nodup_ids_perm _ _ PERM ND) as NDO.
assert (NEQ : pbody <> sb_chars (h_bits h)).
{ pose proof NDO as NDO'. unfold owned in NDO'. rewrite ESt, EBD in NDO'. cbn [opt_blk] in NDO'.
rewrite <- !app_assoc, !map_app in NDO'. apply NoDup_app_remove_l in NDO'. cbn [map app blk_id fst] in NDO'.
inversion NDO' as [|i1 k1 NI1 ND1]; subst. intros E. apply NI1. left. exact E. }
assert (INBODY' : In (pbody, a_Bd x, a_nB x) (lb_remove (sb_chars (h_bits h)) (a_LB x))).
{ apply lb_remove_keep; [exact INBODY| cbn; exact NEQ]. }
pose proof (got_stderr_cell m TP) as GOT1. pose proof (stderr_var_cell m TP) as GOT2.
unfold low_cells, wz in LOW.
unfold implM. iprefix. unfold hregs, wz.

zstep. first [rewrite swrap32_small by lia| rewrite swrap32_u64_plus1 by lia| rewrite swrap32_land64_plus1 by lia]. zstep. rewrite lts_succ_false by lia. cbv iota.
zstep. zstep. zstep. zstep. zstep.
rewrite Z.add_0_r. rewrite swrap32_small by lia.
unfold wz. rewrite (unsigned_lit (pk_e_o_s op)) by lia.
replace (Z.b2z (0 <? pk_e_o_s op)) with eos'.
2:{ subst eos'. destruct (Z.eqb_spec (pk_e_o_s op) 0) as [E0|NE]; [rewrite E0; reflexivity|].
replace (0 <? pk_e_o_s op) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }

zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st (PKPOST dec_rep c br0 oy0) msx) end.
eapply implM_bind.
{ eapply implM_leaves.
eapply (speex_bits_read_from_std FWE FLS rtop_known HRR RHF RBR RBD RND) with
(A := aBITS c) (P := a_Bd x + pk_off op) (D := a_Dc x) (len := pk_bytes op) (pb := pb) (b := h_bits h)
(LB := a_LB x) (lo := x_lo c) (B := x_AB c) (pblk := (pbody, a_Bd x, a_nB x));
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ exact HP | exact INBITS | exact HK | exact BI | exact BOK | exact OWN | lazymatch goal with |- X0qc.RBIG <= _ => unfold X0qc.RBIG; plia end | exact SRC | exact INBODY' | exact AUX | exact ST | exact MI | exact FRM | exact SEW | exact GOT1 | exact GOT2 | reflexivity
| unfold READ_FROM_DEPTH, READ_FROM_LEN_MAX, alloc_ceiling in *; cbn [blk_addr blk_size fst snd]; lia
| unfold RATP; rewrite unsigned_lit by lia; exact ERR ]. }
cbv beta. intros b1 st1 ms1 [PO LEAF].
pose proof (read_from_leaf _ _ _ _ _ _ _ _ _ LEAF) as [BSZ1 LOWN]. clear LEAF.
first [ sf_destruct 33%nat PO as y0 y1 y2 e0 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 Ft fc1 m1 errv1 -> MI1 ST1 ERR1 AUX1 FRM1 FOK10 PEX EFA ESO SE1 OWN1 HK1 (D1 & HP1 & BR1 & BI1 & BOK1) | sf_fb; destruct PO as (y0 & y1 & y2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & Ft & fc1 & m1 & errv1 & -> & MI1 & ST1 & ERR1 & AUX1 & FRM1 & FOK10 & PEX & EFA & ESO & SE1 & OWN1 & HK1 & (D1 & HP1 & BR1 & BI1 & BOK1)) ].
rewrite ?(unsigned_lit (aLOW c)) in ST1 by lia. rewrite ?(unsigned_lit (aLOW c)) in PEX by lia.
unfold RATP in ERR1. rewrite ?unsigned_lit in ERR1 by lia. change (0x4d450 + -164) with RERRNO in ERR1.
replace (ret_pc (Z_to_bv 64 0x1c44c)) with (Z_to_bv 64 0x1c44c) by (symmetry; rpc).
pose proof (agree_of_pres_except _ _ _ _ PEX) as AG.

set (LB1 := (sb_chars b1, D1, sb_buf_size b1) :: lb_remove (sb_chars (h_bits h)) (a_LB x)) in *.
set (x' := hax_bits x LB1 D1). set (g1 := set_bits_st h b1 (Some d) eos').

set (P := fun a => rclient_addr (lb_remove (sb_chars (h_bits h)) (a_LB x)) (aLOW c) a /\ ~ in_ivs (read_from_X (aBITS c)) a) in AG.
assert (PF' : forall a, (aLOW c <= a < aBITS c \/ aBITS c + 48 <= a < usp c) -> P a).
{ intros a Ha. subst P. cbv beta. split; [left; lia|]. unfold read_from_X, BITS_RSTDERR. cbn [in_ivs fst snd]. lia. }
set (restS := stream_blks x h ++ opt_blk (sy_data (h_oy h)) (a_D x) (sy_storage (h_oy h))).
assert (EOWN : owned x h = a_LBD x ++ (sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h)) :: restS).
{ unfold owned, restS, stream_blks. rewrite ESt. rewrite <- !app_assoc. reflexivity. }
assert (IDNE : forall bb, In bb (a_LBD x ++ restS) -> blk_id bb <> sb_chars (h_bits h)).
{ intros bb Hbb E. pose proof NDO as NDO'. rewrite EOWN, <- app_assoc, map_app in NDO'. cbn [map app] in NDO'.
apply in_app_iff in Hbb. destruct Hbb as [Hbb|Hbb].
- eapply (nodup_app_disj _ _ (blk_id bb) NDO'); [apply in_map; exact Hbb| left; cbn; symmetry; exact E].
- apply NoDup_app_remove_l in NDO'. inversion NDO' as [|i1 k1 NI1 ND1']; subst. apply NI1. cbn [blk_id fst snd]. rewrite <- E.
rewrite map_app. apply in_app_iff. left. apply in_map. exact Hbb. }
assert (OWNK : forall bb a, In bb (a_LBD x ++ restS) -> blk_addr bb <= a < blk_addr bb + blk_size bb -> P a).
{ intros bb a Hbb Ra. assert (Hbb' : In bb (a_LB x)). { apply HLo. rewrite EOWN. apply in_app_iff in Hbb. apply in_app_iff. destruct Hbb; [left; assumption| right; right; assumption]. }
pose proof (RBR _ _ _ _ HP Hbb') as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 B5 | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & B5) ]. unfold alloc_ceiling in B4.
subst P. cbv beta. split.
- right; right. exists bb. split; [apply lb_remove_keep; [exact Hbb'| apply IDNE; exact Hbb]| exact Ra].
- unfold read_from_X, BITS_RSTDERR. cbn [in_ivs fst snd]. lia. }

assert (PERM1 : Permutation LB1 (owned x' g1 ++ x_LB0 c)).
{ assert (EO1 : owned x' g1 = a_LBD x ++ (sb_chars b1, D1, sb_buf_size b1) :: restS).
{ unfold owned, restS, stream_blks, x', g1, hax_bits. cbn. rewrite <- !app_assoc. reflexivity. }
rewrite EO1. subst LB1.
pose proof (perm_lb_remove (a_LB x) (a_LBD x) (sb_chars (h_bits h)) (a_Dc x) (sb_buf_size (h_bits h)) (restS ++ x_LB0 c) ND) as PR.
rewrite EOWN, <- app_assoc in PERM. cbn [app] in PERM. specialize (PR PERM).
rewrite <- app_assoc. cbn [app]. eapply Permutation_trans; [apply perm_skip; exact PR|]. apply Permutation_middle. }

eapply (rw_cells_agree _ _ _ _ _ _ AG) in LOW; [| intros a Ha; apply PF'; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in STB; [| intros a Ha; apply PF'; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OPK; [| intros a Ha; apply PF'; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OG; [| intros a Ha; apply PF'; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in FSZ; [| intros a Ha; apply PF'; unfold fsz_cells in Ha; cbn in Ha; lia].
eapply (u8arr_agree _ _ _ _ _ AG) in OUT; [| intros a Ha; apply PF'; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in HI; [| intros a Ha; apply PF'; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in SAV; [| intros a Ha; apply PF'; cbn in Ha; lia].
assert (OSP1 : os_piece m1 c x' g1).
{ unfold os_piece, x', g1, hax_bits. cbn [h_stream_init h_os set_bits_st]. rewrite SI1. cbn [Z.eqb].
eapply (stream_rep_agree2 _ _ _ _ _ _ AG); [exact OSP| intros a Ha; apply PF'; lia|].
intros a (bb & Hbb & Ra). apply (OWNK bb a); [| exact Ra]. apply in_app_iff. right. unfold restS. apply in_app_iff. left. exact Hbb. }
assert (SY1 : sync_rep m1 (aOY c) (a_D x) (h_oy h) (a_sybytes x)).
{ eapply (sync_rep_agree _ _ _ _ _ _ _ AG SY); [intros a Ha; apply PF'; lia|].
intros a Ha. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT.
destruct (sy_data (h_oy h)) as [q|] eqn:ESD; [| first [ sf_destruct 4%nat DAT as _ _ _ ST0 | sf_fb; destruct DAT as (_ & _ & _ & ST0) ]; rewrite SYLEN, ST0 in Ha; lia].
apply (OWNK (q, a_D x, sy_storage (h_oy h)) a); [| cbn; rewrite <- SYLEN; lia].
apply in_app_iff. right. unfold restS. apply in_app_iff. right. cbn. left. reflexivity. }
assert (DEC1 : dec_piece dec_rep m1 c x' g1).
{ unfold dec_piece, x', g1, hax_bits in DEC |- *. cbn [h_st set_bits_st a_S a_LBD] in DEC |- *. rewrite ESt in DEC.
destruct DEC as (DR & SB & BRD). split; [| split; [exact SB| exact BRD]].
eapply DRF; [exact DR|]. intros a Ha HIB. apply AG; [exact Ha|]. destruct HIB as (bb & Hbb & Ra). apply (OWNK bb a); [apply in_app_iff; left; exact Hbb| exact Ra]. }
assert (HG1 : hglob c x' g1 st1 m1).
{ split; [exact HP1|]. split; [exact PERM1|].
split. { eapply (pay_keep c _ _ _ CX AG PAY). intros NE IN a Ha. subst P. cbv beta. split.
- right; right. exists (x_pb c, x_P c, zlength (x_payload c)). split; [| cbn; lia].
eapply in_lb_remove_LB0; [exact ND| exact PERM| | exact IN]. rewrite EOWN, map_app. apply in_app_iff. right. left. reflexivity.
- pose proof (RBR _ _ _ _ HP (HL0 _ IN)) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 B5 | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & B5) ]. cbn [blk_addr blk_size fst snd] in B4, B5. unfold alloc_ceiling in B4.
unfold read_from_X, BITS_RSTDERR. cbn [in_ivs fst snd]. lia. }
split. { eapply rtables_pristine_agree; [exact AG| | exact TP]. intros a Ha. subst P. cbv beta. split.
- right; left. unfold RTABLES_LO, RTABLES_HI, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
- unfold read_from_X, BITS_RSTDERR, RTABLES_LO, RTABLES_HI in *. cbn [in_ivs fst snd]. lia. }
split; [exact SE1|]. split; [exists errv1; exact ERR1|]. split; [exact AUX1|]. split; [exact MI1|]. split; [exact ST1|].
split. { eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP); [exact HL0| exact PE| exact AG|].
intros a Hc Hout Hx. subst P. cbv beta. destruct Hc as [Hc|[Hc|(bb & Hbb & Rbb)]].
- split; [left; lia|]. unfold read_from_X, BITS_RSTDERR. cbn [in_ivs fst snd]. lia.
- split; [right; left; exact Hc|]. unfold read_from_X, BITS_RSTDERR. cbn [in_ivs fst snd].
intros [X1|[X2|[]]]; [lia|]. apply Hx. cbn. left. cbn. exact X2.
- split. { right; right. exists bb. split; [| exact Rbb]. eapply in_lb_remove_LB0; [exact ND| exact PERM| | exact Hbb]. rewrite EOWN, map_app. apply in_app_iff. right. left. reflexivity. }
pose proof (RBR _ _ _ _ HP (HL0 _ Hbb)) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 B5 | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & B5) ]. unfold alloc_ceiling in B4.
unfold read_from_X, BITS_RSTDERR. cbn [in_ivs fst snd]. lia. }
rewrite ESO. exact SO. }
destruct (rw_cells_forget _ _ _ _ OPK) as [opj' OP']. cbn [cells_size csize Nat.add] in OP'.
assert (HR1 : hrep dec_rep c x' g1 st1 m1 (C8 (Z_to_bv 64 nbr)) (C8 (Z_to_bv 64 brem0))).
{ split. { exists j16, jsk, lk. split; [unfold low_cells, wz, g1; cbn [h_extra_headers h_granule_frame_size h_last_granule h_rate set_bits_st]; exact LOW| unfold lk_ok, g1; cbn [h_st set_bits_st]; intros _; apply LKOK; rewrite ESt; discriminate]. }
split; [reflexivity|]. split; [reflexivity|]. split; [exists stb; exact STB|]. split; [exact OSP1|].
split; [exists opj'; exact OP'|]. split; [exists ogj; exact OG|].
split; [exact SY1|]. split; [exact BI1|]. split; [exists pad; exact FSZ|]. split; [exists outb; split; [exact OUT| exact LOUT]|].
split; [exists hij; exact HI|]. split; [exact SAV|]. split; [exact DEC1|]. split; [exact HG1|].
unfold hpure, g1, x', hax_bits. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os set_bits_st a_D a_sybytes a_Dc].
split; [exact SYOK|]. split; [exact BOK1|]. split; [exact OWN1|]. split; [exact SYBLK|]. split; [exact SYLEN|].
split; [exact BR1|]. split; [lia|].
do 10 (split; [assumption|]).
split; [subst eos'; destruct (pk_e_o_s op =? 0); cbn; lia|].
split; [exact BRR|]. split; [exact L4K|]. split; [lia|].
unfold hbudget, hconsumed, hpend. cbn [h_packet_count h_oy h_os h_bytes_remaining set_bits_st]. exact BUD. }
assert (EOSB : 0 <= eos' <= 1) by (subst eos'; destruct (pk_e_o_s op =? 0); cbn; lia).
clear AG PEX OSP SY BI DEC HG PAY TP SEW ERR AUX MI ST PE HP.
unfold implM. iprefix.

zstep. if_cases BN; scond BN; [exfalso; lia|].
zstep. zstep. zstep. zstep. zstep. zstep. zstep.
set (skip := bv_signed (bv_extract 0 32 (le_bytes_to_word (take 4 (drop 0 jsk))))).
pose proof (signed32_range (bv_extract 0 32 (le_bytes_to_word (take 4 (drop 0 jsk))))) as SKR. fold skip in SKR.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st1 (PKPOST dec_rep c br0 oy0) msx) end.
apply implM_bind_assoc.
eapply (frame_loop (Z.to_nat (h_nframes h)) g1 d st1 _ _ (PKPOST dec_rep c br0 oy0)).
- unfold FRC. sf_eexists 16%nat. first [ unshelve sf_eexists 8%nat; [ exact (Ft) | exact (fc1) | exact (m1) | exact (x') | exact (nbr) | exact (brem0) | exact (pno) | exact (skip) | ] | sf_fb; exists Ft, fc1, m1, x', nbr, brem0, pno, skip ].
eexists.
split; [unfold hregs, wz, g1, x', hax_bits; cbn [h_nframes h_last_granule h_packet_count h_speex_serialno h_channels h_eos h_stream_init h_extra_headers set_bits_st a_S];
rewrite Z2Nat.id, Z.sub_diag by lia; reflexivity|].
split; [exact I|]. split; [exact FRM1|]. split; [exact SI1|]. split; [unfold g1; cbn [h_packet_count set_bits_st]; lia|].
split; [exact HR1|]. split; [unfold low_ok, g1 in LOK |- *; cbn [h_bytes_remaining set_bits_st]; exact LOK|].
split; [exact SKR|]. split; [unfold g1; cbn [h_packet_count set_bits_st]; lia|].
split; [apply flag_ok; lia|].
unfold g1. unfold hconsumed, hpend in BUD' |- *. cbn [h_packet_count h_os h_oy h_bytes_remaining set_bits_st]. exact BUD'.
- reflexivity.
- lia.
- unfold g1. cbn [h_nframes set_bits_st]. lia.
- intros d' b' st' ms' PE'. cbv beta. apply implM_retb. cbv beta iota.
eapply (pk_tail dec_rep c fuel' (set_bits_st h b' (Some d') eos') (pn + 1) st' ms' br0 oy0); [exact PE'| exact EOY| exact EBR|].
intros st2 ms2 PK2. apply (K _ (pn + 1) st2 ms2 PK2); [exact EOY| exact EBR| cbn [h_os incr_packet_count set_bits_st]; lia].
Qed.
End PKT3.


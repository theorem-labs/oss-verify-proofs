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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ij X1ii X1il X1im X1is X1ip X1iq X1in X1ja X1iu X1j8 X1j4 X1j9 X1it.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g3 X1g1 X1g6 X1g5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gy X1gn X1gt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CLEANI.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis RFREE : rfree_stmt.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).
Notation POSTQ := (fun (r : Z) st ms => harness_post (x_ra c) (x_sp c) (x_gp c) tpv (x_s0 c) (x_s1 c) (x_s2 c) (x_s3 c) (x_s4 c) (x_s5 c)
(x_s6 c) (x_s7 c) (x_s8 c) (x_s9 c) (x_s10 c) (x_s11 c) (x_st0 c) (x_LB0 c) (x_AB c) (x_lo c) (x_m0 c) r st ms).
Notation cleanupP := (cleanup raw_free (St:=PState)).

Definition CLI (h : hstate bptr) (x : hax) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 q8 q9 a0 a1 a2 a3 a4 a5 a6 a7 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block),
ms = MS (mkR x1 (wz (hsp c)) (x_gp c) tpv t0 t1 t2 q8 q9 a0 a1 a2 a3 a4 a5 a6 a7 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
F (wz 0x1c75c) fc None m (seg_rom rsegs)
/\ frm0 fc /\ h_st h = None /\ h_stream_init h = 1
/\ stk rsegs m (x_lo c) (hsp c)
/\ RHEAP st LB m /\ List.NoDup (map blk_id LB)
/\ Permutation LB ((sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h)) :: stream_blks x h
++ opt_blk (sy_data (h_oy h)) (a_D x) (sy_storage (h_oy h)) ++ x_LB0 c)
/\ bits_rep rsegs m (aBITS c) (a_Dc x) (h_bits h) /\ bits_ok (h_bits h) /\ sb_owner (h_bits h) = 1
/\ rblock_range (a_Dc x) (sb_buf_size (h_bits h))
/\ stream_rep m c x h
/\ sync_rep m (aOY c) (a_D x) (h_oy h) (a_sybytes x) /\ hsync_ok (h_oy h)
/\ (sy_data (h_oy h) <> None -> rblock_range (a_D x) (sy_storage (h_oy h)))
/\ cl_junk c m /\ rw_cells rsegs m (aSAV c) (sav_cells c)
/\ cl_glob c st m.

Notation HFINQ := (fun (_ : unit) st ms => HFIN c st ms).

#[using="RFREE RBR RND CX"] Lemma clean_inl : forall h x st ms, CLI h x st ms -> implM rsegs (cleanupP h) st HFINQ ms.
Proof.
intros h x st ms CC. set (Q := HFINQ).
first [ sf_destruct 51%nat CC as x1 t0 t1 t2 q8 q9 a0 a1 a2 a3 a4 a5 a6 a7 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 F fc m LB -> FRM EST SI1 ST HP ND PERM BI BOK OWN BBR OSP SY SYOK SYBLK JK SAV GL | sf_fb; destruct CC as (x1 & t0 & t1 & t2 & q8 & q9 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & q18 & q19 & q20 & q21 & q22 & q23 & q24 & q25 & q26 & q27 & t3 & t4 & t5 & t6 & F & fc & m & LB & -> & FRM & EST & SI1 & ST & HP & ND & PERM & BI & BOK & OWN & BBR & OSP & SY & SYOK & SYBLK & JK & SAV & GL) ].
pose proof GL as sfP_; first [ sf_destruct 6%nat sfP_ as SEW (errv & ERR) AUX MI PE SO | sf_fb; destruct sfP_ as (SEW & (errv & ERR) & AUX & MI & PE & SO) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
assert (HL0 : forall b, In b (x_LB0 c) -> In b LB).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. cbn [app]. right. rewrite !in_app_iff. right. right. exact Hb. }
unfold cleanup, h_decoder_destroy. rewrite EST, SI1. cbn [Z.eqb negb].
apply implM_retb.
unfold implM. iprefix. unfold wz.

zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st Q msx) end.
eapply implM_bind.
{ eapply (speex_bits_destroy_spec RFREE) with (A := aBITS c) (D := a_Dc x) (nD := sb_buf_size (h_bits h)) (lo := x_lo c) (B := x_AB c) (LB := LB) (b := h_bits h);
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ exact HP | exact AUX | exact ST | exact MI | exact BI | exact BOK | exact OWN | reflexivity | lia
| unfold RATP; rewrite unsigned_lit by lia; exact ERR
| unfold RFREE_STACK; lia
| idtac ].
eapply Permutation_in; [apply Permutation_sym; exact PERM|]. left. reflexivity. }
cbv beta. intros [] st1 ms1 PO.
first [ sf_destruct 25%nat PO as y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 m1 -> MI1 ST1 ERR1 AUX1 HPR EFA ESO HP1 | sf_fb; destruct PO as (y0 & y1 & y2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m1 & -> & MI1 & ST1 & ERR1 & AUX1 & HPR & EFA & ESO & HP1) ].
rewrite ?(unsigned_lit (aLOW c)) in ST1 by lia. rewrite ?(unsigned_lit (aLOW c)) in HPR by lia.
unfold RATP in ERR1. rewrite ?unsigned_lit in ERR1 by lia. change (0x4d450 + -164) with RERRNO in ERR1.
replace (ret_pc (Z_to_bv 64 0x1c764)) with (Z_to_bv 64 0x1c764) by (symmetry; rpc).
pose proof (agree_of_rheap_pres _ _ _ _ HPR) as AG.
pose proof (perm_lb_remove LB [] _ _ _ _ ND PERM) as PERM1. cbn [app] in PERM1.
pose proof (RND _ _ _ HP1) as ND1.
set (LB1 := lb_remove (sb_chars (h_bits h)) LB) in *.
assert (HL1 : forall b, In b (x_LB0 c) -> In b LB1).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM1|]. rewrite !in_app_iff. right. right. exact Hb. }
destruct BI as ((rj & Lrj & BIJ) & _ & _). apply rw_cells_forget in BIJ. rewrite (bits_cells_size _ _ _ Lrj) in BIJ. destruct BIJ as [bij BIJ].
pose proof SY as sfP_; first [ sf_destruct 4%nat sfP_ as SYC SYF DAT SYSEP | sf_fb; destruct sfP_ as (SYC & SYF & DAT & SYSEP) ].
clear ERR MI ST AUX SY.
eapply (stream_rep_agree2 _ _ _ _ _ _ AG) in OSP; [| side1|].
2:{ intros a (bb & Hbb & Ra). right; right. exists bb. split; [| exact Ra].
eapply Permutation_in; [apply Permutation_sym; exact PERM1|]. rewrite !in_app_iff. left. exact Hbb. }
assert (SY1 : sync_rep m1 (aOY c) (a_D x) (h_oy h) (a_sybytes x)).
{ split; [eapply rw_cells_agree; [exact AG| exact SYC| side1]|]. split; [exact SYF|]. split; [| exact SYSEP].
unfold sync_data in DAT |- *. destruct (sy_data (h_oy h)) as [p|] eqn:ED; [| exact DAT].
first [ sf_destruct 5%nat DAT as D1 ARR D3 D4 D5 | sf_fb; destruct DAT as (D1 & ARR & D3 & D4 & D5) ]. split; [exact D1|]. split; [| auto].
eapply u8arr_agree; [exact AG| exact ARR|]. intros a Ha. right; right. exists (p, a_D x, sy_storage (h_oy h)).
split; [| cbn; lia]. eapply Permutation_in; [apply Permutation_sym; exact PERM1|]. rewrite !in_app_iff. right. left. cbn. left. reflexivity. }
clear SYC DAT.
eapply (cl_junk_agree c _ _ _ AG) in JK; [| side1| side1| side1].
xport AG side1.
assert (PE1 : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m1).
{ eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP); [exact HL0| exact PE| exact AG|].
intros a Hc Hout Hx. cbn beta.
destruct Hc as [Hc|[Hc|(bb & Hbb & Rb)]]; [left; lia| right; left; exact Hc| right; right; exists bb; split; [apply HL1; exact Hbb| exact Rb]]. }
clear PE HP HPR AG.

pose proof (stream_blocks_of c _ _ _ _ _ OSP ND1 PERM1) as SBL.
pose proof OSP as (OS & LH & _).
unfold implM. iprefix. zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st1 Q msx) end.
apply implM_bind_assoc. eapply implM_bind.
{ eapply (ogg_stream_clear_spec RFREE) with (os := h_os h) (A := aOS c) (Bd := a_Bd x) (L := a_L x) (Gv := a_Gv x) (lo := x_lo c) (B := x_AB c) (LB := LB1) (hdr := a_hdr x);
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ exact HP1 | exact SBL | exact LH | exact AUX1 | exact ST1 | exact MI1 | exact OS | reflexivity | lia
| unfold RATP; rewrite unsigned_lit by lia; exact ERR1
| unfold RFREE_STACK; lia ]. }
cbv beta. intros os2 st2 ms2 PO.
first [ sf_destruct 26%nat PO as z0 z1 z2 d1 d2 d3 d4 d5 d6 d7 z3 z4 z5 z6 m2 -> MI2 ST2 ERR2 AUX2 CM EFA2 ESO2 HP2 -> OSC | sf_fb; destruct PO as (z0 & z1 & z2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z3 & z4 & z5 & z6 & m2 & -> & MI2 & ST2 & ERR2 & AUX2 & CM & EFA2 & ESO2 & HP2 & -> & OSC) ].
rewrite ?(unsigned_lit (aLOW c)) in ST2 by lia. rewrite ?(unsigned_lit (aLOW c)) in CM by lia.
unfold RATP in ERR2. rewrite ?unsigned_lit in ERR2 by lia. change (0x4d450 + -164) with RERRNO in ERR2.
replace (ret_pc (Z_to_bv 64 0x1c76c)) with (Z_to_bv 64 0x1c76c) by (symmetry; rpc).
pose proof (agree_of_cmod _ _ _ _ _ CM) as AG.
pose proof (perm_stream_clear LB1 x h _ ND1 PERM1) as PERM2.
pose proof (RND _ _ _ HP2) as ND2.
set (LB2 := stream_clear_LB LB1 (h_os h)) in *.
assert (HL2 : forall b, In b (x_LB0 c) -> In b LB2).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM2|]. rewrite !in_app_iff. right. exact Hb. }
apply rw_cells_forget in OSC. rewrite (stream_cells_size _ _ _ _ _ (repeat_length _ _)) in OSC. destruct OSC as [osj OSJ].
pose proof SY1 as sfP_; first [ sf_destruct 4%nat sfP_ as SYC _ DAT _ | sf_fb; destruct sfP_ as (SYC & _ & DAT & _) ].
clear ERR1 MI1 ST1 AUX1 SY1 OS OSP.
assert (SY2 : sync_rep m2 (aOY c) (a_D x) (h_oy h) (a_sybytes x)).
{ split; [eapply rw_cells_agree; [exact AG| exact SYC| side1]|]. split; [exact SYF|]. split; [| exact SYSEP].
unfold sync_data in DAT |- *. destruct (sy_data (h_oy h)) as [p|] eqn:ED; [| exact DAT].
first [ sf_destruct 5%nat DAT as D1 ARR D3 D4 D5 | sf_fb; destruct DAT as (D1 & ARR & D3 & D4 & D5) ]. split; [exact D1|]. split; [| auto].
eapply u8arr_agree; [exact AG| exact ARR|]. intros a Ha. cbn beta.
assert (INp : In (p, a_D x, sy_storage (h_oy h)) LB2).
{ eapply Permutation_in; [apply Permutation_sym; exact PERM2|]. rewrite !in_app_iff. left. cbn. left. reflexivity. }
split; [right; right; exists (p, a_D x, sy_storage (h_oy h)); split; [exact INp| cbn; lia]|].
pose proof (RBR _ _ _ _ HP2 INp) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. cbn in B4. unfold alloc_ceiling in B4. cbn [outside fst snd]. lia. }
clear SYC DAT.
eapply (cl_junk_agree c _ _ _ AG) in JK; [| side1| side1| side1].
xport AG side1.
assert (PE2 : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m2).
{ eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP1); [exact HL1| exact PE1| exact AG|].
intros a Hc Hout Hx. cbn beta. split; [| cbn [outside fst snd]; lia].
destruct Hc as [Hc|[Hc|(bb & Hbb & Rb)]]; [left; lia| right; left; exact Hc| right; right; exists bb; split; [apply HL2; exact Hbb| exact Rb]]. }
apply implM_retb.
clear AG CM PE1 HP1.

clear SYF SYSEP. pose proof SY2 as sfP_; first [ sf_destruct 4%nat sfP_ as SYC SYF DAT SYSEP | sf_fb; destruct sfP_ as (SYC & SYF & DAT & SYSEP) ].
unfold implM. iprefix. zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st2 Q msx) end.
eapply implM_bind.
{ eapply (ogg_sync_clear_spec RFREE) with (sy := h_oy h) (A := aOY c) (D := a_D x) (lo := x_lo c) (B := x_AB c) (LB := LB2);
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ exact HP2 | exact AUX2 | exact ST2 | exact MI2 | exact SYC | reflexivity | lia
| unfold RATP; rewrite unsigned_lit by lia; exact ERR2
| unfold RFREE_STACK; lia
| idtac ].
unfold sync_data in DAT. destruct (sy_data (h_oy h)) as [p|]; [| destruct DAT as (-> & _); reflexivity].
eapply Permutation_in; [apply Permutation_sym; exact PERM2|]. cbn. left. reflexivity. }
cbv beta. intros sy3 st3 ms3 PO.
first [ sf_destruct 26%nat PO as w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 m3 -> MI3 ST3 ERR3 AUX3 CM EFA3 ESO3 HP3 -> SYC3 | sf_fb; destruct PO as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & CM & EFA3 & ESO3 & HP3 & -> & SYC3) ].
rewrite ?(unsigned_lit (aLOW c)) in ST3 by lia. rewrite ?(unsigned_lit (aLOW c)) in CM by lia.
unfold RATP in ERR3. rewrite ?unsigned_lit in ERR3 by lia. change (0x4d450 + -164) with RERRNO in ERR3.
replace (ret_pc (Z_to_bv 64 0x1c774)) with (Z_to_bv 64 0x1c774) by (symmetry; rpc).
pose proof (agree_of_cmod _ _ _ _ _ CM) as AG.
clear SYC DAT ERR2.
eapply (cl_junk_agree c _ _ _ AG) in JK; [| side1| side1| side1].
clear SY2.   xport AG side1.
assert (PE3 : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m3).
{ eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP2); [exact HL2| exact PE2| exact AG|].
intros a Hc Hout Hx. cbn beta. split; [| cbn [outside fst snd]; lia].
destruct (sy_data (h_oy h)) as [p|] eqn:ED.
- rewrite ?ED in PERM2. destruct Hc as [Hc|[Hc|(bb & Hbb & Rbb)]]; [left; lia| right; left; exact Hc| right; right].
exists bb. split; [| exact Rbb]. eapply in_lb_remove_LB0; [exact ND2| exact PERM2| cbn; left; reflexivity| exact Hbb].
- eapply hclient_mono; [exact HL2| exact Hc]. }
apply implM_ret. subst Q. cbv beta.

first [ sf_destruct 5%nat JK as (jl & stb & J1) (opj & ogj & J2) (f8 & J3) (outb & J4 & L4) (hij & J5) | sf_fb; destruct JK as ((jl & stb & J1) & (opj & ogj & J2) & (f8 & J3) & (outb & J4 & L4) & (hij & J5)) ].
release_frame J1 ST3 (aOS c). release_frame OSJ ST3 (aOP c). release_frame J2 ST3 (aOY c).
unfold sync_cells in SYC3. release_frame SYC3 ST3 (aBITS c). release_frame BIJ ST3 (aFSZ c). release_frame J3 ST3 (aOUT c).
apply rw_cells_of_u8arr in J4. release_frame J4 ST3 (aCBK c). release_frame J5 ST3 (aSAV c).
unfold HFIN. zstep.
eapply (ret0 c CX); [exact FRM| exact HP3| | exact ST3| exact SAV| exact ERR3| exact AUX3| exact MI3| assumption| exact PE3| congruence].
destruct (sy_data (h_oy h)) as [p|] eqn:ED; rewrite ?ED in PERM2.
- eapply (perm_lb_remove LB2 [] p (a_D x) (sy_storage (h_oy h)) (x_LB0 c)); [exact ND2| exact PERM2].
- exact PERM2.
Qed.

#[using="RFREE RBR RND CX"] Lemma clean_inl_k : forall {B} (k : unit -> M PState B) (Q : B -> PState -> machine_state -> Prop) h x st ms,
CLI h x st ms ->
(forall st' ms', HFIN c st' ms' -> implM rsegs (k tt) st' Q ms') ->
implM rsegs (X1qx.mbind (cleanupP h) k) st Q ms.
Proof.
intros B k Q h x st ms CC KF. eapply implM_bind; [apply (clean_inl h x st ms CC)|].
cbv beta. intros [] st' ms' HF. apply KF. exact HF.
Qed.
End CLEANI.

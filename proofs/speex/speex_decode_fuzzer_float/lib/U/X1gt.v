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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ij X1il X1im X1ip X1in X1ja X1iu X1j8 X1j4 X1j9 X1it.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g3 X1g1 X1g6 X1g5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gy X1gn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CLEANUP.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis DDESTROY : rspx_decoder_destroy_stmt dec_rep.
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
Notation HFINQ := (fun (_ : unit) st ms => HFIN c st ms).
Notation cleanupP := (cleanup raw_free (St:=PState)).
Notation aF48 c := (bv_unsigned (x_sp c) + -8880).

Definition cl_junk (m : mem) : Prop :=
(exists jl stb, rw_cells rsegs m (aLOW c) [CB 80 jl; CB 24 stb])
/\ (exists opj ogj, rw_cells rsegs m (aOP c) [CB 48 opj; CB 32 ogj])
/\ (exists f8, rw_cells rsegs m (aFSZ c) [CB 8 f8])
/\ (exists outb, u8arr rsegs m (aOUT c) outb /\ Z.of_nat (length outb) = 8000)
/\ (exists hij, rw_cells rsegs m (aCBK c) [CB 48 hij]).
Definition cl_glob (st : PState) (m : mem) : Prop :=
stderr_wfile m /\ (exists errv : word, rw_cells rsegs m RERRNO [C4 errv]) /\ rauxv_ok m (x_AB c) /\ mem_inv rsegs m
/\ pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m /\ ps_so st = ps_so (x_st0 c).

Definition CL330 (h : hstate bptr) (x : hax) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (j0 : list byte),
ms = MS (mkR x1 (wz (aF48 c)) (x_gp c) tpv t0 t1 t2 (wz (aOY c)) (wz (aOS c)) a0 a1 a2 a3 a4 a5 a6 a7
(wz (h_stream_init h)) (wz (aBITS c)) q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
F (wz 0x1c810) fc None m (seg_rom rsegs)
/\ frm0 fc
/\ rw_cells rsegs m (aF48 c) [CB 8 j0; C8 q19; C8 q18; C8 q9; C8 q8; C8 (wz 0x1c790)]
/\ stk rsegs m (x_lo c) (aF48 c)
/\ RHEAP st LB m /\ List.NoDup (map blk_id LB)
/\ Permutation LB ((sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h)) :: stream_blks x h
++ opt_blk (sy_data (h_oy h)) (a_D x) (sy_storage (h_oy h)) ++ x_LB0 c)
/\ bits_rep rsegs m (aBITS c) (a_Dc x) (h_bits h) /\ bits_ok (h_bits h) /\ sb_owner (h_bits h) = 1
/\ rblock_range (a_Dc x) (sb_buf_size (h_bits h))
/\ os_piece m c x h /\ (h_stream_init h = 0 \/ h_stream_init h = 1)
/\ sync_rep m (aOY c) (a_D x) (h_oy h) (a_sybytes x) /\ hsync_ok (h_oy h)
/\ (sy_data (h_oy h) <> None -> rblock_range (a_D x) (sy_storage (h_oy h)))
/\ cl_junk m /\ rw_cells rsegs m (aSAV c) (sav_cells c)
/\ cl_glob st m.

Definition CL344 (oy : sync_st bptr) (D : Z) (bytes : list byte) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 q8 q9 q18 q19 s1v s2v s3v q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (j0 : list byte),
ms = MS (mkR x1 (wz (aF48 c)) (x_gp c) tpv t0 t1 t2 (wz (aOY c)) s1v a0 a1 a2 a3 a4 a5 a6 a7
s2v s3v q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
F (wz 0x1c824) fc None m (seg_rom rsegs)
/\ frm0 fc
/\ rw_cells rsegs m (aF48 c) [CB 8 j0; C8 q19; C8 q18; C8 q9; C8 q8; C8 (wz 0x1c790)]
/\ stk rsegs m (x_lo c) (aF48 c)
/\ RHEAP st LB m /\ List.NoDup (map blk_id LB)
/\ Permutation LB (opt_blk (sy_data oy) D (sy_storage oy) ++ x_LB0 c)
/\ sync_rep m (aOY c) D oy bytes /\ hsync_ok oy /\ (sy_data oy <> None -> rblock_range D (sy_storage oy))
/\ (exists osj, rw_cells rsegs m (aOS c) [CB 408 osj]) /\ (exists bij, rw_cells rsegs m (aBITS c) [CB 48 bij])
/\ cl_junk m /\ rw_cells rsegs m (aSAV c) (sav_cells c)
/\ cl_glob st m.

#[using="Type"] Lemma cl_junk_agree : forall P m m', agree_on rsegs P m m' -> cl_junk m ->
(forall a, aLOW c <= a < aLOW c + 104 -> P a) -> (forall a, aOP c <= a < aOP c + 80 -> P a) ->
(forall a, aFSZ c <= a < aSAV c -> P a) -> cl_junk m'.
Proof.
intros P m m' AG sfH_; first [ sf_destruct 5%nat sfH_ as (jl & stb & J1) (opj & ogj & J2) (f8 & J3) (outb & J4 & L4) (hij & J5) | sf_fb; destruct sfH_ as ((jl & stb & J1) & (opj & ogj & J2) & (f8 & J3) & (outb & J4 & L4) & (hij & J5)) ]; intros H1 H2 H3.
split. { exists jl, stb. eapply rw_cells_agree; [exact AG| exact J1| cbn; intros a Ha; apply H1; lia]. }
split. { exists opj, ogj. eapply rw_cells_agree; [exact AG| exact J2| cbn; intros a Ha; apply H2; lia]. }
split. { exists f8. eapply rw_cells_agree; [exact AG| exact J3| cbn; intros a Ha; apply H3; lia]. }
split. { exists outb. split; [| exact L4]. eapply u8arr_agree; [exact AG| exact J4| intros a Ha; apply H3; lia]. }
exists hij. eapply rw_cells_agree; [exact AG| exact J5| cbn; intros a Ha; apply H3; lia].
Qed.

#[using="RFREE RBR CX"] Lemma clean_344 : forall oy D bytes st ms,
CL344 oy D bytes st ms ->
implM rsegs (X1qx.mbind (ogg_sync_clear raw_free oy) (fun _ => X1qx.mret tt)) st HFINQ ms.
Proof.
intros oy D bytes st ms CC.
first [ sf_destruct 51%nat CC as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 q8 q9 q18 q19 s1v s2v s3v q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 F fc m LB j0 -> FRM FR ST HP ND PERM SY SYOK SYBLK (osj & OSJ) (bij & BIJ) JK SAV GL | sf_fb; destruct CC as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & q8 & q9 & q18 & q19 & s1v & s2v & s3v & q20 & q21 & q22 & q23 & q24 & q25 & q26 & q27 & t3 & t4 & t5 & t6 & F & fc & m & LB & j0 & -> & FRM & FR & ST & HP & ND & PERM & SY & SYOK & SYBLK & (osj & OSJ) & (bij & BIJ) & JK & SAV & GL) ].
pose proof GL as sfP_; first [ sf_destruct 6%nat sfP_ as SEW (errv & ERR) AUX MI PE SO | sf_fb; destruct sfP_ as (SEW & (errv & ERR) & AUX & MI & PE & SO) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
assert (HL0 : forall b, In b (x_LB0 c) -> In b LB).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
pose proof SY as sfP_; first [ sf_destruct 4%nat sfP_ as SYC SYF DAT SYSEP | sf_fb; destruct sfP_ as (SYC & SYF & DAT & SYSEP) ].
unfold wz in FR. unfold implM. iprefix. unfold wz.

do 7 zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st HFINQ msx) end.
release_frame FR ST (hsp c).
eapply implM_bind.
{ eapply (ogg_sync_clear_spec RFREE) with (sy := oy) (A := aOY c) (D := D) (lo := x_lo c) (B := x_AB c) (LB := LB);
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ exact HP | exact AUX | exact ST | exact MI | exact SYC | reflexivity | lia
| unfold RATP; rewrite unsigned_lit by lia; exact ERR
| unfold RFREE_STACK; lia
| idtac ].
unfold sync_data in DAT. destruct (sy_data oy) as [p|]; [| destruct DAT as (-> & _); reflexivity].
eapply Permutation_in; [apply Permutation_sym; exact PERM|]. cbn. left. reflexivity. }
cbv beta. intros sy2 st2 ms2 PO.
first [ sf_destruct 26%nat PO as y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 m2 -> MI2 ST2 ERR2 AUX2 CM EFA ESO HP2 -> SYC2 | sf_fb; destruct PO as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m2 & -> & MI2 & ST2 & ERR2 & AUX2 & CM & EFA & ESO & HP2 & -> & SYC2) ].
rewrite ?(unsigned_lit (aLOW c)) in ST2 by lia. rewrite ?(unsigned_lit (aLOW c)) in CM by lia.
unfold RATP in ERR2. rewrite ?unsigned_lit in ERR2 by lia. change (0x4d450 + -164) with RERRNO in ERR2.
replace (ret_pc (Z_to_bv 64 0x1c790)) with (Z_to_bv 64 0x1c790) by (symmetry; rpc).
pose proof (agree_of_cmod _ _ _ _ _ CM) as AG.

clear SYC DAT ERR.
eapply (cl_junk_agree _ _ _ AG) in JK; [| side1| side1| side1].
clear SY.   xport AG side1.
assert (PE2 : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m2).
{ eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP); [exact HL0| exact PE| exact AG|].
intros a Hc Hout Hx. cbn beta. split; [| cbn [outside fst snd]; lia].
destruct (sy_data oy) as [p|] eqn:ED.
- rewrite ?ED in PERM. destruct Hc as [Hc|[Hc|(bb & Hbb & Rbb)]]; [left; lia| right; left; exact Hc| right; right].
exists bb. split; [| exact Rbb]. eapply in_lb_remove_LB0; [exact ND| exact PERM| cbn; left; reflexivity| exact Hbb].
- eapply hclient_mono; [exact HL0| exact Hc]. }
apply implM_ret.

lazymatch goal with |- evt _ _ ?msx => change (evt rsegs (POSTQ 0 st2) msx) end.
first [ sf_destruct 5%nat JK as (jl & stb & J1) (opj & ogj & J2) (f8 & J3) (outb & J4 & L4) (hij & J5) | sf_fb; destruct JK as ((jl & stb & J1) & (opj & ogj & J2) & (f8 & J3) & (outb & J4 & L4) & (hij & J5)) ].
release_frame J1 ST2 (aOS c). release_frame OSJ ST2 (aOP c). release_frame J2 ST2 (aOY c).
unfold sync_cells in SYC2. release_frame SYC2 ST2 (aBITS c). release_frame BIJ ST2 (aFSZ c). release_frame J3 ST2 (aOUT c).
apply rw_cells_of_u8arr in J4. release_frame J4 ST2 (aCBK c). release_frame J5 ST2 (aSAV c).
change (Z_to_bv 64 0x1c790) with (wz A_RET0).
eapply (ret0 c CX); [exact FRM| exact HP2| | exact ST2| exact SAV| exact ERR2| exact AUX2| exact MI2| assumption| exact PE2| congruence].
destruct (sy_data oy) as [p|] eqn:ED; rewrite ?ED in PERM.
- eapply (perm_lb_remove LB [] p D (sy_storage oy) (x_LB0 c)); [exact ND| exact PERM].
- exact PERM.
Qed.

#[using="Type"] Lemma nodup_ids_remove_mid : forall l1 (b : block) l2,
List.NoDup (map blk_id (l1 ++ b :: l2)) -> List.NoDup (map blk_id (l1 ++ l2)).
Proof. intros l1 b l2 ND. rewrite map_app in *. cbn in ND. eapply NoDup_remove_1. exact ND. Qed.

#[using="Type"] Lemma perm_remove_opt : forall LB o A n R,
List.NoDup (map blk_id LB) -> Permutation LB (opt_blk o A n ++ R) ->
Permutation (lb_remove_opt o LB) R /\ List.NoDup (map blk_id (lb_remove_opt o LB)).
Proof.
intros LB o A n R ND P. destruct o as [p|]; cbn [opt_blk lb_remove_opt app] in *.
- pose proof (perm_lb_remove LB [] p A n R ND P) as P1. cbn [app] in P1. split; [exact P1|].
eapply nodup_ids_perm; [apply Permutation_sym; exact P1|]. apply (nodup_ids_remove_mid [] (p, A, n) R). cbn [app].
eapply nodup_ids_perm; [exact P| exact ND].
- split; [exact P|]. eapply nodup_ids_perm; [apply Permutation_sym; exact P|]. eapply nodup_ids_perm; [exact P| exact ND].
Qed.

#[using="Type"] Lemma perm_stream_clear : forall LB x h R,
List.NoDup (map blk_id LB) -> Permutation LB (stream_blks x h ++ R) ->
Permutation (stream_clear_LB LB (h_os h)) R.
Proof.
intros LB x h R ND P. unfold stream_blks in P. unfold stream_clear_LB. rewrite <- !app_assoc in P.
destruct (perm_remove_opt _ _ _ _ _ ND P) as [P1 ND1].
destruct (perm_remove_opt _ _ _ _ _ ND1 P1) as [P2 ND2].
destruct (perm_remove_opt _ _ _ _ _ ND2 P2) as [P3 _]. exact P3.
Qed.

#[using="Type"] Lemma stream_blocks_of : forall m x h LB R,
stream_rep m c x h -> List.NoDup (map blk_id LB) -> Permutation LB (stream_blks x h ++ R) ->
stream_blocks LB (h_os h) (a_Bd x) (a_L x) (a_Gv x).
Proof.
intros m x h LB R SR ND P.
first [ sf_destruct 23%nat SR as OS LH F1 F2 F3 F4 F5 UL UG UB W1 L1 L2 L3 PB1 PB2 N1 N2 N3 Z1 Z2 Z3 _ | sf_fb; destruct SR as (OS & LH & F1 & F2 & F3 & F4 & F5 & UL & UG & UB & W1 & L1 & L2 & L3 & PB1 & PB2 & N1 & N2 & N3 & Z1 & Z2 & Z3 & _) ].
pose proof (nodup_ids_perm _ _ P ND) as NDR. unfold stream_blks in *.
assert (INLB : forall b, In b (opt_blk (os_body_data (h_os h)) (a_Bd x) (a_nB x) ++ opt_blk (os_lacing_vals (h_os h)) (a_L x) (a_nL x)
++ opt_blk (os_granule_vals (h_os h)) (a_Gv x) (a_nG x)) -> In b LB).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact P|]. rewrite <- !app_assoc. rewrite !in_app_iff in Hb. rewrite !in_app_iff. tauto. }
split. { destruct (os_body_data (h_os h)) as [p|]; [| apply Z1; reflexivity]. exists (a_nB x). apply INLB. cbn. tauto. }
split. { destruct (os_lacing_vals (h_os h)) as [p|]; [| apply Z2; reflexivity]. exists (a_nL x). apply INLB. rewrite !in_app_iff. cbn. tauto. }
split. { destruct (os_granule_vals (h_os h)) as [p|]; [| apply Z3; reflexivity]. exists (a_nG x). apply INLB. rewrite !in_app_iff. cbn. tauto. }
rewrite !map_app in NDR.
split. { intros p q Ep Eq E. subst q. rewrite Ep, Eq in NDR. cbn in NDR. inversion NDR as [|p' l NI ND']; subst. apply NI. left. reflexivity. }
split. { intros p q Ep Eq E. subst q. rewrite Ep, Eq in NDR. cbn in NDR. inversion NDR as [|p' l NI ND']; subst. apply NI.
rewrite !in_app_iff. destruct (os_lacing_vals (h_os h)); cbn; tauto. }
intros p q Ep Eq E. subst q. rewrite Ep, Eq in NDR. destruct (os_body_data (h_os h)); cbn in NDR.
- inversion NDR as [|p0 l NI0 ND']; subst. inversion ND' as [|p' l' NI ND'']; subst. apply NI. left. reflexivity.
- inversion NDR as [|p' l' NI ND'']; subst. apply NI. left. reflexivity.
Qed.

Notation clean_tail h := (X1qx.mbind (speex_bits_destroy raw_free (h_bits h)) (fun _ =>
X1qx.mbind (if negb (h_stream_init h =? 0) then X1qx.mbind (ogg_stream_clear raw_free (h_os h)) (fun _ => X1qx.mret tt) else X1qx.mret tt)
(fun _ => X1qx.mbind (ogg_sync_clear raw_free (h_oy h)) (fun _ => X1qx.mret tt)))).

#[using="RFREE RBR RND CX"] Lemma clean_330 : forall h x st ms, CL330 h x st ms -> implM rsegs (clean_tail h) st HFINQ ms.
Proof.
intros h x st ms CC.
first [ sf_destruct 52%nat CC as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 F fc m LB j0 -> FRM FR ST HP ND PERM BI BOK OWN BBR OSP SI01 SY SYOK SYBLK JK SAV GL | sf_fb; destruct CC as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & q8 & q9 & q18 & q19 & q20 & q21 & q22 & q23 & q24 & q25 & q26 & q27 & t3 & t4 & t5 & t6 & F & fc & m & LB & j0 & -> & FRM & FR & ST & HP & ND & PERM & BI & BOK & OWN & BBR & OSP & SI01 & SY & SYOK & SYBLK & JK & SAV & GL) ].
pose proof GL as sfP_; first [ sf_destruct 6%nat sfP_ as SEW (errv & ERR) AUX MI PE SO | sf_fb; destruct sfP_ as (SEW & (errv & ERR) & AUX & MI & PE & SO) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
assert (HL0 : forall b, In b (x_LB0 c) -> In b LB).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. cbn [app]. right. rewrite !in_app_iff. right. right. exact Hb. }
unfold wz in FR. unfold implM. iprefix. unfold wz.

zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st HFINQ msx) end.
eapply implM_bind.
{ eapply (speex_bits_destroy_spec RFREE) with (A := aBITS c) (D := a_Dc x) (nD := sb_buf_size (h_bits h)) (lo := x_lo c) (B := x_AB c) (LB := LB) (b := h_bits h);
rewrite ?(unsigned_lit (aF48 c)) by lia;
first [ exact HP | exact AUX | exact ST | exact MI | exact BI | exact BOK | exact OWN | reflexivity | lia
| unfold RATP; rewrite unsigned_lit by lia; exact ERR
| unfold RFREE_STACK; lia
| idtac ].
eapply Permutation_in; [apply Permutation_sym; exact PERM|]. left. reflexivity. }
cbv beta. intros [] st1 ms1 PO.
first [ sf_destruct 25%nat PO as y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 m1 -> MI1 ST1 ERR1 AUX1 HPR EFA ESO HP1 | sf_fb; destruct PO as (y0 & y1 & y2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m1 & -> & MI1 & ST1 & ERR1 & AUX1 & HPR & EFA & ESO & HP1) ].
rewrite ?(unsigned_lit (aF48 c)) in ST1 by lia. rewrite ?(unsigned_lit (aF48 c)) in HPR by lia.
unfold RATP in ERR1. rewrite ?unsigned_lit in ERR1 by lia. change (0x4d450 + -164) with RERRNO in ERR1.
replace (ret_pc (Z_to_bv 64 0x1c818)) with (Z_to_bv 64 0x1c818) by (symmetry; rpc).
pose proof (agree_of_rheap_pres _ _ _ _ HPR) as AG.
pose proof (perm_lb_remove LB [] _ _ _ _ ND PERM) as PERM1. cbn [app] in PERM1.
pose proof (RND _ _ _ HP1) as ND1.
set (LB1 := lb_remove (sb_chars (h_bits h)) LB) in *.
assert (HL1 : forall b, In b (x_LB0 c) -> In b LB1).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM1|]. rewrite !in_app_iff. right. right. exact Hb. }

destruct BI as ((rj & Lrj & BIJ) & _ & _). apply rw_cells_forget in BIJ. rewrite (bits_cells_size _ _ _ Lrj) in BIJ. destruct BIJ as [bij BIJ].
pose proof SY as sfP_; first [ sf_destruct 4%nat sfP_ as SYC SYF DAT SYSEP | sf_fb; destruct sfP_ as (SYC & SYF & DAT & SYSEP) ].
clear ERR MI ST AUX SY.
eapply (os_piece_agree2 _ _ _ _ _ _ AG) in OSP; [| side1|].
2:{ intros a (bb & Hbb & Ra). right; right. exists bb. split; [| exact Ra].
eapply Permutation_in; [apply Permutation_sym; exact PERM1|]. rewrite !in_app_iff. left. exact Hbb. }
assert (SY1 : sync_rep m1 (aOY c) (a_D x) (h_oy h) (a_sybytes x)).
{ split; [eapply rw_cells_agree; [exact AG| exact SYC| side1]|]. split; [exact SYF|]. split; [| exact SYSEP].
unfold sync_data in DAT |- *. destruct (sy_data (h_oy h)) as [p|] eqn:ED; [| exact DAT].
first [ sf_destruct 5%nat DAT as D1 ARR D3 D4 D5 | sf_fb; destruct DAT as (D1 & ARR & D3 & D4 & D5) ]. split; [exact D1|]. split; [| auto].
eapply u8arr_agree; [exact AG| exact ARR|]. intros a Ha. right; right. exists (p, a_D x, sy_storage (h_oy h)).
split; [| cbn; lia]. eapply Permutation_in; [apply Permutation_sym; exact PERM1|]. rewrite !in_app_iff. right. left. cbn. left. reflexivity. }
clear SYC DAT.
eapply (cl_junk_agree _ _ _ AG) in JK; [| side1| side1| side1].
xport AG side1.
assert (PE1 : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m1).
{ eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP); [exact HL0| exact PE| exact AG|].
intros a Hc Hout Hx. cbn beta.
destruct Hc as [Hc|[Hc|(bb & Hbb & Rb)]]; [left; lia| right; left; exact Hc| right; right; exists bb; split; [apply HL1; exact Hbb| exact Rb]]. }
assert (GL1 : cl_glob st1 m1).
{ split; [assumption|]. split; [exists errv; exact ERR1|]. split; [exact AUX1|]. split; [exact MI1|]. split; [exact PE1| congruence]. }
clear PE PE1 HP HPR AG.

unfold implM. iprefix. zstep.
if_cases K; zify_cond K.
-
assert (E0 : h_stream_init h = 0) by lia. rewrite E0. cbn [Z.eqb negb].
pose proof (stream_blks_init0 _ _ _ _ OSP E0) as SB0. rewrite SB0 in PERM1. cbn [app] in PERM1.
unfold os_piece in OSP. rewrite E0 in OSP. cbn [Z.eqb] in OSP. destruct OSP as ([osj OSJ] & _).
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st1 HFINQ msx) end.
apply implM_retb. apply (clean_344 (h_oy h) (a_D x) (a_sybytes x)).
unfold CL344. sf_eexists 31%nat. first [ unshelve sf_eexists 5%nat; [ exact (F) | exact (fc) | exact (m1) | exact (LB1) | exact (j0) | ] | sf_fb; exists F, fc, m1, LB1, j0 ].
split; [reflexivity|]. split; [exact FRM|]. split; [exact FR|]. split; [exact ST1|]. split; [exact HP1|]. split; [exact ND1|].
split; [exact PERM1|]. split; [exact SY1|]. split; [exact SYOK|]. split; [exact SYBLK|].
split; [exists osj; exact OSJ|]. split; [exists bij; exact BIJ|]. split; [exact JK|]. split; [exact SAV| exact GL1].
-
assert (E1 : h_stream_init h = 1) by lia. rewrite E1. cbn [Z.eqb negb].
unfold os_piece in OSP. rewrite E1 in OSP. cbn [Z.eqb] in OSP.
pose proof (stream_blocks_of _ _ _ _ _ OSP ND1 PERM1) as SBL.
pose proof OSP as (OS & LH & _).
zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st1 HFINQ msx) end.
first [ sf_destruct 6%nat GL1 as SEW1 (errv1 & ERR1') _ _ PE1 SO1 | sf_fb; destruct GL1 as (SEW1 & (errv1 & ERR1') & _ & _ & PE1 & SO1) ].
apply implM_bind_assoc. eapply implM_bind.
{ eapply (ogg_stream_clear_spec RFREE) with (os := h_os h) (A := aOS c) (Bd := a_Bd x) (L := a_L x) (Gv := a_Gv x) (lo := x_lo c) (B := x_AB c) (LB := LB1) (hdr := a_hdr x);
rewrite ?(unsigned_lit (aF48 c)) by lia;
first [ exact HP1 | exact SBL | exact LH | exact AUX1 | exact ST1 | exact MI1 | exact OS | reflexivity | lia
| unfold RATP; rewrite unsigned_lit by lia; exact ERR1'
| unfold RFREE_STACK; lia ]. }
cbv beta. intros os2 st2 ms2 PO.
first [ sf_destruct 26%nat PO as z0 z1 z2 d1 d2 d3 d4 d5 d6 d7 z3 z4 z5 z6 m2 -> MI2 ST2 ERR2 AUX2 CM EFA2 ESO2 HP2 -> OSC | sf_fb; destruct PO as (z0 & z1 & z2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z3 & z4 & z5 & z6 & m2 & -> & MI2 & ST2 & ERR2 & AUX2 & CM & EFA2 & ESO2 & HP2 & -> & OSC) ].
rewrite ?(unsigned_lit (aF48 c)) in ST2 by lia. rewrite ?(unsigned_lit (aF48 c)) in CM by lia.
unfold RATP in ERR2. rewrite ?unsigned_lit in ERR2 by lia. change (0x4d450 + -164) with RERRNO in ERR2.
replace (ret_pc (Z_to_bv 64 0x1c824)) with (Z_to_bv 64 0x1c824) by (symmetry; rpc).
pose proof (agree_of_cmod _ _ _ _ _ CM) as AG.
pose proof (perm_stream_clear LB1 x h _ ND1 PERM1) as PERM2.
pose proof (RND _ _ _ HP2) as ND2.
set (LB2 := stream_clear_LB LB1 (h_os h)) in *.
assert (HL2 : forall b, In b (x_LB0 c) -> In b LB2).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM2|]. rewrite !in_app_iff. right. exact Hb. }
apply rw_cells_forget in OSC. rewrite (stream_cells_size _ _ _ _ _ (repeat_length _ _)) in OSC. destruct OSC as [osj OSJ].
pose proof SY1 as sfP_; first [ sf_destruct 4%nat sfP_ as SYC _ DAT _ | sf_fb; destruct sfP_ as (SYC & _ & DAT & _) ].
clear ERR1' MI1 ST1 AUX1 SY1 OS OSP.
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
eapply (cl_junk_agree _ _ _ AG) in JK; [| side1| side1| side1].
clear ERR1.   xport AG side1.
assert (PE2 : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m2).
{ eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP1); [exact HL1| exact PE1| exact AG|].
intros a Hc Hout Hx. cbn beta. split; [| cbn [outside fst snd]; lia].
destruct Hc as [Hc|[Hc|(bb & Hbb & Rb)]]; [left; lia| right; left; exact Hc| right; right; exists bb; split; [apply HL2; exact Hbb| exact Rb]]. }
apply implM_retb.
apply (clean_344 (h_oy h) (a_D x) (a_sybytes x)).
unfold CL344. sf_eexists 31%nat. first [ unshelve sf_eexists 5%nat; [ exact (F) | exact (fc) | exact (m2) | exact (LB2) | exact (j0) | ] | sf_fb; exists F, fc, m2, LB2, j0 ].
split; [reflexivity|]. split; [exact FRM|]. split; [exact FR|]. split; [exact ST2|]. split; [exact HP2|]. split; [exact ND2|].
split; [exact PERM2|]. split; [exact SY2|]. split; [exact SYOK|]. split; [exact SYBLK|].
split; [exists osj; exact OSJ|]. split; [exists bij; exact BIJ|]. split; [exact JK|]. split; [exact SAV|].
split; [exact SEW1|]. split; [exists errv1; exact ERR2|]. split; [exact AUX2|]. split; [exact MI2|]. split; [exact PE2| congruence].
Qed.

#[using="DRF DDESTROY RFREE RHF RBR RND CX"] Lemma clean_fn : forall h st ms, CLN dec_rep c h st ms -> implM rsegs (cleanupP h) st HFINQ ms.
Proof.
intros h st ms CC.
first [ sf_destruct 32%nat CC as x1 t0 t1 t2 q8 q9 a5 a6 a7 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 F fc m x cn cb -> FRM HR | sf_fb; destruct CC as (x1 & t0 & t1 & t2 & q8 & q9 & a5 & a6 & a7 & q18 & q19 & q20 & q21 & q22 & q23 & q24 & q25 & q26 & q27 & t3 & t4 & t5 & t6 & F & fc & m & x & cn & cb & -> & FRM & HR) ].
first [ sf_destruct 16%nat HR as (j16 & jsk & lk & LOW & _) CN8 CB8 (stb & STB) OSP (opj & OPK) (ogj & OGJ) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG PURE | sf_fb; destruct HR as ((j16 & jsk & lk & LOW & _) & CN8 & CB8 & (stb & STB) & OSP & (opj & OPK) & (ogj & OGJ) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ]. unfold hbudget, hconsumed, hpend in BUD.
pose proof (RND _ _ _ HP) as ND.
assert (HL0 : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
assert (NUL : sy_data (h_oy h) = None -> a_D x = 0 /\ sy_storage (h_oy h) = 0).
{ intros ED. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT. rewrite ED in DAT. first [ sf_destruct 4%nat DAT as -> _ _ -> | sf_fb; destruct DAT as (-> & _ & _ & ->) ]. auto. }
assert (SYR : a_D x + sy_storage (h_oy h) <= alloc_ceiling).
{ destruct (sy_data (h_oy h)) eqn:ED.
- destruct (SYBLK ltac:(congruence)) as [(_ & _ & _ & B4 & _) _]. exact B4.
- destruct (NUL eq_refl) as [-> ->]. unfold alloc_ceiling. lia. }

apply rw_cells_forget in LOW.
replace (cells_size (low_cells c h j16 cn cb jsk lk)) with 80%nat in LOW by (cbn [cells_size low_cells csize Nat.add]; rewrite CN8, CB8; reflexivity).
destruct LOW as [jl LOW].
assert (J1 : rw_cells rsegs m (aLOW c) [CB 80 jl; CB 24 stb]).
{ apply (proj2 (rw_cells_app rsegs m (aLOW c) [CB 80 jl] [CB 24 stb])). split; [exact LOW|].
lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (aSTEREO c) by (cbn; lia) end. exact STB. }
assert (J2 : rw_cells rsegs m (aOP c) [CB 48 opj; CB 32 ogj]).
{ apply (proj2 (rw_cells_app rsegs m (aOP c) [CB 48 opj] [CB 32 ogj])). split; [exact OPK|].
lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (aOG c) by (cbn; lia) end. exact OGJ. }
apply rw_cells_forget in FSZ. change (cells_size (fsz_cells h pad)) with 8%nat in FSZ. destruct FSZ as [f8 J3].
clear LOW STB OPK OGJ.
pose proof (munch_refl [(aF48 c, aLOW c)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
change (id (rw_cells rsegs m RERRNO [C4 errv])) in ERR.
unfold cleanup, h_decoder_destroy. unfold implM. iprefix. unfold wz.

zstep. zstep.
carve_frame 48%nat ST.
lstep. do 4 zstep. do 4 zstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (m5 := mx) in * end.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG. unfold id in ERR.
assert (HP5 : RHEAP st (a_LB x) m5).
{ eapply RHF; [exact HP| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst]. lia. }
assert (AUX5 : rauxv_ok m5 (x_AB c)).
{ eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]. }
assert (PE5 : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m5).
{ eapply (pres_except_frame RBR c _ _ _ _ _ _ CX HP); [exact HL0| exact PE| exact AG|]. apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]. }
try clear PAY. xportx AG side1.
lazymatch goal with STx : stk rsegs m5 _ _, MIx : mem_inv rsegs m5 |- _ => rename STx into ST5; rename MIx into MI5 end.
clearbody m5. clear MU WM AG HP AUX PE.
assert (JK : cl_junk m5).
{ split; [exists jl, stb; exact J1|]. split; [exists opj, ogj; exact J2|]. split; [exists f8; exact J3|].
split; [exists outb; split; [exact OUT| exact LOUT]|]. exists hij; exact HI. }
clear J1 J2 J3 OUT HI.

unfold owned in PERM. unfold dec_piece in DEC.
destruct (h_st h) as [d|] eqn:EST.
-
destruct DEC as (DR & HS & BRD). rewrite <- !app_assoc in PERM.
zstep. if_cases K; zify_cond K; rewrite ?land64 in K by lia; [exfalso; lia|].
zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st HFINQ msx) end.
eapply implM_bind.
{ eapply (DDESTROY) with (STEREO := aSTEREO c) (S := a_S x) (d := d) (LBD := a_LBD x) (AB := x_AB c) (lo := x_lo c) (LB := a_LB x);
rewrite ?(unsigned_lit (aF48 c)) by lia;
first [ exact HP5 | exact PERM | exact DR | exact AUX5 | exact ST5 | exact MI5 | exact FRM | reflexivity | lia | assumption
| unfold RATP; rewrite unsigned_lit by lia; exact ERR
| unfold DEC_DESTROY_STACK; lia ]. }
cbv beta. intros [] st1 ms1 PO.
first [ sf_destruct 28%nat PO as y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F1 fc1 m1 errv1 -> FRM1 MI1 ST1 ERR1 AUX1 HPR ESO HP1 | sf_fb; destruct PO as (y0 & y1 & y2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F1 & fc1 & m1 & errv1 & -> & FRM1 & MI1 & ST1 & ERR1 & AUX1 & HPR & ESO & HP1) ].
rewrite ?(unsigned_lit (aF48 c)) in ST1 by lia. rewrite ?(unsigned_lit (aF48 c)) in HPR by lia.
unfold RATP in ERR1. rewrite ?unsigned_lit in ERR1 by lia. change (0x4d450 + -164) with RERRNO in ERR1.
replace (ret_pc (Z_to_bv 64 0x1c810)) with (Z_to_bv 64 0x1c810) by (symmetry; rpc).
pose proof (agree_of_rheap_pres _ _ _ _ HPR) as AG.
lazymatch type of HP1 with RHEAP _ ?L _ => set (LB1 := L) in * end.
pose proof (RND _ _ _ HP1) as ND1.
assert (HL1 : forall b, In b (x_LB0 c) -> In b LB1).
{ intros b Hb. subst LB1. rewrite !in_app_iff. right; right; right; right; right. exact Hb. }
clear ERR MI5 ST5 AUX5.
eapply (os_piece_agree2 _ _ _ _ _ _ AG) in OSP; [| side1|].
2:{ intros a (bb & Hbb & Ra). right; right. exists bb. split; [| exact Ra]. subst LB1. unfold stream_blks in Hbb.
rewrite !in_app_iff in Hbb. rewrite !in_app_iff. right. clear -Hbb. tauto. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| side1|].
2:{ intros a Ha. right; right. exists (sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h)). split; [subst LB1; left; reflexivity| cbn; lia]. }
pose proof SY as sfP_; first [ sf_destruct 4%nat sfP_ as SYC SYF DAT SYSEP | sf_fb; destruct sfP_ as (SYC & SYF & DAT & SYSEP) ].
assert (SY1 : sync_rep m1 (aOY c) (a_D x) (h_oy h) (a_sybytes x)).
{ split; [eapply rw_cells_agree; [exact AG| exact SYC| side1]|]. split; [exact SYF|]. split; [| exact SYSEP].
unfold sync_data in DAT |- *. destruct (sy_data (h_oy h)) as [p|] eqn:ED; [| exact DAT].
first [ sf_destruct 5%nat DAT as D1 ARR D3 D4 D5 | sf_fb; destruct DAT as (D1 & ARR & D3 & D4 & D5) ]. split; [exact D1|]. split; [| auto].
eapply u8arr_agree; [exact AG| exact ARR|]. intros a Ha. right; right. exists (p, a_D x, sy_storage (h_oy h)).
split; [| cbn; lia]. subst LB1. rewrite !in_app_iff. cbn. clear. tauto. }
clear SY SYC DAT.
eapply (cl_junk_agree _ _ _ AG) in JK; [| side1| side1| side1].
xport AG side1.
assert (PE1 : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m1).
{ eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP5); [exact HL0| exact PE5| exact AG|].
intros a Hc Hout Hx. cbn beta.
destruct Hc as [Hc|[Hc|(bb & Hbb & Rb)]]; [left; lia| right; left; exact Hc| right; right; exists bb; split; [apply HL1; exact Hbb| exact Rb]]. }
apply (clean_330 h x).
unfold CL330. sf_eexists 28%nat. eexists F1, fc1, m1, LB1, _.
split; [reflexivity|]. split; [exact FRM1|]. split; [exact FR|]. split; [exact ST1|]. split; [exact HP1|]. split; [exact ND1|].
split. { subst LB1. unfold stream_blks. rewrite <- !app_assoc. apply Permutation_refl. }
split; [exact BI|]. split; [exact BOK|]. split; [exact OWN|]. split; [exact BBR|]. split; [exact OSP|]. split; [exact SIR|].
split; [exact SY1|]. split; [exact SYOK|]. split; [intros NE; exact (proj1 (SYBLK NE))|]. split; [exact JK|]. split; [exact SAV|].
split; [exact SEW|]. split; [exists errv1; exact ERR1|]. split; [exact AUX1|]. split; [exact MI1|]. split; [exact PE1| congruence].
-
destruct DEC as [ES ELBD]. rewrite ES. cbn [app] in PERM.
zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity].
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st HFINQ msx) end.
apply implM_retb. apply (clean_330 h x).
unfold CL330. sf_eexists 28%nat. eexists F, fc, m5, (a_LB x), _.
split; [reflexivity|]. split; [exact FRM|]. split; [exact FR|]. split; [exact ST5|]. split; [exact HP5|]. split; [exact ND|].
split. { eapply Permutation_trans; [exact PERM|]. unfold stream_blks. rewrite <- !app_assoc. apply Permutation_refl. }
split; [exact BI|]. split; [exact BOK|]. split; [exact OWN|]. split; [exact BBR|]. split; [exact OSP|]. split; [exact SIR|].
split; [exact SY|]. split; [exact SYOK|]. split; [intros NE; exact (proj1 (SYBLK NE))|]. split; [exact JK|]. split; [exact SAV|].
split; [exact SEW|]. split; [exists errv; exact ERR|]. split; [exact AUX5|]. split; [exact MI5|]. split; [exact PE5| exact SO].
Qed.

#[using="DRF DDESTROY RFREE RHF RBR RND CX"] Theorem clean_ok : forall {B} (k : unit -> M PState B) (Q : B -> PState -> machine_state -> Prop) h st ms,
CLN dec_rep c h st ms ->
(forall st' ms', HFIN c st' ms' -> implM rsegs (k tt) st' Q ms') ->
implM rsegs (X1qx.mbind (cleanupP h) k) st Q ms.
Proof.
intros B k Q h st ms CC K. eapply implM_bind; [apply clean_fn; exact CC|].
cbv beta. intros [] st' ms' HF. apply K. exact HF.
Qed.
End CLEANUP.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bj X1bs X1c2 X1br X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1m6 X1kx X1el X1ec. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h7 X1go X1hk X1ho X1n8.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1r3 X1r4 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Ltac des_ntk := let K := fresh "K" in if_cases K; zify_cond K; rewrite ?sh_land7 in K; [exfalso; lia | clear K].
Ltac des_ntf := let K := fresh "K" in if_cases K; zify_cond K; rewrite ?sh_land7 in K; [clear K | exfalso; lia].
Ltac des_ck := first [ lit_if | des_ntk | des_ntf ].
Ltac des_walk p := repeat (tryif ub_at_pc p then fail else (tryif ub_at_if then des_ck else zstep)); first [ ub_at_pc p | ub_show_pc_fail p ].

Lemma lb_remove_cons : forall (p : bptr) (b : block) L,
lb_remove p (b :: L) = if bptr_eqb (blk_id b) p then lb_remove p L else b :: lb_remove p L.
Proof.
intros p b L. unfold lb_remove. rewrite filter_cons. destruct (bptr_eqb (blk_id b) p) eqn:E; cbn [negb].
- destruct (decide (Is_true false)) as [D|D]; [destruct D| reflexivity].
- destruct (decide (Is_true true)) as [D|D]; [reflexivity| exfalso; apply D; exact I].
Qed.

Lemma bptr_eqb_refl' : forall p : bptr, bptr_eqb p p = true.
Proof. intros [c o]. unfold bptr_eqb. cbn. rewrite X1pv.aptr_eqb_refl, Z.eqb_refl. reflexivity. Qed.

Lemma bptr_eqb_neq : forall p q : bptr, p <> q -> bptr_eqb p q = false.
Proof.
intros p q NE. destruct (bptr_eqb p q) eqn:E; [| reflexivity]. exfalso. apply NE.
unfold bptr_eqb in E. apply andb_true_iff in E. destruct E as [E1 E2].
destruct (X1pv.aptr_eqb_spec (fst p) (fst q)) as [A|A]; [| discriminate]. apply Z.eqb_eq in E2. destruct p, q; cbn in *; congruence.
Qed.

Lemma lb_remove_notin : forall (p : bptr) L, ~ In p (map blk_id L) -> lb_remove p L = L.
Proof.
intros p L. induction L as [|b L IH]; intros NI; [reflexivity|].
rewrite lb_remove_cons. rewrite bptr_eqb_neq by (intros E; apply NI; left; exact E).
rewrite IH by (intros H; apply NI; right; exact H). reflexivity.
Qed.

Lemma lb_remove_perm_of : forall LB (b : block) L,
Permutation LB (b :: L) -> List.NoDup (map blk_id LB) -> Permutation (lb_remove (blk_id b) LB) L.
Proof.
intros LB b L P ND.
assert (ND' : List.NoDup (map blk_id (b :: L))) by (eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND]).
cbn in ND'. apply List.NoDup_cons_iff in ND'. destruct ND' as [NI _].
eapply Permutation_trans; [unfold lb_remove; apply filter_Permutation; exact P|].
fold (lb_remove (blk_id b) (b :: L)). rewrite lb_remove_cons, bptr_eqb_refl', lb_remove_notin by exact NI. apply Permutation_refl.
Qed.

Lemma in_lb_remove_keep : forall (p : bptr) L b, In b L -> blk_id b <> p -> In b (lb_remove p L).
Proof.
intros p L b Hb NE. unfold lb_remove. apply X0p3.In_filter_iff. split; [exact Hb|].
rewrite bptr_eqb_neq by exact NE. exact I.
Qed.

Fixpoint des_depth (d : dec_state bptr) : Z :=
match d with DecNB _ => RFREE_STACK | DecSB _ low => 16 + des_depth low end.

Definition rdes_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(s : PState) (LBr : list block) (AB lo : Z) (m : mem) : unit -> PState -> machine_state -> Prop :=
fun _ s' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ frm0 fc'
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' AB
/\ rheap_pres LBr (bv_unsigned sp) m m'
/\ ps_so s' = ps_so s
/\ RHEAP s' LBr m'.

Definition rdes_at {RCEIL : RunCeiling} (d : dec_state bptr) : Prop :=
forall (OUT STEREO S : Z) (LBD LB LBr : list block) (s : PState) (lo AB : Z) (errv : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
RHEAP s LB m -> Permutation LB (LBD ++ LBr) -> DREP OUT STEREO m S d LBD -> rtables_pristine m ->
rauxv_ok m AB -> bv_unsigned sp <= AB ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - des_depth d ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m -> frm0 fc -> tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 S ->
implM rsegs (speex_decoder_destroy raw_free d) s
(rdes_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LBr AB lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_destroy) fc None m (seg_rom rsegs)).

Theorem rdes_nb {RCEIL : RunCeiling} : forall st, rdes_at (DecNB st).
Proof.
intros st OUT STEREO S LBD LB LBr s lo AB errv ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
HEAP PERM REP TP AUX SB ST CLO LO ERR MI FRM TPE ->.
cbn [des_depth] in LO. cbn [decst_rep] in REP. destruct REP as [ELBD NB].
pose proof CLO as CLOv. unfold alloc_ceiling in CLOv.
assert (HIN : In (nb_blk st, S, NBSTATE_SIZEOF) LB).
{ eapply Permutation_in; [apply Permutation_sym; exact PERM|]. rewrite ELBD. left. reflexivity. }
pose proof (RHEAP_block_range_proof _ _ _ _ HEAP HIN) as BR. unfold blk_addr, blk_size, NBSTATE_SIZEOF in BR. cbn [fst snd] in BR.
first [ sf_destruct 5%nat BR as S0 _ _ SCE _ | sf_fb; destruct BR as (S0 & _ & _ & SCE & _) ]. unfold alloc_ceiling in SCE.
assert (ENB : NB_MODE_PTR = 0x3b7c8) by reflexivity.
first [ sf_destruct 7%nat NB as AL POS INV j JOK CBS X | sf_fb; destruct NB as (AL & POS & INV & j & JOK & CBS & X) ].
apply (nb_pieces_of_cells rsegs _ _ _ m S OUT STEREO st j JOK) in X. destruct X as (P0 & _). unfold nb_hdr_cells in P0.
pose proof (nb_desc_of_pristine m TP) as ND. unfold nb_desc_cells in ND.

eapply (implM_evt rsegs _ _ _ (fun ms1 => ms1 = _)).
{ unfold A_speex_decoder_destroy. des_walk 0x318c0. apply evt_done. reflexivity. }
cbv beta. intros ms1 ->.
cbn [speex_decoder_destroy nb_decoder_destroy].
eapply implM_mono.
{ eapply (rfree_spec_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s LB (nb_blk st) S NBSTATE_SIZEOF lo AB errv);
[exact HEAP| exact HIN| exact AUX| exact SB| exact ST| exact CLO| unfold RFREE_STACK in *; lia| exact ERR| exact MI| exact TPE| reflexivity]. }
cbv beta. intros [] s' ms' sfH_; first [ sf_destruct 25%nat sfH_ as x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m' -> MI' ST' ERR' AUX' HP' PSF PSO HEAP' | sf_fb; destruct sfH_ as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & -> & MI' & ST' & ERR' & AUX' & HP' & PSF & PSO & HEAP') ].
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP) as NDL.
assert (PR : Permutation (lb_remove (nb_blk st) LB) LBr).
{ apply (lb_remove_perm_of LB (nb_blk st, S, NBSTATE_SIZEOF) LBr); [rewrite ELBD in PERM; exact PERM| exact NDL]. }
unfold rdes_post. sf_eexists 15%nat. first [ unshelve sf_eexists 4%nat; [ exact (F) | exact (fc) | exact (m') | exact (errv) | ] | sf_fb; exists F, fc, m', errv ].
split; [reflexivity|]. split; [exact FRM|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
split. { eapply rheap_pres_weaken; [exact HP'| lia|]. intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PR| exact Hb]. }
split; [exact PSO|]. eapply RHEAP_perm; [exact HEAP'| exact PR].
Qed.

Theorem rdes_sb {RCEIL : RunCeiling} : forall s low, rdes_at low -> rdes_at (DecSB s low).
Proof.
intros s low IH OUT STEREO S LBD LB LBr ps lo AB errv ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
HEAP PERM REP TP AUX SB ST CLO LO ERR MI FRM TPE ->.
cbn [des_depth] in LO. fold (des_depth low) in LO.
assert (DD : RFREE_STACK <= des_depth low) by (clear; induction low; cbn; lia). unfold RFREE_STACK in DD.
cbn [decst_rep] in REP. fold (DREP OUT STEREO m) in REP.
first [ sf_destruct 12%nat REP as a j LBL ELBD AL POS INV JOK X BU OUTL RL | sf_fb; destruct REP as (a & j & LBL & ELBD & AL & POS & INV & JOK & X & BU & OUTL & RL) ].
pose proof CLO as CLOv. unfold alloc_ceiling in CLOv.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as Imo Ifs Iffs Isfs Inbs Ilpc Ifi Isr Ien Ies Isid Iis | sf_fb; destruct sfP_ as (Imo & Ifs & Iffs & Isfs & Inbs & Ilpc & Ifi & Isr & Ien & Ies & Isid & Iis) ].
assert (ETP : errno_addr tp = RERRNO) by (rewrite TPE; unfold RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity).
rewrite ETP in ERR. unfold RERRNO in ERR.

assert (INL : forall b, In b (sb_blocks s S a ++ LBr) -> In b LB).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. rewrite ELBD. apply in_app_iff in Hb.
apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; left; exact Hb| right; exact Hb]. }
assert (INS : In (sbd_blk s, S, SBSTATE_SIZEOF) LB) by (apply INL; left; reflexivity).
pose proof (RHEAP_block_range_proof _ _ _ _ HEAP INS) as BRS. unfold blk_addr, blk_size, SBSTATE_SIZEOF in BRS. cbn [fst snd] in BRS.
first [ sf_destruct 5%nat BRS as S0 _ _ SCE SIMG | sf_fb; destruct BRS as (S0 & _ & _ & SCE & SIMG) ]. unfold alloc_ceiling in SCE.
assert (EWB : A_speex_wb_mode = 0x3bbb8) by reflexivity. assert (EUWB : A_speex_uwb_mode = 0x3bc18) by reflexivity.
pose proof (desc_of_pristine m (sbd_mode s) TP) as ND.
unfold sb_cells in X.

pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl rsegs m) as WM0.
carve_frame 16%nat ST.
eapply (implM_evt rsegs _ _ _ (fun ms1 => exists m1,
ms1 = MS (mkR (Z_to_bv 64 0x2e650) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 (Z_to_bv 64 A_sb_decoder_destroy) t2 (Z_to_bv 64 S) s1
(Z_to_bv 64 (a_low a)) (Z_to_bv 64 (sb_mode_ptr NB_MODE_PTR A_speex_wb_mode A_speex_uwb_mode (sbd_mode s))) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_destroy) fc None m1 (seg_rom rsegs)
/\ rw_cells rsegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra]
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + -16))).
{ destruct Imo as [E|E]; rewrite E in X, ND |- *; cbn [sb_mode_ptr desc_cells_of] in X, ND |- *; unfold wb_desc_cells, uwb_desc_cells in ND;
unfold A_speex_decoder_destroy; zstep; des_walk 0x1cf48;
apply evt_done; eexists; (split; [reflexivity|]); (split; [eassumption|]); (split; [exact MU0|]); (split; [exact WM0|]); split; assumption. }
clear MU0 WM0. cbv beta. intros ms1 sfH_; first [ sf_destruct 7%nat sfH_ as m1 -> FRa MU1 WM1 MI1 ST1 | sf_fb; destruct sfH_ as (m1 & -> & FRa & MU1 & WM1 & MI1 & ST1) ].
assert (HEAP1 : RHEAP ps LB m1).
{ eapply RHEAP_frame_proof; [exact HEAP| exact MU1| exact WM1|]. constructor; [|constructor]. left. cbn [fst]. lia. }
assert (AUX1 : rauxv_ok m1 AB).
{ eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]. constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia. }
assert (ERR1 : rw_cells rsegs m1 316332 [C4 errv]).
{ eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. split; [lia| exact I]. }
assert (TP1 : rtables_pristine m1).
{ eapply rtables_pristine_munch; [exact TP| exact MU1|]. intros x Hx. unfold RTABLES_LO, RTABLES_HI in Hx. cbn. split; [lia| exact I]. }
assert (X1 : rw_cells rsegs m1 S (SBCELLS s a OUT j)).
{ unfold sb_cells. eapply rw_cells_transport; [exact X| exact MU1| exact WM1|]. cbn. split; [lia| exact I]. }
assert (RL1 : DREP OUTL STEREO m1 (a_low a) low LBL).
{ eapply decst_rep_munch; [exact RL| exact MU1| exact WM1|]. intros b x Hb Hx.
assert (HbL : In b LB). { eapply Permutation_in; [apply Permutation_sym; exact PERM|]. rewrite ELBD. apply in_app_iff. left. apply in_app_iff. right. exact Hb. }
first [ pose proof (RHEAP_block_range_proof _ _ _ _ HEAP HbL) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (RHEAP_block_range_proof _ _ _ _ HEAP HbL) as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. cbn. split; [lia| exact I]. }
clear X RL ERR TP.

cbn [speex_decoder_destroy]. fold (speex_decoder_destroy raw_free low).
eapply implM_bind.
{ eapply (IH OUTL STEREO (a_low a) LBL LB (sb_blocks s S a ++ LBr) ps lo AB errv); try reflexivity.
- exact HEAP1.
- eapply Permutation_trans; [exact PERM|]. rewrite ELBD, <- app_assoc. apply Permutation_app_swap_app.
- exact RL1.
- exact TP1.
- exact AUX1.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST1.
- exact CLO.
- rewrite unsigned_lit by lia. lia.
- rewrite ETP. unfold RERRNO. exact ERR1.
- exact MI1.
- exact FRM.
- exact TPE. }
cbv beta. intros [] s1' ms2 sfH_; first [ sf_destruct 28%nat sfH_ as x0 x1 x2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 x3 x4 x5 x6 F1 fc1 m2 errv1 -> FRM1 MI2 ST2 ERR2 AUX2 HP2 PSO2 HEAP2 | sf_fb; destruct sfH_ as (x0 & x1 & x2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & x3 & x4 & x5 & x6 & F1 & fc1 & m2 & errv1 & -> & FRM1 & MI2 & ST2 & ERR2 & AUX2 & HP2 & PSO2 & HEAP2) ].
rewrite unsigned_lit in ST2 by lia. rewrite unsigned_lit in HP2 by lia. rewrite ret_pc_even by lia. rewrite ETP in ERR2. unfold RERRNO in ERR2.
assert (X2 : rw_cells rsegs m2 S (SBCELLS s a OUT j)).
{ eapply rheap_pres_rw_cells; [exact HP2| exact X1|]. right; right. exists (sbd_blk s, S, SBSTATE_SIZEOF). split; [apply in_app_iff; left; left; reflexivity|].
unfold blk_addr, blk_size, SBSTATE_SIZEOF. cbn [fst snd]. rewrite sb_cells_size. lia. }
assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP2| exact FRa| left; cbn; lia]).
assert (HPacc2 : rheap_pres LBr (bv_unsigned sp) m m2).
{ eapply rheap_pres_trans.
- eapply (rheap_pres_of_munch LBr (bv_unsigned sp) _ m m1 MU1 WM1). intros x Hx CA. apply outside_single.
destruct CA as [CA|[[CA _]|(b & Hb & Hab)]]; [lia| lia|].
first [ pose proof (RHEAP_block_range_proof _ _ _ b HEAP ltac:(apply INL; apply in_app_iff; right; exact Hb)) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (RHEAP_block_range_proof _ _ _ b HEAP ltac:(apply INL; apply in_app_iff; right; exact Hb)) as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. unfold in_block in Hab. lia.
- eapply rheap_pres_weaken; [exact HP2| lia| intros b Hb; apply in_app_iff; right; exact Hb]. }
clear X1 FRa HP2 HEAP1 AUX1 ERR1 MI1 ST1 RL1 MU1 WM1 HEAP.
unfold sb_cells in X2.

eapply (implM_evt rsegs _ _ _ (fun ms => ms = _)). { step. step. apply evt_done. reflexivity. }
cbv beta. intros ms_g0 ->.
eapply implM_bind.
{ eapply (rfree_spec_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 s1' _ (sbd_g0_mem s) (a_g0 a) (256) lo AB _ HEAP2).
- cbn [app]. right. left. reflexivity.
- exact AUX2.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST2.
- exact CLO.
- rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
- rewrite ETP. unfold RERRNO. exact ERR2.
- exact MI2.
- exact TPE.
- reflexivity. }
cbv beta. intros [] s2' ms3' PF. first [ sf_destruct 25%nat PF as z0x3 z1x3 z2x3 za0x3 za1x3 za2x3 za3x3 za4x3 za5x3 za6x3 za7x3 z3x3 z4x3 z5x3 z6x3 m3 -> MI3 ST3 ERR3 AUX3 HP3 PSF3 PSO3 HEAP3 | sf_fb; destruct PF as (z0x3 & z1x3 & z2x3 & za0x3 & za1x3 & za2x3 & za3x3 & za4x3 & za5x3 & za6x3 & za7x3 & z3x3 & z4x3 & z5x3 & z6x3 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HP3 & PSF3 & PSO3 & HEAP3) ].
rewrite unsigned_lit in ST3 by lia. rewrite unsigned_lit in HP3 by lia. rewrite ret_pc_even by lia. rewrite ETP in ERR3. unfold RERRNO in ERR3.
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP2) as ND2.
apply (RHEAP_perm _ _ ((sbd_blk s, S, SBSTATE_SIZEOF) :: [(sbd_g1_mem s, a_g1 a, 256); (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s); (sbd_old_qlsp s, a_oq a, 32); (sbd_interp_qlpc s, a_iq a, 32); (sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] ++ LBr)) in HEAP3.
2:{ apply (lb_remove_perm_of _ (sbd_g0_mem s, a_g0 a, 256)); [| exact ND2]. cbn [app]. apply perm_swap. }
assert (X3 : rw_cells rsegs m3 S (SBCELLS s a OUT j)).
{ unfold sb_cells. eapply rheap_pres_rw_cells; [exact HP3| exact X2|]. right; right. exists (sbd_blk s, S, SBSTATE_SIZEOF).
split; [apply in_lb_remove_keep; [left; reflexivity| cbn; apply not_eq_sym; eapply (NoDup_app_in_neq [blk_id (sbd_g0_mem s, a_g0 a, 256)] (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: [(sbd_g1_mem s, a_g1 a, 256); (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s); (sbd_old_qlsp s, a_oq a, 32); (sbd_interp_qlpc s, a_iq a, 32); (sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] ++ LBr))); [| left; reflexivity| left; reflexivity]]|].
2:{ unfold blk_addr, blk_size, SBSTATE_SIZEOF. cbn [fst snd]. rewrite sb_cells_size. lia. }
eapply Permutation_NoDup; [| exact ND2]. cbn [map app]. apply perm_swap. }
assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -16) [C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP3| exact FR2| left; cbn; lia]).
assert (HPacc3 : rheap_pres LBr (bv_unsigned sp) m m3).
{ eapply rheap_pres_trans; [exact HPacc2|]. eapply rheap_pres_weaken; [exact HP3| lia|]. intros b Hb. apply in_lb_remove_keep; [cbn [app sb_blocks In]; repeat right; exact Hb|].
apply not_eq_sym. eapply (NoDup_app_in_neq (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: (sbd_g0_mem s, a_g0 a, 256) :: [(sbd_g1_mem s, a_g1 a, 256); (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s); (sbd_old_qlsp s, a_oq a, 32); (sbd_interp_qlpc s, a_iq a, 32); (sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)])) (map blk_id LBr)); [| right; left; reflexivity| apply in_map; exact Hb].
rewrite <- map_app. exact ND2. }
clear X2 FR2 HP3 HEAP2 AUX2 ERR2 MI2 ST2 ND2 HPacc2 PSF3.
unfold sb_cells in X3.

eapply (implM_evt rsegs _ _ _ (fun ms => ms = _)). { step. step. apply evt_done. reflexivity. }
cbv beta. intros ms_g1 ->.
eapply implM_bind.
{ eapply (rfree_spec_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s2' _ (sbd_g1_mem s) (a_g1 a) (256) lo AB _ HEAP3).
- cbn [app]. right. left. reflexivity.
- exact AUX3.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST3.
- exact CLO.
- rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
- rewrite ETP. unfold RERRNO. exact ERR3.
- exact MI3.
- exact TPE.
- reflexivity. }
cbv beta. intros [] s3' ms4' PF. first [ sf_destruct 25%nat PF as z0x4 z1x4 z2x4 za0x4 za1x4 za2x4 za3x4 za4x4 za5x4 za6x4 za7x4 z3x4 z4x4 z5x4 z6x4 m4 -> MI4 ST4 ERR4 AUX4 HP4 PSF4 PSO4 HEAP4 | sf_fb; destruct PF as (z0x4 & z1x4 & z2x4 & za0x4 & za1x4 & za2x4 & za3x4 & za4x4 & za5x4 & za6x4 & za7x4 & z3x4 & z4x4 & z5x4 & z6x4 & m4 & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & PSF4 & PSO4 & HEAP4) ].
rewrite unsigned_lit in ST4 by lia. rewrite unsigned_lit in HP4 by lia. rewrite ret_pc_even by lia. rewrite ETP in ERR4. unfold RERRNO in ERR4.
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP3) as ND3.
apply (RHEAP_perm _ _ ((sbd_blk s, S, SBSTATE_SIZEOF) :: [(sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s); (sbd_old_qlsp s, a_oq a, 32); (sbd_interp_qlpc s, a_iq a, 32); (sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] ++ LBr)) in HEAP4.
2:{ apply (lb_remove_perm_of _ (sbd_g1_mem s, a_g1 a, 256)); [| exact ND3]. cbn [app]. apply perm_swap. }
assert (X4 : rw_cells rsegs m4 S (SBCELLS s a OUT j)).
{ unfold sb_cells. eapply rheap_pres_rw_cells; [exact HP4| exact X3|]. right; right. exists (sbd_blk s, S, SBSTATE_SIZEOF).
split; [apply in_lb_remove_keep; [left; reflexivity| cbn; apply not_eq_sym; eapply (NoDup_app_in_neq [blk_id (sbd_g1_mem s, a_g1 a, 256)] (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: [(sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s); (sbd_old_qlsp s, a_oq a, 32); (sbd_interp_qlpc s, a_iq a, 32); (sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] ++ LBr))); [| left; reflexivity| left; reflexivity]]|].
2:{ unfold blk_addr, blk_size, SBSTATE_SIZEOF. cbn [fst snd]. rewrite sb_cells_size. lia. }
eapply Permutation_NoDup; [| exact ND3]. cbn [map app]. apply perm_swap. }
assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -16) [C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP4| exact FR3| left; cbn; lia]).
assert (HPacc4 : rheap_pres LBr (bv_unsigned sp) m m4).
{ eapply rheap_pres_trans; [exact HPacc3|]. eapply rheap_pres_weaken; [exact HP4| lia|]. intros b Hb. apply in_lb_remove_keep; [cbn [app sb_blocks In]; repeat right; exact Hb|].
apply not_eq_sym. eapply (NoDup_app_in_neq (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: (sbd_g1_mem s, a_g1 a, 256) :: [(sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s); (sbd_old_qlsp s, a_oq a, 32); (sbd_interp_qlpc s, a_iq a, 32); (sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)])) (map blk_id LBr)); [| right; left; reflexivity| apply in_map; exact Hb].
rewrite <- map_app. exact ND3. }
clear X3 FR3 HP4 HEAP3 AUX3 ERR3 MI3 ST3 ND3 HPacc3 PSF4.
unfold sb_cells in X4.

eapply (implM_evt rsegs _ _ _ (fun ms => ms = _)). { step. step. apply evt_done. reflexivity. }
cbv beta. intros ms_ex ->.
eapply implM_bind.
{ eapply (rfree_spec_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 s3' _ (sbd_excBuf s) (a_exc a) (4 * sbd_subframeSize s) lo AB _ HEAP4).
- cbn [app]. right. left. reflexivity.
- exact AUX4.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST4.
- exact CLO.
- rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
- rewrite ETP. unfold RERRNO. exact ERR4.
- exact MI4.
- exact TPE.
- reflexivity. }
cbv beta. intros [] s4' ms5' PF. first [ sf_destruct 25%nat PF as z0x5 z1x5 z2x5 za0x5 za1x5 za2x5 za3x5 za4x5 za5x5 za6x5 za7x5 z3x5 z4x5 z5x5 z6x5 m5 -> MI5 ST5 ERR5 AUX5 HP5 PSF5 PSO5 HEAP5 | sf_fb; destruct PF as (z0x5 & z1x5 & z2x5 & za0x5 & za1x5 & za2x5 & za3x5 & za4x5 & za5x5 & za6x5 & za7x5 & z3x5 & z4x5 & z5x5 & z6x5 & m5 & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & PSF5 & PSO5 & HEAP5) ].
rewrite unsigned_lit in ST5 by lia. rewrite unsigned_lit in HP5 by lia. rewrite ret_pc_even by lia. rewrite ETP in ERR5. unfold RERRNO in ERR5.
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP4) as ND4.
apply (RHEAP_perm _ _ ((sbd_blk s, S, SBSTATE_SIZEOF) :: [(sbd_old_qlsp s, a_oq a, 32); (sbd_interp_qlpc s, a_iq a, 32); (sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] ++ LBr)) in HEAP5.
2:{ apply (lb_remove_perm_of _ (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s)); [| exact ND4]. cbn [app]. apply perm_swap. }
assert (X5 : rw_cells rsegs m5 S (SBCELLS s a OUT j)).
{ unfold sb_cells. eapply rheap_pres_rw_cells; [exact HP5| exact X4|]. right; right. exists (sbd_blk s, S, SBSTATE_SIZEOF).
split; [apply in_lb_remove_keep; [left; reflexivity| cbn; apply not_eq_sym; eapply (NoDup_app_in_neq [blk_id (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s)] (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: [(sbd_old_qlsp s, a_oq a, 32); (sbd_interp_qlpc s, a_iq a, 32); (sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] ++ LBr))); [| left; reflexivity| left; reflexivity]]|].
2:{ unfold blk_addr, blk_size, SBSTATE_SIZEOF. cbn [fst snd]. rewrite sb_cells_size. lia. }
eapply Permutation_NoDup; [| exact ND4]. cbn [map app]. apply perm_swap. }
assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp + -16) [C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP5| exact FR4| left; cbn; lia]).
assert (HPacc5 : rheap_pres LBr (bv_unsigned sp) m m5).
{ eapply rheap_pres_trans; [exact HPacc4|]. eapply rheap_pres_weaken; [exact HP5| lia|]. intros b Hb. apply in_lb_remove_keep; [cbn [app sb_blocks In]; repeat right; exact Hb|].
apply not_eq_sym. eapply (NoDup_app_in_neq (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) :: [(sbd_old_qlsp s, a_oq a, 32); (sbd_interp_qlpc s, a_iq a, 32); (sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)])) (map blk_id LBr)); [| right; left; reflexivity| apply in_map; exact Hb].
rewrite <- map_app. exact ND4. }
clear X4 FR4 HP5 HEAP4 AUX4 ERR4 MI4 ST4 ND4 HPacc4 PSF5.
unfold sb_cells in X5.

eapply (implM_evt rsegs _ _ _ (fun ms => ms = _)). { step. step. apply evt_done. reflexivity. }
cbv beta. intros ms_oq ->.
eapply implM_bind.
{ eapply (rfree_spec_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 s4' _ (sbd_old_qlsp s) (a_oq a) (32) lo AB _ HEAP5).
- cbn [app]. right. left. reflexivity.
- exact AUX5.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST5.
- exact CLO.
- rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
- rewrite ETP. unfold RERRNO. exact ERR5.
- exact MI5.
- exact TPE.
- reflexivity. }
cbv beta. intros [] s5' ms6' PF. first [ sf_destruct 25%nat PF as z0x6 z1x6 z2x6 za0x6 za1x6 za2x6 za3x6 za4x6 za5x6 za6x6 za7x6 z3x6 z4x6 z5x6 z6x6 m6 -> MI6 ST6 ERR6 AUX6 HP6 PSF6 PSO6 HEAP6 | sf_fb; destruct PF as (z0x6 & z1x6 & z2x6 & za0x6 & za1x6 & za2x6 & za3x6 & za4x6 & za5x6 & za6x6 & za7x6 & z3x6 & z4x6 & z5x6 & z6x6 & m6 & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & PSF6 & PSO6 & HEAP6) ].
rewrite unsigned_lit in ST6 by lia. rewrite unsigned_lit in HP6 by lia. rewrite ret_pc_even by lia. rewrite ETP in ERR6. unfold RERRNO in ERR6.
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP5) as ND5.
apply (RHEAP_perm _ _ ((sbd_blk s, S, SBSTATE_SIZEOF) :: [(sbd_interp_qlpc s, a_iq a, 32); (sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] ++ LBr)) in HEAP6.
2:{ apply (lb_remove_perm_of _ (sbd_old_qlsp s, a_oq a, 32)); [| exact ND5]. cbn [app]. apply perm_swap. }
assert (X6 : rw_cells rsegs m6 S (SBCELLS s a OUT j)).
{ unfold sb_cells. eapply rheap_pres_rw_cells; [exact HP6| exact X5|]. right; right. exists (sbd_blk s, S, SBSTATE_SIZEOF).
split; [apply in_lb_remove_keep; [left; reflexivity| cbn; apply not_eq_sym; eapply (NoDup_app_in_neq [blk_id (sbd_old_qlsp s, a_oq a, 32)] (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: [(sbd_interp_qlpc s, a_iq a, 32); (sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] ++ LBr))); [| left; reflexivity| left; reflexivity]]|].
2:{ unfold blk_addr, blk_size, SBSTATE_SIZEOF. cbn [fst snd]. rewrite sb_cells_size. lia. }
eapply Permutation_NoDup; [| exact ND5]. cbn [map app]. apply perm_swap. }
assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp + -16) [C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP6| exact FR5| left; cbn; lia]).
assert (HPacc6 : rheap_pres LBr (bv_unsigned sp) m m6).
{ eapply rheap_pres_trans; [exact HPacc5|]. eapply rheap_pres_weaken; [exact HP6| lia|]. intros b Hb. apply in_lb_remove_keep; [cbn [app sb_blocks In]; repeat right; exact Hb|].
apply not_eq_sym. eapply (NoDup_app_in_neq (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: (sbd_old_qlsp s, a_oq a, 32) :: [(sbd_interp_qlpc s, a_iq a, 32); (sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)])) (map blk_id LBr)); [| right; left; reflexivity| apply in_map; exact Hb].
rewrite <- map_app. exact ND5. }
clear X5 FR5 HP6 HEAP5 AUX5 ERR5 MI5 ST5 ND5 HPacc5 PSF6.
unfold sb_cells in X6.

eapply (implM_evt rsegs _ _ _ (fun ms => ms = _)). { step. step. apply evt_done. reflexivity. }
cbv beta. intros ms_iq ->.
eapply implM_bind.
{ eapply (rfree_spec_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 s5' _ (sbd_interp_qlpc s) (a_iq a) (32) lo AB _ HEAP6).
- cbn [app]. right. left. reflexivity.
- exact AUX6.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST6.
- exact CLO.
- rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
- rewrite ETP. unfold RERRNO. exact ERR6.
- exact MI6.
- exact TPE.
- reflexivity. }
cbv beta. intros [] s6' ms7' PF. first [ sf_destruct 25%nat PF as z0x7 z1x7 z2x7 za0x7 za1x7 za2x7 za3x7 za4x7 za5x7 za6x7 za7x7 z3x7 z4x7 z5x7 z6x7 m7 -> MI7 ST7 ERR7 AUX7 HP7 PSF7 PSO7 HEAP7 | sf_fb; destruct PF as (z0x7 & z1x7 & z2x7 & za0x7 & za1x7 & za2x7 & za3x7 & za4x7 & za5x7 & za6x7 & za7x7 & z3x7 & z4x7 & z5x7 & z6x7 & m7 & -> & MI7 & ST7 & ERR7 & AUX7 & HP7 & PSF7 & PSO7 & HEAP7) ].
rewrite unsigned_lit in ST7 by lia. rewrite unsigned_lit in HP7 by lia. rewrite ret_pc_even by lia. rewrite ETP in ERR7. unfold RERRNO in ERR7.
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP6) as ND6.
apply (RHEAP_perm _ _ ((sbd_blk s, S, SBSTATE_SIZEOF) :: [(sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] ++ LBr)) in HEAP7.
2:{ apply (lb_remove_perm_of _ (sbd_interp_qlpc s, a_iq a, 32)); [| exact ND6]. cbn [app]. apply perm_swap. }
assert (X7 : rw_cells rsegs m7 S (SBCELLS s a OUT j)).
{ unfold sb_cells. eapply rheap_pres_rw_cells; [exact HP7| exact X6|]. right; right. exists (sbd_blk s, S, SBSTATE_SIZEOF).
split; [apply in_lb_remove_keep; [left; reflexivity| cbn; apply not_eq_sym; eapply (NoDup_app_in_neq [blk_id (sbd_interp_qlpc s, a_iq a, 32)] (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: [(sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] ++ LBr))); [| left; reflexivity| left; reflexivity]]|].
2:{ unfold blk_addr, blk_size, SBSTATE_SIZEOF. cbn [fst snd]. rewrite sb_cells_size. lia. }
eapply Permutation_NoDup; [| exact ND6]. cbn [map app]. apply perm_swap. }
assert (FR7 : rw_cells rsegs m7 (bv_unsigned sp + -16) [C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP7| exact FR6| left; cbn; lia]).
assert (HPacc7 : rheap_pres LBr (bv_unsigned sp) m m7).
{ eapply rheap_pres_trans; [exact HPacc6|]. eapply rheap_pres_weaken; [exact HP7| lia|]. intros b Hb. apply in_lb_remove_keep; [cbn [app sb_blocks In]; repeat right; exact Hb|].
apply not_eq_sym. eapply (NoDup_app_in_neq (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: (sbd_interp_qlpc s, a_iq a, 32) :: [(sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)])) (map blk_id LBr)); [| right; left; reflexivity| apply in_map; exact Hb].
rewrite <- map_app. exact ND6. }
clear X6 FR6 HP7 HEAP6 AUX6 ERR6 MI6 ST6 ND6 HPacc6 PSF7.
unfold sb_cells in X7.

eapply (implM_evt rsegs _ _ _ (fun ms => ms = _)). { step. step. apply evt_done. reflexivity. }
cbv beta. intros ms_pg ->.
eapply implM_bind.
{ eapply (rfree_spec_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 s6' _ (sbd_pi_gain s) (a_pg a) (16) lo AB _ HEAP7).
- cbn [app]. right. left. reflexivity.
- exact AUX7.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST7.
- exact CLO.
- rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
- rewrite ETP. unfold RERRNO. exact ERR7.
- exact MI7.
- exact TPE.
- reflexivity. }
cbv beta. intros [] s7' ms8' PF. first [ sf_destruct 25%nat PF as z0x8 z1x8 z2x8 za0x8 za1x8 za2x8 za3x8 za4x8 za5x8 za6x8 za7x8 z3x8 z4x8 z5x8 z6x8 m8 -> MI8 ST8 ERR8 AUX8 HP8 PSF8 PSO8 HEAP8 | sf_fb; destruct PF as (z0x8 & z1x8 & z2x8 & za0x8 & za1x8 & za2x8 & za3x8 & za4x8 & za5x8 & za6x8 & za7x8 & z3x8 & z4x8 & z5x8 & z6x8 & m8 & -> & MI8 & ST8 & ERR8 & AUX8 & HP8 & PSF8 & PSO8 & HEAP8) ].
rewrite unsigned_lit in ST8 by lia. rewrite unsigned_lit in HP8 by lia. rewrite ret_pc_even by lia. rewrite ETP in ERR8. unfold RERRNO in ERR8.
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP7) as ND7.
apply (RHEAP_perm _ _ ((sbd_blk s, S, SBSTATE_SIZEOF) :: [(sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] ++ LBr)) in HEAP8.
2:{ apply (lb_remove_perm_of _ (sbd_pi_gain s, a_pg a, 16)); [| exact ND7]. cbn [app]. apply perm_swap. }
assert (X8 : rw_cells rsegs m8 S (SBCELLS s a OUT j)).
{ unfold sb_cells. eapply rheap_pres_rw_cells; [exact HP8| exact X7|]. right; right. exists (sbd_blk s, S, SBSTATE_SIZEOF).
split; [apply in_lb_remove_keep; [left; reflexivity| cbn; apply not_eq_sym; eapply (NoDup_app_in_neq [blk_id (sbd_pi_gain s, a_pg a, 16)] (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: [(sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] ++ LBr))); [| left; reflexivity| left; reflexivity]]|].
2:{ unfold blk_addr, blk_size, SBSTATE_SIZEOF. cbn [fst snd]. rewrite sb_cells_size. lia. }
eapply Permutation_NoDup; [| exact ND7]. cbn [map app]. apply perm_swap. }
assert (FR8 : rw_cells rsegs m8 (bv_unsigned sp + -16) [C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP8| exact FR7| left; cbn; lia]).
assert (HPacc8 : rheap_pres LBr (bv_unsigned sp) m m8).
{ eapply rheap_pres_trans; [exact HPacc7|]. eapply rheap_pres_weaken; [exact HP8| lia|]. intros b Hb. apply in_lb_remove_keep; [cbn [app sb_blocks In]; repeat right; exact Hb|].
apply not_eq_sym. eapply (NoDup_app_in_neq (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: (sbd_pi_gain s, a_pg a, 16) :: [(sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)])) (map blk_id LBr)); [| right; left; reflexivity| apply in_map; exact Hb].
rewrite <- map_app. exact ND7. }
clear X7 FR7 HP8 HEAP7 AUX7 ERR7 MI7 ST7 ND7 HPacc7 PSF8.
unfold sb_cells in X8.

eapply (implM_evt rsegs _ _ _ (fun ms => ms = _)). { step. step. apply evt_done. reflexivity. }
cbv beta. intros ms_er ->.
eapply implM_bind.
{ eapply (rfree_spec_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 s7' _ (sbd_exc_rms s) (a_er a) (16) lo AB _ HEAP8).
- cbn [app]. right. left. reflexivity.
- exact AUX8.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST8.
- exact CLO.
- rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
- rewrite ETP. unfold RERRNO. exact ERR8.
- exact MI8.
- exact TPE.
- reflexivity. }
cbv beta. intros [] s8' ms9' PF. first [ sf_destruct 25%nat PF as z0x9 z1x9 z2x9 za0x9 za1x9 za2x9 za3x9 za4x9 za5x9 za6x9 za7x9 z3x9 z4x9 z5x9 z6x9 m9 -> MI9 ST9 ERR9 AUX9 HP9 PSF9 PSO9 HEAP9 | sf_fb; destruct PF as (z0x9 & z1x9 & z2x9 & za0x9 & za1x9 & za2x9 & za3x9 & za4x9 & za5x9 & za6x9 & za7x9 & z3x9 & z4x9 & z5x9 & z6x9 & m9 & -> & MI9 & ST9 & ERR9 & AUX9 & HP9 & PSF9 & PSO9 & HEAP9) ].
rewrite unsigned_lit in ST9 by lia. rewrite unsigned_lit in HP9 by lia. rewrite ret_pc_even by lia. rewrite ETP in ERR9. unfold RERRNO in ERR9.
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP8) as ND8.
apply (RHEAP_perm _ _ ((sbd_blk s, S, SBSTATE_SIZEOF) :: [(sbd_mem_sp s, a_msp a, 64)] ++ LBr)) in HEAP9.
2:{ apply (lb_remove_perm_of _ (sbd_exc_rms s, a_er a, 16)); [| exact ND8]. cbn [app]. apply perm_swap. }
assert (X9 : rw_cells rsegs m9 S (SBCELLS s a OUT j)).
{ unfold sb_cells. eapply rheap_pres_rw_cells; [exact HP9| exact X8|]. right; right. exists (sbd_blk s, S, SBSTATE_SIZEOF).
split; [apply in_lb_remove_keep; [left; reflexivity| cbn; apply not_eq_sym; eapply (NoDup_app_in_neq [blk_id (sbd_exc_rms s, a_er a, 16)] (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: [(sbd_mem_sp s, a_msp a, 64)] ++ LBr))); [| left; reflexivity| left; reflexivity]]|].
2:{ unfold blk_addr, blk_size, SBSTATE_SIZEOF. cbn [fst snd]. rewrite sb_cells_size. lia. }
eapply Permutation_NoDup; [| exact ND8]. cbn [map app]. apply perm_swap. }
assert (FR9 : rw_cells rsegs m9 (bv_unsigned sp + -16) [C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP9| exact FR8| left; cbn; lia]).
assert (HPacc9 : rheap_pres LBr (bv_unsigned sp) m m9).
{ eapply rheap_pres_trans; [exact HPacc8|]. eapply rheap_pres_weaken; [exact HP9| lia|]. intros b Hb. apply in_lb_remove_keep; [cbn [app sb_blocks In]; repeat right; exact Hb|].
apply not_eq_sym. eapply (NoDup_app_in_neq (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: (sbd_exc_rms s, a_er a, 16) :: [(sbd_mem_sp s, a_msp a, 64)])) (map blk_id LBr)); [| right; left; reflexivity| apply in_map; exact Hb].
rewrite <- map_app. exact ND8. }
clear X8 FR8 HP9 HEAP8 AUX8 ERR8 MI8 ST8 ND8 HPacc8 PSF9.
unfold sb_cells in X9.

eapply (implM_evt rsegs _ _ _ (fun ms => ms = _)). { step. step. apply evt_done. reflexivity. }
cbv beta. intros ms_ms ->.
eapply implM_bind.
{ eapply (rfree_spec_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 s8' _ (sbd_mem_sp s) (a_msp a) (64) lo AB _ HEAP9).
- cbn [app]. right. left. reflexivity.
- exact AUX9.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST9.
- exact CLO.
- rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
- rewrite ETP. unfold RERRNO. exact ERR9.
- exact MI9.
- exact TPE.
- reflexivity. }
cbv beta. intros [] s9' ms10' PF. first [ sf_destruct 25%nat PF as z0x10 z1x10 z2x10 za0x10 za1x10 za2x10 za3x10 za4x10 za5x10 za6x10 za7x10 z3x10 z4x10 z5x10 z6x10 m10 -> MI10 ST10 ERR10 AUX10 HP10 PSF10 PSO10 HEAP10 | sf_fb; destruct PF as (z0x10 & z1x10 & z2x10 & za0x10 & za1x10 & za2x10 & za3x10 & za4x10 & za5x10 & za6x10 & za7x10 & z3x10 & z4x10 & z5x10 & z6x10 & m10 & -> & MI10 & ST10 & ERR10 & AUX10 & HP10 & PSF10 & PSO10 & HEAP10) ].
rewrite unsigned_lit in ST10 by lia. rewrite unsigned_lit in HP10 by lia. rewrite ret_pc_even by lia. rewrite ETP in ERR10. unfold RERRNO in ERR10.
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP9) as ND9.
apply (RHEAP_perm _ _ ((sbd_blk s, S, SBSTATE_SIZEOF) :: [] ++ LBr)) in HEAP10.
2:{ apply (lb_remove_perm_of _ (sbd_mem_sp s, a_msp a, 64)); [| exact ND9]. cbn [app]. apply perm_swap. }
assert (X10 : rw_cells rsegs m10 S (SBCELLS s a OUT j)).
{ unfold sb_cells. eapply rheap_pres_rw_cells; [exact HP10| exact X9|]. right; right. exists (sbd_blk s, S, SBSTATE_SIZEOF).
split; [apply in_lb_remove_keep; [left; reflexivity| cbn; apply not_eq_sym; eapply (NoDup_app_in_neq [blk_id (sbd_mem_sp s, a_msp a, 64)] (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: [] ++ LBr))); [| left; reflexivity| left; reflexivity]]|].
2:{ unfold blk_addr, blk_size, SBSTATE_SIZEOF. cbn [fst snd]. rewrite sb_cells_size. lia. }
eapply Permutation_NoDup; [| exact ND9]. cbn [map app]. apply perm_swap. }
assert (FR10 : rw_cells rsegs m10 (bv_unsigned sp + -16) [C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP10| exact FR9| left; cbn; lia]).
assert (HPacc10 : rheap_pres LBr (bv_unsigned sp) m m10).
{ eapply rheap_pres_trans; [exact HPacc9|]. eapply rheap_pres_weaken; [exact HP10| lia|]. intros b Hb. apply in_lb_remove_keep; [cbn [app sb_blocks In]; repeat right; exact Hb|].
apply not_eq_sym. eapply (NoDup_app_in_neq (map blk_id ((sbd_blk s, S, SBSTATE_SIZEOF) :: (sbd_mem_sp s, a_msp a, 64) :: [])) (map blk_id LBr)); [| right; left; reflexivity| apply in_map; exact Hb].
rewrite <- map_app. exact ND9. }
clear X9 FR9 HP10 HEAP9 AUX9 ERR9 MI9 ST9 ND9 HPacc9 PSF10.
unfold sb_cells in X10.

eapply (implM_evt rsegs _ _ _ (fun ms => ms = _)). { step. step. step. step. step. apply evt_done. reflexivity. }
cbv beta. intros ms_fin ->.
release_frame FR10 ST10 (bv_unsigned sp).
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP10) as ND10.
eapply implM_mono.
{ eapply (rfree_spec_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m10 s9' _ (sbd_blk s) S SBSTATE_SIZEOF lo AB _ HEAP10).
- left. reflexivity.
- exact AUX10.
- exact SB.
- exact ST10.
- exact CLO.
- unfold RFREE_STACK. lia.
- rewrite ETP. unfold RERRNO. exact ERR10.
- exact MI10.
- exact TPE.
- reflexivity. }
cbv beta. intros [] s10' ms11' PF. first [ sf_destruct 25%nat PF as z0x11 z1x11 z2x11 za0x11 za1x11 za2x11 za3x11 za4x11 za5x11 za6x11 za7x11 z3x11 z4x11 z5x11 z6x11 m11 -> MI11 ST11 ERR11 AUX11 HP11 PSF11 PSO11 HEAP11' | sf_fb; destruct PF as (z0x11 & z1x11 & z2x11 & za0x11 & za1x11 & za2x11 & za3x11 & za4x11 & za5x11 & za6x11 & za7x11 & z3x11 & z4x11 & z5x11 & z6x11 & m11 & -> & MI11 & ST11 & ERR11 & AUX11 & HP11 & PSF11 & PSO11 & HEAP11') ].
apply (RHEAP_perm _ _ LBr) in HEAP11'.
2:{ apply (lb_remove_perm_of _ (sbd_blk s, S, SBSTATE_SIZEOF)); [| exact ND10]. cbn [app]. apply Permutation_refl. }
unfold rdes_post. sf_eexists 15%nat. first [ unshelve sf_eexists 4%nat; [ exact (F1) | exact (fc1) | exact (m11) | exact (errv1) | ] | sf_fb; exists F1, fc1, m11, errv1 ].
split; [reflexivity|]. split; [exact FRM1|]. split; [exact MI11|]. split; [exact ST11|]. split; [exact ERR11|]. split; [exact AUX11|].
split.
{ eapply rheap_pres_trans; [exact HPacc10|]. eapply rheap_pres_weaken; [exact HP11| lia|]. intros b Hb. apply in_lb_remove_keep; [cbn [app sb_blocks In]; repeat right; exact Hb|].
apply not_eq_sym. eapply (NoDup_app_in_neq (map blk_id [(sbd_blk s, S, SBSTATE_SIZEOF)]) (map blk_id LBr)); [| left; reflexivity| apply in_map; exact Hb].
rewrite <- map_app. exact ND10. }
split; [| exact HEAP11'].
rewrite PSO11, PSO10, PSO9, PSO8, PSO7, PSO6, PSO5, PSO4, PSO3. exact PSO2.
Qed.

Theorem rdes_all {RCEIL : RunCeiling} : forall d, rdes_at d.
Proof. induction d as [st|s low IH]; [apply rdes_nb| apply rdes_sb; exact IH]. Qed.

Lemma des_depth_le : forall d : dec_state bptr, (dec_depth d <= 3)%nat -> des_depth d <= 8224.
Proof.
intros d Hd. destruct d as [st|s1 [st|s2 [st|s3 low]]]; cbn -[Z.add]; unfold RFREE_STACK; try lia.
exfalso. cbn in Hd. pose proof (dec_depth_pos low). lia.
Qed.

Theorem rspx_decoder_destroy_proof {RCEIL : RunCeiling} : rspx_decoder_destroy_stmt DECREP.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ps LB LBD LBr STEREO S d AB lo errv
HEAP PERM REP TP AUX SB ABB ST CLO LO ERR MI FRM TPE HA0.
first [ sf_destruct 7%nat REP as TOP DE ND LAP NE OUT R | sf_fb; destruct REP as (TOP & DE & ND & LAP & NE & OUT & R) ]. unfold DEC_DESTROY_STACK in LO. unfold wz in TPE, HA0.
pose proof (des_depth_le d DE) as DD.
eapply (rdes_all d OUT STEREO S LBD LB LBr ps lo AB errv); try eassumption. lia.
Qed.

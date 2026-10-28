(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bj X1bs X1c2 X1br X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1m6 X1kx X1el X1ec. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h7 X1go X1hk X1ho X1n8 X1my X1nc X1ne X1nf.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1r3 X1r4 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c4.
Local Ltac plia_gen stock ::= plia_size stock.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Lemma dbl_mod32 : forall lr, (lr mod 2^64 * 2) mod 2^64 mod 2^32 = (lr * 2) mod 2^32.
Proof.
intros lr. rewrite mod64_mod32.
replace (lr mod 2^64 * 2) with (lr * 2 + (- (lr / 2^64) * 2 * 2^32) * 2^32) by (Z.div_mod_to_equations; lia).
apply Z_mod_plus_full.
Qed.

Lemma land3_mod4 : forall v, Z.land v 3 = v mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; rewrite ?land3_mod4 in K; rewrite ?signed_lit_small in K by lia; [exfalso; lia | clear K].
Ltac nt := first [ if_false_x | ntk ].

Theorem rinit_sbA2 {RCEIL : RunCeiling} : forall (mo : spx_mode)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(s : PState) (LB : list block) (AB lo : Z) (m0 : mem),
(mo = ModeWB \/ mo = ModeUWB) ->
bv_unsigned sp <= AB -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - init_depth mo -> tp = Z_to_bv 64 RATP ->
(forall blk S lr low LBL st1 ms1,
sb_at78 mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s LB AB lo m0 blk S lr low LBL st1 ms1 ->
implM rsegs (sb_init_rest mo blk lr low) st1 (rinit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo mo m0) ms1) ->
forall blk S low LBL st ms,
sb_at40 mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m0 blk S low LBL st ms ->
implM rsegs (sb_init_rest2 mo blk low) st (rinit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo mo m0) ms.
Proof.
intros mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s LB AB lo m0 Hmo SB CLO LO TPE KONT blk S low LBL st ms sfH_; first [ sf_destruct 46%nat sfH_ as t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F5 fc m errv j8 SL lr -> FRM MI ST FR ERR AUX PRES PSO TP HEAP BR SLB XA XP LRR ELR XB RL DM DD RATE STO NES SP16 | sf_fb; destruct sfH_ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F5 & fc & m & errv & j8 & SL & lr & -> & FRM & MI & ST & FR & ERR & AUX & PRES & PSO & TP & HEAP & BR & SLB & XA & XP & LRR & ELR & XB & RL & DM & DD & RATE & STO & NES & SP16) ].
pose proof (mode_facts mo Hmo) as sfP_; first [ sf_destruct 7%nat sfP_ as FSS LPC NBS DSM IDP IRT MDP | sf_fb; destruct sfP_ as (FSS & LPC & NBS & DSM & IDP & IRT & MDP) ]. rewrite IDP in LO. clear FSS LPC NBS IRT MDP.
pose proof CLO as CLOv. unfold alloc_ceiling in CLOv.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (ETP : errno_addr tp = RERRNO) by (rewrite TPE; unfold RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity).
rewrite ETP in ERR. unfold RERRNO in ERR.
assert (IDL : 8272 <= init_depth (lower_mode mo)) by (destruct Hmo as [-> | ->]; cbn; lia).
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as S0 S16 _ SCE SIMG | sf_fb; destruct sfP_ as (S0 & S16 & _ & SCE & SIMG) ]. unfold alloc_ceiling, SBSTATE_SIZEOF in SCE. unfold SBSTATE_SIZEOF in SIMG.
unfold sb_init_rest2. destruct (speex_decoder_ctl low CtlGetSamplingRate) as [lr' low1] eqn:EC1. cbn [fst snd] in ELR, RL, RATE. subst lr'.
destruct (speex_decoder_ctl low1 (CtlSetWideband 1)) as [vv low2] eqn:EC2.

pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP) as ND.
assert (NDL : List.NoDup (map blk_id LBL)) by (pose proof ND as ND'; rewrite map_app in ND'; apply List.NoDup_app_remove_r in ND'; exact ND').
assert (LAPL : lbd_apart LBL).
{ intros b1 b2 H1 H2 NE. eapply (RHEAP_blocks_disjoint_proof _ _ _ b1 b2 HEAP); [apply in_app_iff; left; exact H1| apply in_app_iff; left; exact H2| exact NE]. }
assert (BRL : forall b, In b LBL -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; eapply RHEAP_block_range_proof; [exact HEAP| apply in_app_iff; left; exact Hb]).
assert (SAPL : forall b, In b LBL -> S + 160 <= blk_addr b \/ blk_addr b + blk_size b <= S).
{ intros b Hb. destruct (RHEAP_blocks_disjoint_proof _ _ _ (blk, S, SBSTATE_SIZEOF) b HEAP ltac:(apply in_app_iff; right; left; reflexivity) ltac:(apply in_app_iff; left; exact Hb)) as [D|D].
{ intros E. pose proof ND as ND'. rewrite map_app in ND'. eapply (NoDup_app_in_neq _ _ _ _ ND'); [apply in_map; exact Hb| left; reflexivity| cbn; cbn in E; rewrite E; reflexivity]. }
all: cbn [blk_addr blk_size fst snd] in D |- *; unfold SBSTATE_SIZEOF in D; lia. }
assert (BLB : forall b, In b LB -> blk_addr b + blk_size b <= alloc_ceiling /\ (S + 160 <= blk_addr b \/ blk_addr b + blk_size b <= S)
/\ (forall b', In b' LBL -> blk_addr b' + blk_size b' <= blk_addr b \/ blk_addr b + blk_size b <= blk_addr b')).
{ intros b Hb. split; [| split].
- first [ pose proof (RHEAP_block_range_proof _ _ _ _ HEAP ltac:(apply in_app_iff; right; right; exact Hb)) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (RHEAP_block_range_proof _ _ _ _ HEAP ltac:(apply in_app_iff; right; right; exact Hb)) as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. lia.
- destruct (RHEAP_blocks_disjoint_proof _ _ _ (blk, S, SBSTATE_SIZEOF) b HEAP ltac:(apply in_app_iff; right; left; reflexivity) ltac:(apply in_app_iff; right; right; exact Hb)) as [D|D].
{ intros E. pose proof ND as ND'. rewrite map_app in ND'. cbn [map] in ND'. apply List.NoDup_app_remove_l in ND'. apply (proj1 (List.NoDup_cons_iff _ _)) in ND'. destruct ND' as [NI _]. apply NI. cbn [blk_id fst snd] in E |- *. rewrite E. apply in_map. exact Hb. }
all: cbn [blk_addr blk_size fst snd] in D |- *; unfold SBSTATE_SIZEOF in D; lia.
- intros b' Hb'. destruct (RHEAP_blocks_disjoint_proof _ _ _ b' b HEAP ltac:(apply in_app_iff; left; exact Hb') ltac:(apply in_app_iff; right; right; exact Hb)) as [D|D]; [| lia| lia].
intros E. pose proof ND as ND'. rewrite map_app in ND'. eapply (NoDup_app_in_neq _ _ _ _ ND'); [apply in_map; exact Hb'| right; apply in_map; exact Hb| exact E]. }
assert (DDL : (dec_depth low1 <= 2)%nat).
{ pose proof (ctl_depth_same low CtlGetSamplingRate) as E. rewrite EC1 in E. cbn [snd] in E. rewrite E, DD. destruct Hmo as [-> | ->]; cbn; lia. }
pose proof (ctl_depth_le low1 ltac:(lia)) as CDL.

unfold sbinit_frame0 in FR.
assert (LRB : 0 < lr <= 16000) by (destruct Hmo as [-> | ->]; cbn in RATE; lia).
eapply (implM_evt rsegs _ _ _ (fun ms5 => exists m5 (srw : word) j4,
ms5 = MS (mkR (Z_to_bv 64 0x2e544) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 1073741824)
(Z_to_bv 64 SL) (Z_to_bv 64 105) (Z_to_bv 64 (bv_unsigned sp + -48 + 4)) a3 a4 a5 a6 a7
(Z_to_bv 64 (sbmode_addr mo)) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F5 (Z_to_bv 64 A_speex_decoder_ctl) fc None m5 (seg_rom rsegs)
/\ rw_cells rsegs m5 (S + 40) [C4 srw] /\ bv_unsigned srw mod 2^32 = (lr * 2) mod 2^32
/\ rw_cells rsegs m5 (bv_unsigned sp + -48) (sbinit_frame j4 (Z_to_bv 64 1) s3 s2 s1 s0 ra)
/\ munch [(S + 40, S + 44); (bv_unsigned sp + -48, bv_unsigned sp + -40)] m m5 /\ wmono rsegs m m5 /\ mem_inv rsegs m5)).
{ pose proof (munch_refl [(S + 40, S + 44); (bv_unsigned sp + -48, bv_unsigned sp + -40)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
clear PRES HEAP. assert (SLT : S + 160 <= bv_unsigned sp + -48) by lia.
step. rewrite sx32_lit by lia. zstep. zstep. zstep. rewrite ?(swrap32_small (lr + 1073741824)) by lia. nt.
step. step. lstep. step. lstep. step. step. rewrite ?unsigned_lit by lia. step.
apply evt_done. sf_eexists 3%nat. split; [reflexivity|]. split; [eassumption|].
split.
{ rewrite Z_to_bv_unsigned, Z.shiftl_mul_pow2, Z_to_bv_unsigned by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64). change (2^1) with 2.
apply dbl_mod32. }
split; [unfold sbinit_frame; eassumption|]. split; [exact MU|]. split; [exact WM| assumption]. }
cbv beta. intros ms5 sfH_; first [ sf_destruct 10%nat sfH_ as m5 srw j4 -> XP5 SRW FR5 MU5 WM5 MI5 | sf_fb; destruct sfH_ as (m5 & srw & j4 & -> & XP5 & SRW & FR5 & MU5 & WM5 & MI5) ].
assert (SLT : S + 160 <= bv_unsigned sp + -48) by lia.
assert (XA5 : rw_cells rsegs m5 S [C8 (Z_to_bv 64 (mode_addr mo)); C8 (Z_to_bv 64 SL); C4 (Z_to_bv 64 (2 * sbm_frameSize mo)); C4 (Z_to_bv 64 (sbm_frameSize mo));
C4 (Z_to_bv 64 (sbm_subframeSize mo)); C4 (Z_to_bv 64 4); C4 (Z_to_bv 64 8); C4 w0]).
{ eapply rw_cells_transport; [exact XA| exact MU5| exact WM5| cbn; lia]. }
assert (XB5 : rw_cells rsegs m5 (S + 44) [C4 w0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 w0; C4 w0; C4 (Z_to_bv 64 1); CB 4 z4; C8 (Z_to_bv 64 0); C4 w0; CB 4 z4]).
{ eapply rw_cells_transport; [exact XB| exact MU5| exact WM5| cbn; lia]. }
assert (ERR5 : rw_cells rsegs m5 316332 [C4 errv]) by (eapply rw_cells_transport; [exact ERR| exact MU5| exact WM5| cbn; lia]).
assert (HEAP5 : RHEAP st (LBL ++ (blk, S, SBSTATE_SIZEOF) :: LB) m5).
{ eapply RHEAP_frame_proof; [exact HEAP| exact MU5| exact WM5|]. constructor; [| constructor; [| constructor]].
- right. right. exists (blk, S, SBSTATE_SIZEOF). split; [apply in_app_iff; right; left; reflexivity|]. cbn. unfold SBSTATE_SIZEOF. lia.
- left. cbn. unfold alloc_ceiling. lia. }
assert (AUX5 : rauxv_ok m5 AB).
{ eapply rauxv_ok_frame; [exact AUX| exact MU5| exact WM5|]. constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold RAUXV_CELL; lia. }
assert (ST5 : stk rsegs m5 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST| exact MU5| exact WM5| cbn; lia]).
assert (TP5 : rtables_pristine m5).
{ eapply rtables_pristine_munch; [exact TP| exact MU5|]. intros x Hx. unfold RTABLES_LO, RTABLES_HI in Hx. cbn. lia. }
assert (RL5 : forall STEREO, DREP 0 STEREO m5 SL low1 LBL).
{ intros STEREO. eapply decst_rep_munch; [exact (RL STEREO)| exact MU5| exact WM5|]. intros b x Hb Hx. pose proof (SAPL _ Hb). first [ pose proof (BRL _ Hb) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (BRL _ Hb) as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. cbn. lia. }
assert (PRES5 : rheap_pres LB (bv_unsigned sp) m0 m5).
{ eapply rheap_pres_trans; [exact PRES|]. eapply rheap_pres_of_munch; [exact MU5| exact WM5|]. intros x Hx CA.
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in CA. cbn.
destruct CA as [CA|[CA|(b' & Hb' & Hab')]]; [lia| lia|]. unfold in_block in Hab'. destruct (BLB _ Hb') as (B1 & B2 & _). lia. }
clear XA XP XB ERR HEAP AUX ST TP RL PRES MU5 WM5 MI FR.

unfold sbinit_frame in FR5.
apply (rw_cells_app rsegs m5 (bv_unsigned sp + -48) [CB 4 j4]) in FR5. destruct FR5 as [FRj FR5]. cbn [cells_size csize Nat.add] in FR5.
apply (rw_cells_app rsegs m5 _ [C4 (Z_to_bv 64 1)]) in FR5. destruct FR5 as [FRt FRr]. cbn [cells_size csize Nat.add] in FRr.
replace (bv_unsigned sp + -48 + Z.of_nat 4) with (bv_unsigned sp + -48 + 4) in FRt by lia.
replace (bv_unsigned sp + -48 + Z.of_nat 4 + Z.of_nat 4) with (bv_unsigned sp + -40) in FRr by lia.
eapply (implM_evt rsegs).
{ eapply (rctl_all low1 0 0 SL LBL (CtlSetWideband 1) (bv_unsigned sp + -48 + 4) lo); try reflexivity.
all: first [ exact (RL5 0) | exact TP5 | exact BRL | exact NDL | exact LAPL | exact MI5 | exact FRM | exact CLO
| (cbn [creq_ok]; right; reflexivity)
| (cbn [creq_pre]; exists (Z_to_bv 64 1); split; [exact FRt| split; [reflexivity| lia]])
| (rewrite unsigned_lit by lia; exact ST5)
| (cbn [creq_size]; intros b Hb; first [ pose proof (BRL _ Hb) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (BRL _ Hb) as (_ & _ & _ & BC & _) ]; unfold alloc_ceiling in BC; lia)
| (cbn [creq_ptr_ok]; lia)
| (cbn [creq_size]; rewrite ?unsigned_lit by lia; lia)
| lia ]. }
cbv beta. intros ms6 sfH_; first [ sf_destruct 26%nat sfH_ as u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 F6 fc6 m6 -> MU6 WM6 MI6 FRM6 ST6 RL6 CP6 _ | sf_fb; destruct sfH_ as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & F6 & fc6 & m6 & -> & MU6 & WM6 & MI6 & FRM6 & ST6 & RL6 & CP6 & _) ].
rewrite unsigned_lit in MU6 by lia. rewrite unsigned_lit in ST6 by lia. rewrite ret_pc_even by lia. rewrite EC2 in RL6. cbn [snd] in RL6.
cbn [creq_post] in CP6. destruct CP6 as (tmp & FRt6 & _).
assert (OUTW : forall x, (S <= x < S + 160 \/ bv_unsigned sp + -48 <= x < bv_unsigned sp + -44 \/ bv_unsigned sp + -40 <= x < bv_unsigned sp
\/ (316332 <= x < 316336) \/ (RTABLES_LO <= x < RTABLES_HI)) ->
outside (ctlW lo (bv_unsigned sp + -48) (bv_unsigned sp + -48 + 4) (CtlSetWideband 1) LBL) x).
{ intros x Hx. apply outside_ctlW. cbn [creq_size]. unfold RTABLES_LO, RTABLES_HI in Hx. split; [lia| split; [lia|]].
intros b Hb. pose proof (SAPL _ Hb) as D. first [ pose proof (BRL _ Hb) as sfP_; sf_destruct 5%nat sfP_ as B0 _ _ BC BW | sf_fb; destruct (BRL _ Hb) as (B0 & _ & _ & BC & BW) ]. unfold alloc_ceiling in BC. lia. }
assert (XA6 : rw_cells rsegs m6 S [C8 (Z_to_bv 64 (mode_addr mo)); C8 (Z_to_bv 64 SL); C4 (Z_to_bv 64 (2 * sbm_frameSize mo)); C4 (Z_to_bv 64 (sbm_frameSize mo));
C4 (Z_to_bv 64 (sbm_subframeSize mo)); C4 (Z_to_bv 64 4); C4 (Z_to_bv 64 8); C4 w0]).
{ eapply rw_cells_munch_out; [exact XA5| exact MU6| exact WM6|]. cbn [cells_size csize Nat.add]. intros x Hx. apply OUTW. lia. }
assert (XP6 : rw_cells rsegs m6 (S + 40) [C4 (Z_to_bv 64 (lr * 2))]).
{ eapply C4_samebytes; [| rewrite SRW, Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64); rewrite mod64_mod32; reflexivity].
eapply rw_cells_munch_out; [exact XP5| exact MU6| exact WM6|]. cbn [cells_size csize Nat.add]. intros x Hx. apply OUTW. lia. }
assert (XB6 : rw_cells rsegs m6 (S + 44) [C4 w0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 w0; C4 w0; C4 (Z_to_bv 64 1); CB 4 z4; C8 (Z_to_bv 64 0); C4 w0; CB 4 z4]).
{ eapply rw_cells_munch_out; [exact XB5| exact MU6| exact WM6|]. cbn [cells_size csize Nat.add]. intros x Hx. apply OUTW. lia. }
assert (FRj6 : rw_cells rsegs m6 (bv_unsigned sp + -48) [CB 4 j4]).
{ eapply rw_cells_munch_out; [exact FRj| exact MU6| exact WM6|]. cbn [cells_size csize Nat.add]. intros x Hx. apply OUTW. lia. }
assert (FRr6 : rw_cells rsegs m6 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_munch_out; [exact FRr| exact MU6| exact WM6|]. cbn [cells_size csize Nat.add]. intros x Hx. apply OUTW. lia. }
assert (ERR6 : rw_cells rsegs m6 316332 [C4 errv]).
{ eapply rw_cells_munch_out; [exact ERR5| exact MU6| exact WM6|]. cbn [cells_size csize Nat.add]. intros x Hx. apply OUTW. lia. }
assert (TP6 : rtables_pristine m6).
{ eapply rtables_pristine_munch; [exact TP5| exact MU6|]. intros x Hx. apply OUTW. lia. }
assert (HEAP6 : RHEAP st (LBL ++ (blk, S, SBSTATE_SIZEOF) :: LB) m6).
{ eapply RHEAP_frame_proof; [exact HEAP5| exact MU6| exact WM6|]. unfold ctlW. cbn [creq_ivs creq_size app].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; unfold alloc_ceiling; lia|].
apply Forall_forall. intros iv Hiv. unfold blocks_ivs in Hiv. apply in_map_iff in Hiv. destruct Hiv as (b & <- & Hb). right. right. exists b. split; [apply in_app_iff; left; exact Hb| cbn [fst snd]; lia]. }
assert (AUX6 : rauxv_ok m6 AB).
{ eapply rauxv_ok_frame; [exact AUX5| exact MU6| exact WM6|]. unfold ctlW. cbn [creq_ivs creq_size app].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|].
apply Forall_forall. intros iv Hiv. unfold blocks_ivs in Hiv. apply in_map_iff in Hiv. destruct Hiv as (b & <- & Hb). cbn [fst snd].
first [ pose proof (BRL _ Hb) as sfP_; sf_destruct 5%nat sfP_ as B0 _ _ BC BW | sf_fb; destruct (BRL _ Hb) as (B0 & _ & _ & BC & BW) ]. unfold alloc_ceiling in BC. unfold RAUXV_CELL. lia. }
assert (PRES6 : rheap_pres LB (bv_unsigned sp) m0 m6).
{ eapply rheap_pres_trans; [exact PRES5|]. eapply rheap_pres_of_munch; [exact MU6| exact WM6|]. intros x Hx CA. apply outside_ctlW. cbn [creq_size].
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in CA.
destruct CA as [CA|[CA|(b' & Hb' & Hab')]].
- split; [lia|]. split; [lia|]. intros b Hb. first [ pose proof (BRL _ Hb) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (BRL _ Hb) as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. lia.
- split; [lia|]. split; [lia|]. intros b Hb. first [ pose proof (BRL _ Hb) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ BW | sf_fb; destruct (BRL _ Hb) as (_ & _ & _ & _ & BW) ]. lia.
- unfold in_block in Hab'. destruct (BLB _ Hb') as (B1 & B2 & B3). split; [lia|]. split; [lia|]. intros b Hb. pose proof (B3 _ Hb). lia. }
clear XA5 XP5 XB5 FRj FRt FRr ERR5 TP5 HEAP5 AUX5 PRES5 MU6 WM6 MI5 ST5 RL5.

pose proof (sb_mode_struct m6 mo Hmo TP6) as MSTR.
eapply (implM_evt rsegs _ _ _ (fun ms7 => exists m7,
ms7 = MS (mkR (Z_to_bv 64 0x2e544) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 1073741824)
(Z_to_bv 64 (sbm_defaultSubmode mo)) (Z_to_bv 64 (sbmode_addr mo + 40)) ua2 ua3 ua4 ua5 ua6 ua7
(Z_to_bv 64 (sbmode_addr mo)) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
F6 (Z_to_bv 64 0x2e558) fc6 None m7 (seg_rom rsegs)
/\ rw_cells rsegs m7 S [C8 (Z_to_bv 64 (mode_addr mo)); C8 (Z_to_bv 64 SL); C4 (Z_to_bv 64 (2 * sbm_frameSize mo)); C4 (Z_to_bv 64 (sbm_frameSize mo));
C4 (Z_to_bv 64 (sbm_subframeSize mo)); C4 (Z_to_bv 64 4); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 1)]
/\ rw_cells rsegs m7 (S + 44) [C4 w0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 w0; C4 w0; C4 (Z_to_bv 64 1); CB 4 z4;
C8 (Z_to_bv 64 (sbmode_addr mo + 40)); C4 (Z_to_bv 64 (sbm_defaultSubmode mo)); CB 4 z4]
/\ munch [(S + 36, S + 40); (S + 144, S + 156)] m6 m7 /\ wmono rsegs m6 m7 /\ mem_inv rsegs m7)).
{ pose proof (munch_refl [(S + 36, S + 40); (S + 144, S + 156)] m6) as MU. pose proof (wmono_refl rsegs m6) as WM. clear PRES6 HEAP6.
destruct Hmo as [-> | ->]; cbn [mode_addr lower_mode sbmode_addr app skipn sbm_frameSize sbm_subframeSize sbm_lpcSize sbm_defaultSubmode] in MSTR |- *;
unfold sb_wb_mode_cells, sb_uwb_mode_cells, A_speex_wb_mode, A_speex_uwb_mode, A_speex_nb_mode, A_sb_wb_mode, A_sb_uwb_mode in MSTR |- *;
cbn [app skipn] in MSTR.
all: step; rewrite sx32_lit by lia; step; rewrite ?unsigned_lit by lia; lstep; lstep; lstep.
all: apply evt_done; eexists; (split; [reflexivity|]); (split; [eassumption|]); (split; [eassumption|]); (split; [exact MU|]); split; [exact WM| assumption]. }
cbv beta. intros ms7 sfH_; first [ sf_destruct 7%nat sfH_ as m7 -> XA7 XB7 MU7 WM7 MI7 | sf_fb; destruct sfH_ as (m7 & -> & XA7 & XB7 & MU7 & WM7 & MI7) ].
assert (XP7 : rw_cells rsegs m7 (S + 40) [C4 (Z_to_bv 64 (lr * 2))]) by (eapply rw_cells_transport; [exact XP6| exact MU7| exact WM7| cbn; lia]).
assert (FRj7 : rw_cells rsegs m7 (bv_unsigned sp + -48) [CB 4 j4]) by (eapply rw_cells_transport; [exact FRj6| exact MU7| exact WM7| cbn; lia]).
assert (FRt7 : rw_cells rsegs m7 (bv_unsigned sp + -48 + 4) [C4 tmp]) by (eapply rw_cells_transport; [exact FRt6| exact MU7| exact WM7| cbn; lia]).
assert (FRr7 : rw_cells rsegs m7 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rw_cells_transport; [exact FRr6| exact MU7| exact WM7| cbn; lia]).
assert (ERR7 : rw_cells rsegs m7 316332 [C4 errv]) by (eapply rw_cells_transport; [exact ERR6| exact MU7| exact WM7| cbn; lia]).
assert (ST7 : stk rsegs m7 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST6| exact MU7| exact WM7| cbn; lia]).
assert (TP7 : rtables_pristine m7).
{ eapply rtables_pristine_munch; [exact TP6| exact MU7|]. intros x Hx. unfold RTABLES_LO, RTABLES_HI in Hx. cbn. lia. }
assert (HEAP7 : RHEAP st (LBL ++ (blk, S, SBSTATE_SIZEOF) :: LB) m7).
{ eapply RHEAP_frame_proof; [exact HEAP6| exact MU7| exact WM7|]. constructor; [|constructor; [|constructor]]; right; right;
exists (blk, S, SBSTATE_SIZEOF); (split; [apply in_app_iff; right; left; reflexivity|]); cbn; unfold SBSTATE_SIZEOF; lia. }
assert (AUX7 : rauxv_ok m7 AB).
{ eapply rauxv_ok_frame; [exact AUX6| exact MU7| exact WM7|]. constructor; [|constructor; [|constructor]]; cbn [fst snd]; unfold RAUXV_CELL; lia. }
assert (RL7 : forall STEREO, DREP 0 STEREO m7 SL low2 LBL).
{ intros STEREO. eapply decst_rep_munch; [| exact MU7| exact WM7|].
- eapply decst_rep_stereo_any; [| exact RL6]. pose proof (ctl_stereo_off low1 (CtlSetWideband 1) I) as SO2. rewrite EC2 in SO2. apply SO2.
pose proof (ctl_stereo_off low CtlGetSamplingRate I STO) as SO1. rewrite EC1 in SO1. exact SO1.
- intros b x Hb Hx. pose proof (SAPL _ Hb). cbn. lia. }
assert (PRES7 : rheap_pres LB (bv_unsigned sp) m0 m7).
{ eapply rheap_pres_trans; [exact PRES6|]. eapply rheap_pres_of_munch; [exact MU7| exact WM7|]. intros x Hx CA. cbn.
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in CA.
destruct CA as [CA|[CA|(b' & Hb' & Hab')]]; [lia| lia|]. unfold in_block in Hab'. destruct (BLB _ Hb') as (B1 & B2 & _). lia. }

pose proof (rw_cells_join _ _ _ _ _ XA7 (rw_cells_join _ _ _ _ _ XP7 XB7 ltac:(cbn; lia)) ltac:(cbn; lia)) as X7. cbn [app] in X7.
pose proof (rw_cells_join _ _ _ _ _ FRj7 (rw_cells_join _ _ _ _ _ FRt7 FRr7 ltac:(cbn; lia)) ltac:(cbn; lia)) as FR7. cbn [app] in FR7.
apply (KONT blk S lr low2 LBL). unfold sb_at78. sf_eexists 15%nat. first [ unshelve sf_eexists 7%nat; [ exact (F6) | exact (fc6) | exact (m7) | exact (errv) | exact (j4) | exact (tmp) | exact (SL) | ] | sf_fb; exists F6, fc6, m7, errv, j4, tmp, SL ].
split; [reflexivity|]. split; [exact FRM6|]. split; [exact MI7|]. split; [exact ST7|]. split; [unfold sbinit_frame; exact FR7|].
split; [rewrite ETP; unfold RERRNO; exact ERR7|]. split; [exact AUX7|]. split; [exact PRES7|]. split; [exact PSO|]. split; [exact TP7|].
split; [eapply RHEAP_perm; [exact HEAP7| cbn [app]; apply Permutation_sym; apply Permutation_middle]|]. split; [exact BR|]. split; [exact SLB|]. split; [unfold sbx_cells; exact X7|]. split; [exact RL7|].
split; [pose proof (ctl_mode_same low1 (CtlSetWideband 1)) as E2; rewrite EC2 in E2; cbn [snd] in E2; rewrite E2;
pose proof (ctl_mode_same low CtlGetSamplingRate) as E1; rewrite EC1 in E1; cbn [snd] in E1; rewrite E1; exact DM|].
split; [pose proof (ctl_depth_same low1 (CtlSetWideband 1)) as E2; rewrite EC2 in E2; cbn [snd] in E2; rewrite E2;
pose proof (ctl_depth_same low CtlGetSamplingRate) as E1; rewrite EC1 in E1; cbn [snd] in E1; rewrite E1; exact DD|].
split; [exact RATE|].
split.
{ pose proof (ctl_stereo_off low1 (CtlSetWideband 1) I) as SO2. rewrite EC2 in SO2. apply SO2.
pose proof (ctl_stereo_off low CtlGetSamplingRate I STO) as SO1. rewrite EC1 in SO1. exact SO1. }
pose proof (ctl_nested_same low1 (CtlSetWideband 1)) as NE2. rewrite EC2 in NE2. apply NE2.
pose proof (ctl_nested_same low CtlGetSamplingRate NES) as NE1. rewrite EC1 in NE1. exact NE1.
Qed.

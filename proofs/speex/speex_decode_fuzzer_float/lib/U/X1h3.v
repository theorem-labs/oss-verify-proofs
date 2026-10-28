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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gy X1hg X1hh X1hi X1gz X1gt X1gu X1h6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma in_owned_stream : forall x h bb, In bb (stream_blks x h) -> In bb (owned x h).
Proof.
intros x h bb H. unfold owned. unfold stream_blks in H. apply in_app_iff; right. apply in_app_iff; right.
apply in_app_iff in H. destruct H as [H|H]; [apply in_app_iff; left; exact H|].
apply in_app_iff in H. destruct H as [H|H]; [apply in_app_iff; right; apply in_app_iff; left; exact H|].
apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact H.
Qed.
Lemma in_owned_bits : forall x h, In (sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h)) (owned x h).
Proof. intros. unfold owned. apply in_app_iff; right. apply in_app_iff; left. left. reflexivity. Qed.
Lemma in_owned_sync : forall x h p, sy_data (h_oy h) = Some p -> In (p, a_D x, sy_storage (h_oy h)) (owned x h).
Proof. intros x h p E. unfold owned. rewrite E. do 5 (apply in_app_iff; right). left. reflexivity. Qed.

Section HDR4.
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

#[using="RFREE RBR RND CX"] Lemma hdr_f294 : forall fuel' h blk pn st ms (br0 : Z) (oy0 : sync_st bptr),
F294 c h blk st ms ->
implM rsegs (X1qx.mbind (X1qx.mbind (raw_free blk) (fun _ => X1qx.mret (@None (hstate bptr)))) (hdr_tailK fuel' h pn))
st (PKPOST dec_rep c br0 oy0) ms.
Proof.
intros fuel' h blk pn st ms br0 oy0 FX.
first [ sf_destruct 39%nat FX as x1 t0 t1 t2 q8 q9 a0 a1 a2 a3 a4 a5 a6 a7 q18 q19 q20 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 F fc m x nbr brem0 HB -> FRM PU JF HG | sf_fb; destruct FX as (x1 & t0 & t1 & t2 & q8 & q9 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & q18 & q19 & q20 & q22 & q23 & q24 & q25 & q26 & q27 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & HB & -> & FRM & PU & JF & HG) ].
pose proof PU as sfP_; first [ sf_destruct 9%nat sfP_ as SI1 EOS0 PC0 EST AS0 ALBD PURE LOK BUD' | sf_fb; destruct sfP_ as (SI1 & EOS0 & PC0 & EST & AS0 & ALBD & PURE & LOK & BUD') ].
pose proof JF as sfP_; first [ sf_destruct 5%nat sfP_ as OSP SY BI JK SAV | sf_fb; destruct sfP_ as (OSP & SY & BI & JK & SAV) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof PURE as sfP_; first [ sf_destruct 8%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ _ | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & _) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof (RND _ _ _ HP) as ND. cbn [map app] in ND.
assert (HL0 : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
assert (ELB : lb_remove blk ((blk, HB, SIZEOF_SPEEX_HEADER_Z) :: a_LB x) = a_LB x).
{ rewrite lb_remove_cons. cbn [blk_id fst]. rewrite bptr_eqb_refl. apply lb_remove_other.
pose proof (proj1 (List.NoDup_cons_iff _ _) ND) as [NI ND']. cbn [blk_id fst] in NI.
intros b Hb E. apply NI. rewrite <- E. apply in_map. exact Hb. }
apply implM_bind_assoc.
unfold implM. iprefix. unfold wz.

zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st (PKPOST dec_rep c br0 oy0) msx) end.
eapply implM_bind.
{ eapply RFREE with (LB := (blk, HB, SIZEOF_SPEEX_HEADER_Z) :: a_LB x) (lo := x_lo c) (B := x_AB c);
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ exact HP | left; reflexivity | exact AUX | exact ST | exact MI | reflexivity | lia
| unfold RATP; rewrite unsigned_lit by lia; exact ERR
| unfold RFREE_STACK; lia ]. }
cbv beta. intros [] st1 ms1 PO.
first [ sf_destruct 25%nat PO as y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 m1 -> MI1 ST1 ERR1 AUX1 HPR EFA ESO HP1 | sf_fb; destruct PO as (y0 & y1 & y2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m1 & -> & MI1 & ST1 & ERR1 & AUX1 & HPR & EFA & ESO & HP1) ].
rewrite ELB in HPR, HP1.
rewrite ?(unsigned_lit (aLOW c)) in ST1 by lia. rewrite ?(unsigned_lit (aLOW c)) in HPR by lia.
unfold RATP in ERR1. rewrite ?unsigned_lit in ERR1 by lia. change (0x4d450 + -164) with RERRNO in ERR1.
replace (ret_pc (Z_to_bv 64 0x1c75c)) with (Z_to_bv 64 0x1c75c) by (symmetry; rpc).
pose proof (agree_of_rheap_pres _ _ _ _ HPR) as AG.

pose proof SY as sfP_; first [ sf_destruct 4%nat sfP_ as SYC SYF DAT SYSEP | sf_fb; destruct sfP_ as (SYC & SYF & DAT & SYSEP) ].
eapply (stream_rep_agree2 _ _ _ _ _ _ AG) in OSP; [| side1|].
2:{ intros a (bb & Hbb & Ra). right; right. exists bb. split; [| exact Ra].
eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. apply in_owned_stream. exact Hbb. }
assert (SY1 : sync_rep m1 (aOY c) (a_D x) (h_oy h) (a_sybytes x)).
{ split; [eapply rw_cells_agree; [exact AG| exact SYC| side1]|]. split; [exact SYF|]. split; [| exact SYSEP].
unfold sync_data in DAT |- *. destruct (sy_data (h_oy h)) as [p|] eqn:ED; [| exact DAT].
first [ sf_destruct 5%nat DAT as D1 ARR D3 D4 D5 | sf_fb; destruct DAT as (D1 & ARR & D3 & D4 & D5) ]. split; [exact D1|]. split; [| auto].
eapply u8arr_agree; [exact AG| exact ARR|]. intros a Ha. right; right. exists (p, a_D x, sy_storage (h_oy h)).
split; [| cbn; lia]. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. apply in_owned_sync. exact ED. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| side1|].
2:{ intros a Ha. right; right. exists (sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h)). split; [| cbn; lia].
eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. apply in_owned_bits. }
eapply (cl_junk_agree c _ _ _ AG) in JK; [| side1| side1| side1].
clear SYC DAT. clear ERR SY.   xport AG side1.
assert (PE1 : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m1).
{ eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP); [intros b Hb; right; apply HL0; exact Hb| exact PE| exact AG|].
intros a Hc Hout Hx. cbn beta.
destruct Hc as [Hc|[Hc|(bb & Hbb & Rb)]]; [left; lia| right; left; exact Hc| right; right; exists bb; split; [apply HL0; exact Hbb| exact Rb]]. }
apply implM_retb. unfold hdr_tailK. apply implM_bind_assoc.
eapply (clean_inl_k RFREE RBR RND c CX); [| intros st' ms' HF; apply implM_retb; apply implM_ret; apply evt_done; exact HF].
unfold CLI. sf_eexists 28%nat. first [ unshelve sf_eexists 4%nat; [ exact (F) | exact (fc) | exact (m1) | exact ((a_LB x)) | ] | sf_fb; exists F, fc, m1, (a_LB x) ]. instantiate (1 := x) || idtac.
split; [reflexivity|]. split; [exact FRM|]. split; [exact EST|]. split; [exact SI1|]. split; [exact ST1|].
split; [exact HP1|]. split; [exact (RND _ _ _ HP1)|].
split. { unfold stream_blks. rewrite <- !app_assoc. unfold owned in PERM. rewrite EST in PERM. rewrite <- !app_assoc in PERM. cbn [app] in PERM. exact PERM. }
split; [exact BI|]. split; [exact BOK|]. split; [exact OWN|]. split; [exact BBR|]. split; [exact OSP|].
split; [exact SY1|]. split; [exact SYOK|]. split; [intros NE; exact (proj1 (SYBLK NE))|]. split; [exact JK|]. split; [exact SAV|].
split; [assumption|]. split; [exists errv; exact ERR1|]. split; [exact AUX1|]. split; [exact MI1|]. split; [exact PE1| congruence].
Qed.

#[using="DDESTROY RFREE RBR RND CX"] Lemma hdr_f28c : forall fuel' h blk d pn st ms (br0 : Z) (oy0 : sync_st bptr),
F28c dec_rep c h blk d st ms ->
implM rsegs (X1qx.mbind (X1qx.mbind (h_decoder_destroyP d) (fun _ => X1qx.mbind (raw_free blk) (fun _ => X1qx.mret (@None (hstate bptr)))))
(hdr_tailK fuel' h pn))
st (PKPOST dec_rep c br0 oy0) ms.
Proof.
intros fuel' h blk d pn st ms br0 oy0 FX.
first [ sf_destruct 43%nat FX as x1 t0 t1 t2 q8 q9 a0 a1 a2 a3 a4 a5 a6 a7 q19 q20 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 F fc m x nbr brem0 HB S LBD -> FRM PU JF HG SPOS DR BRD | sf_fb; destruct FX as (x1 & t0 & t1 & t2 & q8 & q9 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & q19 & q20 & q22 & q23 & q24 & q25 & q26 & q27 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & HB & S & LBD & -> & FRM & PU & JF & HG & SPOS & DR & BRD) ].
pose proof PU as sfP_; first [ sf_destruct 9%nat sfP_ as SI1 EOS0 PC0 EST AS0 ALBD PURE LOK BUD' | sf_fb; destruct sfP_ as (SI1 & EOS0 & PC0 & EST & AS0 & ALBD & PURE & LOK & BUD') ].
pose proof JF as sfP_; first [ sf_destruct 5%nat sfP_ as OSP SY BI JK SAV | sf_fb; destruct sfP_ as (OSP & SY & BI & JK & SAV) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof PURE as sfP_; first [ sf_destruct 8%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ _ | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & _) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof (RND _ _ _ HP) as ND.
assert (HL0 : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
apply implM_bind_assoc.
unfold h_decoder_destroy. unfold implM. iprefix. unfold wz.

zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st (PKPOST dec_rep c br0 oy0) msx) end.
eapply implM_bind.
{ eapply DDESTROY with (LB := (LBD ++ [(blk, HB, SIZEOF_SPEEX_HEADER_Z)]) ++ a_LB x) (LBD := LBD) (LBr := (blk, HB, SIZEOF_SPEEX_HEADER_Z) :: a_LB x)
(STEREO := aSTEREO c) (S := S) (d := d) (AB := x_AB c) (lo := x_lo c);
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ exact HP | exact DR | exact TP | exact AUX | exact ST | exact MI | exact FRM | reflexivity | lia
| unfold RATP; rewrite unsigned_lit by lia; exact ERR
| unfold DEC_DESTROY_STACK; lia
| rewrite <- app_assoc; cbn [app]; apply Permutation_refl ]. }
cbv beta. intros [] st1 ms1 PO.
first [ sf_destruct 28%nat PO as y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F1 fc1 m1 errv1 -> FRM1 MI1 ST1 ERR1 AUX1 HPR ESO HP1 | sf_fb; destruct PO as (y0 & y1 & y2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F1 & fc1 & m1 & errv1 & -> & FRM1 & MI1 & ST1 & ERR1 & AUX1 & HPR & ESO & HP1) ].
rewrite ?(unsigned_lit (aLOW c)) in ST1 by lia. rewrite ?(unsigned_lit (aLOW c)) in HPR by lia.
unfold RATP in ERR1. rewrite ?unsigned_lit in ERR1 by lia. change (0x4d450 + -164) with RERRNO in ERR1.
replace (ret_pc (Z_to_bv 64 0x1c754)) with (Z_to_bv 64 0x1c754) by (symmetry; rpc).
pose proof (agree_of_rheap_pres _ _ _ _ HPR) as AG.

pose proof SY as sfP_; first [ sf_destruct 4%nat sfP_ as SYC SYF DAT SYSEP | sf_fb; destruct sfP_ as (SYC & SYF & DAT & SYSEP) ].
eapply (stream_rep_agree2 _ _ _ _ _ _ AG) in OSP; [| side1|].
2:{ intros a (bb & Hbb & Ra). right; right. exists bb. split; [| exact Ra]. right.
eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. apply in_owned_stream. exact Hbb. }
assert (SY1 : sync_rep m1 (aOY c) (a_D x) (h_oy h) (a_sybytes x)).
{ split; [eapply rw_cells_agree; [exact AG| exact SYC| side1]|]. split; [exact SYF|]. split; [| exact SYSEP].
unfold sync_data in DAT |- *. destruct (sy_data (h_oy h)) as [p|] eqn:ED; [| exact DAT].
first [ sf_destruct 5%nat DAT as D1 ARR D3 D4 D5 | sf_fb; destruct DAT as (D1 & ARR & D3 & D4 & D5) ]. split; [exact D1|]. split; [| auto].
eapply u8arr_agree; [exact AG| exact ARR|]. intros a Ha. right; right. exists (p, a_D x, sy_storage (h_oy h)).
split; [| cbn; lia]. right. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. apply in_owned_sync. exact ED. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| side1|].
2:{ intros a Ha. right; right. exists (sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h)). split; [| cbn; lia]. right.
eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. apply in_owned_bits. }
eapply (cl_junk_agree c _ _ _ AG) in JK; [| side1| side1| side1].
clear SYC DAT. clear PAY ERR SY.   xport AG side1.
assert (HG1 : hglobX c x h st1 m1 [(blk, HB, SIZEOF_SPEEX_HEADER_Z)]).
{ eapply (hglobX_agree2 RBR c x h st st1 m m1 _ _ _ errv1 CX HG AG); [exact HP1| exact MI1| exact ST1| | exact ERR1| exact AUX1| exact ESO|].
- exact SEW.
- intros a [Ha|[(Ha & Hs & _)|(bb & Hbb & Rbb)]]; [left; lia| right; left; split; [exact Ha| exact Hs]| right; right; exists bb; split; [right; apply HL0; exact Hbb| exact Rbb]]. }
apply (hdr_f294 fuel' h blk pn st1 _ br0 oy0).
unfold F294. sf_eexists 27%nat. first [ unshelve sf_eexists 7%nat; [ exact (F1) | exact (fc1) | exact (m1) | exact (x) | exact (nbr) | exact (brem0) | exact (HB) | ] | sf_fb; exists F1, fc1, m1, x, nbr, brem0, HB ].
split; [reflexivity|]. split; [exact FRM1|]. split; [exact PU|].
split; [split; [exact OSP| split; [exact SY1| split; [exact BI| split; [exact JK| exact SAV]]]]|].
exact HG1.
Qed.
End HDR4.

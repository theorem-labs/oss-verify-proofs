(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeDefs TimeKit TimeKit2 TimeFmtPure TimeToTmDefs W_time_leaves
     W_time_to_tm_A W_time_to_tm_it W_time_to_tm_B W_time_to_tm_C W_time_to_tm_D.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling. Context {CE__ : Ceiling}.

Local Ltac reget MU WM H :=
  eapply ro_cells_agree; [apply (agree_on_of_munch _ _ _ MU WM)| exact H| intros a Ha; cbn in Ha |- *; split; [lia| exact I]].

(* [comment removed for export] *)
Theorem time_to_tm_check_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo DA GS ms : Z) (t : tm6),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  ro_cells ctusegs m DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> (DA + 24 <= lo \/ bv_unsigned sp <= DA) -> DA + 24 <= 2^64 ->
  0 < DA -> DA mod 8 = 0 ->
  ro_cells ctusegs m GS (gcells t ms) -> (GS + 19 <= lo \/ bv_unsigned sp <= GS) -> 0 < GS -> GS + 19 <= 2^63 ->
  tm_valid t -> 0 <= ms < 1000 ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 DA ->
  evt ctusegs (t2t_leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 1 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OSSL_ASN1_TIME_TO_TM) fc None m (seg_rom ctusegs)).
Proof.
  intros until t. intros ST MI GLO LO SP63 HD SEPD DHI DA0 DAL HS SEPS GS0 SHI TV MSR -> ->.
  pose proof LO as LO'. unfold TIME_TO_TM_STACK, GLOBALS_TOP in LO', GLO.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (ro_cells_bound _ _ _ _ HS) as GSB. cbn [cells_size csize Nat.add gcells zb8 length] in GSB.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply t2t_front with (lo := lo) (l := 19) (tm := 0); try eassumption; try reflexivity; try (unfold GLOBALS_TOP; lia); lia. }
  intros ms1 PO. unfold t2t_head0_post in PO.
  destruct PO as (x1 & x5 & x6 & x7 & x9 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x21 & x22 & x27 & x28 & x29 & x30 & x31 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
  assert (HD1 : ro_cells ctusegs m1 DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)]) by reget MU1 WM1 HD.
  assert (HS1 : ro_cells ctusegs m1 GS (gcells t ms)) by reget MU1 WM1 HS.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply t2t_segB with (lo := lo) (ms := ms); try eassumption; try reflexivity. }
  intros ms2 PO. unfold t2t_head_post in PO.
  destruct PO as (y1 & y5 & y6 & y7 & y9 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y21 & y22 & y27 & y28 & y29 & y30 & y31 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FR2).
  assert (HD2 : ro_cells ctusegs m2 DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)]) by reget MU2 WM2 HD1.
  assert (HS2 : ro_cells ctusegs m2 GS (gcells t ms)) by reget MU2 WM2 HS1.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply t2t_segC with (lo := lo) (ms := ms); try eassumption; try reflexivity. }
  intros ms3 (wd & yd & PO). unfold t2t_head_post in PO.
  destruct PO as (z1 & z5 & z6 & z7 & z9 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z21 & z22 & z27 & z28 & z29 & z30 & z31 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3).
  assert (HD3 : ro_cells ctusegs m3 DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)]) by reget MU3 WM3 HD2.
  assert (HS3 : ro_cells ctusegs m3 GS (gcells t ms)) by reget MU3 WM3 HS2.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply t2t_segD with (lo := lo) (ms := ms); try eassumption; try reflexivity; lia. }
  intros ms4 PO. unfold t2t_fin_post in PO.
  destruct PO as (w1 & w5 & w6 & w7 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w20 & w21 & w22 & w23 & w24 & w25 & w26 & w27 & w28 & w29 & w30 & w31 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4).
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply t2t_end0 with (lo := lo); try eassumption; try reflexivity. }
  intros ms5 PO.
  destruct PO as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m5 & -> & MU5 & WM5 & MI5 & ST5).
  apply evt_done. unfold t2t_leaf_post. do 14 eexists. exists m5. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU1|]. eapply munch_trans; [exact MU2|]. eapply munch_trans; [exact MU3|]. eapply munch_trans; [exact MU4| exact MU5]. }
  split. { eapply wmono_trans; [exact WM1|]. eapply wmono_trans; [exact WM2|]. eapply wmono_trans; [exact WM3|]. eapply wmono_trans; [exact WM4| exact WM5]. }
  split; [exact MI5| exact ST5].
Qed.

(* [comment removed for export] *)
Theorem time_to_tm_copy_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo DA GS ms TMA : Z) (t : tm6) (junk : list byte),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  ro_cells ctusegs m DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> (DA + 24 <= lo \/ bv_unsigned sp <= DA) -> DA + 24 <= 2^64 ->
  0 < DA -> DA mod 8 = 0 ->
  ro_cells ctusegs m GS (gcells t ms) -> (GS + 19 <= lo \/ bv_unsigned sp <= GS) -> 0 < GS -> GS + 19 <= 2^63 ->
  tm_valid t -> 0 <= ms < 1000 ->
  rw_cells ctusegs m TMA [CB 56%nat junk] -> bv_unsigned sp <= TMA -> TMA + 56 <= 2^63 ->
  (TMA + 56 <= DA \/ DA + 24 <= TMA) -> (TMA + 56 <= GS \/ GS + 19 <= TMA) ->
  a0 = Z_to_bv 64 TMA -> a1 = Z_to_bv 64 DA ->
  evt ctusegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (wd yd : Z),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(lo, bv_unsigned sp); (TMA, TMA + 56)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' TMA [CB 56%nat (cells_bytes (TM_CELLS (t_sec t) (t_min t) (t_hour t) (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OSSL_ASN1_TIME_TO_TM) fc None m (seg_rom ctusegs)).
Proof.
  intros until junk. intros ST MI GLO LO SP63 HD SEPD DHI DA0 DAL HS SEPS GS0 SHI TV MSR HT TLO THI SEP1 SEP2 -> ->.
  pose proof LO as LO'. unfold TIME_TO_TM_STACK, GLOBALS_TOP in LO', GLO.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (ro_cells_bound _ _ _ _ HS) as GSB. cbn [cells_size csize Nat.add gcells zb8 length] in GSB.
  pose proof (munch_weaken [(lo, bv_unsigned sp)] [(lo, bv_unsigned sp); (TMA, TMA + 56)] ) as MWK.
  assert (SUB : sub_fp [(lo, bv_unsigned sp)] [(lo, bv_unsigned sp); (TMA, TMA + 56)]) by (unfold sub_fp; cbn [outside]; intros y Hy; lia).
  Local Ltac regetw MU WM H :=
    eapply rw_cells_agree; [apply (agree_on_of_munch _ _ _ MU WM)| exact H| intros a Ha; cbn in Ha |- *; split; [lia| exact I]].
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply t2t_front with (lo := lo) (l := 19) (tm := TMA); try eassumption; try reflexivity; try (unfold GLOBALS_TOP; lia); lia. }
  intros ms1 PO. unfold t2t_head0_post in PO.
  destruct PO as (x1 & x5 & x6 & x7 & x9 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x21 & x22 & x27 & x28 & x29 & x30 & x31 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
  assert (HD1 : ro_cells ctusegs m1 DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)]) by reget MU1 WM1 HD.
  assert (HS1 : ro_cells ctusegs m1 GS (gcells t ms)) by reget MU1 WM1 HS.
  assert (HT1 : rw_cells ctusegs m1 TMA [CB 56%nat junk]) by regetw MU1 WM1 HT.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply t2t_segB with (lo := lo) (ms := ms); try eassumption; try reflexivity. }
  intros ms2 PO. unfold t2t_head_post in PO.
  destruct PO as (y1 & y5 & y6 & y7 & y9 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y21 & y22 & y27 & y28 & y29 & y30 & y31 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FR2).
  assert (HD2 : ro_cells ctusegs m2 DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)]) by reget MU2 WM2 HD1.
  assert (HS2 : ro_cells ctusegs m2 GS (gcells t ms)) by reget MU2 WM2 HS1.
  assert (HT2 : rw_cells ctusegs m2 TMA [CB 56%nat junk]) by regetw MU2 WM2 HT1.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply t2t_segC with (lo := lo) (ms := ms); try eassumption; try reflexivity. }
  intros ms3 (wd & yd & PO). unfold t2t_head_post in PO.
  destruct PO as (z1 & z5 & z6 & z7 & z9 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z21 & z22 & z27 & z28 & z29 & z30 & z31 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3).
  assert (HD3 : ro_cells ctusegs m3 DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)]) by reget MU3 WM3 HD2.
  assert (HS3 : ro_cells ctusegs m3 GS (gcells t ms)) by reget MU3 WM3 HS2.
  assert (HT3 : rw_cells ctusegs m3 TMA [CB 56%nat junk]) by regetw MU3 WM3 HT2.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply t2t_segD with (lo := lo) (ms := ms); try eassumption; try reflexivity; lia. }
  intros ms4 PO. unfold t2t_fin_post in PO.
  destruct PO as (w1 & w5 & w6 & w7 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w20 & w21 & w22 & w23 & w24 & w25 & w26 & w27 & w28 & w29 & w30 & w31 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4).
  assert (HT4 : rw_cells ctusegs m4 TMA [CB 56%nat junk]) by regetw MU4 WM4 HT3.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply t2t_end1 with (lo := lo) (junk := junk); try eassumption; try reflexivity; try lia. unfold TM_CELLS. cbn. tauto. }
  intros ms5 PO.
  destruct PO as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m5 & -> & MU5 & WM5 & MI5 & ST5 & HT5).
  apply evt_done. do 14 eexists. exists m5, wd, yd. split; [reflexivity|].
  split. { eapply munch_trans; [apply (MWK _ _ SUB MU1)|]. eapply munch_trans; [apply (MWK _ _ SUB MU2)|]. eapply munch_trans; [apply (MWK _ _ SUB MU3)|].
           eapply munch_trans; [apply (MWK _ _ SUB MU4)| exact MU5]. }
  split. { eapply wmono_trans; [exact WM1|]. eapply wmono_trans; [exact WM2|]. eapply wmono_trans; [exact WM3|]. eapply wmono_trans; [exact WM4| exact WM5]. }
  split; [exact MI5|]. split; [exact ST5|]. exact HT5.
Qed.

(* [comment removed for export] *)
Definition time_to_tm_reject_spec := @t2t_reject.

End WithCeiling.

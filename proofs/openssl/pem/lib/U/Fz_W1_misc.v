(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP SFModel Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_W1_defs Fz_W1_bits Fz_W1_bits2 Fz_W1_bioflags Fz_W1_sync Fz_W1_write Fz_W1_read.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition W1_method_stmt (ENTRY TABLE : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
    evt usegs (fun ms' => exists (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TABLE) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).

Theorem W1_BIO_s_mem_proof : W1_method_stmt 0x183168 0x2d3fc8.
Proof.
  unfold W1_method_stmt. intros until lo. intros ST LO0 LO MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  ths. th_frame 16%nat [8; 8]%nat ST. do 3 ths. do 2 ths. do 2 ths.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => th_release FRh (bv_unsigned sp) end.
  ths. ths. finish.
Qed.

Theorem W1_BIO_s_secmem_proof : W1_method_stmt 0x183190 0x2d4038.
Proof.
  unfold W1_method_stmt. intros until lo. intros ST LO0 LO MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  ths. th_frame 16%nat [8; 8]%nat ST. do 3 ths. do 2 ths. do 2 ths.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => th_release FRh (bv_unsigned sp) end.
  ths. ths. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma t_zx32_small : forall z, 0 <= z < 2 ^ 32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Definition W1_ctrl_info_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI BB BM RP fl : Z) (leftw dataw rmaxw rflw : word),
    a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 3 -> a3 = Z_to_bv 64 0 -> 0 < BI ->
    ro_cells usegs m (BI + 48) [C4 (Z_to_bv 64 fl)] -> fl_ok fl -> ro_cells usegs m (BI + 64) [C8 (Z_to_bv 64 BB)] ->
    0 < BB -> BB + 16 < 2 ^ 63 -> ro_cells usegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)] ->
    0 < RP -> ro_cells usegs m RP [C8 leftw; C8 dataw; C8 rmaxw; C8 rflw] ->
    0 < BM -> BM + 32 < 2 ^ 63 -> BI mod 8 = 0 -> BB mod 8 = 0 -> BM mod 8 = 0 -> RP mod 8 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 64 -> BI + 72 <= lo -> BB + 16 <= lo -> RP + 32 <= lo ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 leftw a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x183744) fc None m (seg_rom usegs)).

Theorem W1_ctrl_info_proof : W1_ctrl_info_stmt.
Proof.
  unfold W1_ctrl_info_stmt. intros until rflw. intros -> -> -> HBI FLC [FLR FLB] PTRC HBB HBB63 BBC HRP RPC HBM HBM63 ALBI ALBB ALBM ALRP ST LO0 LO SBI SBB SRP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  ths. th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST. do 8 ths.
  ths. ubs_if. ths. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ubs_if.
  ths. ths. ths. rewrite (t_zx32_small fl) by lia. ths. rewrite (unsigned_lit fl) by lia. rewrite FLB.
  ths. ths. ths.
  change (bv_unsigned (v_sltiu (Z_to_bv 64 0) 1) ≪ 3) with 8.
  ths. ths. ubs_if. ths. ths. ubs_if.
  ths. ths. ths.
  try change (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) ≪ 3) with 0. rewrite ?Z.add_0_r.
  ths. ths. ubs_if. ths. ths. ubs_if.
  ths. ths.
  ths. ths. th_if_lit. ths. ths. ths. th_if_lit.
  ths. ths. ths. ths. ths. ths. ths.
  ths. th_if_lit. ths. ths. ths.
  do 7 ths.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp) end.
  ths. ths. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W1_read_eof_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI BB BM RP fl outl OUT : Z) (dataw rmaxw rflw : word),
    a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 outl -> 0 < BI -> 0 < OUT < 2 ^ 64 -> 0 < outl < 2 ^ 31 ->
    rw_cells usegs m (BI + 48) [C4 (Z_to_bv 64 fl)] -> fl_ok fl -> ro_cells usegs m (BI + 56) [C4 (Z_to_bv 64 (-1))] ->
    ro_cells usegs m (BI + 64) [C8 (Z_to_bv 64 BB)] ->
    0 < BB -> BB + 16 < 2 ^ 63 -> ro_cells usegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)] ->
    0 < RP -> ro_cells usegs m RP [C8 (Z_to_bv 64 0); C8 dataw; C8 rmaxw; C8 rflw] ->
    BI mod 8 = 0 -> BB mod 8 = 0 -> RP mod 8 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 80 -> BI + 72 <= lo -> BB + 16 <= lo -> RP + 32 <= lo ->
    tbox (BI + 52 <= RP \/ RP + 32 <= BI + 48) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (fl' : Z) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (BI + 48, BI + 52)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ fl_ok fl' /\ rw_cells usegs m' (BI + 48) [C4 (Z_to_bv 64 fl')])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x183440) fc None m (seg_rom usegs)).

Theorem W1_read_eof_proof : W1_read_eof_stmt.
Proof.
  unfold W1_read_eof_stmt. intros until rflw.
  intros -> -> -> HBI HOUT HOUTL FLC FLOK NUMC PTRC HBB HBB63 BBC HRP RPC ALBI ALBB ALRP ST LO0 LO SBI SBB SRP BOX MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (BI + 48, BI + 52)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (fl_ok_sel fl FLOK) as SEL. pose proof FLOK as [FLR FLB].
  box RPC. pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (BI + 48, BI + 52)]%Z m) as MUp.
  ths. th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST. do 8 ths.
  ths. ubs_if. ths. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ths. ubs_if.
  ths. ths. rewrite (t_sx32_small fl) by lia. ths. ths. ths. ths.
  rewrite SEL.
  ths. ths. ths. ths.
  tcallr W1_bio_clear15_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mb end.
  unbox RPC. unfold tbox in BOX.
  assert (RPCb : ro_cells usegs mb RP [C8 (Z_to_bv 64 0); C8 dataw; C8 rmaxw; C8 rflw])
    by (eapply ro_cells_transport; [exact RPC| exact MUp| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  clear RPC MUp BOX.
  ths. if_cases KS; zify_cond KS. { exfalso. lia. }
  ths. ubs_if. ths. ths. ubs_if.
  ths. ths. if_cases KM; zify_cond KM. 2:{ exfalso. rewrite ?unsigned_lit in KM by lia. lia. }
  ths. ths. if_cases KO; zify_cond KO. { exfalso. rewrite ?unsigned_lit in KO by lia. lia. }
  ths. th_if_lit. ths. ubs_if. ths. ubs_if.
  ths. ths. th_if_lit. ths. ths. th_if_lit. ths. ths. ths.
  assert (FLOK1 : fl_ok (Z.land fl 18446744073709551600)) by (apply fl_ok_land; [exact FLOK| lia]).
  pose proof W1_bio_set9_proof as S9. unfold W1_bio_flags_stmt in S9.
  tcall (S9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo BI (Z.land fl 18446744073709551600)).
  all: try first [eassumption | reflexivity | lia | (destruct FLOK1; lia)].
  clear S9.
  cbv beta delta [mkR].
  ths. do 7 ths.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp) end.
  ths. ths.
  lazymatch goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] =>
    replace (Z_to_bv 64 (bv_swrap 32 e)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity) end.
  apply evt_done. do 14 eexists. exists (Z.lor (Z.land fl 18446744073709551600) 9). eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [apply fl_ok_lor; [exact FLOK1| lia| reflexivity]| eassumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W1_gets_empty_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI BB BM RP fl size OUT : Z) (dataw rmaxw rflw : word) (ob : byte),
    a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 size -> 0 < BI -> 0 < OUT -> 1 <= size < 2 ^ 31 ->
    rw_cells usegs m (BI + 48) [C4 (Z_to_bv 64 fl)] -> fl_ok fl -> ro_cells usegs m (BI + 64) [C8 (Z_to_bv 64 BB)] ->
    0 < BB -> BB + 16 < 2 ^ 63 -> ro_cells usegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)] ->
    0 < RP -> ro_cells usegs m RP [C8 (Z_to_bv 64 0); C8 dataw; C8 rmaxw; C8 rflw] ->
    rw_cells usegs m OUT [C1 ob] ->
    BI mod 8 = 0 -> BB mod 8 = 0 -> RP mod 8 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 64 -> BI + 72 <= lo -> BB + 16 <= lo -> RP + 32 <= lo ->
    tbox ((BI + 52 <= RP \/ RP + 32 <= BI + 48) /\ (OUT + 1 <= lo \/ bv_unsigned sp <= OUT) /\ (OUT + 1 <= BI + 48 \/ BI + 52 <= OUT)) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (fl' : Z) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (BI + 48, BI + 52); (OUT, OUT + 1)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ fl_ok fl' /\ rw_cells usegs m' (BI + 48) [C4 (Z_to_bv 64 fl')] /\ rw_cells usegs m' OUT [C1 (Z_to_bv 8 0)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1835f0) fc None m (seg_rom usegs)).

Theorem W1_gets_empty_proof : W1_gets_empty_stmt.
Proof.
  unfold W1_gets_empty_stmt. intros until ob.
  intros -> -> -> HBI HOUT HSZ FLC FLOK PTRC HBB HBB63 BBC HRP RPC OUTC ALBI ALBB ALRP ST LO0 LO SBI SBB SRP BOX MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (BI + 48, BI + 52); (OUT, OUT + 1)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (fl_ok_sel fl FLOK) as SEL. pose proof FLOK as [FLR FLB].
  pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
  box RPC. box OUTC.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (BI + 48, BI + 52)]%Z m) as MUp. pose proof (wmono_refl usegs m) as WMp.
  ths. th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST. do 7 ths.
  ths. ubs_if. ths. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ths. ubs_if.
  ths. ths. rewrite (t_sx32_small fl) by lia. ths. ths. ths. ths.
  rewrite SEL.
  ths. ths. ths. ths.
  tcallr W1_bio_clear15_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mb end.
  unbox RPC. unbox OUTC. unfold tbox in BOX. destruct BOX as (B1 & B2 & B3).
  assert (RPCb : ro_cells usegs mb RP [C8 (Z_to_bv 64 0); C8 dataw; C8 rmaxw; C8 rflw])
    by (eapply ro_cells_transport; [exact RPC| exact MUp| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  assert (OUTCb : rw_cells usegs mb OUT [C1 ob])
    by (eapply rw_cells_transport; [exact OUTC| exact MUp| exact WMp| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  clear RPC OUTC MUp WMp B1.
  ths. ubs_if. ths. ths. ubs_if.
  ths. ths. if_cases KS; zify_cond KS; rewrite (swrap32_small (size + -1)) in KS by lia; signed_lits_in KS. { exfalso. lia. }
  ths. ths. ths. ths. th_if_lit.
  ths. if_cases KJ; zify_cond KJ; rewrite (swrap32_small (size + -1)) in KJ by lia; signed_lits_in KJ.
  2:{ exfalso. rewrite <- (unsigned_lit_land (size + -1)), unsigned_lit in KJ by lia. lia. }
  ths. ths. th_if_lit.
  ths. ubs_if.
  ths.
  remember OUT as Pk eqn:EPk.
  ths.
  do 6 ths.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -48) _ |- _ => th_release FRh (bv_unsigned sp) end.
  ths. ths. subst Pk.
  apply evt_done. do 14 eexists. exists (Z.land fl 18446744073709551600). eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [apply fl_ok_land; [exact FLOK| lia]|]. split; eassumption.
Qed.

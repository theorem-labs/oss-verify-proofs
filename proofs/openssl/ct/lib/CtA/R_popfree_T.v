(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk SysStep ITree. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread R_cache_defs R_classid R_prim_defs R_mmapfixed R_popfree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Fixpoint carve (ws : list word) (total auser size : Z) (i : nat) : list word :=
  match i with
  | O => ws
  | S j => upd (carve ws total auser size j) (Z.to_nat (total - 1 - Z.of_nat j)) (Z_to_bv 64 ((auser + Z.of_nat j * size) / 16))
  end.

Lemma carve_length : forall ws total auser size i, length (carve ws total auser size i) = length ws.
Proof. intros ws total auser size i. induction i as [|i IH]; cbn [carve]; [reflexivity|]. rewrite upd_length. exact IH. Qed.

Lemma carve_succ : forall ws total auser size i, (0 <= i)%Z ->
  carve ws total auser size (Z.to_nat (i + 1)) =
  upd (carve ws total auser size (Z.to_nat i)) (Z.to_nat (total - 1 - i)) (Z_to_bv 64 ((auser + i * size) ≫ 4)).
Proof.
  intros ws total auser size i Hi. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. cbn [carve].
  rewrite Z2Nat.id by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fa_idx : forall X i, (0 <= i < 2^62)%Z ->
  Z_to_bv 64 (X + Z.shiftl (Z.lxor i 18446744073709551615) 2) = Z_to_bv 64 (X - 4 - 4 * i).
Proof.
  intros X i Hi. rewrite lnot_mod64 by lia.
  assert (E2 : ((Z.lnot i) mod 2^64 = 2^64 - i - 1)%Z).
  { unfold Z.lnot. symmetry. apply Z.mod_unique with (-1)%Z; lia. }
  rewrite E2, Z.shiftl_mul_pow2 by lia.
  apply bv_eq. rewrite !unsigned_lit_wrap.
  replace (X + (2 ^ 64 - i - 1) * 2 ^ 2)%Z with ((X - 4 - 4 * i) + 4 * 2^64)%Z by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Definition pfa_tail_W (sp : word) (SB c R total : Z) : list (Z * Z) :=
  [(fa SB c, fa SB c + 4 * total); (R + 16, R + 40); (R + 68, R + 69); (bv_unsigned sp - 64, bv_unsigned sp)]%Z.

(* [comment removed for export] *)
Definition pfa_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SB c R total mfa auser' muser : Z) (ws' : list word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom ctasegs)
    /\ munch (pfa_tail_W sp SB c R total) m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ fl_arr m' SB c ws'
    /\ ri_core m' R total mfa auser' muser
    /\ rw_cells ctasegs m' (R + 68) [C1 (Z_to_bv 8 0)]
    /\ stk ctasegs m' lo (bv_unsigned sp).

Section Tail.
Variables (ra sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (ACEIL SB c R nfree mfa auser muser newc lo : Z) (ws : list word) (m0 : mem).
Hypothesis HSB : SB_ok ACEIL SB.
Hypothesis Hc : (1 <= c <= 31)%Z.
Hypothesis ER : R = rinfo (RIS_of SB) c.
Hypothesis Hau : (0 <= auser <= muser)%Z.
Hypothesis Hmu : (muser <= 0xE0000000)%Z.
Hypothesis Enewc : newc = ((muser - auser) / ClassSize c)%Z.
Hypothesis Hnewc : (1 <= newc)%Z.
Hypothesis Hnf : (0 <= nfree)%Z.
Hypothesis Hcap : (4 * (nfree + newc) <= mfa)%Z.
Hypothesis Hmfa : (mfa <= 2^29)%Z.
Hypothesis Hws : (4 * Z.of_nat (length ws) = mfa)%Z.
Hypothesis HLO : (ACEIL <= lo)%Z.
Hypothesis HLOH : (kHighShadowEnd + 8 <= lo)%Z.
Hypothesis HLO2 : (lo <= bv_unsigned sp - 64)%Z.
Hypothesis HSP : (bv_unsigned sp <= 2^47)%Z.

Definition pfa_Q : machine_state -> Prop :=
  pfa_tail_post ra sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc SB c R (nfree + newc) mfa
    (auser + newc * ClassSize c) muser (carve ws (nfree + newc) auser (ClassSize c) (Z.to_nat newc)) lo m0.

(* [comment removed for export] *)
Lemma pfa_t36b40 : forall ra' t0 t1 t2 a0 a2 a4 a5 a6 a7 s6 t3 t4 t5 t6 (m : mem) (s4v : word) (exh : byte),
  pfa_frame m sp ra s0o s1o s2o s3o s4o s5o s6o ->
  rw_cells ctasegs m (R + 16) [C8 (Z_to_bv 64 nfree); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 auser); C8 (Z_to_bv 64 0);
                             C8 (Z_to_bv 64 muser); C8 (Z_to_bv 64 0)] ->
  rw_cells ctasegs m (R + 68) [C1 exh] ->
  fl_arr m SB c (carve ws (nfree + newc) auser (ClassSize c) (Z.to_nat newc)) ->
  stk ctasegs m lo (bv_unsigned sp - 64) ->
  munch (pfa_tail_W sp SB c R (nfree + newc)) m0 m -> wmono ctasegs m0 m -> mem_inv ctasegs m ->
  evt ctasegs pfa_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 (4 * (nfree + newc))) a0
             (Z_to_bv 64 (fa SB c + 4 * (nfree + newc))) a2 (Z_to_bv 64 auser) a4 a5 a6 a7 (Z_to_bv 64 (rb SB c))
             (Z_to_bv 64 newc) s4v (Z_to_bv 64 (ClassSize c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a12b0) fc None m (seg_rom ctasegs)).
Proof.
  intros until exh. intros FR RC EXH FL ST MU WM MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4). unfold rinfo, RIS_of, kHighShadowEnd, pfa_frame, pfa_tail_W, fl_arr in *.
  pose proof (ClassSize_range c Hc) as HCS. unfold fa, rb in FL.
  pose proof (carve_length ws (nfree + newc) auser (ClassSize c) (Z.to_nat newc)) as CL.
  assert (Hnc : (newc * ClassSize c <= muser - auser)%Z).
  { rewrite Enewc. pose proof (Z.mul_div_le (muser - auser) (ClassSize c) ltac:(lia)). lia. }
  do 6 zstep.
  zstep. zstep. ifF.
  do 2 zstep. zstep. ifF.
  zstep; try fix_lit_store.
  do 11 zstep.
  replace (bv_unsigned sp - 64 + 64)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
Qed.
(* [comment removed for export] *)
Lemma pfa_loop : forall (k : nat) (i : Z) ra' t0 t1 t2 a4 a5 a6 a7 s6 t3 t4 t5 t6 (m : mem) (s4v : word) (exh : byte),
  i = (newc - Z.of_nat k)%Z -> (0 <= i)%Z -> (1 <= k)%nat ->
  pfa_frame m sp ra s0o s1o s2o s3o s4o s5o s6o ->
  rw_cells ctasegs m (R + 16) [C8 (Z_to_bv 64 nfree); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 auser); C8 (Z_to_bv 64 0);
                             C8 (Z_to_bv 64 muser); C8 (Z_to_bv 64 0)] ->
  rw_cells ctasegs m (R + 68) [C1 exh] ->
  fl_arr m SB c (carve ws (nfree + newc) auser (ClassSize c) (Z.to_nat i)) ->
  stk ctasegs m lo (bv_unsigned sp - 64) ->
  munch (pfa_tail_W sp SB c R (nfree + newc)) m0 m -> wmono ctasegs m0 m -> mem_inv ctasegs m ->
  evt ctasegs pfa_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 (4 * (nfree + newc)))
             (Z_to_bv 64 i) (Z_to_bv 64 (fa SB c + 4 * (nfree + newc))) (Z_to_bv 64 (auser + i * ClassSize c))
             (Z_to_bv 64 auser) a4 a5 a6 a7 (Z_to_bv 64 (rb SB c))
             (Z_to_bv 64 newc) s4v (Z_to_bv 64 (ClassSize c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a1290) fc None m (seg_rom ctasegs)).
Proof.
  induction k as [|k IH]; intros i ra' t0 t1 t2 a4 a5 a6 a7 s6 t3 t4 t5 t6 m s4v exh Ei Hi Hk FR RC EXH FL ST MU WM MI; [lia|].
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4). unfold rinfo, RIS_of, kHighShadowEnd in *.
  pose proof (ClassSize_range c Hc) as HCS.
  assert (Hnc : (newc * ClassSize c <= muser - auser)%Z).
  { rewrite Enewc. pose proof (Z.mul_div_le (muser - auser) (ClassSize c) ltac:(lia)). lia. }
  assert (FAB : (SB + 2^32 <= fa SB c /\ fa SB c + 2^29 <= SB + 2^37)%Z) by (unfold fa, rb; lia).
  pose proof (carve_length ws (nfree + newc) auser (ClassSize c) (Z.to_nat i)) as CL.
  unfold fl_arr, pfa_frame, pfa_tail_W in *.
  do 5 zstep.
  rewrite (fa_idx (fa SB c + 4 * (nfree + newc)) i) by lia.
  pose proof (u32arr_store_ok ctasegs m (fa SB c) _ (nfree + newc - 1 - i) (Z_to_bv 64 (fa SB c + 4 * (nfree + newc) - 4 - 4 * i))
                FL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SO.
  zstep.
  pose proof (u32arr_write ctasegs m (fa SB c) _ (nfree + newc - 1 - i) (Z_to_bv 64 ((auser + i * ClassSize c) ≫ 4)) FL ltac:(lia))
    as FL'.
  replace (fa SB c + 4 * (nfree + newc - 1 - i))%Z with (fa SB c + 4 * (nfree + newc) - 4 - 4 * i)%Z in FL' by lia.
  rewrite <- carve_succ in FL' by lia.
  clear FL.
  store_done.
  zstep.
  replace (auser + i * ClassSize c + ClassSize c)%Z with (auser + (i + 1) * ClassSize c)%Z by lia.
  zstep.
  destruct k as [|k].
  - (* [comment removed for export] *)
    ifF.
    replace (i + 1)%Z with newc in FL' by lia.
    eapply pfa_t36b40; eassumption.
  - ifT.
    eapply (IH (i + 1)%Z); try eassumption; lia.
Qed.
(* [comment removed for export] *)
Lemma pfa_T_spec : forall ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 (exh : byte),
  pfa_frame m0 sp ra s0o s1o s2o s3o s4o s5o s6o ->
  ri_core m0 R nfree mfa auser muser ->
  rw_cells ctasegs m0 (R + 68) [C1 exh] ->
  fl_arr m0 SB c ws ->
  stk ctasegs m0 lo (bv_unsigned sp - 64) ->
  mem_inv ctasegs m0 ->
  evt ctasegs pfa_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 (nfree + newc)) (Z_to_bv 64 1)
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (rb SB c)) (Z_to_bv 64 newc) (Z_to_bv 64 (muser - auser))
             (Z_to_bv 64 (ClassSize c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a1268) fc None m0 (seg_rom ctasegs)).
Proof.
  intros until exh. intros FR RC EXH FL ST MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4). unfold rinfo, RIS_of, kHighShadowEnd, ri_core in *.
  pose proof (ClassSize_range c Hc) as HCS.
  assert (Hnc : (newc * ClassSize c <= muser - auser)%Z).
  { rewrite Enewc. pose proof (Z.mul_div_le (muser - auser) (ClassSize c) ltac:(lia)). lia. }
  assert (Hsz : (ClassSize c <= muser - auser)%Z).
  { assert (H1 : (1 * ClassSize c <= newc * ClassSize c)%Z) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  pose proof (munch_refl (pfa_tail_W sp SB c R (nfree + newc)) m0) as MU. pose proof (wmono_refl ctasegs m0) as WM.
  unfold pfa_frame in FR.
  zstep. ifF.
  zstep. zstep. ifF.
  do 7 zstep.
  replace (rb SB c + 3758096384)%Z with (fa SB c) by (unfold fa; lia).
  rewrite (Z.shiftl_mul_pow2 (nfree + newc) 2) by lia. change (2 ^ 2)%Z with 4%Z.
  replace ((nfree + newc) * 4)%Z with (4 * (nfree + newc))%Z by lia.
  assert (E0 : Z_to_bv 64 auser = Z_to_bv 64 (auser + 0 * ClassSize c)) by (f_equal; lia).
  rewrite E0 at 2.
  eapply (pfa_loop (Z.to_nat newc) 0%Z); try eassumption; try lia.
Qed.
End Tail.

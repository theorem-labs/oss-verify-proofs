(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small F_memset X_atexit X_gdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac fold_closed_regs :=
  repeat match goal with
  | |- context [Z_to_bv 64 ?z] => lazymatch z with Z0 => fail | Zpos _ => fail | Zneg _ => fail | _ => idtac end;
       let v := eval vm_compute in z in is_Zlit v; change (Z_to_bv 64 z) with (Z_to_bv 64 v)
  end.
Lemma land_7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma C8_first_byte : forall (m : mem) A v pre post, ro_cells asegs m A (pre ++ C8 v :: post) ->
  ov_read_bytes asegs m (wa (A + Z.of_nat (cells_size pre))) 1 = Some [Z_to_bv 8 (bv_unsigned v)].
Proof.
  intros m A v pre post [Hwf Hb]. apply cells_wf_app in Hwf. destruct Hwf as [Hw1 _].
  rewrite <- (cells_bytes_length pre Hw1). rewrite (bytes_at_ov_read asegs m A _ _ 1 Hb).
  - rewrite cells_bytes_app, skipn_app_exact. reflexivity.
  - rewrite cells_bytes_app, length_app. cbn [cells_bytes cbytes]. rewrite length_app, length_le8. lia.
Qed.

Lemma byte_land7 : forall z, z mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 8 z)) 7 = 0.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  rewrite land_7 by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations. lia.
Qed.

Lemma stk_window : forall (m : mem) lo hi a n, stk asegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n ->
  stk asegs m lo a /\ (exists junk, rw_cells asegs m a [CB (Z.to_nat n) junk]) /\ stk asegs m (a + n) hi.
Proof.
  intros m lo hi a n ST H1 H2 H3.
  destruct (stk_split asegs m lo a hi ST ltac:(lia)) as [S1 S23].
  destruct (stk_split asegs m a (a + n) hi S23 ltac:(lia)) as [S2 S3].
  split; [exact S1|]. split; [| exact S3].
  destruct (stk_carve asegs m a (a + n) (Z.to_nat n) S2 ltac:(lia)) as [_ (junk & FR)].
  exists junk. replace (a + n - Z.of_nat (Z.to_nat n)) with a in FR by lia. exact FR.
Qed.

Lemma stk_unwindow : forall (m : mem) lo hi a n cs, stk asegs m lo a -> rw_cells asegs m a cs -> Z.of_nat (cells_size cs) = n ->
  stk asegs m (a + n) hi -> lo <= a -> a + n <= hi -> stk asegs m lo hi.
Proof.
  intros m lo hi a n cs S1 C En S3 H1 H2. pose proof (stk_of_rw_cells asegs m a cs C) as S2. rewrite En in S2.
  apply (stk_merge asegs m lo a hi S1); [| lia]. apply (stk_merge asegs m a (a + n) hi S2 S3). lia.
Qed.

Definition can_poison_entry := 0x1c453c%Z.

Lemma can_poison_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  ro_cells asegs m 0x66c39c [C1 (Z_to_bv 8 1)] ->
  mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c453c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros CI MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 5 zstep.
  finish.
Qed.


Lemma unreg_iter_head : forall (A K beg srz : Z)
    (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sp : word) F fc (m : mem),
  ro_cells asegs m A [C8 (Z_to_bv 64 beg)] -> ro_cells asegs m (A + 16) [C8 (Z_to_bv 64 srz)] ->
  rw_cells asegs m 0x66d818 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x66c39c [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x66a350 [C4 (Z_to_bv 64 1)] ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m 0x6fe6e0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells asegs m 0x5a77f0 [C8 (Z_to_bv 64 0x526914)] ->
  stk asegs m SHW_LO SHW_HI ->
  (SHW_LO <= SHB + beg / 8 /\ SHB + beg / 8 + srz / 8 <= SHW_HI) ->
  0 <= beg -> beg mod 8 = 0 -> 8 <= srz -> srz mod 8 = 0 -> beg + srz <= 0xbc6000 -> srz / 8 < 0x10000 ->
  0x5aaa60 <= A -> A + 64 <= 0x669460 -> 1 <= K <= GT_N ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        ms' = MS (mkR (Z_to_bv 64 0x1aa07c) sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x6fe668) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 2) (Z_to_bv 64 0x3581a) (Z_to_bv 64 A) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x66a3b0)
                      (Z_to_bv 64 0x5a77f0) (Z_to_bv 64 0x66a3f0) (Z_to_bv 64 0x66a338) (Z_to_bv 64 0x66cb38) (Z_to_bv 64 K)
                      t3' t4' t5' t6')
                 F (Z_to_bv 64 0x1aa07c) fc None m' (seg_rom asegs)
        /\ munch [(SHW_LO, SHW_HI)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' SHW_LO SHW_HI)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x6fe668) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x3581a) (Z_to_bv 64 A) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x66a3b0)
             (Z_to_bv 64 0x5a77f0) (Z_to_bv 64 0x66a3f0) (Z_to_bv 64 0x66a338) (Z_to_bv 64 0x66cb38) (Z_to_bv 64 K)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1aa094) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros REC REC2 AI CP RG SHC THR RMS SC1 INS B0 B8 S8 S8m BT ST8 A0 A1 HK MI.
  unfold SHB, GT_N in *.
  pose proof (munch_refl [(0x7fff8000 + beg / 8, 0x7fff8000 + beg / 8 + srz / 8)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EUb : bv_unsigned (Z_to_bv 64 beg) = beg) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 srz) = srz) by (apply unsigned_lit; lia).
  assert (EUA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  astep.
  call asan_inited_spec; [exact AI| exact MI|].
  xsteps_to 0x1aa0b8%Z.
  do 6 xstep. fold_closed_regs.
  xstep.
  lstep. rewrite (land_7 beg B0), B8. xstep.
  lazymatch goal with REC2 : ro_cells asegs ?mm (A + 16) [C8 ?v] |- _ =>
    pose proof (C8_first_byte mm (A + 16) v [] [] REC2) as HR end.
  cbn [cells_size Z.of_nat] in HR. rewrite Z.add_0_r in HR.
  lstep. lstep. rewrite (byte_land7 srz S8m). xstep. xstep. clear HR.
  call can_poison_spec; [exact CP| assumption|].
  xstep.
  do 12 lstep.
  assert (E1 : beg ≫ 3 = beg / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (E2 : (beg + srz + -8) ≫ 3 = beg / 8 + srz / 8 - 1).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  rewrite E1, E2.
  replace (2147450880 + (beg / 8 + srz / 8 - 1) + 1) with (2147450880 + beg / 8 + srz / 8) by lia.
  assert (EUN : bv_unsigned (Z_to_bv 64 (srz / 8)) = srz / 8) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  lstep.
  rewrite (Z.mod_small (2147450880 + beg / 8 + srz / 8)) by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (2147450880 + beg / 8)) by (Z.div_mod_to_equations; lia).
  replace (2147450880 + beg / 8 + srz / 8 - (2147450880 + beg / 8)) with (srz / 8) by lia.
  if_true.
  lstep. lstep. lstep.
  assert (N0 : 0 <= srz / 8) by (Z.div_mod_to_equations; lia).
  assert (DB : 0 <= 2147450880 + beg / 8 /\ 2147450880 + beg / 8 + srz / 8 <= 2^64) by (Z.div_mod_to_equations; lia).
  destruct INS as (SL0 & SH0).
  destruct (stk_window _ _ _ (2147450880 + beg / 8) (srz / 8) SC1 SL0 SH0 N0) as (SA & (junk & DST) & SB). clear SC1.
  call memset_callZ; [exact DST| assumption| lia| lia| lia| lia|].
  pose proof (stk_unwindow _ _ _ _ (srz / 8) _ SA POST ltac:(cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; reflexivity)
                SB SL0 SH0) as SC1.
  apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM|]. split; [assumption|]. exact SC1.
Qed.

(* [comment removed for export] *)
Lemma unreg_iter_tail : forall (A K odr : Z)
    (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sp : word) F fc (m : mem),
  ro_cells asegs m (A + 56) [C8 (Z_to_bv 64 odr)] ->
  stk asegs m ODR_LO ODR_HI ->
  (odr = ODR_NONE \/ ODR_LO <= odr < ODR_HI) ->
  0x5aaa60 <= A -> A + 64 <= 0x669460 -> 1 <= K <= GT_N ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (ra' s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x6fe668) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 2) (Z_to_bv 64 0x3581a) (Z_to_bv 64 (A + 64)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x66a3b0)
                      (Z_to_bv 64 0x5a77f0) (Z_to_bv 64 0x66a3f0) (Z_to_bv 64 0x66a338) (Z_to_bv 64 0x66cb38) (Z_to_bv 64 (K - 1))
                      t3' t4' t5' t6')
                 F (Z_to_bv 64 (if K =? 1 then 0x1aa298 else 0x1aa094)) fc None m' (seg_rom asegs)
        /\ munch [(ODR_LO, ODR_HI)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' ODR_LO ODR_HI)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x6fe668) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x3581a) (Z_to_bv 64 A) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x66a3b0)
             (Z_to_bv 64 0x5a77f0) (Z_to_bv 64 0x66a3f0) (Z_to_bv 64 0x66a338) (Z_to_bv 64 0x66cb38) (Z_to_bv 64 K)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1aa07c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros REC OW ODR A0 A1 HK MI. unfold GT_N in HK.
  pose proof (munch_refl [(ODR_LO, ODR_HI)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EUA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (EUK : bv_unsigned (Z_to_bv 64 K) = K) by (apply unsigned_lit; lia).
  assert (EUK1 : K <> 1 -> bv_unsigned (Z_to_bv 64 (K + -1)) = K + -1) by (intros; apply unsigned_lit; lia).
  unfold ODR_NONE in ODR.
  destruct ODR as [ -> | ODR ].
  - (* [comment removed for export] *)
    lstep. lstep. xstep. lstep. lstep.
    destruct (Z.eqb_spec K 1) as [EK|NK].
    + subst K. xstep.
      apply evt_done. do 18 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; assumption.
    + specialize (EUK1 NK). lstep. if_false.
      replace (if K =? 1 then 1745560 else 1745044) with 1745044 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]).
      apply evt_done. do 18 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; assumption.
  - (* [comment removed for export] *)
    assert (EUo : bv_unsigned (Z_to_bv 64 odr) = odr) by (apply unsigned_lit; lia).
    assert (EUo1 : bv_unsigned (Z_to_bv 64 (odr + 1)) = odr + 1) by (apply unsigned_lit; lia).
    destruct (stk_window _ _ _ odr 1 OW ltac:(lia) ltac:(lia) ltac:(lia)) as (SA & (junk & DST) & SB). clear OW.
    change (Z.to_nat 1) with 1%nat in DST.
    lstep. lstep. xstep. lstep. lstep. lstep.
    lazymatch goal with DST' : rw_cells asegs ?mm odr ?cs |- _ =>
      pose proof (stk_unwindow mm _ _ odr 1 cs SA DST' ltac:(reflexivity) SB ltac:(lia) ltac:(lia)) as OW' end.
    destruct (Z.eqb_spec K 1) as [EK|NK].
    + subst K. xstep. xstep.
      apply evt_done. do 18 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; assumption.
    + specialize (EUK1 NK). lstep. if_true.
      replace (if K =? 1 then 1745560 else 1745044) with 1745044 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]).
      apply evt_done. do 18 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; assumption.
Qed.

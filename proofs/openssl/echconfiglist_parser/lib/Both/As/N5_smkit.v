(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel SysStep.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import InNth.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsWalk FakeStackRep N5_tls.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition mts_post (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (p : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 a2 a3 a4 a5 a6 a7,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sh p)) (Z_to_bv 64 ASHADOW_BASE) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs).
Lemma mts_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p : Z),
  mem_inv asegs m -> a0 = Z_to_bv 64 p ->
  ((0 <= p /\ p + 8 <= ALOWSH_LO) \/ (AHI_LO <= p /\ p + 8 <= AAPP_HI)) ->     (* [comment removed for export] *)
  rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
  rw_cells asegs m AGOT_MIDBEG [C8 (wz AMIDBEG_CELL)] -> rw_cells asegs m AGOT_MIDEND [C8 (wz AMIDEND_CELL)] ->
  rw_cells asegs m AGOT_HIEND [C8 (wz AHIEND_CELL)] ->
  rw_cells asegs m AHIEND_CELL [C8 (wz (2^47 - 1)); C8 (wz 0); C8 (wz 0)] ->
  evt asegs (mts_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc p m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a3728) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros MI Ha0 PP G1 C1 G2 G3 G4 C4. subst a0.
  unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_MIDBEG, AMIDBEG_CELL, AGOT_MIDEND, AMIDEND_CELL, AGOT_HIEND, AHIEND_CELL, AHI_LO, AAPP_HI, ALOWSH_LO, wz in *.
  rewrite ASHADOW_BASE_val in *.
  do 7 zstep.
  replace (Z.land (Z.land (Z.b2z (2147450880 <? 2147450879) + -1) 18446744073709551615) 2147450879)
    with 2147450879 by reflexivity.
  zstep. if_cases K1; zify_cond K1.
  { (* [comment removed for export] *)
    zstep. zstep. rewrite Z.add_comm, sh_shiftr by lia. zstep. unfold mts_post. finish. }
  destruct PP as [PP|PP]; [exfalso; lia|]. destruct PP as [P0 P1].
  do 7 zstep.
  replace (0 + -1) with (-1) by reflexivity.
  zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
  do 5 zstep.
  change (Z.shiftr (2^47 - 1) 3 + 2147450880) with 17594333495295.
  zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
  zstep. if_cases K4; zify_cond K4; [exfalso; lia|].
  zstep. zstep. rewrite Z.add_comm, sh_shiftr by lia. zstep. unfold mts_post. finish.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_8191 : forall x, Z.land x 8191 = x mod 8192.
Proof. intros. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_1023 : forall x, Z.land x 1023 = x mod 1024.
Proof. intros. change 1023 with (Z.ones 10). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma unsigned_wrap_mod : forall e k, 0 <= k <= 64 -> bv_unsigned (Z_to_bv 64 e) mod 2 ^ k = e mod 2 ^ k.
Proof.
  intros e k Hk. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  apply Z.mod_mod_divide. exists (2 ^ (64 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma wrap_mod_8192 : forall e, bv_unsigned (Z_to_bv 64 e) mod 8192 = e mod 8192.
Proof. intros e. exact (unsigned_wrap_mod e 13 ltac:(lia)). Qed.
Lemma wrap_mod_1024 : forall e, bv_unsigned (Z_to_bv 64 e) mod 1024 = e mod 1024.
Proof. intros e. exact (unsigned_wrap_mod e 10 ltac:(lia)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ACONST_mts : forall m, ACONST m ->
     rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] /\ rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)]
  /\ rw_cells asegs m AGOT_MIDBEG [C8 (wz AMIDBEG_CELL)] /\ rw_cells asegs m AGOT_MIDEND [C8 (wz AMIDEND_CELL)]
  /\ rw_cells asegs m AGOT_HIEND [C8 (wz AHIEND_CELL)]
  /\ rw_cells asegs m AHIEND_CELL [C8 (wz (2^47 - 1)); C8 (wz 0); C8 (wz 0)].
Proof. intros m AC. repeat split; (eapply ACONST_cell; [exact AC| in_nth]). Qed.

Lemma sh_add8 : forall a k, a mod 8 = 0 -> sh (a + 8 * k) = sh a + k.
Proof. intros a k Ha. unfold sh. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma shad16_of_words : forall m A, 0 <= A -> A mod 8 = 0 ->
  rw_cells asegs m (sh A) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> SHAD m A (poison_bytes 16 0).
Proof.
  intros m A H0 H8 RC. split; [exact H0|]. split; [exact H8|].
  apply (u8arr_of_rw_cells asegs m (sh A) 16).
  pose proof (rw_cells_merge asegs m (sh A) [] [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] []) as M.
  rewrite app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
  exact (M RC).
Qed.

(* [comment removed for export] *)
Lemma sh1d9790_of_words : forall m A, 0 <= A -> A mod 8 = 0 ->
  rw_cells asegs m (sh A) (repeat (C8 (Z_to_bv 64 0)) 16) -> SHAD m A (poison_bytes 128 0).
Proof.
  intros m A H0 H8 RC. split; [exact H0|]. split; [exact H8|].
  apply (u8arr_of_rw_cells asegs m (sh A) 128).
  pose proof (rw_cells_merge asegs m (sh A) [] (repeat (C8 (Z_to_bv 64 0)) 16) []) as M.
  rewrite app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add repeat] in M.
  exact (M RC).
Qed.

(* [comment removed for export] *)
Lemma aconst_ok_hi5 : forall lo hi, AHI_LO <= lo -> aconst_ok (lo, hi).
Proof.
  intros lo hi L1. apply aconst_ok_high; cbn; [| unfold AHI_LO in *; lia].
  pose proof (sh_below_app AIMG_TOP ltac:(unfold AIMG_TOP, AAPP_HI; lia)). apply (Z.le_trans _ AHI_LO); [| exact L1].
  unfold sh, AIMG_TOP, AHI_LO. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
Qed.
Lemma aconst_ok_aapp5 : forall A n lo hi, aapp A n -> A <= lo -> hi <= A + n -> aconst_ok (lo, hi).
Proof.
  intros A n lo hi AP L1 L2. destruct AP as [[P1 P2]|[P1 P2]]; [| apply aconst_ok_hi5; lia].
  apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
    AF_DCO_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP, ALOWSH_LO in *; rewrite ?ASHADOW_BASE_val; try lia.
Qed.
(* [comment removed for export] *)
Lemma aconst_ok_shadow5 : forall A lo hi, AIMG_TOP <= A -> sh A <= lo -> aconst_ok (lo, hi).
Proof.
  intros A lo hi HA HS. apply aconst_ok_high; cbn.
  - pose proof (sh_mono AIMG_TOP A HA). lia.
  - right; left. unfold sh, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *. lia.
Qed.
End HCW.

(* [comment removed for export] *)
Ltac aconst5 G1 G4 :=
  first [ eapply aconst_ok_aapp5; [exact G4| unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *; lia| unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *; lia]
        | eapply aconst_ok_shadow5; [exact G1| unfold sh in *; rewrite ?ASHADOW_BASE_val in *; lia]
        | apply aconst_ok_high; [| right; left]; acb; unfold sh, AIMG_TOP in *; rewrite ?ASHADOW_BASE_val in *; lia ].

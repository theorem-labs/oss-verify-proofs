(* WireCmCmp: lib/B/Prog/WireCmIface.v cm_cmp_stmt, the checks after the call of rp_meter_counter in check_meter of
   fuzz_wire.asan-ubsan (0x80350 .. 0x803c0, to CM_REL = 0x803c4), stepped by lib/Lib/StepF.v in the form of
   reac-repacer/fuzz_uci's lib/B/Prog/UciCvBSegs.v (recipes commit 0295462466b2), the shadow checks of the two frame
   bytes stepped with lib/B/Prog/AsanKAProof.v (gen_addi, gen_shr, rdw0, sxb_eq0, land7, lts_low, zxb_u):
     0x80350 `bne a0, s10` falls through (both are the want bit); 0x80354 `lhu a1, 0(s5)` reads ctr;
     want bit 0: 0x80358 `beqz s10` taken to 0x803b8, a0 := 0xa5c3, 0x803c0 `bne a1, a0` falls through;
     want bit 1: the UBSan wrap checks of f + eo + 2 / f + eo + 3 (0x80364, 0x8036c) fall through, the shadow checks of
     f + eo + 2 (0x80380) and f + eo + 3 (0x80398) pass (k = 0, or the in-granule check at 0x80484 / 0x80490 taken),
     a0 := f[eo + 2] | f[eo + 3] << 8, 0x803a8 `beq a0, a1` taken. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof WireCmIface.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Lemma cm_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma cm_eo_cases : forall n bs, PMC.meter_eo n bs = 12%nat \/ PMC.meter_eo n bs = 16%nat.
Proof. intros n bs. unfold PMC.meter_eo. destruct (_ && _ && _); auto. Qed.

Lemma cm_mb : forall bs (k j : nat), PMC.meter_byte bs (k + j) = bv_unsigned (cm_byte bs (Z.of_nat k + Z.of_nat j)).
Proof. intros bs k j. unfold PMC.meter_byte, cm_byte. rewrite <- Nat2Z.inj_add, Nat2Z.id. reflexivity. Qed.

(* the in-granule check `andi; blt` of a shadow byte k <> 0, taken *)
Ltac cm_lts := match goal with
  | |- context [bv_lts (Z_to_bv 64 (Z.land (bv_unsigned ?w) 7)) (sxb ?k)] =>
      rewrite (land7 (bv_unsigned w));
      rewrite (lts_low (bv_unsigned w mod 8) k ltac:(apply Z.mod_pos_bound; lia));
      rewrite (proj2 (Z.ltb_lt (bv_unsigned w mod 8) (bv_signed k)) ltac:(Z.div_mod_to_equations; lia)); cbn [negb]
  end.
(* `not a2, s3` of f, with f + 20 < 2 ^ 64 *)
Ltac cm_gen_not w U := match goal with
  | |- context [Some (Z_to_bv 64 (Z.lxor (bv_unsigned ?x) 18446744073709551615))] =>
      let Ew := fresh "Ew" in
      assert (U : bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned x) 18446744073709551615))
                  = 18446744073709551615 - bv_unsigned x)
        by (pose proof (bv_unsigned_in_range 64 x) as Rx; unfold bv_modulus in Rx;
            change (2 ^ Z.of_N 64) with (2^64) in Rx;
            rewrite zb_lxor_ones by lia; apply unsigned_lit; lia);
      remember (Z_to_bv 64 (Z.lxor (bv_unsigned x) 18446744073709551615)) as w eqn:Ew; clear Ew
  end.

(* `beq a0, a1` at 0x803a8: a0 = f[eo + 2] | f[eo + 3] << 8 (after `slli`, `or`), a1 = ctr read by `lhu` *)
Lemma cm_beq : forall x y : byte,
  bv_eqb (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb y)) 8))) (bv_unsigned (zxb x))))
         (zx16 (Z_to_bv 64 (bv_unsigned x + 256 * bv_unsigned y))) = true.
Proof.
  intros x y. pose proof (byte_range x). pose proof (byte_range y).
  unfold zxb. rewrite !zxb_u. unfold bv_eqb. apply Z.eqb_eq.
  rewrite lor_bytes16. unfold zx16.
  rewrite (unsigned_lit (bv_unsigned x + 256 * bv_unsigned y)) by lia.
  rewrite Z.mod_small by lia. rewrite unsigned_lit by lia. reflexivity.
Qed.

Ltac cm_lit X := let v := eval vm_compute in X in change X with v.
Ltac cm_lits :=
  repeat match goal with
  | |- context [CM_RET_LEAF] => cm_lit CM_RET_LEAF
  | |- context [CM_REL] => cm_lit CM_REL
  end.

Lemma cm_cmp : cm_cmp_stmt.
Proof.
  unfold cm_cmp_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s11 t3 t4 t5 t6 F fc m f n Fa bs Q
    HN HL HFa HFa2 CT RCT OK K.
  cm_lits.
  let v := eval vm_compute in CM_REL in change CM_REL with v in K.
  unfold cm_ctr in CT. unfold cm_bit in K |- *.
  destruct (PMC.meter_ok n bs) eqn:MOK; cbv iota in K |- *.
  2:{
    pose proof (cm_rd_all _ _ _ CT) as RDC. rewrite length_le2 in RDC.
    (* bne a0, s10 (not taken); lhu a1, 0(s5); beqz s10 (taken); lui; addiw; bne a1, a0 (not taken) *)
    step. if_false.
    step.
    step. if_true.
    do 2 step. step. if_false.
    apply K. }
  destruct (OK eq_refl) as (Hf0 & Hf20 & RD & ADR & RF & RSH). clear OK.
  unfold PMC.meter_value in CT. cbv zeta in CT. rewrite !cm_mb in CT.
  set (e := Z.of_nat (PMC.meter_eo n bs)) in *.
  assert (HE : e = 12 \/ e = 16) by (unfold e; destruct (cm_eo_cases n bs) as [-> | ->]; auto).
  clearbody e.
  change (Z.of_nat 2) with 2 in CT. change (Z.of_nat 3) with 3 in CT.
  pose proof (RD (e + 2) ltac:(lia)) as F2. pose proof (RD (e + 3) ltac:(lia)) as F3.
  set (b2 := cm_byte bs (e + 2)) in *. set (b3 := cm_byte bs (e + 3)) in *.
  clearbody b2 b3. clear RD.
  pose proof (cm_rd_all _ _ _ CT) as RDC. rewrite length_le2 in RDC.
  destruct ADR as (P0 & N0 & PE & AB).
  destruct (AB (e - 10) ltac:(lia)) as (APP2 & k2 & MK2 & SK2).
  destruct (AB (e - 9) ltac:(lia)) as (APP3 & k3 & MK3 & SK3).
  clear AB.
  remember (Z_to_bv 64 f) as fw eqn:Efw.
  assert (Uf : bv_unsigned fw = f) by (subst fw; apply unsigned_lit; lia).
  clear Efw.
  assert (DV2 : (f + 12) / 8 <= (f + 12 + (e - 10)) / 8) by (apply Z.div_le_mono; lia).
  assert (DV3 : (f + 12 + (e - 9)) / 8 <= (f + 19) / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.mod_pos_bound (f + 12 + (e - 10)) 8 ltac:(lia)) as MB2.
  pose proof (Z.mod_pos_bound (f + 12 + (e - 9)) 8 ltac:(lia)) as MB3.
  unfold shadow_addr, ASAN_K, shadow_ok in *.
  destruct HE as [-> | ->].
  (* bne a0, s10 (not taken); lhu a1, 0(s5); beqz s10 (not taken) *)
  all: step; if_false.
  all: step.
  all: step; if_false.
  (* addi a0, s9, 2; not a2, s3; bltu a2, a0 (not taken); addi s9, s9, 3; bltu a2, s9 (not taken) *)
  all: step.
  all: step; cm_gen_not nw NU.
  all: step; if_false.
  all: step.
  all: step; if_false.
  (* f + eo + 2: its shadow byte and check *)
  all: step; gen_addi fw w2 U2.
  all: step; gen_shr w2 g2 G2.
  all: rewrite U2 in G2.
  all: step; gen_addi g2 h2 H2.
  all: pose proof (rdw0 m h2 _ _ MK2 ltac:(lia)) as R; step; clear R.
  all: step.
  all: destruct SK2 as [C|[C Cu]].
  1, 3: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  all: try (rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k2) 0) ltac:(lia)); cbn [negb]; step; step; cm_lts).
  (* f + eo + 3: its shadow byte and check (s3 := f + eo + 3), the load of f[eo + 2] between them *)
  all: step; gen_addi fw w3 U3.
  all: step; gen_shr w3 g3 G3.
  all: rewrite U3 in G3.
  all: step; gen_addi g3 h3 H3.
  all: pose proof (rdw0 m h3 _ _ MK3 ltac:(lia)) as R; step; clear R.
  all: pose proof (rdw0 m w2 _ _ F2 ltac:(lia)) as R; step; clear R.
  all: step.
  all: destruct SK3 as [C'|[C' Cu']].
  1, 3, 5, 7: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C'); cbn [negb].
  all: try (rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k3) 0) ltac:(lia)); cbn [negb]; step; step; cm_lts).
  (* f[eo + 3]; slli; or; beq a0, a1 *)
  all: pose proof (rdw0 m w3 _ _ F3 ltac:(lia)) as R; step; clear R.
  all: do 2 step.
  all: step; if_true_by (cm_beq b2 b3).
  all: apply K.
Qed.

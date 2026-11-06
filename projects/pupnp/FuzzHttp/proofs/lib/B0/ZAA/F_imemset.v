(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_memset STRW_tac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs.
Import ListNotations.
Open Scope bv_scope.

Definition imemset_entry := 0x69998%Z.

Ltac with_arr tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
  end.
Ltac brute256 c Rc :=
  first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
  repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
  revert c Rc; apply brute256_ok; vm_compute; reflexivity.

Definition imemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (c n : Z) (a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1' a2' a3' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c n : Z).
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + n < 2^64 /\ 0 <= n < 2^63)%Z.
  Hypothesis Rc : (0 <= c < 256)%Z.

  Notation A := (bv_unsigned a0).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + n)]%Z.
  Notation POST := (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 c n a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 m).

  Notation ST pc mm x11 x12 x13 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Ltac fin_with cover :=
    zstep;
    with_arr ltac:(fun segs ARR FIL LEN A cb =>
      let E := fresh "E" in
      pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
      rewrite LEN in E; rewrite E in ARR;
      apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
    finish; subst; assumption.
  Ltac fin := fin_with ltac:(intros j Hj; cbv beta; lia).

  Lemma imemset_bloop : forall (K : nat) (p : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop) (x13 : word),
    Z.to_nat (n - p) = K ->
    u8arr asegs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
    mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
    (forall j, (0 <= j < p)%Z -> Q j) -> (0 <= p < n)%Z -> x13 = Z_to_bv 64 (A + p) ->
    evt asegs POST (ST 0x699b0 m1 (Z_to_bv 64 c) (Z_to_bv 64 (A + n)) x13).
  Proof using AB Rc.
    induction K as [K IH] using lt_wf_ind; intros p m1 bs Q x13 HK ARR FIL LEN MI MU WM HQ Hp ->.
    mst p 1%nat ltac:(rewrite le1_byte, unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
    zstep. zstep. if_cases KK; zify_cond KK.
    -
      replace (A + p + 1)%Z with (A + (p + 1))%Z by lia.
      eapply (IH (Z.to_nat (n - (p + 1))) ltac:(lia) (p + 1)%Z _ _ _ _ eq_refl ARR FIL LEN MI MU WM); [| lia | reflexivity].
      intros j Hj. destruct (Z_lt_le_dec j p); [left; apply HQ; lia | right; lia].
    - zstep.   fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j p); [left; apply HQ; lia | right; lia]).
  Qed.

  Lemma imemset_wloop : forall (K : nat) (p : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop) (x13 : word),
    Z.to_nat (n - p) = K ->
    u8arr asegs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
    mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
    (forall j, (0 <= j < p)%Z -> Q j) -> (0 <= p)%Z -> (p + 16 <= n)%Z -> (exists q, n - p = 16 * q)%Z -> x13 = Z_to_bv 64 (A + p) ->
    evt asegs POST (ST 0x699e4 m1 (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 (A + n)) x13).
  Proof using AB Rc.
    induction K as [K IH] using lt_wf_ind; intros p m1 bs Q x13 HK ARR FIL LEN MI MU WM HQ Hp Hpn [q Hq] ->.
    mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    zstep. zstep. if_cases KK; zify_cond KK.
    - replace (A + p + 16)%Z with (A + (p + 16))%Z by lia.
      eapply (IH (Z.to_nat (n - (p + 16))) ltac:(lia) (p + 16)%Z _ _ _ _ eq_refl ARR FIL LEN MI MU WM); [| lia | lia | exists (q - 1)%Z; lia | reflexivity].
      intros j Hj. destruct (Z_lt_le_dec j p); [left; left; apply HQ; lia|].
      destruct (Z_lt_le_dec j (p + 8)); [left; right; lia | right; lia].
    - fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j p); [left; left; apply HQ; lia|];
                      destruct (Z_lt_le_dec j (p + 8)); [left; right; lia | right; lia]).
  Qed.

  Lemma imemset_body : forall junk (x13 : word),
    rw_cells asegs m A [CB (Z.to_nat n) junk] ->
    evt asegs POST (ST imemset_entry m (Z_to_bv 64 c) (Z_to_bv 64 n) x13).
  Proof using AB MI0 Rc.
    intros junk x13 DST. pose proof MI0 as MI. unfold imemset_entry.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
    pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
    pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.
    zstep. zstep. zstep. if_cases K0; zify_cond K0.
    -
      assert (AL : (A mod 16 = 0 /\ n mod 16 = 0)%Z).
      { rewrite Z.land_lor_distr_l in K0. change 15%Z with (Z.ones 4) in K0. rewrite !Z.land_ones in K0 by lia.
        change (2^4)%Z with 16%Z in K0. pose proof (Z.lor_nonneg (A mod 16) (n mod 16)).
        assert (N1 : (0 <= A mod 16 < 16)%Z) by (apply Z.mod_pos_bound; lia).
        assert (N2 : (0 <= n mod 16 < 16)%Z) by (apply Z.mod_pos_bound; lia).
        apply Z.lor_eq_0_iff in K0. lia. }
      zstep. if_cases K1; zify_cond K1. {   fin. }
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      setreg 11%Z (Z_to_bv 64 (c * BC8)) ltac:(brute256 c Rc).
      eapply (imemset_wloop (Z.to_nat (n - 0)) 0 m junk _ _ eq_refl ARR FIL LEN MI MU WM); try lia.
      all: try (exists (n / 16)%Z; Z.div_mod_to_equations; lia).
      all: try (rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned).
    - zstep. if_cases K1; zify_cond K1. { fin. }
      zstep. zstep.
      eapply (imemset_bloop (Z.to_nat (n - 0)) 0 m junk _ _ eq_refl ARR FIL LEN MI MU WM); try lia.
      all: try (rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned).
  Qed.
End Proofs.

Theorem imemset_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c n : Z) (junk : list byte),
    mem_inv asegs m ->
    (0 <= c < 256)%Z -> (0 <= n < 2^63)%Z -> (bv_unsigned a0 + n < 2^64)%Z ->
    a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n ->
    rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat n) junk] ->
    evt asegs (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 c n a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 imemset_entry) fc None m (seg_rom asegs)).
Proof.
  intros. subst. pose proof (bv_unsigned_in_range 64 a0).
  eapply imemset_body; eauto. lia.
Qed.

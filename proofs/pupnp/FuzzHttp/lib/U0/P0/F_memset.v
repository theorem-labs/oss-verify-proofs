(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_memset.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
Import ListNotations.
Open Scope bv_scope.

Definition memset_entry := 0x24660%Z.

Ltac with_arr tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
  end.

Ltac brute256 c Rc :=
  first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
  repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
  revert c Rc; apply brute256_ok; vm_compute; reflexivity.

Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.

Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof.
  intros x Hx H4.
  transitivity (Z.land (x mod 8) 4).
  { change 8%Z with (2^3)%Z. rewrite <- Z.land_ones by lia. change (Z.ones 3) with 7%Z.
    rewrite <- Z.land_assoc. reflexivity. }
  assert (R : (x mod 8 = 0 \/ x mod 8 = 4)%Z) by (Z.div_mod_to_equations; lia).
  destruct R as [R|R]; rewrite R; reflexivity.
Qed.

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).

  Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Ltac fin_with cover :=
    zstep;
    with_arr ltac:(fun segs ARR FIL LEN A cb =>
      let E := fresh "E" in
      pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
      rewrite LEN in E; rewrite E in ARR;
      apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
    finish; subst; assumption.
  Ltac fin := fin_with ltac:(intros j Hj; cbv beta; lia).
  Ltac disj_lia := first [ lia | right; lia | left; disj_lia ].

  Lemma memset_loop : forall (K : nat) (c p r e : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop)
      (x15 x16 : word),
    Z.to_nat r = K ->
    c = (bv_unsigned a1 mod 256)%Z ->
    u8arr rsegs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
    mem_inv rsegs m1 -> munch W m m1 -> wmono rsegs m m1 ->
    (forall j, (0 <= j < p \/ e <= j < n) -> Q j)%Z ->
    (0 <= p)%Z -> (32 <= r)%Z -> (exists q, r = 4 * q)%Z -> (p + r <= n)%Z -> (e + 28 <= p + r)%Z ->
    evt rsegs POST (ST 0x24738 m1 (Z_to_bv 64 (A + p)) (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 31) (Z_to_bv 64 r) x15 x16).
  Proof using AB.
    induction K as [K IH] using lt_wf_ind; intros c p r e m1 bs Q x15 x16 HK Hc ARR FIL LEN MI MU WM HQ Hp Hr [q4 Hq4] Hpr He;
      assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
    mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 16)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 24)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    zstep. zstep. zstep.
    if_cases KK; zify_cond KK.
    -
      replace (A + p + 32)%Z with (A + (p + 32))%Z by lia.
      replace (r + -32)%Z with (r - 32)%Z by lia.
      eapply (IH (Z.to_nat (r - 32)) ltac:(lia) c (p + 32)%Z (r - 32)%Z e _ _ _ x15 x16 eq_refl Hc ARR); try eassumption; try LiaTuning.alia.
      2:{ exists (q4 - 8)%Z. lia. }
      intros j Hj.
      destruct (Z_lt_le_dec j p) as [Hlt|Hge]. { left; left; left; left. apply HQ. lia. }
      destruct (Z_lt_le_dec j (p + 32)) as [Hlt2|Hge2]. 2:{ left; left; left; left. apply HQ. lia. }
      assert (D : ((p <= j < p + 8 \/ p + 8 <= j < p + 16) \/ (p + 16 <= j < p + 24 \/ p + 24 <= j < p + 32))%Z) by lia.
      destruct D as [[?|?]|[?|?]]; [left; left; left; right| left; left; right| left; right| right]; lia.
    - fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j p); [repeat left; apply HQ; lia|];
                      destruct (Z_lt_le_dec j (p + 32)); [|repeat left; apply HQ; lia]; disj_lia).
  Qed.

  Lemma memset_body : forall junk,
    rw_cells rsegs m A [CB (Z.to_nat n) junk] ->
    evt rsegs POST (ST 0x24660 m a1 a2 a3 a4 a5 a6).
  Proof using AB MI0.
    intros junk DST. pose proof MI0 as MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (zr_word a1) as R1. unfold inr64 in R1.
    remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
    assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
    pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
    pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.

    zstep. if_cases K0; zify_cond K0. { fin. }
    assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
    pose proof (ms_store_ok rsegs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
    zstep. ms_arr_store MF ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. zstep. mst (n - 1)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K3; zify_cond K3. { fin. }
    mst 1%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    mst 2%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep.
    mst (n - 3)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    mst (n - 2)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K7; zify_cond K7. { fin. }
    mst 3%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep.
    mst (n - 4)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K9; zify_cond K9. { fin. }

    zstep. zstep.
    setreg 16%Z (Z_to_bv 64 (c * 2^56)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; subst c; Z.div_mod_to_equations; lia).
    zstep. zstep.
    remember (Z.land (bv_swrap 32 (0 - A) mod 18446744073709551616) 3) as k eqn:Hk.
    assert (Rk : (0 <= k < 4 /\ (A + k) mod 4 = 0)%Z).
    { subst k. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia.
      unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
      change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
      Z.div_mod_to_equations. lia. }
    clear Hk.
    zstep. zstep. zstep. zstep. zstep.
    change 18446744073709551612%Z with (2^64 - 2^2)%Z. rewrite land_align_down by lia.
    remember (n - k - (n - k) mod 2^2)%Z as n4 eqn:Hn4.
    assert (Rn4 : (exists q, n4 = 4 * q)%Z /\ (n - k - 3 <= n4 <= n - k)%Z).
    { split. { exists ((n - k) / 4)%Z. subst n4. Z.div_mod_to_equations. lia. } subst n4. Z.div_mod_to_equations. lia. }
    clear Hn4. destruct Rn4 as [[q4 Hq4] Rn4].
    zstep. setreg 12%Z (Z_to_bv 64 (c * BC4)) ltac:(unfold BC4; brute256 c Rc).

    mst k 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. mst (k + n4 - 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K9'; zify_cond K9'. { fin. }
    mst (k + 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep.
    mst (k + n4 - 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K25; zify_cond K25. { fin. }
    mst (k + 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).

    zstep.
    remember (Z.land (A + k) 4) as k4 eqn:Hk4.
    assert (Rk4 : ((k4 = 0 \/ k4 = 4) /\ (A + k + k4 + 24) mod 8 = 0)%Z).
    { subst k4. rewrite land4_of_aligned by lia. Z.div_mod_to_equations. lia. }
    clear Hk4.
    zstep. zstep. zstep.
    mst (k + n4 - 28)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K32; zify_cond K32. { fin. }

    zstep. zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (c * BC8)) ltac:(unfold BC4, BC8; brute256 c Rc).
    zstep.
    replace (A + k + (k4 + 24))%Z with (A + (k + k4 + 24))%Z by lia.
    eapply (memset_loop _ c (k + k4 + 24) _ (k + n4 - 28) _ _ _ _ _ eq_refl Hc ARR); try eassumption; try LiaTuning.alia.
    exists (q4 - Z.div k4 4 - 6)%Z. lia.
  Qed.
End Proofs.

Lemma memset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  mem_inv rsegs m ->
  evt rsegs (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24660) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros DST MI.
  eapply memset_body; [exact MI | | exact DST].
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.

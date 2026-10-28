(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Walk.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout R_sizeclass.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Lemma brute_eq : forall (f g : Z -> Z) lo hi, allb (fun x => f x =? g x) lo hi = true ->
  forall x, (lo <= x <= hi)%Z -> f x = g x.
Proof. intros f g lo hi H x Hx. apply Z.eqb_eq. exact (allb_ok _ lo hi H x Hx). Qed.

(* [comment removed for export] *)
Definition classid_post (ra sp gp tp t2 s1 a0 a1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : Z) (m : mem) (pc' : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' a2' a4' a5' a6' a7' : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 (ClassID s)) s1 a0 a1 a2' a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6) F (Z_to_bv 64 pc') fc None m (seg_rom bsegs).

Definition sm (k x : Z) : Z := Z.lor x (Z.shiftr x k).

(* [comment removed for export] *)
Lemma smear_ok : forall s, (1 <= s <= 65536)%Z -> sm 32 (sm 16 (sm 8 (sm 4 (sm 2 (sm 1 s))))) = (2 ^ (Z.log2 s + 1) - 1)%Z.
Proof.
  intros s Hs.
  exact (brute_eq (fun s => sm 32 (sm 16 (sm 8 (sm 4 (sm 2 (sm 1 s)))))) (fun s => 2 ^ (Z.log2 s + 1) - 1)%Z 1 65536
           ltac:(vm_compute; reflexivity) s Hs).
Qed.

Lemma log2_range : forall s, (513 <= s <= 65536)%Z -> (9 <= Z.log2 s <= 16)%Z.
Proof.
  intros s Hs. split.
  - change 9%Z with (Z.log2 512). apply Z.log2_le_mono. lia.
  - change 16%Z with (Z.log2 65536). apply Z.log2_le_mono. lia.
Qed.

(* [comment removed for export] *)
Definition pc_e (X7 : Z) : Z :=
  Z.shiftr ((Z.land ((Z.land ((X7 - Z.land (Z.shiftr X7 1) 6148914691236517205) mod 18446744073709551616) 3689348814741910323
    + Z.land (Z.shiftr ((X7 - Z.land (Z.shiftr X7 1) 6148914691236517205) mod 18446744073709551616) 2) 3689348814741910323
    + Z.shiftr ((Z.land ((X7 - Z.land (Z.shiftr X7 1) 6148914691236517205) mod 18446744073709551616) 3689348814741910323
       + Z.land (Z.shiftr ((X7 - Z.land (Z.shiftr X7 1) 6148914691236517205) mod 18446744073709551616) 2) 3689348814741910323)
       mod 18446744073709551616) 4) mod 18446744073709551616) 1085102592571150095 * 72340172838076673) mod 18446744073709551616) 56.

Lemma popcnt_ok : forall L, (9 <= L <= 16)%Z ->
  pc_e (Z.lxor ((2 ^ (L + 1) - 1) mod 18446744073709551616) 18446744073709551615) = (63 - L)%Z.
Proof.
  intros L HL.
  exact (brute_eq (fun L => pc_e (Z.lxor ((2 ^ (L + 1) - 1) mod 18446744073709551616) 18446744073709551615)) (fun L => 63 - L)%Z 9 16
           ltac:(vm_compute; reflexivity) L HL).
Qed.

(* [comment removed for export] *)
Definition final_e (s L : Z) : Z :=
  Z.lor (Z.lxor (Z.shiftl (63 - L) 1 mod 18446744073709551616) 126)
        (Z.land (Z.shiftr s ((bv_swrap 32 (62 - (63 - L)) mod 18446744073709551616) mod 64)) 1)
  + Z.b2z (0 <? Z.land s (Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 ((bv_swrap 32 (62 - (63 - L)) mod 18446744073709551616) mod 32))
                                   mod 18446744073709551616) 18446744073709551615)) + -2.

Lemma swrap_Lm1 : forall L, (9 <= L <= 16)%Z -> (bv_swrap 32 (62 - (63 - L)) mod 18446744073709551616 = L - 1)%Z.
Proof. intros L HL. exact (brute_eq (fun L => bv_swrap 32 (62 - (63 - L)) mod 18446744073709551616) (fun L => L - 1)%Z 9 16 ltac:(vm_compute; reflexivity) L HL). Qed.

Lemma mask_Lm1 : forall L, (9 <= L <= 16)%Z ->
  Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 ((L - 1) mod 32)) mod 18446744073709551616) 18446744073709551615 = (2 ^ (L - 1) - 1)%Z.
Proof.
  intros L HL. exact (brute_eq (fun L => Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 ((L - 1) mod 32)) mod 18446744073709551616) 18446744073709551615)
                               (fun L => 2 ^ (L - 1) - 1)%Z 9 16 ltac:(vm_compute; reflexivity) L HL).
Qed.

Lemma twoL : forall L, (9 <= L <= 16)%Z -> Z.lxor (Z.shiftl (63 - L) 1 mod 18446744073709551616) 126 = (2 * L)%Z.
Proof. intros L HL. exact (brute_eq (fun L => Z.lxor (Z.shiftl (63 - L) 1 mod 18446744073709551616) 126) (fun L => 2 * L)%Z 9 16 ltac:(vm_compute; reflexivity) L HL). Qed.

Lemma lor_2L_1 : forall L, (9 <= L <= 16)%Z -> Z.lor (2 * L) 1 = (2 * L + 1)%Z.
Proof. intros L HL. exact (brute_eq (fun L => Z.lor (2 * L) 1) (fun L => 2 * L + 1)%Z 9 16 ltac:(vm_compute; reflexivity) L HL). Qed.

Lemma final_ok : forall s, (513 <= s <= 65536)%Z -> final_e s (Z.log2 s) = ClassID s.
Proof.
  intros s Hs. pose proof (log2_range s Hs) as HL. unfold final_e, ClassID.
  rewrite (proj2 (Z.leb_gt s 512)) by lia. cbv zeta.
  remember (Z.log2 s) as L eqn:EL.
  rewrite (swrap_Lm1 L HL). rewrite (Z.mod_small (L - 1) 64) by lia.
  rewrite (mask_Lm1 L HL), (twoL L HL).
  replace (2 ^ (L - 1) - 1)%Z with (Z.ones (L - 1)) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (Z.land (s / 2 ^ (L - 1)) 1) with ((s / 2 ^ (L - 1)) mod 2)%Z by (symmetry; exact (Z.land_ones _ 1 ltac:(lia))).
  pose proof (Z.mod_pos_bound (s / 2 ^ (L - 1)) 2 ltac:(lia)) as B.
  assert (Hb : ((s / 2 ^ (L - 1)) mod 2 = 0 \/ (s / 2 ^ (L - 1)) mod 2 = 1)%Z) by lia.
  pose proof (Z.mod_pos_bound s (2 ^ (L - 1)) ltac:(apply Z.pow_pos_nonneg; lia)) as B2.
  destruct Hb as [-> | ->]; [rewrite Z.lor_0_r| rewrite (lor_2L_1 L HL)];
    destruct (Z.eqb_spec (s mod 2 ^ (L - 1)) 0) as [E|E];
    [rewrite E; cbn [Z.ltb Z.compare Z.b2z]; lia| |rewrite E; cbn [Z.ltb Z.compare Z.b2z]; lia|];
    rewrite (proj2 (Z.ltb_lt 0 _)) by lia; cbn [Z.b2z]; lia.
Qed.

Lemma classid_35x_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s : Z),
  (1 <= s <= 65536)%Z ->
  mem_inv bsegs m ->
  evt bsegs (classid_post ra sp gp tp t2 s1 a0 a1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc s m 0x19a61c)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 s) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19a508) fc None m (seg_rom bsegs)).
Proof.
  intros until s. intros Hs MI.
  zhide.
  do 2 zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    do 28 zstep.
    let e := getreg 12%Z in lazymatch e with Z_to_bv 64 ?E =>
      replace E with (2 ^ (Z.log2 s + 1) - 1)%Z by (exact (eq_sym (smear_ok s ltac:(lia)))) end.
    zstep.
    pose proof (log2_range s ltac:(lia)) as HL. remember (Z.log2 s) as L eqn:EL.
    name_reg 12%Z X7.
    do 14 zstep.
    let e := getreg 12%Z in lazymatch e with Z_to_bv 64 ?E =>
      replace E with (63 - L)%Z by (subst X7; exact (eq_sym (popcnt_ok L HL))) end.
    do 12 zstep.
    let e := getreg 8%Z in lazymatch e with Z_to_bv 64 ?E =>
      replace E with (ClassID s) by (subst L; exact (eq_sym (final_ok s ltac:(lia)))) end.
    apply evt_done. unfold classid_post. do 7 eexists. reflexivity.
  - (* [comment removed for export] *)
    do 3 zstep.
    let e := getreg 8%Z in lazymatch e with Z_to_bv 64 ?E =>
      replace E with (ClassID s) by (rewrite (ClassID_small s ltac:(lia)), Z.shiftr_div_pow2 by lia; reflexivity) end.
    apply evt_done. unfold classid_post. do 7 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Definition classid2_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 : word) (F : bvmap 5 word) (fc : bv 32)
    (A s : Z) (m : mem) (pc' : Z) : machine_state -> Prop :=
  fun ms' => exists (a2' a3' a4' a5' a6' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + 112)) (Z_to_bv 64 (ClassID s)) a2' a3' a4' a5' a6' a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc') fc None m (seg_rom bsegs).

Lemma classid_31fx_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A s : Z),
  (1 <= s <= 65536)%Z -> (0 <= A < 2^63)%Z ->
  mem_inv bsegs m ->
  evt bsegs (classid2_post ra sp gp tp t0 t1 t2 s0 s1 s2 (Z_to_bv 64 s) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 F fc A s m 0x1962b8)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 s) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1961c4) fc None m (seg_rom bsegs)).
Proof.
  intros until s. intros Hs HA MI.
  zhide.
  do 3 zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    do 28 zstep.
    let e := getreg 11%Z in lazymatch e with Z_to_bv 64 ?E =>
      replace E with (2 ^ (Z.log2 s + 1) - 1)%Z by (exact (eq_sym (smear_ok s ltac:(lia)))) end.
    zstep.
    pose proof (log2_range s ltac:(lia)) as HL. remember (Z.log2 s) as L eqn:EL.
    name_reg 11%Z X7.
    do 14 zstep.
    let e := getreg 11%Z in lazymatch e with Z_to_bv 64 ?E =>
      replace E with (63 - L)%Z by (subst X7; exact (eq_sym (popcnt_ok L HL))) end.
    do 12 zstep.
    let e := getreg 11%Z in lazymatch e with Z_to_bv 64 ?E =>
      replace E with (ClassID s) by (subst L; exact (eq_sym (final_ok s ltac:(lia)))) end.
    apply evt_done. unfold classid2_post. do 5 eexists. reflexivity.
  - (* [comment removed for export] *)
    do 3 zstep.
    let e := getreg 11%Z in lazymatch e with Z_to_bv 64 ?E =>
      replace E with (ClassID s) by (rewrite (ClassID_small s ltac:(lia)), Z.shiftr_div_pow2 by lia; reflexivity) end.
    apply evt_done. unfold classid2_post. do 5 eexists. reflexivity.
Qed.

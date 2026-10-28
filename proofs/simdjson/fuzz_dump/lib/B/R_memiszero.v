(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

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

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition memiszero_entry : Z := 0x92050.

Lemma land_m8 : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551608 = (x / 8 * 8)%Z.
Proof.
  intros x Hx. change 18446744073709551608%Z with (Z.land (Z.ones 64) (Z.lnot (Z.ones 3))).
  rewrite Z.land_assoc, (Z.land_ones x 64) by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma skipn_repeat_P : forall {X} (x : X) k n, skipn k (repeat x n) = repeat x (n - k).
Proof. intros X x k. induction k as [|k IH]; intros [|n]; cbn; auto. Qed.

Lemma firstn_repeat_P : forall {X} (x : X) k n, firstn k (repeat x n) = repeat x (Nat.min k n).
Proof. intros X x k. induction k as [|k IH]; intros [|n]; cbn; auto. f_equal. apply IH. Qed.

Lemma zero_read : forall (m : mem) beg size p (n : nat),
  bytes_at bsegs m beg (repeat z8 (Z.to_nat size)) -> (beg <= p)%Z -> (p + Z.of_nat n <= beg + size)%Z ->
  ov_read_bytes bsegs m (Z_to_bv 64 p) n = Some (repeat z8 n).
Proof.
  intros m beg size p n ZB H1 H2.
  pose proof (bytes_at_ov_read bsegs m beg _ (Z.to_nat (p - beg)) n ZB ltac:(rewrite repeat_length; lia)) as R.
  replace (beg + Z.of_nat (Z.to_nat (p - beg)))%Z with p in R by lia. unfold wa in R. rewrite R. f_equal.
  rewrite skipn_repeat_P, firstn_repeat_P. f_equal. lia.
Qed.

Section MZ.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 m : mem) (beg size lo : Z) (junk : list byte).
Hypothesis Hsz : (0 <= size <= 2^40)%Z.
Hypothesis Hbeg : (0 <= beg)%Z.
Hypothesis Hend : (beg + size + 8 <= 2^64)%Z.
Hypothesis ZB : bytes_at bsegs m beg (repeat z8 (Z.to_nat size)).
Hypothesis FR : rw_cells bsegs m (bv_unsigned sp - 16) [CB 8 junk; C8 ra].
Hypothesis ST : stk bsegs m lo (bv_unsigned sp - 16).
Hypothesis HLO : (0 <= lo <= bv_unsigned sp - 16)%Z.
Hypothesis MU : munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m0 m.
Hypothesis WM : wmono bsegs m0 m.
Hypothesis MI : mem_inv bsegs m.

Definition mz_Q : machine_state -> Prop :=
  frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m0.

Lemma mz_end : forall t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  evt bsegs mz_Q
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x920dc) fc None m (seg_rom bsegs)).
Proof.
  intros. clear ZB.
  zhide.
  do 3 zstep.
  replace (bv_unsigned sp - 16 + 16)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  pose proof FR as FR'. pose proof ST as ST'.
  release_frame FR' ST' (bv_unsigned sp).
  zstep.
  finish.
Qed.

Lemma mz_tail : forall (k : nat) q t0 t1 t2 a0 a3 a5 a6 a7 t3 t4 t5 t6,
  (beg <= q)%Z -> (q + Z.of_nat k = beg + size)%Z -> (1 <= k)%nat ->
  evt bsegs mz_Q
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) (Z_to_bv 64 q) a3
             (Z_to_bv 64 (Z.of_nat k)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x920c8) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros q t0 t1 t2 a0 a3 a5 a6 a7 t3 t4 t5 t6 H1 H2 H3; [lia|].
  pose proof (zero_read m beg size q 1 ZB H1 ltac:(lia)) as RD.
  change (repeat z8 1) with [Z_to_bv 8 0] in RD.
  zhide.
  zstep. clear RD.
  do 4 zstep.
  destruct k as [|k].
  - ifF. eapply mz_end.
  - ifT.
    replace (Z.of_nat (S (S k)) + -1)%Z with (Z.of_nat (S k)) by lia.
    eapply (IH (q + 1)%Z); lia.
Qed.

Lemma mz_t64f80 : forall t0 t1 t2 a3 a5 a6 a7 t3 t4 t5 t6,
  evt bsegs mz_Q
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 beg) (Z_to_bv 64 0)
             (Z_to_bv 64 ((beg + size) / 8 * 8)) a3 (Z_to_bv 64 (beg + size)) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x920bc) fc None m (seg_rom bsegs)).
Proof.
  intros.
  pose proof (Z.div_mod (beg + size) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (beg + size) 8 ltac:(lia)) as D2.
  zhide.
  zstep.
  destruct (Z.ltb_spec ((beg + size) / 8 * 8) beg) as [C1|C1].
  - ifT. eapply mz_end.
  - ifF. zstep.
    destruct (Z.leb_spec (beg + size) ((beg + size) / 8 * 8)) as [C2|C2].
    + ifT. eapply mz_end.
    + ifF. zstep.
      assert (E : Z_to_bv 64 (beg + size - (beg + size) / 8 * 8) =
                  Z_to_bv 64 (Z.of_nat (Z.to_nat (beg + size - (beg + size) / 8 * 8)))) by (f_equal; lia).
      rewrite E.
      eapply (mz_tail (Z.to_nat (beg + size - (beg + size) / 8 * 8)) ((beg + size) / 8 * 8)); lia.
Qed.

Lemma mz_words : forall (k : nat) q t0 t1 t2 a3 a6 a7 t3 t4 t5 t6,
  (beg <= q)%Z -> (q + 8 * Z.of_nat k = (beg + size) / 8 * 8)%Z -> (1 <= k)%nat ->
  evt bsegs mz_Q
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 beg) (Z_to_bv 64 0)
             (Z_to_bv 64 ((beg + size) / 8 * 8)) a3 (Z_to_bv 64 (beg + size)) (Z_to_bv 64 q) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x920ac) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros q t0 t1 t2 a3 a6 a7 t3 t4 t5 t6 H1 H2 H3; [lia|].
  pose proof (Z.div_mod (beg + size) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (beg + size) 8 ltac:(lia)) as D2.
  pose proof (zero_read m beg size q 8 ZB H1 ltac:(lia)) as RD.
  cbn [repeat] in RD. unfold z8 in RD.
  zhide.
  zstep. clear RD.
  do 3 zstep.
  destruct k as [|k].
  - ifF. eapply mz_t64f80.
  - ifT. eapply (IH (q + 8)%Z); lia.
Qed.

Lemma mz_t64f6c : forall t0 t1 t2 a3 a6 a7 t3 t4 t5 t6,
  evt bsegs mz_Q
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 beg) (Z_to_bv 64 0)
             (Z_to_bv 64 ((beg + size) / 8 * 8)) a3 (Z_to_bv 64 (beg + size)) (Z_to_bv 64 ((beg + 7) / 8 * 8)) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x920a8) fc None m (seg_rom bsegs)).
Proof.
  intros.
  pose proof (Z.div_mod (beg + size) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (beg + size) 8 ltac:(lia)) as D2.
  pose proof (Z.div_mod (beg + 7) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (beg + 7) 8 ltac:(lia)) as D4.
  zhide.
  zstep.
  destruct (Z.leb_spec ((beg + size) / 8 * 8) ((beg + 7) / 8 * 8)) as [C1|C1].
  - ifT. eapply mz_t64f80.
  - ifF.
    eapply (mz_words (Z.to_nat (((beg + size) / 8 - (beg + 7) / 8))) ((beg + 7) / 8 * 8)); lia.
Qed.

Lemma mz_head : forall (k : nat) p t0 t1 t2 a6 a7 t3 t4 t5 t6,
  (beg <= p)%Z -> (p < (beg + 7) / 8 * 8)%Z -> (p < beg + size)%Z ->
  (Z.of_nat k = Z.min ((beg + 7) / 8 * 8) (beg + size) - p)%Z ->
  evt bsegs mz_Q
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 beg) (Z_to_bv 64 0)
             (Z_to_bv 64 ((beg + size) / 8 * 8)) (Z_to_bv 64 (p + 1)) (Z_to_bv 64 (beg + size))
             (Z_to_bv 64 ((beg + 7) / 8 * 8)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x92090) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros p t0 t1 t2 a6 a7 t3 t4 t5 t6 H1 H2 H3 H4; [lia|].
  pose proof (zero_read m beg size p 1 ZB H1 ltac:(lia)) as RD.
  replace (Z_to_bv 64 p) with (Z_to_bv 64 (p + 1 + -1)) in RD by (f_equal; lia).
  change (repeat z8 1) with [Z_to_bv 8 0] in RD.
  zhide.
  do 2 zstep. clear RD.
  zstep. zstep.
  destruct (Z.leb_spec ((beg + 7) / 8 * 8) (p + 1)) as [C1|C1].
  - ifT. eapply mz_t64f6c.
  - ifF. zstep. zstep.
    destruct (Z.ltb_spec (p + 1) (beg + size)) as [C2|C2].
    + ifT. replace (p + 2)%Z with (p + 1 + 1)%Z by lia.
      eapply (IH (p + 1)%Z); lia.
    + ifF. eapply mz_t64f6c.
Qed.
End MZ.

Lemma memiszero_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (beg size lo : Z),
  (0 <= size <= 2^40)%Z -> (0 <= beg)%Z -> (beg + size + 8 <= 2^64)%Z ->
  bytes_at bsegs m beg (repeat z8 (Z.to_nat size)) -> (beg + size <= lo)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z ->
  mem_inv bsegs m ->
  evt bsegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 beg) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 memiszero_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros Hsz Hbeg Hend ZB HZL ST HLO MI. unfold memiszero_entry.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  apply box in ZB.
  carve_frame 16%nat ST.
  zhide.
  do 7 zstep.
  ifF.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply unbox in ZB; assert (ZB1 : bytes_at bsegs mm beg (repeat z8 (Z.to_nat size)))
      by (apply (bytes_at_transport bsegs _ m mm _ _ ZB MU); cbn [disjoint_from]; rewrite repeat_length; lia) end.
  clear ZB.
  do 5 zstep.
  rewrite !land_m8 by lia.
  replace (bv_unsigned sp + -16)%Z with (bv_unsigned sp - 16)%Z in * by lia.
  pose proof (Z.div_mod (beg + 7) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (beg + 7) 8 ltac:(lia)) as D4.
  zstep.
  destruct (Z.leb_spec ((beg + 7) / 8 * 8) beg) as [C1|C1].
  - ifT. eapply mz_t64f6c; try eassumption; lia.
  - ifF. zstep.
    destruct (Z.eqb_spec size 0) as [C2|C2].
    + ifT. eapply mz_t64f6c; try eassumption; lia.
    + ifF. do 2 zstep.
      eapply mz_head with (k := Z.to_nat (Z.min ((beg + 7) / 8 * 8) (beg + size) - beg)); try eassumption; lia.
Qed.

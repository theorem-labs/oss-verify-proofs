(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxImg FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition zbvs (n : nat) : list bval := List.map (fun j => BV (lconst 0) (Z.of_nat j)) (seq 0 n).
(* [comment removed for export] *)
Definition all_bk0 (c : tree bval) (o : Z) (n : nat) : bool :=
  forallb (fun j => match tget (okey (o + Z.of_nat j)) c with Some (BK 0) => true | _ => false end) (seq 0 n).
Definition rebz_rg (o : Z) (n : nat) (R : region) : region := RG (rg_base R) (rg_size R) (rg_kind R) (put_bytes (rg_cont R) o (zbvs n)).
Definition hx_rebz (i : nat) (o : Z) (n : nat) (S : sst) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => if (Z.leb 0 o && all_bk0 (rg_cont R) o n)%bool
              then Some (SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i (rebz_rg o n R)) (s_facts S) (s_next S) (s_resv S))
              else None
  | None => None
  end.

(* [comment removed for export] *)
Definition zero_at (k : rkind) (c : tree bval) (p : positive) : bool :=
  match tget p c with Some (BK 0) => true | None => match k with RZ => true | _ => false end | _ => false end.
Definition all_zr (R : region) (o : Z) (n : nat) : bool :=
  (forallb (fun j => zero_at (rg_kind R) (rg_cont R) (okey (o + Z.of_nat j))) (seq 0 n) &&
   match is_const (rg_size R) with Some z => Z.leb (o + Z.of_nat n) z | None => false end)%bool.
Definition hx_rebzr (i : nat) (o : Z) (n : nat) (S : sst) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => if (Z.leb 0 o && all_zr R o n)%bool
              then Some (SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i (rebz_rg o n R)) (s_facts S) (s_next S) (s_resv S))
              else None
  | None => None
  end.
(* [comment removed for export] *)
Definition reb1_rg (o c : Z) (R : region) : region := RG (rg_base R) (rg_size R) (rg_kind R) (put_bytes (rg_cont R) o [BV (lconst c) 0]).
Definition hx_reb1 (i : nat) (o : Z) (S : sst) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match tget (okey o) (rg_cont R) with
              | Some (BK c) => if (Z.leb 0 o && Z.leb 0 c && Z.ltb c 256)%bool
                               then Some (SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i (reb1_rg o c R)) (s_facts S) (s_next S) (s_resv S))
                               else None
              | _ => None
              end
  | None => None
  end.

(* [comment removed for export] *)
Definition zbks (n : nat) : list bval := List.repeat (BK 0) n.
Definition zbk_rg (o : Z) (n : nat) (R : region) : region := RG (rg_base R) (rg_size R) (rg_kind R) (put_bytes (rg_cont R) o (zbks n)).
Definition hx_zbk (i : nat) (o : Z) (n : nat) (S : sst) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => if (Z.leb 0 o && all_zr R o n)%bool
              then Some (SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i (zbk_rg o n R)) (s_facts S) (s_next S) (s_resv S))
              else None
  | None => None
  end.

(* [comment removed for export] *)
Definition kbyte (k : rkind) (c : tree bval) (p : positive) : option Z :=
  match tget p c with Some (BK b) => Some b | None => match k with RZ => Some 0 | _ => None end | _ => None end.
Fixpoint kbytes (k : rkind) (c : tree bval) (o : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match kbyte k c (okey o), kbytes k c (o + 1) n' with Some b, Some bs => Some (b :: bs) | _, _ => None end
  end.
Definition cval (bs : list Z) : Z := fold_right (fun b acc => b + 256 * acc) 0 bs.
Definition cbvs (C : Z) (n : nat) : list bval := List.map (fun j => BV (lconst C) (Z.of_nat j)) (seq 0 n).
Definition rebk_rg (o : Z) (n : nat) (C : Z) (R : region) : region := RG (rg_base R) (rg_size R) (rg_kind R) (put_bytes (rg_cont R) o (cbvs C n)).
Definition hx_rebk (i : nat) (o : Z) (n : nat) (S : sst) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match kbytes (rg_kind R) (rg_cont R) o n, is_const (rg_size R) with
              | Some bs, Some z => if (Z.leb 0 o && Nat.leb n 8 && forallb (fun b => Z.leb 0 b && Z.ltb b 256) bs && Z.leb (o + Z.of_nat n) z)%bool
                                   then Some (SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i (rebk_rg o n (cval bs) R)) (s_facts S) (s_next S) (s_resv S))
                                   else None
              | _, _ => None
              end
  | None => None
  end.

Lemma kbytes_spec : forall k c n o bs, kbytes k c o n = Some bs -> length bs = n /\
  forall j, (j < n)%nat -> kbyte k c (okey (o + Z.of_nat j)) = Some (nth j bs 0).
Proof.
  intros k c n. induction n as [|n IH]; intros o bs H; cbn [kbytes] in H.
  - injection H as <-. split; [reflexivity | intros j Hj; lia].
  - destruct (kbyte k c (okey o)) as [b|] eqn:Hb; [|discriminate]. destruct (kbytes k c (o + 1) n) as [bs'|] eqn:Hbs; [|discriminate].
    injection H as <-. destruct (IH (o + 1) bs' Hbs) as [Hl Hn]. split; [cbn; lia|].
    intros [|j] Hj.
    + rewrite Z.add_0_r. exact Hb.
    + cbn [nth]. rewrite <- (Hn j ltac:(lia)). f_equal. f_equal. lia.
Qed.
Lemma cval_nonneg : forall bs, Forall (fun b => 0 <= b < 256) bs -> 0 <= cval bs.
Proof.
  induction bs as [|b bs IH]; intros Hf; cbn [cval fold_right]; [lia|]. inversion Hf as [|? ? Hb Hf']; subst.
  fold (cval bs). specialize (IH Hf'). lia.
Qed.
Lemma cval_byte : forall bs j, Forall (fun b => 0 <= b < 256) bs -> (j < length bs)%nat ->
  Z.shiftr (cval bs) (8 * Z.of_nat j) mod 256 = nth j bs 0.
Proof.
  induction bs as [|b bs IH]; intros j Hf Hj; cbn [length] in Hj; [lia|]. inversion Hf as [|? ? Hb Hf']; subst.
  pose proof (cval_nonneg bs Hf') as Hc.
  cbn [cval fold_right]. fold (cval bs). destruct j as [|j].
  - cbn [nth]. rewrite Z.mul_0_r, Z.shiftr_0_r. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - cbn [nth]. replace (8 * Z.of_nat (S j)) with (8 + 8 * Z.of_nat j) by lia. rewrite <- Z.shiftr_shiftr by lia.
    replace (Z.shiftr (b + 256 * cval bs) 8) with (cval bs).
    + apply IH; [exact Hf' | lia].
    + rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia.
      rewrite Z.div_small by lia. lia.
Qed.
Lemma cval_bound : forall bs, Forall (fun b => 0 <= b < 256) bs -> 0 <= cval bs < 256 ^ Z.of_nat (length bs).
Proof.
  induction bs as [|b bs IH]; intros Hf; cbn [cval fold_right length]; [cbn; lia|]. inversion Hf as [|? ? Hb Hf']; subst.
  fold (cval bs). specialize (IH Hf'). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Section Reb.
Variable segs : list Segment.

#[using="Type"] Lemma rebz_rg_ok : forall E m R o n, 0 <= o -> all_bk0 (rg_cont R) o n = true -> rg_ok segs E m R -> rg_ok segs E m (rebz_rg o n R).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o n Ho Hz (H1 & H2 & H3 & H4). unfold rebz_rg. unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont]. unfold rsz in *. cbn [rg_size rg_base] in *.
  assert (Hin : forall p, (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length (zbvs n))))%bool = true ->
             tget p (rg_cont R) = Some (BK 0) /\ nth_error (zbvs n) (Z.to_nat (Zpos p - 1 - o)) = Some (BV (lconst 0) (Zpos p - 1 - o))).
  { intros p Hp. apply andb_prop in Hp as [Hp1 Hp2]. apply Z.leb_le in Hp1. apply Z.ltb_lt in Hp2.
    unfold zbvs in Hp2. rewrite length_map, length_seq in Hp2.
    unfold all_bk0 in Hz. rewrite forallb_forall in Hz. pose proof (Hz (Z.to_nat (Zpos p - 1 - o)) ltac:(apply in_seq; lia)) as X.
    replace (okey (o + Z.of_nat (Z.to_nat (Zpos p - 1 - o)))) with p in X
      by (unfold okey; rewrite Z2Nat.id by lia; replace (o + (Zpos p - 1 - o) + 1) with (Zpos p) by lia; reflexivity).
    split.
    - destruct (tget p (rg_cont R)) as [[b|l j]|]; try discriminate. destruct b as [|b|b]; try discriminate. reflexivity.
    - unfold zbvs. rewrite nth_error_map, nth_error_seq by lia. cbn [option_map Nat.add].
      rewrite (proj2 (Nat.ltb_lt _ _)) by lia. cbn [option_map]. rewrite Z2Nat.id by lia. reflexivity. }
  split; [exact H1|]. split; [exact H2|]. split.
  - intros i Hi. pose proof (H3 i Hi) as X. destruct (rg_kind R); try exact X.
    + destruct X as [X1 X2]. split; [exact X1|]. intros Hn. apply X2. rewrite put_bytes_spec in Hn by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length (zbvs n))))%bool eqn:Hp.
      * destruct (Hin _ Hp) as (_ & Y). rewrite Y in Hn. discriminate.
      * exact Hn.
    + destruct X as [X1 X2]. split; [exact X1|]. intros Hn. apply X2. rewrite put_bytes_spec in Hn by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length (zbvs n))))%bool eqn:Hp.
      * destruct (Hin _ Hp) as (_ & Y). rewrite Y in Hn. discriminate.
      * exact Hn.
  - intros p v Hp. rewrite put_bytes_spec in Hp by exact Ho.
    destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length (zbvs n))))%bool eqn:Hq.
    + destruct (Hin _ Hq) as (Y1 & Y2). rewrite Y2 in Hp. injection Hp as <-.
      destruct (H4 p _ Y1) as (Z1 & Z2). split; [exact Z1|]. rewrite Z2. cbn [bden]. rewrite lden_lconst.
      f_equal. rewrite u_Z_to_bv. unfold bv_wrap. change (bv_modulus 64) with two64. rewrite Z.mod_0_l by (unfold two64; lia).
      rewrite Z.shiftr_0_l. reflexivity.
    + exact (H4 p v Hp).
Qed.


#[using="Type"] Lemma rebzr_rg_ok : forall E m R o n, 0 <= o -> all_zr R o n = true -> rg_ok segs E m R -> rg_ok segs E m (rebz_rg o n R).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o n Ho Hz HR. pose proof HR as (H1 & H2 & H3 & H4). unfold rebz_rg. unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont]. unfold rsz in *. cbn [rg_size rg_base] in *.
  unfold all_zr in Hz. apply andb_prop in Hz as [Hz Hsz].
  destruct (is_const (rg_size R)) as [z|] eqn:Hzc; [|discriminate]. apply Z.leb_le in Hsz.
  assert (Hrz : bv_unsigned (lden E (rg_size R)) = z).
  { exact (is_const_u E (rg_size R) z Hzc). }
  assert (Hin : forall p, (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length (zbvs n))))%bool = true ->
             zero_at (rg_kind R) (rg_cont R) p = true /\ nth_error (zbvs n) (Z.to_nat (Zpos p - 1 - o)) = Some (BV (lconst 0) (Zpos p - 1 - o)) /\
             Zpos p - 1 < z).
  { intros p Hp. apply andb_prop in Hp as [Hp1 Hp2]. apply Z.leb_le in Hp1. apply Z.ltb_lt in Hp2.
    unfold zbvs in Hp2. rewrite length_map, length_seq in Hp2.
    rewrite forallb_forall in Hz. pose proof (Hz (Z.to_nat (Zpos p - 1 - o)) ltac:(apply in_seq; lia)) as X.
    replace (okey (o + Z.of_nat (Z.to_nat (Zpos p - 1 - o)))) with p in X
      by (unfold okey; rewrite Z2Nat.id by lia; replace (o + (Zpos p - 1 - o) + 1) with (Zpos p) by lia; reflexivity).
    split; [exact X|]. split; [|lia].
    unfold zbvs. rewrite nth_error_map, nth_error_seq by lia. cbn [option_map Nat.add].
    rewrite (proj2 (Nat.ltb_lt _ _)) by lia. cbn [option_map]. rewrite Z2Nat.id by lia. reflexivity. }
  split; [exact H1|]. split; [exact H2|]. split.
  - intros i Hi. pose proof (H3 i Hi) as X. destruct (rg_kind R); try exact X.
    + destruct X as [X1 X2]. split; [exact X1|]. intros Hn. apply X2. rewrite put_bytes_spec in Hn by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length (zbvs n))))%bool eqn:Hp.
      * destruct (Hin _ Hp) as (_ & Y & _). rewrite Y in Hn. discriminate.
      * exact Hn.
    + destruct X as [X1 X2]. split; [exact X1|]. intros Hn. apply X2. rewrite put_bytes_spec in Hn by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length (zbvs n))))%bool eqn:Hp.
      * destruct (Hin _ Hp) as (_ & Y & _). rewrite Y in Hn. discriminate.
      * exact Hn.
  - intros p v Hp. rewrite put_bytes_spec in Hp by exact Ho.
    destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length (zbvs n))))%bool eqn:Hq.
    + destruct (Hin _ Hq) as (Y1 & Y2 & Y3). rewrite Y2 in Hp. injection Hp as <-.
      assert (Hbv : bden E (BV (lconst 0) (Zpos p - 1 - o)) = Z_to_bv 8 0).
      { cbn [bden]. rewrite lden_lconst. f_equal. rewrite u_Z_to_bv. unfold bv_wrap. change (bv_modulus 64) with two64.
        rewrite Z.mod_0_l by (unfold two64; lia). rewrite Z.shiftr_0_l. reflexivity. }
      rewrite Hbv. split; [rewrite Hrz; exact Y3|].
      unfold zero_at in Y1. destruct (tget p (rg_cont R)) as [[b|l j]|] eqn:Ht.
      * destruct b as [|b|b]; try discriminate. destruct (H4 p _ Ht) as (_ & Z2). rewrite Z2. cbn [bden]. reflexivity.
      * discriminate.
      * destruct (rg_kind R) eqn:Hk; try discriminate.
        pose proof (H3 (Zpos p - 1) ltac:(rewrite Hrz; lia)) as X. destruct X as [_ X2].
        replace (okey (Zpos p - 1)) with p in X2 by (unfold okey; replace (Zpos p - 1 + 1) with (Zpos p) by lia; reflexivity).
        exact (X2 Ht).
    + exact (H4 p v Hp).
Qed.
#[using="Type"] Lemma zbk_rg_ok : forall E m R o n, 0 <= o -> all_zr R o n = true -> rg_ok segs E m R -> rg_ok segs E m (zbk_rg o n R).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o n Ho Hz HR. pose proof HR as (H1 & H2 & H3 & H4). unfold zbk_rg. unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont]. unfold rsz in *. cbn [rg_size rg_base] in *.
  unfold all_zr in Hz. apply andb_prop in Hz as [Hz Hsz].
  destruct (is_const (rg_size R)) as [z|] eqn:Hzc; [|discriminate]. apply Z.leb_le in Hsz.
  assert (Hrz : bv_unsigned (lden E (rg_size R)) = z).
  { exact (is_const_u E (rg_size R) z Hzc). }
  assert (Hin : forall p, (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length (zbks n))))%bool = true ->
             zero_at (rg_kind R) (rg_cont R) p = true /\ nth_error (zbks n) (Z.to_nat (Zpos p - 1 - o)) = Some (BK 0) /\
             Zpos p - 1 < z).
  { intros p Hp. apply andb_prop in Hp as [Hp1 Hp2]. apply Z.leb_le in Hp1. apply Z.ltb_lt in Hp2.
    unfold zbks in Hp2. rewrite repeat_length in Hp2.
    rewrite forallb_forall in Hz. pose proof (Hz (Z.to_nat (Zpos p - 1 - o)) ltac:(apply in_seq; lia)) as X.
    replace (okey (o + Z.of_nat (Z.to_nat (Zpos p - 1 - o)))) with p in X
      by (unfold okey; rewrite Z2Nat.id by lia; replace (o + (Zpos p - 1 - o) + 1) with (Zpos p) by lia; reflexivity).
    split; [exact X|]. split; [|lia].
    unfold zbks. apply nth_error_repeat. lia. }
  split; [exact H1|]. split; [exact H2|]. split.
  - intros i Hi. pose proof (H3 i Hi) as X. destruct (rg_kind R); try exact X.
    + destruct X as [X1 X2]. split; [exact X1|]. intros Hn. apply X2. rewrite put_bytes_spec in Hn by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length (zbks n))))%bool eqn:Hp.
      * destruct (Hin _ Hp) as (_ & Y & _). rewrite Y in Hn. discriminate.
      * exact Hn.
    + destruct X as [X1 X2]. split; [exact X1|]. intros Hn. apply X2. rewrite put_bytes_spec in Hn by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length (zbks n))))%bool eqn:Hp.
      * destruct (Hin _ Hp) as (_ & Y & _). rewrite Y in Hn. discriminate.
      * exact Hn.
  - intros p v Hp. rewrite put_bytes_spec in Hp by exact Ho.
    destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length (zbks n))))%bool eqn:Hq.
    + destruct (Hin _ Hq) as (Y1 & Y2 & Y3). rewrite Y2 in Hp. injection Hp as <-.
      assert (Hbv : bden E (BK 0) = Z_to_bv 8 0) by reflexivity.
      rewrite Hbv. split; [rewrite Hrz; exact Y3|].
      unfold zero_at in Y1. destruct (tget p (rg_cont R)) as [[b|l j]|] eqn:Ht.
      * destruct b as [|b|b]; try discriminate. destruct (H4 p _ Ht) as (_ & Z2). rewrite Z2. cbn [bden]. reflexivity.
      * discriminate.
      * destruct (rg_kind R) eqn:Hk; try discriminate.
        pose proof (H3 (Zpos p - 1) ltac:(rewrite Hrz; lia)) as X. destruct X as [_ X2].
        replace (okey (Zpos p - 1)) with p in X2 by (unfold okey; replace (Zpos p - 1 + 1) with (Zpos p) by lia; reflexivity).
        exact (X2 Ht).
    + exact (H4 p v Hp).
Qed.

#[using="Type"] Lemma reb1_rg_ok : forall E m R o c, 0 <= o -> 0 <= c < 256 -> tget (okey o) (rg_cont R) = Some (BK c) -> rg_ok segs E m R -> rg_ok segs E m (reb1_rg o c R).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o c Ho Hc Ht HR. pose proof HR as (H1 & H2 & H3 & H4). unfold reb1_rg. unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont]. unfold rsz in *. cbn [rg_size rg_base] in *.
  assert (Hin : forall p, (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length [BV (lconst c) 0])))%bool = true -> p = okey o).
  { intros p Hp. apply andb_prop in Hp as [Hp1 Hp2]. apply Z.leb_le in Hp1. apply Z.ltb_lt in Hp2. cbn [length] in Hp2.
    unfold okey. apply Pos2Z.inj. rewrite Z2Pos.id by lia. lia. }
  split; [exact H1|]. split; [exact H2|]. split.
  - intros i Hi. pose proof (H3 i Hi) as X. destruct (rg_kind R); try exact X.
    + destruct X as [X1 X2]. split; [exact X1|]. intros Hn. apply X2. rewrite put_bytes_spec in Hn by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length [BV (lconst c) 0])))%bool eqn:Hp.
      * assert (E0 : Zpos (okey i) - 1 - o = 0) by (apply andb_prop in Hp as [P1 P2]; apply Z.leb_le in P1; apply Z.ltb_lt in P2; cbn [length] in P2; lia).
        rewrite E0 in Hn. cbn in Hn. discriminate.
      * exact Hn.
    + destruct X as [X1 X2]. split; [exact X1|]. intros Hn. apply X2. rewrite put_bytes_spec in Hn by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length [BV (lconst c) 0])))%bool eqn:Hp.
      * assert (E0 : Zpos (okey i) - 1 - o = 0) by (apply andb_prop in Hp as [P1 P2]; apply Z.leb_le in P1; apply Z.ltb_lt in P2; cbn [length] in P2; lia).
        rewrite E0 in Hn. cbn in Hn. discriminate.
      * exact Hn.
  - intros p v Hp. rewrite put_bytes_spec in Hp by exact Ho.
    destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length [BV (lconst c) 0])))%bool eqn:Hq.
    + assert (E0 : Zpos p - 1 - o = 0) by (apply andb_prop in Hq as [P1 P2]; apply Z.leb_le in P1; apply Z.ltb_lt in P2; cbn [length] in P2; lia).
      pose proof (Hin _ Hq) as E1. rewrite E0 in Hp. cbn in Hp. injection Hp as <-. rewrite E1.
      destruct (H4 _ _ Ht) as (Z1 & Z2). split; [exact Z1|]. rewrite Z2. cbn [bden]. rewrite lden_lconst. f_equal.
      rewrite u_Z_to_bv. unfold bv_wrap. change (bv_modulus 64) with two64. rewrite Z.shiftr_0_r. rewrite Z.mod_small by (unfold two64; lia). reflexivity.
    + exact (H4 p v Hp).
Qed.
#[using="Type"] Lemma shape_upd_rg : forall rgs i R R', nth_error rgs i = Some R -> rg_base R' = rg_base R -> rg_size R' = rg_size R -> shape (upd_nth rgs i R') = shape rgs.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction rgs as [|R0 rs IH]; intros [|i] R R' Hn Hb Hs; cbn in *; try discriminate.
  - injection Hn as <-. rewrite Hb, Hs. reflexivity.
  - f_equal. exact (IH i R R' Hn Hb Hs).
Qed.

#[using="Type"] Lemma rebk_rg_ok : forall E m R o n bs z, 0 <= o -> (n <= 8)%nat -> kbytes (rg_kind R) (rg_cont R) o n = Some bs ->
  Forall (fun b => 0 <= b < 256) bs -> is_const (rg_size R) = Some z -> o + Z.of_nat n <= z ->
  rg_ok segs E m R -> rg_ok segs E m (rebk_rg o n (cval bs) R).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o n bs z Ho Hn8 Hk Hbs Hzc Hsz HR. pose proof HR as (H1 & H2 & H3 & H4). unfold rebk_rg. unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont]. unfold rsz in *. cbn [rg_size rg_base] in *.
  assert (Hrz : bv_unsigned (lden E (rg_size R)) = z) by exact (is_const_u E (rg_size R) z Hzc).
  destruct (kbytes_spec _ _ _ _ _ Hk) as [Hlen Hkb].
  assert (Hlc : length (cbvs (cval bs) n) = n) by (unfold cbvs; rewrite length_map, length_seq; reflexivity).
  assert (Hin : forall p, (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length (cbvs (cval bs) n))))%bool = true ->
             kbyte (rg_kind R) (rg_cont R) p = Some (nth (Z.to_nat (Zpos p - 1 - o)) bs 0) /\
             nth_error (cbvs (cval bs) n) (Z.to_nat (Zpos p - 1 - o)) = Some (BV (lconst (cval bs)) (Zpos p - 1 - o)) /\
             Zpos p - 1 < z /\ (Z.to_nat (Zpos p - 1 - o) < n)%nat).
  { intros p Hp. apply andb_prop in Hp as [Hp1 Hp2]. apply Z.leb_le in Hp1. apply Z.ltb_lt in Hp2. rewrite Hlc in Hp2.
    pose proof (Hkb (Z.to_nat (Zpos p - 1 - o)) ltac:(lia)) as X.
    replace (okey (o + Z.of_nat (Z.to_nat (Zpos p - 1 - o)))) with p in X
      by (unfold okey; rewrite Z2Nat.id by lia; replace (o + (Zpos p - 1 - o) + 1) with (Zpos p) by lia; reflexivity).
    split; [exact X|]. split; [|split; lia].
    unfold cbvs. rewrite nth_error_map, nth_error_seq by lia. cbn [option_map Nat.add].
    rewrite (proj2 (Nat.ltb_lt _ _)) by lia. cbn [option_map]. rewrite Z2Nat.id by lia. reflexivity. }
  split; [exact H1|]. split; [exact H2|]. split.
  - intros i Hi. pose proof (H3 i Hi) as X. destruct (rg_kind R); try exact X.
    + destruct X as [X1 X2]. split; [exact X1|]. intros Hnone. apply X2. rewrite put_bytes_spec in Hnone by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length (cbvs (cval bs) n))))%bool eqn:Hp.
      * destruct (Hin _ Hp) as (_ & Y & _). rewrite Y in Hnone. discriminate.
      * exact Hnone.
    + destruct X as [X1 X2]. split; [exact X1|]. intros Hnone. apply X2. rewrite put_bytes_spec in Hnone by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length (cbvs (cval bs) n))))%bool eqn:Hp.
      * destruct (Hin _ Hp) as (_ & Y & _). rewrite Y in Hnone. discriminate.
      * exact Hnone.
  - intros p v Hp. rewrite put_bytes_spec in Hp by exact Ho.
    destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length (cbvs (cval bs) n))))%bool eqn:Hq.
    + destruct (Hin _ Hq) as (Y1 & Y2 & Y3 & Y4). rewrite Y2 in Hp. injection Hp as <-.
      assert (HCb : 0 <= cval bs < two64).
      { pose proof (cval_bound bs Hbs) as X. rewrite Hlen in X. split; [lia|].
        assert (256 ^ Z.of_nat n <= 256 ^ 8) by (apply Z.pow_le_mono_r; lia). unfold two64. change (256 ^ 8) with 18446744073709551616 in H. lia. }
      assert (Hbv : bden E (BV (lconst (cval bs)) (Zpos p - 1 - o)) = Z_to_bv 8 (nth (Z.to_nat (Zpos p - 1 - o)) bs 0)).
      { cbn [bden]. rewrite lden_lconst. apply bv_eq. rewrite !Z_to_bv_unsigned.
        unfold bv_wrap. change (bv_modulus 64) with two64. change (bv_modulus 8) with 256.
        rewrite (Z.mod_small (cval bs)) by exact HCb.
        pose proof (cval_byte bs (Z.to_nat (Zpos p - 1 - o)) Hbs ltac:(lia)) as CB. rewrite Z2Nat.id in CB by lia. rewrite CB.
        assert (Hnb : 0 <= nth (Z.to_nat (Zpos p - 1 - o)) bs 0 < 256).
        { rewrite Forall_forall in Hbs. apply Hbs. apply nth_In. lia. }
        symmetry. apply Z.mod_small. exact Hnb. }
      rewrite Hbv. split; [rewrite Hrz; exact Y3|].
      unfold kbyte in Y1. destruct (tget p (rg_cont R)) as [[b|l j]|] eqn:Ht.
      * injection Y1 as Eb. destruct (H4 p _ Ht) as (_ & Z2). rewrite Z2. cbn [bden]. rewrite Eb. reflexivity.
      * discriminate.
      * destruct (rg_kind R) eqn:Hk0; try discriminate. injection Y1 as Eb. rewrite <- Eb.
        pose proof (H3 (Zpos p - 1) ltac:(rewrite Hrz; lia)) as X. destruct X as [_ X2].
        replace (okey (Zpos p - 1)) with p in X2 by (unfold okey; replace (Zpos p - 1 + 1) with (Zpos p) by lia; reflexivity).
        exact (X2 Ht).
    + exact (H4 p v Hp).
Qed.

#[using="Type"] Lemma upd_nth_forall : forall (P : region -> Prop) rgs i R R', nth_error rgs i = Some R -> P R' -> Forall P rgs -> Forall P (upd_nth rgs i R').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros P rgs. induction rgs as [|R0 rs IH]; intros [|i] R R' Hn HP HF; cbn in *; try discriminate.
  - injection Hn as <-. inversion HF; subst. constructor; assumption.
  - inversion HF; subst. constructor; [assumption | exact (IH i R R' Hn HP H2)].
Qed.
#[using="Type"] Lemma shape_upd_rebz : forall rgs i R o n, nth_error rgs i = Some R -> shape (upd_nth rgs i (rebz_rg o n R)) = shape rgs.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction rgs as [|R0 rs IH]; intros [|i] R o n Hn; cbn in *; try discriminate.
  - injection Hn as <-. reflexivity.
  - f_equal. exact (IH i R o n Hn).
Qed.
End Reb.

Section RebRule.
Variable segs : list Segment.
Definition hcall_rule0 (S K : sst) : Prop :=
  forall E ms, sden segs E S ms ->
  exists ms'' E'', isteps segs ms ms'' /\ sden segs E'' K ms'' /\ agree (s_next S) E E'' /\
    (forall x, fr_pt E (s_rgs S) x -> ms_mem ms'' x = ms_mem ms x).

#[using="Type"] Theorem hx_rebz_ok : forall i o n S K, hx_rebz i o n S = Some K ->
  hcall_rule0 S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i o n S K H. unfold hx_rebz in H.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hn; [|discriminate].
  destruct (Z.leb 0 o && all_bk0 (rg_cont R) o n)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Ho Hz]. apply Z.leb_le in Ho.
  split; [|split; [cbn [s_next]; apply Pos.le_refl | cbn [s_rgs]; exact (shape_upd_rebz _ i R o n Hn)]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj _ (conj _ (conj HF0 Hfrm0))))))).
  - apply (upd_nth_forall (rg_ok segs E' (ms_mem ms)) (s_rgs S) i R (rebz_rg o n R) Hn); [|exact HG0].
    rewrite Forall_forall in HG0. apply (rebz_rg_ok segs E' (ms_mem ms) R o n Ho Hz). apply HG0. exact (nth_error_In _ _ Hn).
  - exact (rgs_disj_upd E' (s_rgs S) i (rebz_rg o n R) R Hn eq_refl eq_refl HD0).
Qed.

#[using="Type"] Theorem hx_rebzr_ok : forall i o n S K, hx_rebzr i o n S = Some K ->
  hcall_rule0 S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i o n S K H. unfold hx_rebzr in H.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hn; [|discriminate].
  destruct (Z.leb 0 o && all_zr R o n)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Ho Hz]. apply Z.leb_le in Ho.
  split; [|split; [cbn [s_next]; apply Pos.le_refl | cbn [s_rgs]; exact (shape_upd_rebz _ i R o n Hn)]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj _ (conj _ (conj HF0 Hfrm0))))))).
  - apply (upd_nth_forall (rg_ok segs E' (ms_mem ms)) (s_rgs S) i R (rebz_rg o n R) Hn); [|exact HG0].
    rewrite Forall_forall in HG0. apply (rebzr_rg_ok segs E' (ms_mem ms) R o n Ho Hz). apply HG0. exact (nth_error_In _ _ Hn).
  - exact (rgs_disj_upd E' (s_rgs S) i (rebz_rg o n R) R Hn eq_refl eq_refl HD0).
Qed.
#[using="Type"] Theorem hx_zbk_ok : forall i o n S K, hx_zbk i o n S = Some K ->
  hcall_rule0 S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i o n S K H. unfold hx_zbk in H.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hn; [|discriminate].
  destruct (Z.leb 0 o && all_zr R o n)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Ho Hz]. apply Z.leb_le in Ho.
  split; [|split; [cbn [s_next]; apply Pos.le_refl | cbn [s_rgs]; exact (shape_upd_rg _ i R (zbk_rg o n R) Hn eq_refl eq_refl)]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj _ (conj _ (conj HF0 Hfrm0))))))).
  - apply (upd_nth_forall (rg_ok segs E' (ms_mem ms)) (s_rgs S) i R (zbk_rg o n R) Hn); [|exact HG0].
    rewrite Forall_forall in HG0. apply (zbk_rg_ok segs E' (ms_mem ms) R o n Ho Hz). apply HG0. exact (nth_error_In _ _ Hn).
  - exact (rgs_disj_upd E' (s_rgs S) i (zbk_rg o n R) R Hn eq_refl eq_refl HD0).
Qed.
#[using="Type"] Theorem hx_reb1_ok : forall i o S K, hx_reb1 i o S = Some K ->
  hcall_rule0 S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i o S K H. unfold hx_reb1 in H.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hn; [|discriminate].
  destruct (tget (okey o) (rg_cont R)) as [[[|c|c]|l j]|] eqn:Ht; try discriminate.
  - destruct (Z.leb 0 o && Z.leb 0 0 && Z.ltb 0 256)%bool eqn:Hc; [|discriminate]. injection H as <-.
    apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Ho _]. apply Z.leb_le in Ho.
    split; [|split; [cbn [s_next]; apply Pos.le_refl | cbn [s_rgs]; exact (shape_upd_rg _ i R (reb1_rg o _ R) Hn eq_refl eq_refl)]].
    intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
    intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
    unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
    refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj _ (conj _ (conj HF0 Hfrm0))))))).
    + apply (upd_nth_forall (rg_ok segs E' (ms_mem ms)) (s_rgs S) i R (reb1_rg o 0 R) Hn); [|exact HG0].
      rewrite Forall_forall in HG0. apply (reb1_rg_ok segs E' (ms_mem ms) R o 0 Ho ltac:(lia) Ht). apply HG0. exact (nth_error_In _ _ Hn).
    + exact (rgs_disj_upd E' (s_rgs S) i (reb1_rg o 0 R) R Hn eq_refl eq_refl HD0).
  - destruct (Z.leb 0 o && Z.leb 0 (Zpos c) && Z.ltb (Zpos c) 256)%bool eqn:Hc; [|discriminate]. injection H as <-.
    apply andb_prop in Hc as [Hc Hc3]. apply andb_prop in Hc as [Ho Hc2]. apply Z.leb_le in Ho. apply Z.leb_le in Hc2. apply Z.ltb_lt in Hc3.
    split; [|split; [cbn [s_next]; apply Pos.le_refl | cbn [s_rgs]; exact (shape_upd_rg _ i R (reb1_rg o _ R) Hn eq_refl eq_refl)]].
    intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
    intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
    unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
    refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj _ (conj _ (conj HF0 Hfrm0))))))).
    + apply (upd_nth_forall (rg_ok segs E' (ms_mem ms)) (s_rgs S) i R (reb1_rg o (Zpos c) R) Hn); [|exact HG0].
      rewrite Forall_forall in HG0. apply (reb1_rg_ok segs E' (ms_mem ms) R o (Zpos c) Ho ltac:(lia) Ht). apply HG0. exact (nth_error_In _ _ Hn).
    + exact (rgs_disj_upd E' (s_rgs S) i (reb1_rg o (Zpos c) R) R Hn eq_refl eq_refl HD0).
  - exfalso. destruct (Z.leb 0 o); cbn in H; discriminate.
Qed.

#[using="Type"] Theorem hx_rebk_ok : forall i o n S K, hx_rebk i o n S = Some K ->
  hcall_rule0 S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i o n S K H. unfold hx_rebk in H.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hn; [|discriminate].
  destruct (kbytes (rg_kind R) (rg_cont R) o n) as [bs|] eqn:Hk; [|discriminate].
  destruct (is_const (rg_size R)) as [z|] eqn:Hzc; [|discriminate].
  destruct (Z.leb 0 o && Nat.leb n 8 && forallb (fun b => Z.leb 0 b && Z.ltb b 256) bs && Z.leb (o + Z.of_nat n) z)%bool eqn:Hc; [|discriminate].
  injection H as <-.
  apply andb_prop in Hc as [Hc Hsz]. apply andb_prop in Hc as [Hc Hbs]. apply andb_prop in Hc as [Ho Hn8].
  apply Z.leb_le in Ho. apply Nat.leb_le in Hn8. apply Z.leb_le in Hsz.
  assert (Hbs' : Forall (fun b => 0 <= b < 256) bs).
  { apply Forall_forall. intros b Hb. rewrite forallb_forall in Hbs. specialize (Hbs b Hb). apply andb_prop in Hbs as [X1 X2].
    apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia. }
  split; [|split; [cbn [s_next]; apply Pos.le_refl | cbn [s_rgs]; exact (shape_upd_rg _ i R (rebk_rg o n (cval bs) R) Hn eq_refl eq_refl)]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj _ (conj _ (conj HF0 Hfrm0))))))).
  - apply (upd_nth_forall (rg_ok segs E' (ms_mem ms)) (s_rgs S) i R (rebk_rg o n (cval bs) R) Hn); [|exact HG0].
    rewrite Forall_forall in HG0. apply (rebk_rg_ok segs E' (ms_mem ms) R o n bs z Ho Hn8 Hk Hbs' Hzc Hsz). apply HG0. exact (nth_error_In _ _ Hn).
  - exact (rgs_disj_upd E' (s_rgs S) i (rebk_rg o n (cval bs) R) R Hn eq_refl eq_refl HD0).
Qed.
End RebRule.

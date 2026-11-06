(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ms_eq_tac ::=
  cbv beta delta [mkR];
  repeat first [ reflexivity
               | lazymatch goal with |- @eq (bv _) _ _ => ms_leaf_eq end
               | progress f_equal ].

Notation BSEGS := AsanUbsan.M.loaded_segments.
Definition EXPMAX : Z := 2684354569.

Lemma slit64 : forall z, (- 2 ^ 63 <= z < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63)%Z. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite Z.add_mod_idemp_l by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma mulh10_small : forall t : Z, (0 <= t <= 268435455)%Z -> v_mulh (Z_to_bv 64 t) (Z_to_bv 64 10) = Z_to_bv 64 0.
Proof.
  intros t Ht. unfold v_mulh. rewrite !slit64 by lia. f_equal. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia.
Qed.
Lemma srai63_small : forall t : Z, (0 <= t < 2 ^ 63)%Z -> v_srai (Z_to_bv 64 t) 63 = Z_to_bv 64 0.
Proof.
  intros t Ht. unfold v_srai. rewrite slit64 by lia. f_equal. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia.
Qed.

Lemma mulh10_form : forall e, (0 <= e <= 268435455)%Z -> Z.shiftr (bv_signed (Z_to_bv 64 e) * 10) 64 = 0%Z.
Proof. intros e He. rewrite slit64 by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
Lemma sra63_form : forall t, (0 <= t < 2 ^ 63)%Z -> Z.shiftr (bv_signed (Z_to_bv 64 t)) 63 = 0%Z.
Proof. intros t Ht. rewrite slit64 by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Section EXP.
  Variables (x1 x2 x3 x4 x5 x6 x8 x9 x10 x12 x13 x15 x18 x20 x21 x24 x26 x27 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (T Y0 Y1 : Z).
  #[local] Notation L := (Z.of_nat (length bs)).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  Hypothesis TXT : bytes_at BSEGS m T bs.
  Hypothesis HL : (1 <= L <= 128)%Z.
  Hypothesis HT : (6537216 <= T <= 140737488355072)%Z.
  Hypothesis SHT : shz BSEGS m (ASAN_B + Y0) (Y1 - Y0).
  Hypothesis HY : (8 * Y0 <= T /\ T + L <= 8 * Y1)%Z.

  #[local] Notation EST pc x7 x11 x14 x17 x23 x25 x28 x29 x30 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Zw 9) x17 x18 (Zw ASAN_B) x20 x21 (Zw (T + L)) x23 x24 x25 x26 x27
             x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom BSEGS)) (only parsing).

  Definition exp_post : machine_state -> Prop := fun ms' =>
    exists y7 y11 y14 y17 y23 y25 y28 y29 y30 : word,
      ((ms' = EST 0x94614 y7 y11 y14 y17 y23 y25 y28 y29 y30 /\ bv_unsigned y25 < T + L)%Z \/
       (ms' = EST 0x9461c y7 y11 y14 y17 y23 y25 y28 y29 y30 /\ bv_unsigned y25 = T + L)%Z) /\
      (0 <= bv_unsigned y7 <= EXPMAX)%Z /\ (T <= bv_unsigned y25 <= T + L)%Z.

  #[using="HY"] Lemma tx_gran : forall A, (T <= A < T + L)%Z -> (ASAN_B + Y0 <= A / 8 + ASAN_B)%Z /\ (A / 8 + ASAN_B + 1 <= ASAN_B + Y0 + (Y1 - Y0))%Z.
  Proof. LiaFast.lf_pins (fun (HY : LiaFast.U) => LiaFast.u0). intros A HA. destruct HY as [Y1a Y2a]. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY"] Lemma loopE : forall (n : nat) (k e : Z) (x14 x17 x23 : word),
      (L - k <= Z.of_nat n)%Z -> (0 <= k < L)%Z -> (0 <= e <= EXPMAX)%Z ->
      evt BSEGS exp_post (EST 0x937a8 (Zw e) (Zw (T + k)) x14 x17 x23 (Zw (T + k)) (Zw 10) (Zw 268435455) (Zw 2)).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros k e x14 x17 x23 Hn HK He; [exfalso; lia|].
    pose proof (shz_bound _ _ _ _ SHT) as BT.
    pose proof (tx_gran (T + k) ltac:(lia)) as G0.
    unfold EXPMAX in *.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT k RD. pose proof (tx_range bs k) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs k.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd.
    - cond_cleanup Hd. clear Hd. apply evt_done.
      do 9 eexists. split; [left; split; [reflexivity | rewrite unsigned_lit by lia; lia]|].
      rewrite !unsigned_lit by lia. unfold EXPMAX; split; lia.
    - cond_cleanup Hd. pose proof (dig_yes_m _ Rk Hd) as D. clear Hd. unfold isdig in D.
      step. (* [comment removed for export] *)
      if_cases Hs.
      + (* [comment removed for export] *)
        cond_cleanup Hs. try rewrite !slit64 in Hs by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hu; [| cond_cleanup Hu; exfalso; lia]. cond_cleanup Hu.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hmore.
        * cond_cleanup Hmore. goto (eapply (IH (k + 1)%Z e)); [lia | lia | lia].
        * cond_cleanup Hmore. step. (* [comment removed for export] *)
          apply evt_done. do 9 eexists. split; [right; split; [reflexivity | rewrite unsigned_lit by lia; lia]|].
          rewrite !unsigned_lit by lia. unfold EXPMAX; split; lia.
      + cond_cleanup Hs. try rewrite !slit64 in Hs by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite (mulh10_form e) by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite ?(unsigned_lit e) by lia. rewrite (sra63_form (e * 10)%Z) by lia.
        assert (A7 : Z.land (bv_unsigned (Z_to_bv 64 (tx bs k + -48))) 255 = (tx bs k - 48)%Z).
        { rewrite unsigned_lit by lia. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
        rewrite A7.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hu; [| cond_cleanup Hu; exfalso; lia]. cond_cleanup Hu.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hmore.
        * cond_cleanup Hmore. goto (eapply (IH (k + 1)%Z (e * 10 + (tx bs k - 48))%Z)); [lia | lia | lia].
        * cond_cleanup Hmore. step. (* [comment removed for export] *)
          apply evt_done. do 9 eexists. split; [right; split; [reflexivity | rewrite unsigned_lit by lia; lia]|].
          rewrite !unsigned_lit by lia. unfold EXPMAX; split; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY"] Lemma blockE : forall (k : Z) (x7 x11 x14 x17 x23 x28 x29 x30 : word),
      (0 <= k < L)%Z -> evt BSEGS exp_post (EST 0x93790 x7 x11 x14 x17 x23 (Zw (T + k)) x28 x29 x30).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY : LiaFast.U) => LiaFast.u0).
    intros k x7 x11 x14 x17 x23 x28 x29 x30 HK.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    goto (eapply (loopE (Datatypes.S (Z.to_nat (L - k))) k 0)); [lia | lia | unfold EXPMAX; lia].
  Qed.
End EXP.

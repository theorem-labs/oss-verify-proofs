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
From OSSVerify.fast_float.from_chars.images Require Import Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ms_eq_tac ::=
  cbv beta delta [mkR];
  repeat first [ reflexivity
               | lazymatch goal with |- @eq (bv _) _ _ => ms_leaf_eq end
               | progress f_equal ].

Notation ASEGS := Asan.M.loaded_segments.

Definition C19 : Z := 999999999999999999.

Lemma seqz_m48 : forall t, (0 <= t < 256)%Z -> t <> 48%Z -> v_sltiu (Z_to_bv 64 (t + -48)) 1 = Z_to_bv 64 0.
Proof.
  intros t Ht Hne. rewrite v_sltiu_b2z. rewrite unsigned_lit_wrap.
  replace (bv_wrap 64 1) with 1%Z by reflexivity.
  destruct (Z.ltb_spec0 ((t + -48) mod 2^64) 1) as [Hl|Hl]; [|reflexivity].
  exfalso. destruct (Z_lt_le_dec t 48).
  - rewrite <- (Z.mod_add _ 1) in Hl by lia. rewrite Z.mod_small in Hl by lia. lia.
  - rewrite Z.mod_small in Hl by lia. lia.
Qed.

Section TMF.
  Variables (x2 x3 x4 x6 x8 x9 x17 x18 x20 x21 x25 x26 x27 x29 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte).
  Variables (T S IE fp fL Y0 Y1 T3 : Z).
  #[local] Notation L := (Z.of_nat (length bs)).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  #[local] Notation k3 := (S - T)%Z.
  #[local] Notation kI := (IE - T)%Z.
  Hypothesis TXT : bytes_at ASEGS m T bs.
  Hypothesis HL : (1 <= L <= 128)%Z.
  Hypothesis HT : (6529024 <= T <= 140737488355072)%Z.
  Hypothesis SHT : shz ASEGS m (ASAN_B + Y0) (Y1 - Y0).
  Hypothesis HY : (8 * Y0 <= T /\ T + L <= 8 * Y1)%Z.
  Hypothesis HS : (T <= S <= IE /\ IE <= T + L)%Z.
  Hypothesis DGI : digs bs k3 kI.
  Hypothesis FL0 : (0 <= fL <= 128)%Z.
  Hypothesis SPANS : ((fp = 0 /\ fL = 0) \/
                      (fp = IE + 1 /\ IE < T + L /\ tx bs kI = 46 /\ IE + 1 + fL <= T + L /\ digs bs (kI + 1) (kI + 1 + fL)))%Z.
  Hypothesis HFP0 : (0 <= fp < 2 ^ 64)%Z.
  Hypothesis HT3 : (T3 mod 256 = 46 /\ 0 <= T3 < 2 ^ 64)%Z.
  Hypothesis PR : pristine m 65536 188416.   (* [comment removed for export] *)

  #[local] Notation EST4 pc x5 x7 x10 x11 x13 x14 x15 x16 x28 y29 x30 :=
    (MS (mkR (Zw fp) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Zw fL) x13 x14 x15 x16 x17 x18 (Zw ASAN_B) x20 x21
             (Zw S) (Zw (T + L)) (Zw T3) x25 x26 x27 x28 y29 x30 x31)
        F (Zw pc) fc None m (seg_rom ASEGS)) (only parsing).
  #[local] Notation EST pc x5 x7 x10 x11 x13 x14 x15 x16 x28 x30 := (EST4 pc x5 x7 x10 x11 x13 x14 x15 x16 x28 x29 x30) (only parsing).

  Definition tm_post : machine_state -> Prop := fun ms' =>
    exists y5 y7 y10 y11 y13 y14 y15 y16 y28 y30 : word,
      ms' = EST 0x9b51c y5 y7 y10 y11 y13 y14 y15 y16 y28 y30 /\
      (bv_unsigned y10 = 0 \/ (bv_unsigned y10 = 1 /\ bv_unsigned y15 <> 0 /\ bv_unsigned y15 < 10 ^ 19))%Z.

  (* [comment removed for export] *)
  Definition NZ : Prop := Spf_text.zeros bs k3 kI -> (fL = 0 \/ Spf_text.zeros bs (kI + 1) (kI + 1 + fL))%Z -> False.

  #[using="T3 HY"] Lemma tx_gran : forall A, (T <= A < T + L)%Z -> (ASAN_B + Y0 <= A / 8 + ASAN_B)%Z /\ (A / 8 + ASAN_B + 1 <= ASAN_B + Y0 + (Y1 - Y0))%Z.
  Proof. LiaFast.lf_pins (fun (T3 HY : LiaFast.U) => LiaFast.u0). intros A HA. destruct HY as [Y1a Y2a]. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma tm_done : forall y5 y7 y10 y11 y13 y14 y15 y16 y28 y30,
    (bv_unsigned y10 = 0 \/ (bv_unsigned y10 = 1 /\ bv_unsigned y15 <> 0 /\ bv_unsigned y15 < 10 ^ 19))%Z ->
    evt ASEGS tm_post (EST 0x9b51c y5 y7 y10 y11 y13 y14 y15 y16 y28 y30).
  Proof. LiaFast.lf_pins LiaFast.u0. intros. apply evt_done. do 10 eexists. split; [reflexivity | assumption]. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma tm_fin0 : forall x5 x7 x10 x11 x13 x14 x15 x16 x28 x30,
      evt ASEGS tm_post (EST 0x9a4b8 x5 x7 x10 x11 x13 x14 x15 x16 x28 x30).
  Proof. LiaFast.lf_pins LiaFast.u0.
    intros. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    apply tm_done. left. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma tm_58 : forall x5 x7 x10 x11 x13 x14 x16 x28 x30 (wv : Z),
      (0 < wv < 10 ^ 19)%Z ->
      evt ASEGS tm_post (EST 0x9b510 x5 x7 x10 x11 x13 x14 (Zw wv) x16 x28 x30).
  Proof. LiaFast.lf_pins LiaFast.u0.
    intros x5 x7 x10 x11 x13 x14 x16 x28 x30 wv WV.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    apply tm_done. right. rewrite !unsigned_lit by lia. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma tm_54 : forall x5 x7 x10 x11 x13 x14 x16 x28 x30 (wv : Z),
      (0 < wv < 10 ^ 19)%Z ->
      evt ASEGS tm_post (EST 0x9b50c x5 x7 x10 x11 x13 x14 (Zw wv) x16 x28 x30).
  Proof. LiaFast.lf_pins LiaFast.u0.
    intros x5 x7 x10 x11 x13 x14 x16 x28 x30 wv WV.
    step. (* [comment removed for export] *)
    goto (eapply tm_58); [lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma tm_50 : forall x5 x7 x10 x11 x13 x14 x16 x28 x30 (wv : Z),
      (0 < wv < 10 ^ 19)%Z ->
      evt ASEGS tm_post (EST 0x9b508 x5 x7 x10 x11 x13 x14 (Zw wv) x16 x28 x30).
  Proof. LiaFast.lf_pins LiaFast.u0.
    intros x5 x7 x10 x11 x13 x14 x16 x28 x30 wv WV.
    step. (* [comment removed for export] *)
    goto (eapply tm_54); [lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HS FL0 SPANS HT3"] Lemma loopF : forall (n : nat) (kf wv : Z) (x14 x16 x28 x30 : word),
      (kI + 1 + fL - kf <= Z.of_nat n)%Z ->
      NZ -> (fp = IE + 1)%Z -> (IE + 1 + fL <= T + L)%Z -> digs bs (kI + 1) (kI + 1 + fL) ->
      (kI + 1 <= kf < kI + 1 + fL)%Z -> (0 <= wv <= C19)%Z ->
      (wv = 0%Z -> Spf_text.zeros bs k3 kI /\ Spf_text.zeros bs (kI + 1) kf) ->
      evt ASEGS tm_post (EST 0x9a4e0 (Zw 10) (Zw (kI + fL - kf)) (Zw (T + kf)) (Zw C19) (Zw (T + kf)) x14 (Zw wv) x16 x28 x30).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HS FL0 SPANS HT3 : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros kf wv x14 x16 x28 x30 Hn NZH FP FEND DGF KF WV ZF.
    { exfalso. lia. }
    unfold C19 in *. pose proof (shz_bound _ _ _ _ SHT) as BT.
    pose proof (tx_gran (T + kf) ltac:(lia)) as G0.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT kf RD. pose proof (tx_range bs kf) as Rk. pose proof (DGF kf ltac:(lia)) as Dk. unfold isdig in Dk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs kf.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit wv), ?(unsigned_lit (wv * 10)%Z), ?(unsigned_lit (wv * 10 + tx bs kf)%Z) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hbig.
    2:{ cond_cleanup Hbig. rewrite ?Z.mod_small in Hbig by lia.
        step. (* [comment removed for export] *)
        goto (eapply (tm_54 _ _ _ _ _ _ _ _ _ (wv * 10 + tx bs kf + -48)%Z)); [lia]. }
    - cond_cleanup Hbig. rewrite ?Z.mod_small in Hbig by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite ?(unsigned_lit (kI + fL - kf)%Z) by lia.
      step. (* [comment removed for export] *)
      if_cases Hmore.
      + cond_cleanup Hmore.
        goto (eapply (IH (kf + 1)%Z (wv * 10 + tx bs kf + -48)%Z));
          [lia | exact NZH | lia | lia | exact DGF | lia | unfold C19; lia | ].
        intros Hz. assert (wv = 0%Z) as -> by lia. destruct (ZF eq_refl) as [Z1 Z2].
        split; [exact Z1|]. apply zeros_snoc; [exact Z2 | lia].
      + cond_cleanup Hmore.
        step. (* [comment removed for export] *)
        assert (NZW : (wv * 10 + tx bs kf + -48 <> 0)%Z).
        { intros Hz. assert (wv = 0%Z) as -> by lia. destruct (ZF eq_refl) as [Z1 Z2].
          apply (NZH Z1). right. replace (kI + 1 + fL)%Z with (kf + 1)%Z by lia.
          apply zeros_snoc; [exact Z2 | lia]. }
        goto (eapply (tm_54 _ _ _ _ _ _ _ _ _ (wv * 10 + tx bs kf + -48)%Z)); [lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HS FL0 SPANS HT3 PR"] Lemma after_int : forall (wv : Z) (x7 x14 x16 x28 x30 : word) (a1w a3w : word),
      NZ -> (0 <= wv <= C19)%Z -> (wv = 0%Z -> Spf_text.zeros bs k3 kI) ->
      evt ASEGS tm_post (EST 0x9a4c0 (Zw 10) x7 (Zw IE) a1w a3w x14 (Zw wv) x16 x28 x30).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HS FL0 SPANS HT3 PR : LiaFast.U) => LiaFast.u0).
    intros wv x7 x14 x16 x28 x30 a1w a3w NZH WV ZF. unfold C19 in *.
    rewrite ?(unsigned_lit fL) by lia.
    step. (* [comment removed for export] *)
    if_cases Hf0.
    2:{ cond_cleanup Hf0.
        step. (* [comment removed for export] *)
        assert (NZW : wv <> 0%Z).
        { intros ->. apply (NZH (ZF eq_refl)). left. lia. }
        goto (eapply (tm_50 _ _ _ _ _ _ _ _ _ wv)); [lia]. }
    - cond_cleanup Hf0.
      destruct SPANS as [(F1 & F2)|(F1 & F2 & F3 & F4 & F5)]; [exfalso; lia|].
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite F1. replace (IE + 1)%Z with (T + (kI + 1))%Z by lia.
      goto (eapply (loopF (Datatypes.S (Z.to_nat fL)) (kI + 1)%Z wv));
        [lia | exact NZH | exact F1 | lia | exact F5 | lia | unfold C19; lia | ].
      intros Hz. split; [exact (ZF Hz) | apply zeros_nil].
  Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS HT3 PR"] Lemma loopI : forall (n : nat) (ki wv : Z) (x14 x16 x28 x30 : word),
      (kI - ki <= Z.of_nat n)%Z ->
      NZ -> (k3 <= ki <= kI)%Z -> (0 <= wv <= C19)%Z -> (wv = 0%Z -> Spf_text.zeros bs k3 ki) ->
      evt ASEGS tm_post (EST 0x9a474 (Zw 10) (Zw 1000000000000000000) (Zw IE) (Zw (T + ki)) (Zw (T + ki)) x14 (Zw wv) x16 x28 x30).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS HT3 PR : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros ki wv x14 x16 x28 x30 Hn NZH KI WV ZF.
    { unfold C19 in *.
      rewrite ?(unsigned_lit (T + ki)%Z), ?(unsigned_lit IE) by lia.
      step. (* [comment removed for export] *)
      if_cases Hend; [| cond_cleanup Hend; exfalso; lia]. cond_cleanup Hend.
      goto (eapply (after_int wv)); [exact NZH | unfold C19; lia | replace kI with ki by lia; exact ZF]. }
    unfold C19 in *.
    rewrite ?(unsigned_lit (T + ki)%Z), ?(unsigned_lit IE) by lia.
    step. (* [comment removed for export] *)
    if_cases Hend.
    { cond_cleanup Hend.
      goto (eapply (after_int wv)); [exact NZH | unfold C19; lia | replace kI with ki by lia; exact ZF]. }
    cond_cleanup Hend.
    pose proof (shz_bound _ _ _ _ SHT) as BT.
    pose proof (tx_gran (T + ki) ltac:(lia)) as G0.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT ki RD. pose proof (tx_range bs ki) as Rk. pose proof (DGI ki ltac:(lia)) as Dk. unfold isdig in Dk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs ki.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit wv), ?(unsigned_lit (wv * 10)%Z), ?(unsigned_lit (wv * 10 + tx bs ki)%Z) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hsmall.
    - cond_cleanup Hsmall. rewrite ?Z.mod_small in Hsmall by lia.
      goto (eapply (IH (ki + 1)%Z (wv * 10 + tx bs ki + -48)%Z));
        [lia | exact NZH | lia | unfold C19; lia | ].
      intros Hz. assert (wv = 0%Z) as -> by lia. apply zeros_snoc; [exact (ZF eq_refl) | lia].
    - cond_cleanup Hsmall. rewrite ?Z.mod_small in Hsmall by lia.
      step. (* [comment removed for export] *)
      goto (eapply (tm_58 _ _ _ _ _ _ _ _ _ (wv * 10 + tx bs ki + -48)%Z)); [lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS HT3 PR"] Lemma setupI : forall (x5 x7 x11 x13 x14 x15 x16 x28 x30 : word),
      NZ -> evt ASEGS tm_post (EST 0x9a450 x5 x7 (Zw IE) x11 x13 x14 x15 x16 x28 x30).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS HT3 PR : LiaFast.U) => LiaFast.u0).
    intros x5 x7 x11 x13 x14 x15 x16 x28 x30 NZH.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    do 5 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    replace S with (T + k3)%Z by lia.
    goto (eapply (loopI (Datatypes.S (Z.to_nat (kI - k3))) k3 0%Z));
      [lia | exact NZH | lia | unfold C19; lia | intros _; apply zeros_nil].
  Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS HT3 PR"] Lemma scan_exit : forall (ks : Z) (x7 x11 x13 x14 x15 x28 y29 x30 : word),
      (k3 <= ks <= L)%Z ->
      (forall k, (k3 <= k < ks)%Z -> tx bs k = 48%Z \/ tx bs k = 46%Z) ->
      (ks = L \/ (tx bs ks <> 48%Z /\ tx bs ks <> 46%Z)) ->
      evt ASEGS tm_post (EST4 0x9a444 (Zw ((kI - k3) + fL - cnt48 bs k3 (Z.to_nat (ks - k3)))) x7 (Zw IE) x11 x13 x14 x15 x29 x28 y29 x30).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS HT3 PR : LiaFast.U) => LiaFast.u0).
    intros ks x7 x11 x13 x14 x15 x28 y29 x30 KS SCAN EXIT.
    pose proof (cnt48_range bs k3 (Z.to_nat (ks - k3))) as CR.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H20.
    - clear H20. goto (eapply tm_fin0).
    - cond_cleanup H20. rewrite signed_lit in H20 by lia.
      goto (eapply setupI).
      intros ZI ZF.
      assert (SP' : (fL = 0 \/ (kI < L /\ tx bs kI = 46 /\ kI + 1 + fL <= L /\ Spf_text.zeros bs (kI + 1) (kI + 1 + fL)))%Z).
      { destruct SPANS as [(F1 & F2)|(F1 & F2 & F3 & F4 & F5)]; [left; exact F2|].
        destruct ZF as [F0|ZF]; [left; exact F0 | right].
        split; [lia|]. split; [exact F3|]. split; [lia | exact ZF]. }
      exact (strip_contra bs L k3 kI fL ks 46 ltac:(lia) ltac:(lia) ltac:(lia) KS ZI SP' SCAN EXIT H20).
  Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS HT3 PR"] Lemma loopS : forall (n : nat) (ks t1v : Z) (x13 x14 x15 x30 : word),
      (L - ks <= Z.of_nat n)%Z -> (k3 <= ks < L)%Z ->
      (forall k, (k3 <= k < ks)%Z -> tx bs k = 48%Z \/ tx bs k = 46%Z) ->
      t1v = ((kI - k3) + fL - cnt48 bs k3 (Z.to_nat (ks - k3)))%Z ->
      evt ASEGS tm_post (EST4 0x9a3fc (Zw t1v) (Zw 46) (Zw IE) (Zw (T + ks)) x13 x14 x15 x29 (Zw 48) (Zw (T + ks)) x30).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS HT3 PR : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros ks t1v x13 x14 x15 x30 Hn KS SCAN T1V.
    { exfalso. lia. }
    pose proof (shz_bound _ _ _ _ SHT) as BT.
    pose proof (cnt48_range bs k3 (Z.to_nat (ks - k3))) as CR.
    pose proof (tx_gran (T + ks) ltac:(lia)) as G0.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT ks RD. pose proof (tx_range bs ks) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs ks.
    (* [comment removed for export] *)
    assert (TAIL : forall a4w, (tx bs ks = 48%Z \/ tx bs ks = 46%Z) ->
      evt ASEGS tm_post (EST4 0x9a418 (Zw t1v) (Zw 46) (Zw IE) (Zw (T + ks)) x13 a4w x15 x29 (Zw 48) (Zw (T + ks)) (Zw (tx bs ks)))).
    { intros a4w HB.
      set (is0 := (if (tx bs ks =? 48)%Z then 1 else 0)%Z).
      assert (IS0R : (0 <= is0 <= 1)%Z) by (unfold is0; destruct (tx bs ks =? 48)%Z; lia).
      assert (SCAN' : forall k, (k3 <= k < ks + 1)%Z -> tx bs k = 48%Z \/ tx bs k = 46%Z).
      { intros k Hk. destruct (Z.eq_dec k ks) as [->|]; [exact HB|]. apply SCAN. lia. }
      assert (T1V' : (t1v - is0 = (kI - k3) + fL - cnt48 bs k3 (Z.to_nat (ks + 1 - k3)))%Z).
      { replace (Z.to_nat (ks + 1 - k3)) with (Datatypes.S (Z.to_nat (ks - k3))) by lia.
        rewrite cnt48_step. replace (k3 + Z.of_nat (Z.to_nat (ks - k3)))%Z with ks by lia. unfold is0. lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      assert (SEQ : v_sltiu (Zw (tx bs ks + -48)) 1 = Zw is0).
      { unfold is0. destruct (Z.eqb_spec (tx bs ks) 48) as [E48|N48].
        - rewrite E48. reflexivity.
        - apply seqz_m48; [exact Rk | exact N48]. }
      rewrite SEQ.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite ?(unsigned_lit (T + ks)%Z) by lia.
      step. (* [comment removed for export] *)
      if_cases Hmore.
      - cond_cleanup Hmore.
        goto (eapply (IH (ks + 1)%Z (t1v - is0)%Z)); [lia | lia | exact SCAN' | exact T1V'].
      - cond_cleanup Hmore.
        step. (* [comment removed for export] *)
        goto (eapply (scan_exit (ks + 1)%Z)); [lia | exact SCAN' | left; lia]. }
    step. (* [comment removed for export] *)
    if_cases H48.
    - cond_cleanup H48. apply TAIL. left. exact H48.
    - cond_cleanup H48.
      step. (* [comment removed for export] *)
      if_cases Hdp.
      + cond_cleanup Hdp.
        goto (eapply (scan_exit ks)); [lia | exact SCAN | right; split; [exact H48 | exact Hdp]].
      + cond_cleanup Hdp. apply TAIL. right. exact Hdp.
  Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS HT3 PR"] Lemma blockTM : forall (x7 x11 x13 x14 x15 x16 x28 x30 : word),
      evt ASEGS tm_post (EST 0x9a3dc (Zw ((kI - k3) + fL)) x7 (Zw IE) x11 x13 x14 x15 x16 x28 x30).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS HT3 PR : LiaFast.U) => LiaFast.u0).
    intros x7 x11 x13 x14 x15 x16 x28 x30.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit ((kI - k3) + fL)%Z) by lia.
    step. (* [comment removed for export] *)
    if_cases H20.
    - clear H20. goto (eapply tm_fin0).
    - cond_cleanup H20. rewrite signed_lit in H20 by lia.
      rewrite ?(unsigned_lit S) by lia.
      step. (* [comment removed for export] *)
      if_cases Hk3.
      { cond_cleanup Hk3. exfalso. destruct SPANS as [(F1 & F2)|(F1 & F2 & F3 & F4 & F5)]; lia. }
      cond_cleanup Hk3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      assert (ZB : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 T3)) 255) = Zw 46).
      { rewrite unsigned_lit by lia. change 255%Z with (2 ^ 8 - 1)%Z. rewrite zb_land_mask by lia.
        change (2 ^ 8)%Z with 256%Z. rewrite (proj1 HT3). reflexivity. }
      rewrite ZB. replace S with (T + k3)%Z by lia.
      goto (eapply (loopS (Datatypes.S (Z.to_nat (L - k3))) k3 ((kI - k3) + fL)%Z)); [lia | lia | intros; lia | ].
      replace (Z.to_nat (k3 - k3)) with O by lia. cbn [cnt48]. lia.
  Qed.
End TMF.

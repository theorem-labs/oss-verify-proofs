(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxEnt FxRgs FxFacts FxPlan FxFrame FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require HxGenFp HxSemB HxBaseB HxIntBF HxDefsBF HxExpBWF.

Module HxTmBWF.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require Import HxExpBWF.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ms_eq_tac ::=
  cbv beta delta [mkR];
  repeat first [ reflexivity
               | lazymatch goal with |- @eq (bv _) _ _ => ms_leaf_eq end
               | progress f_equal ].

Definition C19 : Z := 999999999999999999.

(* [comment removed for export] *)
Lemma v_slt_lit : forall a b, (- 2 ^ 63 <= a < 2 ^ 63)%Z -> (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
  v_slt (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.b2z (a <? b)%Z).
Proof. intros a b Ha Hb. unfold v_slt, c_lts, bv_lts. rewrite !slit64 by lia. destruct (a <? b)%Z; reflexivity. Qed.
Lemma v_slti_lit : forall a imm, (- 2 ^ 63 <= a < 2 ^ 63)%Z ->
  v_slti (Z_to_bv 64 a) imm = Z_to_bv 64 (Z.b2z (a <? imm)%Z).
Proof. intros a imm Ha. unfold v_slti, zsig. rewrite slit64 by lia. destruct (a <? imm)%Z; reflexivity. Qed.

(* [comment removed for export] *)
Lemma lxor_ones64 : forall x, (0 <= x < 2 ^ 64)%Z -> Z.lxor x 18446744073709551615 = (18446744073709551615 - x)%Z.
Proof.
  intros x Hx. change 18446744073709551615%Z with (Z.ones 64).
  assert (E : Z.lxor x (Z.ones 64) = Z.land (Z.lnot x) (Z.ones 64)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.ltb_spec i 64) as [Hlt|Hge].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x i); reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r, Bool.xorb_false_r.
      destruct (Z.eq_dec x 0) as [->|Hn]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. assert (Z.log2 x < 64)%Z by (apply Z.log2_lt_pow2; lia). lia. }
  rewrite E, Z.land_ones by lia. unfold Z.lnot. change (Z.ones 64) with (2 ^ 64 - 1)%Z.
  Z.div_mod_to_equations. lia.
Qed.

Section TM.
  Variables (x2 x3 x4 x8 x18 x20 x23 x24 x25 x26 x27 x30 x31 X5 X15 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte).
  Variables (T S IE fp fL S1 Y0 Y1 ev : Z).
  #[local] Notation L := (Z.of_nat (length bs)).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  #[local] Notation k3 := (S - T)%Z.
  #[local] Notation kI := (IE - T)%Z.
  Hypothesis TXT : bytes_at BSEGS m T bs.
  Hypothesis HL : (1 <= L <= 128)%Z.
  Hypothesis HT : (6537216 <= T <= 140737488355072)%Z.
  Hypothesis SHT : shz BSEGS m (ASAN_B + Y0) (Y1 - Y0).
  Hypothesis HY : (8 * Y0 <= T /\ T + L <= 8 * Y1)%Z.
  Hypothesis HS : (T <= S <= IE /\ IE <= T + L)%Z.
  Hypothesis DGI : digs bs k3 kI.
  Hypothesis FL0 : (0 <= fL <= 128)%Z.
  Hypothesis SPANS : ((fp = 0 /\ fL = 0) \/
                      (fp = IE + 1 /\ IE < T + L /\ tx bs kI = 46 /\ IE + 1 + fL <= T + L /\ digs bs (kI + 1) (kI + 1 + fL)))%Z.
  Hypothesis HS1 : (2 ^ 40 <= S1 <= 2 ^ 47)%Z.
  Hypothesis LOC : ro_cells BSEGS m (S1 + 48) [C8 (Zw fL)].
  Hypothesis HEV : (- EXPMAX <= ev <= EXPMAX)%Z.
  Hypothesis PR : pristine m 65536 188416.   (* [comment removed for export] *)
  Hypothesis H20 : (20 <= (kI - k3) + fL)%Z.  (* [comment removed for export] *)

  #[local] Notation EST pc x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 :=
    (MS (mkR (Zw 46) x2 x3 x4 x5 x6 (Zw ev) x8 (Zw S1) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Zw ASAN_B) x20 (Zw S) (Zw (T + L)) x23 x24 x25 x26 x27
             x28 (Zw fp) x30 x31)
        F (Zw pc) fc None m (seg_rom BSEGS)) (only parsing).

  Definition tm_post : machine_state -> Prop := fun ms' =>
    exists y5 y6 y10 y11 y12 y13 y14 y15 y17 y28 : word,
      (ms' = EST 0x9c5f8 y5 y6 y10 y11 y12 y13 y14 y15 (Zw (IE - S)) y17 y28 /\ y5 = X5 /\ y15 = X15) \/
      (ms' = EST 0x9cc68 y5 y6 y10 y11 y12 y13 y14 y15 (Zw (IE - S)) y17 y28 /\
       (1 <= bv_unsigned y15 < 10 ^ 19)%Z /\ exists d, (-128 <= d <= 128)%Z /\ y5 = Zw (d + ev)).

  (* [comment removed for export] *)
  Definition NZ : Prop := Spf_text.zeros bs k3 kI -> (fL = 0 \/ Spf_text.zeros bs (kI + 1) (kI + 1 + fL))%Z -> False.

  #[using="HY"] Lemma tx_gran : forall A, (T <= A < T + L)%Z -> (ASAN_B + Y0 <= A / 8 + ASAN_B)%Z /\ (A / 8 + ASAN_B + 1 <= ASAN_B + Y0 + (Y1 - Y0))%Z.
  Proof. LiaFast.lf_pins (fun (HY : LiaFast.U) => LiaFast.u0). intros A HA. destruct HY as [Y1a Y2a]. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  #[using="HEV"] Lemma tm_50 : forall x5 x6 x11 x13 x14 x16 x17 x28 (d wv : Z),
      (-128 <= d <= 128)%Z -> (0 < wv < 10 ^ 19)%Z ->
      evt BSEGS tm_post (EST 0x9cc54 x5 x6 (Zw d) x11 (Zw (IE - S)) x13 x14 (Zw wv) x16 x17 x28).
  Proof. LiaFast.lf_pins (fun (HEV : LiaFast.U) => LiaFast.u0).
    intros x5 x6 x11 x13 x14 x16 x17 x28 d wv HD WV. unfold EXPMAX in *.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (v_slt_lit (d + ev) d) by lia. rewrite (v_slti_lit ev 0) by lia.
    replace (d + ev <? d)%Z with (ev <? 0)%Z by (destruct (Z.ltb_spec ev 0); destruct (Z.ltb_spec (d + ev) d); lia).
    step. (* [comment removed for export] *)
    if_cases Hu; [cond_cleanup Hu; exfalso; exact (Hu eq_refl) |]. clear Hu.
    apply evt_done. do 10 eexists. right. split; [reflexivity|]. split; [rewrite unsigned_lit by lia; lia|].
    exists d. split; [exact HD | reflexivity].
  Qed.

  (* [comment removed for export] *)
  #[using="HL HT HS SPANS HEV H20"] Lemma tm_4c : forall x5 x6 x11 x13 x14 x16 x17 x28 (kf wv : Z),
      (fp = IE + 1)%Z -> (kI + 1 <= kf <= kI + 1 + fL)%Z -> (0 < wv < 10 ^ 19)%Z ->
      evt BSEGS tm_post (EST 0x9cc50 x5 x6 (Zw (T + kf)) x11 (Zw (IE - S)) x13 x14 (Zw wv) x16 x17 x28).
  Proof. LiaFast.lf_pins (fun (HL HT HS SPANS HEV H20 : LiaFast.U) => LiaFast.u0).
    intros x5 x6 x11 x13 x14 x16 x17 x28 kf wv FP KF WV.
    step. (* [comment removed for export] *)
    goto (eapply (tm_50 _ _ _ _ _ _ _ _ (fp - (T + kf))%Z wv)); [lia | exact WV].
  Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HS FL0 SPANS HEV H20"] Lemma loopF : forall (n : nat) (kf wv : Z) (x14 x17 x28 : word),
      (kI + 1 + fL - kf <= Z.of_nat n)%Z ->
      NZ -> (fp = IE + 1)%Z -> (IE + 1 + fL <= T + L)%Z -> digs bs (kI + 1) (kI + 1 + fL) ->
      (kI + 1 <= kf < kI + 1 + fL)%Z -> (0 <= wv <= C19)%Z ->
      (wv = 0%Z -> Spf_text.zeros bs k3 kI /\ Spf_text.zeros bs (kI + 1) kf) ->
      evt BSEGS tm_post (EST 0x9c640 (Zw 10) (Zw (T + kf)) (Zw (T + kf)) (Zw C19) (Zw (IE - S)) (Zw (-1)) x14 (Zw wv) (Zw (kI + fL - kf)) x17 x28).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HS FL0 SPANS HEV H20 : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros kf wv x14 x17 x28 Hn NZH FP FEND DGF KF WV ZF.
    { exfalso. lia. }
    unfold C19 in *. pose proof (shz_bound _ _ _ _ SHT) as BT.
    pose proof (tx_gran (T + kf) ltac:(lia)) as G0.
    rewrite ?(unsigned_lit (T + kf)%Z) by lia.
    step. (* [comment removed for export] *)
    if_cases Hu1; [cond_cleanup Hu1; exfalso; lia|]. cond_cleanup Hu1. clear Hu1.
    step. (* [comment removed for export] *)
    if_cases Hu2; [cond_cleanup Hu2; exfalso; lia|]. cond_cleanup Hu2. clear Hu2.
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
    - cond_cleanup Hbig. rewrite ?Z.mod_small in Hbig by lia.
      goto (eapply (tm_4c _ _ _ _ _ _ _ _ (kf + 1)%Z (wv * 10 + tx bs kf + -48)%Z)); [exact FP | lia | lia].
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
        goto (eapply (tm_4c _ _ _ _ _ _ _ _ (kf + 1)%Z (wv * 10 + tx bs kf + -48)%Z)); [exact FP | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HS FL0 SPANS LOC HEV PR H20"] Lemma after_int : forall (wv : Z) (x6 x11 x13 x14 x16 x17 x28 : word),
      NZ -> (0 <= wv <= C19)%Z -> (wv = 0%Z -> Spf_text.zeros bs k3 kI) ->
      evt BSEGS tm_post (EST 0x9c600 (Zw 1000000000000000000) x6 (Zw IE) x11 (Zw (IE - S)) x13 x14 (Zw wv) x16 x17 x28).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HS FL0 SPANS LOC HEV PR H20 : LiaFast.U) => LiaFast.u0).
    intros wv x6 x11 x13 x14 x16 x17 x28 NZH WV ZF. unfold C19 in *.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    assert (FPR : (0 <= fp <= 140737488355328 /\ (fp = 0%Z -> fL = 0%Z))%Z).
    { destruct SPANS as [(F1 & F2)|(F1 & F2 & F3 & F4 & F5)]; lia. }
    rewrite ?(unsigned_lit (fL + fp)%Z), ?(unsigned_lit fp) by lia.
    step. (* [comment removed for export] *)
    if_cases Hu1; [cond_cleanup Hu1; exfalso; lia|]. cond_cleanup Hu1. clear Hu1.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    assert (XOR1 : Z.lxor (bv_unsigned (v_sltu (Zw 0) (Zw fp))) (bv_unsigned (v_sltiu (Zw (fL + fp)) 1)) = 1%Z).
    { rewrite v_sltu_b2z, v_sltiu_b2z. rewrite (unsigned_lit 0), (unsigned_lit fp), (unsigned_lit (fL + fp)%Z) by lia.
      replace (bv_wrap 64 1) with 1%Z by reflexivity.
      destruct (Z.eq_dec fp 0) as [E0|N0].
      - rewrite E0, (proj2 FPR E0). reflexivity.
      - destruct (Z.ltb_spec 0 fp); [|lia]. destruct (Z.ltb_spec (fL + fp) 1); [lia|]. reflexivity. }
    rewrite XOR1.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit fL) by lia.
    step. (* [comment removed for export] *)
    if_cases Hf0.
    - cond_cleanup Hf0.
      assert (NZW : wv <> 0%Z).
      { intros ->. apply (NZH (ZF eq_refl)). left. lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply (tm_50 _ _ _ _ _ _ _ _ 0%Z wv)); [lia | lia].
    - cond_cleanup Hf0.
      destruct SPANS as [(F1 & F2)|(F1 & F2 & F3 & F4 & F5)]; [exfalso; lia|].
      step. (* [comment removed for export] *)
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
  #[using="Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS LOC HEV PR H20"] Lemma loopI : forall (n : nat) (ki wv : Z) (x14 x17 x28 : word),
      (kI - ki <= Z.of_nat n)%Z ->
      NZ -> (k3 <= ki <= kI)%Z -> (0 <= wv <= C19)%Z -> (wv = 0%Z -> Spf_text.zeros bs k3 ki) ->
      evt BSEGS tm_post (EST 0x9c5ac (Zw 1000000000000000000) (Zw (T + ki)) (Zw IE) (Zw (T + ki)) (Zw (IE - S)) (Zw 2) x14 (Zw wv) (Zw 10) x17 x28).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS LOC HEV PR H20 : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros ki wv x14 x17 x28 Hn NZH KI WV ZF.
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
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hu; [cond_cleanup Hu; exfalso; lia|]. cond_cleanup Hu. clear Hu.
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
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply (tm_50 _ _ _ _ _ _ _ _ (IE - (T + ki + 1))%Z (wv * 10 + tx bs ki + -48)%Z)); [lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS LOC HEV PR H20"] Lemma setupI : forall (x5 x6 x11 x12 x13 x14 x15 x17 x28 : word),
      NZ -> evt BSEGS tm_post (EST 0x9c578 x5 x6 (Zw IE) x11 x12 x13 x14 x15 (Zw (IE - S)) x17 x28).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS LOC HEV PR H20 : LiaFast.U) => LiaFast.u0).
    intros x5 x6 x11 x12 x13 x14 x15 x17 x28 NZH.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit S) by lia. rewrite (lxor_ones64 S) by lia.
    rewrite ?(unsigned_lit (18446744073709551615 - S)%Z), ?(unsigned_lit (IE - S)%Z) by lia.
    step. (* [comment removed for export] *)
    if_cases Hu; [cond_cleanup Hu; exfalso; lia|]. cond_cleanup Hu. clear Hu.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
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
  #[using="Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS LOC HEV PR H20"] Lemma scan_exit : forall (ks : Z) (x11 x13 x14 x16 x17 x28 : word),
      (k3 <= ks <= L)%Z ->
      (forall k, (k3 <= k < ks)%Z -> tx bs k = 48%Z \/ tx bs k = 46%Z) ->
      (ks = L \/ (tx bs ks <> 48%Z /\ tx bs ks <> 46%Z)) ->
      evt BSEGS tm_post (EST 0x9c56c X5 (Zw ((kI - k3) + fL - cnt48 bs k3 (Z.to_nat (ks - k3)))) (Zw IE) x11 (Zw (IE - S)) x13 x14 X15 x16 x17 x28).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS LOC HEV PR H20 : LiaFast.U) => LiaFast.u0).
    intros ks x11 x13 x14 x16 x17 x28 KS SCAN EXIT.
    pose proof (cnt48_range bs k3 (Z.to_nat (ks - k3))) as CR.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H20'.
    - clear H20'. apply evt_done. do 10 eexists. left. split; [reflexivity|]. split; reflexivity.
    - cond_cleanup H20'. rewrite signed_lit in H20' by lia.
      goto (eapply setupI).
      intros ZI ZF.
      assert (SP' : (fL = 0 \/ (kI < L /\ tx bs kI = 46 /\ kI + 1 + fL <= L /\ Spf_text.zeros bs (kI + 1) (kI + 1 + fL)))%Z).
      { destruct SPANS as [(F1 & F2)|(F1 & F2 & F3 & F4 & F5)]; [left; exact F2|].
        destruct ZF as [F0|ZF]; [left; exact F0 | right].
        split; [lia|]. split; [exact F3|]. split; [lia | exact ZF]. }
      exact (strip_contra bs L k3 kI fL ks 46 ltac:(lia) ltac:(lia) ltac:(lia) KS ZI SP' SCAN EXIT H20').
  Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS LOC HEV PR H20"] Lemma loopS : forall (n : nat) (ks t1v : Z) (x14 x17 : word),
      (L - ks <= Z.of_nat n)%Z -> (k3 <= ks < L)%Z ->
      (forall k, (k3 <= k < ks)%Z -> tx bs k = 48%Z \/ tx bs k = 46%Z) ->
      t1v = ((kI - k3) + fL - cnt48 bs k3 (Z.to_nat (ks - k3)))%Z ->
      evt BSEGS tm_post (EST 0x9c51c X5 (Zw t1v) (Zw IE) (Zw (T + ks)) (Zw (IE - S)) (Zw 48) x14 X15 (Zw (-1)) x17 (Zw (T + ks))).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS LOC HEV PR H20 : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros ks t1v x14 x17 Hn KS SCAN T1V.
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
    assert (TAIL : forall a4w t1v', (tx bs ks = 48%Z \/ tx bs ks = 46%Z) ->
      t1v' = ((kI - k3) + fL - cnt48 bs k3 (Z.to_nat (ks + 1 - k3)))%Z ->
      forall a7w, evt BSEGS tm_post (EST 0x9c548 X5 (Zw t1v') (Zw IE) (Zw (T + ks)) (Zw (IE - S)) (Zw 48) a4w X15 (Zw (-1)) a7w (Zw (T + ks)))).
    { intros a4w t1v' HB T1V' a7w.
      assert (SCAN' : forall k, (k3 <= k < ks + 1)%Z -> tx bs k = 48%Z \/ tx bs k = 46%Z).
      { intros k Hk. destruct (Z.eq_dec k ks) as [->|]; [exact HB|]. apply SCAN. lia. }
      rewrite ?(unsigned_lit (T + ks)%Z) by lia.
      step. (* [comment removed for export] *)
      if_cases Hu; [cond_cleanup Hu; exfalso; lia|]. cond_cleanup Hu. clear Hu.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite ?(unsigned_lit (T + ks + 1)%Z) by lia.
      step. (* [comment removed for export] *)
      if_cases Hmore.
      - cond_cleanup Hmore.
        goto (eapply (IH (ks + 1)%Z t1v')); [lia | lia | exact SCAN' | exact T1V'].
      - cond_cleanup Hmore.
        step. (* [comment removed for export] *)
        rewrite T1V'.
        goto (eapply (scan_exit (ks + 1)%Z)); [lia | exact SCAN' | left; lia]. }
    assert (CS : (cnt48 bs k3 (Z.to_nat (ks + 1 - k3)) = cnt48 bs k3 (Z.to_nat (ks - k3)) + (if (tx bs ks =? 48)%Z then 1 else 0))%Z).
    { replace (Z.to_nat (ks + 1 - k3)) with (Datatypes.S (Z.to_nat (ks - k3))) by lia.
      rewrite cnt48_step. replace (k3 + Z.of_nat (Z.to_nat (ks - k3)))%Z with ks by lia. reflexivity. }
    step. (* [comment removed for export] *)
    if_cases H48.
    - cond_cleanup H48.
      step. (* [comment removed for export] *)
      if_cases H48'; [cond_cleanup H48'; exfalso; lia|]. clear H48'.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hu; [cond_cleanup Hu; try rewrite !signed_lit in Hu by lia; exfalso; lia|]. clear Hu.
      step. (* [comment removed for export] *)
      goto (eapply (TAIL _ (t1v + -1)%Z)); [left; exact H48 | ].
      rewrite CS, T1V. rewrite H48. cbn [Z.eqb Pos.eqb]. lia.
    - cond_cleanup H48.
      step. (* [comment removed for export] *)
      if_cases Hdp.
      + cond_cleanup Hdp. rewrite T1V.
        goto (eapply (scan_exit ks)); [lia | exact SCAN | right; split; [exact H48 | exact Hdp]].
      + cond_cleanup Hdp.
        step. (* [comment removed for export] *)
        if_cases H48'; [| cond_cleanup H48'; exfalso; lia]. clear H48'.
        goto (eapply (TAIL _ t1v)); [right; exact Hdp | ].
        rewrite CS, T1V. destruct (Z.eqb_spec (tx bs ks) 48); [exfalso; lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS LOC HEV PR H20"] Lemma blockTM : forall (x11 x12 x13 x14 x17 x28 : word),
      evt BSEGS tm_post (EST 0x9c504 X5 (Zw ((kI - k3) + fL)) (Zw IE) x11 x12 x13 x14 X15 (Zw (IE - S)) x17 x28).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HS DGI FL0 SPANS LOC HEV PR H20 : LiaFast.U) => LiaFast.u0).
    intros x11 x12 x13 x14 x17 x28.
    rewrite ?(unsigned_lit S), ?(unsigned_lit (T + L)%Z) by lia.
    step. (* [comment removed for export] *)
    if_cases Hk3.
    { cond_cleanup Hk3. exfalso. destruct SPANS as [(F1 & F2)|(F1 & F2 & F3 & F4 & F5)]; lia. }
    cond_cleanup Hk3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    replace S with (T + k3)%Z by lia.
    goto (eapply (loopS (Datatypes.S (Z.to_nat (L - k3))) k3 ((kI - k3) + fL)%Z)); [lia | lia | intros; lia | ].
    replace (Z.to_nat (k3 - k3)) with O by lia. cbn [cnt48]. lia.
  Qed.
End TM.
End HxTmBWF.

Import OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxGenFp OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxSemB OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxBaseB OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxIntBF OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxDefsBF OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxExpBWF OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxTmBF.HxTmBWF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Theorem tm_kit : hx_kitm_fp BSEGS xok_spd 0x9c504 TM_KEYS tm_chk TM_EXITS.
Proof.
  intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold tm_chk in Hchk. cbn [xs_st xs_x] in Hchk.
  destruct (s_resv L) eqn:Hrv; try discriminate.
  destruct (fl_of L) as [fLl|] eqn:Hfl; [|discriminate].
  apply andb_prop in Hchk as [Hchk Hx1]. apply andb_prop in Hchk as [Hchk Hx0]. apply andb_prop in Hchk as [Hchk Hfx].
  apply andb_prop in Hchk as [Hchk Hrod]. apply andb_prop in Hchk as [Hchk H1c]. apply andb_prop in Hchk as [Hchk H19].
  apply andb_prop in Hchk as [Hrg H22]. apply lin_eqb_eq in H22, H19, H1c.
  rewrite forallb_app in Hfx. apply andb_prop in Hfx as [Hfx HfS].
  pose proof (txt_bounds E ms L Hd Hfx) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (txt_bytes E ms L Hd Hrg Hfx) as (bs & TXT & Hlen).
  pose proof (txt_shadow E ms L Hd Hrg Hfx) as SHT.
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  set (Tz := bv_unsigned (E 1%positive)) in *. set (Lz := bv_unsigned (E 2%positive)) in *.
  set (Y0z := bv_unsigned (E 7%positive)) in *. set (Y1z := bv_unsigned (E 8%positive)) in *.
  set (S := rgl L 21) in *. set (IE := rgl L 10) in *. set (S1l := rgl L 9) in *. set (fpl := rgl L 29) in *.
  set (Sz := bv_unsigned (lden E S)). set (IEz := bv_unsigned (lden E IE)). set (fLz := bv_unsigned (lden E fLl)).
  set (S1z := bv_unsigned (lden E S1l)). set (fpz := bv_unsigned (lden E fpl)).
  set (r6z := bv_unsigned (lden E (rgl L 6))). set (r16z := bv_unsigned (lden E (rgl L 16))). set (r7z := bv_unsigned (lden E (rgl L 7))).
  pose proof (bv_unsigned_in_range _ (lden E S)) as BS. pose proof (bv_unsigned_in_range _ (lden E IE)) as BIE.
  pose proof (bv_unsigned_in_range _ (lden E fLl)) as BfL. pose proof (bv_unsigned_in_range _ (lden E S1l)) as BS1.
  pose proof (bv_unsigned_in_range _ (lden E (rgl L 6))) as B6'. pose proof (bv_unsigned_in_range _ (lden E (rgl L 16))) as B16.
  pose proof (bv_unsigned_in_range _ (lden E (rgl L 7))) as B7.
  unfold bv_modulus in BS, BIE, BfL, BS1, B6', B16, B7. change (2 ^ Z.of_N 64) with two64 in BS, BIE, BfL, BS1, B6', B16, B7.
  (* [comment removed for export] *)
  unfold tm_facts in HfS. fold S IE S1l in HfS. cbn [forallb] in HfS.
  repeat match type of HfS with (?a && ?b)%bool = true => apply andb_prop in HfS as [?F HfS] end.
  pose proof (fact_implied_ok E _ _ HF F) as X1. pose proof (fact_implied_ok E _ _ HF F0) as X2.
  pose proof (fact_implied_ok E _ _ HF F1) as X3. pose proof (fact_implied_ok E _ _ HF F2) as X4.
  pose proof (fact_implied_ok E _ _ HF F3) as X5. pose proof (fact_implied_ok E _ _ HF F4) as X6.
  pose proof (fact_implied_ok E _ _ HF F5) as X7. pose proof (fact_implied_ok E _ _ HF F6) as X8.
  pose proof (fact_implied_ok E _ _ HF F7) as X9.
  cbn [fact_ok] in X1, X2, X3, X4, X5, X6, X7, X8, X9.
  rewrite (u_sub E) in X1, X2, X3, X6, X7. rewrite (u_add E), (u_sub E) in X6. rewrite (u_sub E) in X7. unfold TXT_TL, TXT_T, TXT_L in X1, X3.
  rewrite (u_add E) in X3. rewrite !lden_lvar in X1. rewrite !lden_lvar in X3. rewrite lden_laddc, u_Z_to_bv in X8.
  fold Sz Tz Lz IEz fLz S1z r6z r16z r7z in X1, X2, X3, X4, X5, X6, X7, X8, X9.
  assert (M3 : (Tz + Lz) mod two64 = Tz + Lz) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite M3 in X3.
  assert (HS : Tz <= Sz <= IEz /\ IEz <= Tz + Lz) by (clear -X1 X2 X3 BS BIE B1 B2; unfold two64 in *; split; [split|]; Z.div_mod_to_equations; lia).
  assert (HDC : r6z = IEz - Sz + fLz).
  { clear -X6 X4 HS B6' B1 B2. unfold two64 in *. rewrite (Z.mod_small (IEz - Sz)) in X6 by lia. rewrite (Z.mod_small (IEz - Sz + fLz)) in X6 by lia.
    Z.div_mod_to_equations. lia. }
  assert (H16 : r16z = IEz - Sz).
  { clear -X7 HS B16 B1 B2. unfold two64 in *. rewrite (Z.mod_small (IEz - Sz)) in X7 by lia. Z.div_mod_to_equations. lia. }
  set (evz := (r7z + EXPMAXz) mod two64 - EXPMAXz).
  assert (HEV : - EXPMAX <= evz <= EXPMAX) by (unfold evz, EXPMAX, EXPMAXz in *; clear -X8; lia).
  assert (HEVw : Z_to_bv 64 evz = lden E (rgl L 7)).
  { apply bv_eq. rewrite u_Z_to_bv. fold r7z. unfold evz, EXPMAXz in *. clear -B7 X8. unfold two64 in *. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (RG : forall k, getr (ms_regs ms) (Z_to_bv 5 k) = lden E (rgl L k)).
  { intros k. rewrite (HR _). reflexivity. }
  assert (Rw : forall k z, bv_unsigned (lden E (rgl L k)) = z -> getr (ms_regs ms) (Z_to_bv 5 k) = Z_to_bv 64 z).
  { intros k z Hz. rewrite RG. rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 46).
  { transitivity (lden E (rgl L 1)); [exact (RG 1)|]. rewrite H1c, lden_lconst. reflexivity. }
  assert (R9 : getr (ms_regs ms) 9%bv = Z_to_bv 64 S1z) by (apply (Rw 9); reflexivity).
  assert (R10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 IEz) by (apply (Rw 10); reflexivity).
  assert (R21 : getr (ms_regs ms) 21%bv = Z_to_bv 64 Sz) by (apply (Rw 21); reflexivity).
  assert (R29 : getr (ms_regs ms) 29%bv = Z_to_bv 64 fpz) by (apply (Rw 29); reflexivity).
  assert (R6 : getr (ms_regs ms) 6%bv = Z_to_bv 64 ((IEz - Tz) - (Sz - Tz) + fLz)).
  { apply (Rw 6). fold r6z. rewrite HDC. ring. }
  assert (R16 : getr (ms_regs ms) 16%bv = Z_to_bv 64 (IEz - Sz)) by (apply (Rw 16); fold r16z; exact H16).
  assert (R7 : getr (ms_regs ms) 7%bv = Z_to_bv 64 evz) by (transitivity (lden E (rgl L 7)); [exact (RG 7) | symmetry; exact HEVw]).
  assert (R22 : getr (ms_regs ms) 22%bv = Z_to_bv 64 (Tz + Lz)).
  { transitivity (lden E (rgl L 22)); [exact (RG 22)|]. rewrite H22. unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, !lden_lvar.
    apply bv_eq. rewrite bv_add_unsigned, u_Z_to_bv. reflexivity. }
  assert (R19 : getr (ms_regs ms) 19%bv = Z_to_bv 64 ASAN_B).
  { transitivity (lden E (rgl L 19)); [exact (RG 19)|]. rewrite H19. rewrite lden_lconst. reflexivity. }
  (* [comment removed for export] *)
  unfold fl_of in Hfl. destruct (find_cell (s_rgs L) (laddc (rgl L 9) 48)) as [[[Rc o] l0]|] eqn:Hfc; [|discriminate].
  injection Hfl as ->.
  destruct (find_cell_spec _ _ _ _ _ Hfc) as (HinR & Ho & Hosm & Htr).
  destruct (is_const_sound E _ _ Ho) as [Xo Hor].
  assert (HGc : rg_ok BSEGS E (ms_mem ms) Rc) by (rewrite Forall_forall in HG; exact (HG _ HinR)).
  assert (CB : bytes_at BSEGS (ms_mem ms) (bv_unsigned (lden E (rg_base Rc)) + o) (le8 (lden E fLl))).
  { destruct Htr as [Htr|(-> & Htr)].
    - pose proof (cont_bytes_at BSEGS E (ms_mem ms) Rc o (bv8l fLl) HGc ltac:(lia) ltac:(cbn; lia) Htr) as X.
      unfold bv8l in X. rewrite map_bden_bv8 in X. exact X.
    - pose proof (cont_bytes_at BSEGS E (ms_mem ms) Rc o (List.repeat (BK 0) 8) HGc ltac:(lia) ltac:(cbn; lia) Htr) as X.
      rewrite lden_lconst. exact X. }
  pose proof (bytes_at_bound BSEGS (ms_mem ms) _ _ CB) as CBb. rewrite length_le8 in CBb.
  assert (HA : bv_unsigned (lden E (rg_base Rc)) + o = S1z + 48).
  { pose proof (f_equal bv_unsigned Xo) as Y. rewrite (u_sub E), lden_laddc, u_Z_to_bv in Y. fold S1l in Y. fold S1z in Y.
    rewrite u_Z_to_bv in Y. unfold two64 in *. rewrite (Z.mod_small (S1z + 48)) in Y by lia.
    pose proof (bv_unsigned_in_range _ (lden E (rg_base Rc))) as Bb. unfold bv_modulus in Bb. change (2 ^ Z.of_N 64) with (2 ^ 64) in Bb.
    Z.div_mod_to_equations. lia. }
  rewrite HA in CB.
  assert (LOC : ro_cells BSEGS (ms_mem ms) (S1z + 48) [C8 (Z_to_bv 64 fLz)]).
  { split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold fLz. rewrite Z_to_bv_bv_unsigned. exact CB. }
  (* [comment removed for export] *)
  assert (PR : pristine (ms_mem ms) 65536 188416).
  { unfold rod_ok in Hrod. apply existsb_exists in Hrod as (Rr & HRr & Hr). unfold rg_is in Hr.
    apply andb_prop in Hr as [Hr Hcr]. apply andb_prop in Hr as [Hr Hkr]. apply andb_prop in Hr as [Hbr Hsr].
    apply lin_eqb_eq in Hbr, Hsr. destruct (rg_kind Rr) eqn:Hk; cbn in Hkr; try discriminate.
    rewrite Forall_forall in HG.
    assert (PRb : pristine (ms_mem ms) 65536 (65536 + 188416)).
    { apply (pristine_of_rg_ro BSEGS E (ms_mem ms) Rr 65536 188416 (HG _ HRr) Hk).
      - rewrite Hbr, lden_lconst. reflexivity.
      - unfold rsz. rewrite Hsr, lden_lconst. reflexivity. }
    destruct PRb as (P1 & P2 & P3). split; [exact P1|]. split; [lia|]. intros i Hi. apply P3. lia. }
  (* [comment removed for export] *)
  apply existsb_exists in Hx0 as (f0 & Hf0 & Hq0). apply xf_eqb_eq in Hq0. subst f0.
  apply existsb_exists in Hx1 as (f1 & Hf1 & Hq1). apply xf_eqb_eq in Hq1. subst f1.
  rewrite Forall_forall in HxF. pose proof (HxF _ Hf0) as XD. pose proof (HxF _ Hf1) as XS.
  unfold xfact_ok in XD, XS. cbn [xf_tag xf_args List.map xok_spd] in XD, XS. fold S IE fpl in XD, XS. fold Sz IEz fLz fpz in XD, XS.
  assert (TXT0 : bytes_at BSEGS m0 Tz bs).
  { apply (bytes_at_transport (ms_mem ms)); [exact TXT|]. intros i Hi.
    unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1' rs]] eqn:Hr; try discriminate.
    apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 Hk0].
    apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. destruct (rg_kind R0) eqn:Hk; cbn in Hk0; try discriminate.
    rewrite <- Hr in Hm0. exact (txt_frame E L ms m0 R0 (R1' :: rs) i Hr Hb0 Hs0 Hk Hm0 ltac:(lia) ltac:(unfold two64 in *; lia)). }
  destruct XD as (Td & bsd & TXd & Dd1 & Dd2 & DGd).
  assert (DGI : digs bs (Sz - Tz) (IEz - Tz)).
  { apply (digs_transport m0 Tz bs Td bsd Sz IEz TXT0 TXd); [lia | lia | lia | lia | exact DGd]. }
  assert (SPANS : ((fpz = 0 /\ fLz = 0) \/
                   (fpz = IEz + 1 /\ IEz < Tz + Lz /\ tx bs (IEz - Tz) = 46 /\ IEz + 1 + fLz <= Tz + Lz /\
                    digs bs (IEz - Tz + 1) (IEz - Tz + 1 + fLz)))%Z).
  { destruct XS as [XS|(Hfp & Hend & Ts & bss & TXs & Hs1 & Hs2 & Hdot & DGs)]; [left; exact XS|right].
    unfold TXT_TL, TXT_T, TXT_L in Hend. rewrite lden_ladd, bv_add_unsigned, !lden_lvar in Hend. fold Tz Lz in Hend.
    unfold bv_wrap, bv_modulus in Hend. change (2 ^ Z.of_N 64) with two64 in Hend. rewrite M3 in Hend.
    split; [exact Hfp|]. assert (HIEL : IEz < Tz + Lz) by lia.
    split; [exact HIEL|].
    split; [rewrite (tx_transport m0 Tz bs Ts bss IEz TXT0 TXs ltac:(lia) ltac:(lia)); exact Hdot|].
    split; [lia|].
    replace (IEz - Tz + 1 + fLz) with (IEz + 1 + fLz - Tz) by lia. replace (IEz - Tz + 1) with (IEz + 1 - Tz) by lia.
    apply (digs_transport m0 Tz bs Ts bss (IEz + 1) (IEz + 1 + fLz) TXT0 TXs); [lia | lia | lia | lia | exact DGs]. }
  (* [comment removed for export] *)
  set (R := ms_regs ms) in *.
  assert (HK : evt BSEGS (tm_post (getr R 2) (getr R 3) (getr R 4) (getr R 8) (getr R 18) (getr R 20) (getr R 23) (getr R 24) (getr R 25)
                 (getr R 26) (getr R 27) (getr R 30) (getr R 31) (getr R 5) (getr R 15)
                 (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) bs Tz Sz IEz fpz S1z evz)
             (kms BSEGS ms)).
  { assert (P1 : 1 <= Z.of_nat (length bs) <= 128) by (clear -Hlen B1; lia).
    assert (P2 : 6537216 <= Tz <= 140737488355072) by (clear -B2; lia).
    assert (P3 : 8 * Y0z <= Tz /\ Tz + Z.of_nat (length bs) <= 8 * Y1z) by (clear -Hlen B5 B6; lia).
    assert (P4 : Tz <= Sz <= IEz /\ IEz <= Tz + Z.of_nat (length bs)) by (clear -Hlen HS; lia).
    assert (P5 : 0 <= fLz <= 128) by (clear -X4; lia).
    assert (P6 : 2 ^ 40 <= S1z <= 2 ^ 47) by (clear -X5; lia).
    assert (P7 : 20 <= (IEz - Tz) - (Sz - Tz) + fLz) by (clear -X9 HDC; lia).
    rewrite <- Hlen in SPANS.
    unfold kms, mkR_of. fold R. rewrite Hpc0, Hresv0, R1, R6, R7, R9, R10, R16, R19, R21, R22, R29, Hpc. rewrite <- Hlen.
    eapply (blockTM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs Tz Sz IEz fpz fLz S1z Y0z Y1z evz);
      first [ exact TXT | exact P1 | exact P2 | exact SHT | exact P3 | exact P4 | exact DGI | exact P5 | exact SPANS | exact P6
            | exact LOC | exact HEV | exact PR | exact P7 ]. }
  destruct (kit_run BSEGS _ ms Hsvc0 HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  destruct Hpost as (y5 & y6 & y10 & y11 & y12 & y13 & y14 & y15 & y17 & y28 & HTM).
  set (vs := [y5; y6; y10; y11; y12; y13; y14; y15; y17; y28]).
  set (E' := E_of TM_KEYS vs (s_next L) E).
  assert (Hy5 : E' (fv (s_next L) 0) = y5) by (exact (E_of_nth TM_KEYS vs (s_next L) E 0 y5 eq_refl eq_refl)).
  assert (Hy15 : E' (fv (s_next L) 7) = y15) by (exact (E_of_nth TM_KEYS vs (s_next L) E 7 y15 eq_refl eq_refl)).
  assert (Hag : agree (s_next L) E E') by apply E_of_agree.
  unfold state_wf in Hw. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hwr Hwg].
  assert (Hw5 : lwf (s_next L) (rgl L 5) = true) by (exact (regs_wf_n_spec _ _ 31 Hwr 5%nat ltac:(lia))).
  assert (Hw15 : lwf (s_next L) (rgl L 15) = true) by (exact (regs_wf_n_spec _ _ 31 Hwr 15%nat ltac:(lia))).
  assert (E5' : lden E' (rgl L 5) = lden E (rgl L 5)) by (symmetry; exact (lden_agree _ E E' _ Hw5 Hag)).
  assert (E15' : lden E' (rgl L 15) = lden E (rgl L 15)) by (symmetry; exact (lden_agree _ E E' _ Hw15 Hag)).
  assert (COMMON : forall pc1 (msx : machine_state),
     msx = MS (mkR (Z_to_bv 64 46) (getr R 2) (getr R 3) (getr R 4) y5 y6 (Z_to_bv 64 evz) (getr R 8) (Z_to_bv 64 S1z) y10 y11 y12 y13 y14 y15
                   (Z_to_bv 64 (IEz - Sz)) y17 (getr R 18) (Z_to_bv 64 ASAN_B) (getr R 20) (Z_to_bv 64 Sz) (Z_to_bv 64 (Tz + Z.of_nat (length bs)))
                   (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) y28 (Z_to_bv 64 fpz) (getr R 30) (getr R 31))
              (ms_fregs ms) (Z_to_bv 64 pc1) (ms_fcsr ms) None (ms_mem ms) (seg_rom BSEGS) ->
     ms_eqv ms1 (with_rom msx (ms_rom ms)) ->
     isteps BSEGS ms ms1 /\ length vs = length TM_KEYS /\
      ms_mem ms1 = ms_mem ms /\ ms_fcsr ms1 = ms_fcsr ms /\ ms_resv ms1 = ms_resv ms /\ ms_svc_pending ms1 = None /\
      ms_pc_val ms1 = Z_to_bv 64 pc1 /\
      (forall r, ~ In (bv_unsigned r) TM_KEYS -> getr (ms_regs ms1) r = getr (ms_regs ms) r) /\
      (forall i k v, nth_error TM_KEYS i = Some k -> nth_error vs i = Some v -> getr (ms_regs ms1) (Z_to_bv 5 k) = v) /\
      (forall r, reg_get (ms_fregs ms1) r = reg_get (ms_fregs ms) r)).
  { intros pc1 msx -> Heq2. destruct Heq2 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
    split; [exact Hst|]. split; [reflexivity|]. split; [exact E7|]. split; [exact E6|]. split; [rewrite E5, Hresv0; reflexivity|].
    split; [exact E4|]. split; [exact E3|]. split; [|split; [|exact E2]].
    - intros r Hr. rewrite (E1 r). destruct (reg_of_nat r) as (n & -> & Hn). rewrite getr_mkR. rewrite u5 by lia. rewrite Nat2Z.id.
      unfold TM_KEYS in Hr. cbn [In] in Hr. rewrite u5 in Hr by lia.
      do 32 (destruct n as [|n]; [cbn; first [reflexivity | (symmetry; exact R1) | (symmetry; exact R7) | (symmetry; exact R9)
                                              | (symmetry; exact R16) | (symmetry; exact R19) | (symmetry; exact R21)
                                              | (rewrite Hlen; symmetry; exact R22) | (symmetry; exact R29)
                                              | (exfalso; apply Hr; repeat (first [left; reflexivity | right]))]|]).
      lia.
    - intros i k v Hi Hv. rewrite (E1 _).
      destruct i as [|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]; cbn in Hi, Hv;
        first [ (injection Hi as <-; injection Hv as <-; reflexivity) | (destruct i; discriminate) ]. }
  destruct HTM as [(Hms2 & H5 & H15)|(Hms2 & H15 & (d & Hd1 & H5))].
  - exists 0x9c5f8, tm_newf0, nox, ms1, vs. split; [left; reflexivity|].
    destruct (COMMON 0x9c5f8 ms2 Hms2 Heq) as (C1' & C2' & C3' & C4' & C5' & C6' & C7' & C8' & C9' & C10').
    do 9 (split; [assumption|]). fold E'. split; [|split; [constructor | exact C10']].
    unfold tm_newf0. constructor; [|constructor; [|constructor]]; cbn [fact_ok].
    + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy5, E5', H5. unfold R. replace (getr (ms_regs ms) 5) with (lden E (rgl L 5)) by (symmetry; exact (RG 5)).
      rewrite Z.sub_diag. unfold bv_wrap. rewrite Z.mod_0_l by (unfold bv_modulus; lia). lia.
    + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy15, E15', H15. unfold R. replace (getr (ms_regs ms) 15) with (lden E (rgl L 15)) by (symmetry; exact (RG 15)).
      rewrite Z.sub_diag. unfold bv_wrap. rewrite Z.mod_0_l by (unfold bv_modulus; lia). lia.
  - exists 0x9cc68, tm_newf1, nox, ms1, vs. split; [right; left; reflexivity|].
    destruct (COMMON 0x9cc68 ms2 Hms2 Heq) as (C1' & C2' & C3' & C4' & C5' & C6' & C7' & C8' & C9' & C10').
    do 9 (split; [assumption|]). fold E'. split; [|split; [constructor | exact C10']].
    unfold tm_newf1. constructor; [|constructor; [|constructor]]; cbn [fact_ok].
    + rewrite lden_lvar, Hy15. clear -H15. lia.
    + rewrite lden_laddc, lden_lvar, Hy5, H5, !u_Z_to_bv. unfold EXPMAX, EXPMAXz in *. clear -Hd1 HEV. unfold two64.
      rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

Theorem H_TM_ok : hand_okx_fp BSEGS xok_spd H_TM.
Proof. apply hx_okm_fp. exact tm_kit. Qed.

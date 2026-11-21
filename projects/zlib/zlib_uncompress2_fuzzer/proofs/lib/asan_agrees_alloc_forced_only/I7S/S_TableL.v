(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.I7S Require Import SBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.I7S Require Import S_Type S_MatchL S_DistL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Definition L_TAB_LOOP : Z := 87404.
Definition L_TAB_BODY : Z := 88200.
Definition L_LL_BODY : Z := 88332.
Definition L_LL_HEAD : Z := 88380.
Definition L_LL_FILL0 : Z := 88424.
Definition L_LL_FLOOP : Z := 88468.
Definition L_LL_FEND : Z := 88504.
Definition A_ORDER : Z := 67132.

Definition KS_LL : list positive := [2; 3; 4; 5; 9; 10; 11; 12; 20; 21; 22; 23; 26; 27; 30; 32]%positive.
Definition KS_TB : list positive := [2; 3; 4; 5; 9; 10; 11; 12; 20; 21; 22; 23; 26; 30; 32]%positive.
Definition KS_LF : list positive := [2; 3; 4; 5; 9; 10; 11; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 30; 32]%positive.
End FXG.
Ltac keptc_close ::= cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF]; split_conj; try exact I; zreg.
Ltac keptc_chain HK ::= cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF] in HK |- *; destr_conj HK; split_conj; try exact I;
  cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; first [assumption | reflexivity].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Lemma zext32_shift31 : forall x, 0 <= x < 4294967296 ->
  Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) (31 mod 64) = 2 * x.
Proof.
  intros x Hx. change (31 mod 64) with 31. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia_std.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia_std).
  change (2 ^ 32) with (2 * 2 ^ 31). rewrite Z.mul_assoc, Z.div_mul by lia_std. lia_std.
Qed.
Lemma shiftl_1m : forall x, Z.shiftl x (1 mod 64) = 2 * x.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia_std. change (2 ^ (1 mod 64)) with 2. lia_std. Qed.
Lemma land7_range : forall h, 0 <= Z.land h 7 < 8.
Proof. intros. apply land_7. Qed.
Lemma drop3_bound : forall H B, 0 <= H < 2 ^ B -> 3 <= B -> 0 <= H / 2 ^ 3 < 2 ^ (B - 3).
Proof. intros H B HH HB. apply hold_shr_bound; lia_std. Qed.

Lemma land_m32 : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x Hx. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia_std. apply Z.mod_small. exact Hx. Qed.

Lemma order_f_lt : forall i, 0 <= i < 19 -> 0 <= order_f i < 65536.
Proof. intros i Hi. pose proof (order_f_range i Hi). lia_std. Qed.

End FXG.
Ltac zside1 := first [reflexivity | exact I | zlia].
Ltac tstoreP fd HP HPres :=
  let pc := zpc in
  fd pc ltac:(fun F E D =>
    lazymatch type of D with
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply zu_sb; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply zu_sh; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply zu_sw; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply zu_sd; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    end);
  lazymatch goal with
  | |- realizes _ (zcfg _ _ _ (wbytes ?M (w64 ?a) (Z_to_le_bytes ?kk ?v)) _) _ =>
      (let HP' := fresh in pose proof (HPres M _ a v HP ltac:(zside1) ltac:(zside1)) as HP'; clear HP; rename HP' into HP);
      zmem_post_arr; zmem_post
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.
End FXG.
Ltac tstore_arrP2 fd Ha i HP HPres :=
  lazymatch type of Ha with
  | mem_arr ?k ?segs ?M ?base ?n ?f =>
      let pc := zpc in
      fd pc ltac:(fun F E D =>
        lazymatch type of D with
        | decode_any _ = Some (Store SZ1 _ _ _, _) =>
            eapply zu_sb; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        | decode_any _ = Some (Store SZ2 _ _ _, _) =>
            eapply zu_sh; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        | decode_any _ = Some (Store SZ4 _ _ _, _) =>
            eapply zu_sw; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        end);
      lazymatch goal with
      | |- realizes _ (zcfg _ _ _ (wbytes M (w64 ?a) (Z_to_le_bytes ?kk ?v)) _) _ =>
          apply (mem_arr_upd segs k M base n f a i v) in Ha; [| zlia | zlia];
          (let kn := eval cbv in (Z.to_nat k) in change (Z.to_nat k) with kn in Ha);
          (let HP' := fresh in pose proof (HPres M _ a v HP ltac:(zside1) ltac:(zside1)) as HP'; clear HP; rename HP' into HP);
          repeat match goal with
          | H : mem_arr ?k' segs M ?base' ?n' ?f' |- _ =>
              first [ apply (mem_arr_frame segs k' M base' n' f' a (Z_to_le_bytes kk v)) in H; [|unfold zdisj; zlen_norm; zlia]
                    | idtac "tstore_arrP2: mem_arr fact dropped at array store" a; clear H ]
          end;
          zmem_post
      end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.
End FXG.
Ltac keptc_trans :=
  repeat match goal with H : keptc _ _ _ _ |- _ => cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF] in H; destr_conj H end;
  cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF]; split_conj; try exact I;
  rewrite ?zget_zupd in *; cbv [zget_l] in *; cbn [alookup Pos.eqb] in *;
  first [ assumption | reflexivity
        | etransitivity; [eassumption|]; first [assumption | reflexivity | symmetry; assumption] ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Lemma lenlens_loop : forall (N : nat) (P : Z -> mem -> Prop) Rb l M MD T
    (p q n ncode j ci B H : Z) (fin lf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kS0 = p -> zget_l Rb l kS6 = p + 168 ->
  zget_l Rb l kA3 = A_ORDER + 2 * j -> zget_l Rb l kA4 = ncode - j -> zget_l Rb l kA5 = j + 1 -> zget_l Rb l kA2 = ncode ->
  zget_l Rb l kS8 = B -> zget_l Rb l kS7 = H -> zget_l Rb l kS2 = n - ci -> zget_l Rb l kS11 = q + ci ->
  ncode - j <= Z.of_nat N -> 0 <= j -> j < ncode -> ncode <= 19 ->
  0 <= ci -> ci <= n -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) -> ZSEP (p + 7176 <= 65536 \/ 135168 <= p) ->
  mem_wr R_segs M p 7176 ->
  mem_arr 1 R_segs M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 2 R_segs M A_ORDER 19 order_f ->
  mem_arr 2 R_segs M (p + 168) 320 lf -> (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) ->
  (forall i, 0 <= i < j -> lf (order_f i) <= 7) ->
  P j M ->
  (forall M' jo (a v : Z), P jo M' -> a = p + 156 -> 0 <= v < 4294967296 -> P v (wbytes M' (w64 a) (Z_to_le_bytes 4 v))) ->
  (forall M' jo (a v : Z), P jo M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (forall R' M' (j' B' H' : Z) (lf' : Z -> Z),
     zget R' kS8 = B' -> zget R' kS7 = H' -> zget R' kS2 = 0 -> zget R' kS11 = q + n ->
     j <= j' -> j' < ncode -> 0 <= B' -> B' < 3 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * n ->
     B' + 3 * (j' - j) = 8 * (n - ci) + B ->
     mem_wr R_segs M' p 7176 -> mem_arr 1 R_segs M' q n fin -> mem_arr 2 R_segs M' A_ORDER 19 order_f ->
     mem_arr 2 R_segs M' (p + 168) 320 lf' -> (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) ->
     (forall i, 0 <= i < j' -> lf' (order_f i) <= 7) -> P j' M' ->
     keptc Rb l R' KS_LL ->
     realizes R_segs (zcfg R_segs L_LEAVE_LD (zupd R' []) M' MD) T) ->
  (forall R' M' (ci' B' H' : Z) (lf' : Z -> Z),
     zget R' kS8 = B' -> zget R' kS7 = H' -> zget R' kS2 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kA2 = ncode ->
     zget R' kS0 = p -> zget R' kS6 = p + 168 ->
     ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' + 3 * (ncode - j) = 8 * (n - ci) + B ->
     mem_wr R_segs M' p 7176 -> mem_arr 1 R_segs M' q n fin -> mem_arr 2 R_segs M' A_ORDER 19 order_f ->
     mem_arr 2 R_segs M' (p + 168) 320 lf' -> (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) ->
     (forall i, 0 <= i < ncode -> lf' (order_f i) <= 7) -> P ncode M' ->
     keptc Rb l R' KS_LL ->
     realizes R_segs (zcfg R_segs L_LL_FILL0 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_LL_HEAD (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T p q n ncode j ci B H fin lf Hh L26 L2 La3 La4 La5 La2 Ls0 Ls7 Ls8 Ls10
    HN Hj0 Hj1 Hnc Hc0 Hc1 HB0 HB1 HH0 HH1 HBc Hq1 Hn26 Hq2 Hp1 Hp2 SPQ SPR Wp Hin Rfin Hord Hlens Rlf Hlf7 HP HPa HPb KX KD; [lia|].
  zkeys. unfold L_LL_HEAD, L_LL_FILL0, L_LEAVE_LD, A_ORDER in *. pose proof two64_eq as TW64.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  zstep Rfd.
  assert (BODY : forall RJ (cib Hb Bb : Z),
    zget RJ kS0 = p -> zget RJ kS6 = p + 168 ->
    zget RJ kA3 = 67132 + 2 * j -> zget RJ kA4 = ncode - j -> zget RJ kA5 = j + 1 -> zget RJ kA2 = ncode ->
    zget RJ kS8 = Bb -> zget RJ kS7 = Hb -> zget RJ kS2 = n - cib -> zget RJ kS11 = q + cib ->
    ci <= cib -> cib <= n -> 3 <= Bb -> Bb <= 40 -> 0 <= Hb -> Hb < 2 ^ Bb -> Bb <= 8 * cib ->
    8 * (n - cib) + Bb = 8 * (n - ci) + B ->
    keptc Rb l RJ KS_LL ->
    realizes R_segs (zcfg R_segs L_LL_BODY (zupd RJ []) M MD) T).
  { intros RJ cib Hb Bb G26 G2 G14 G15 G16 G13 G9 G24 G25 G27 X1 X2 X3 X4 X5 X6 X7 X8 HK.
    unfold L_LL_BODY. zkeys.
    pose proof (pow2_48 Bb ltac:(lia)) as HPBb.
    pose proof (land7_range Hb) as Hv.
    pose proof (order_f_range j ltac:(lia)) as Ho. pose proof (order_f_lt j ltac:(lia)) as Ho2.
    zstep Rfd.
    tstoreP Rfd HP HPa.
    tstep Rfd.
    zstep Rfd.
    zsetreg (Hb / 2 ^ 3) ltac:(symmetry; apply (srl_hold Hb Bb 3); lia).
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (2 * order_f j) ltac:(rewrite shiftl_1m; reflexivity).
    zstep Rfd.
    tstore_arrP2 Rfd Hlens (order_f j) HP HPb.
    zstep Rfd.
    pose proof (drop3_bound Hb Bb ltac:(lia) ltac:(lia)) as Hd3.
    assert (Rlf1 : forall i, 0 <= i < 320 -> 0 <= zfupd lf (order_f j) (Z.land Hb 7) i < 65536).
    { intros i Hi. unfold zfupd. destruct (Z.eqb_spec i (order_f j)); [lia | apply Rlf; lia]. }
    assert (Hlf7' : forall i, 0 <= i < j + 1 -> zfupd lf (order_f j) (Z.land Hb 7) (order_f i) <= 7).
    { intros i Hi. unfold zfupd. destruct (Z.eqb_spec (order_f i) (order_f j)); [lia|]. apply Hlf7.
      destruct (Z.eq_dec i j); [subst; congruence | lia]. }
    destruct (Z.eq_dec (ncode - j) 1) as [Hlast | Hmore].
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KD Rx Mx cib (Bb - 3) (Hb / 2 ^ 3) (zfupd lf (order_f j) (Z.land Hb 7))) end;
        try zreg; try assumption; try lia.
      + intros i Hi. apply Hlf7'. lia.
      + replace ncode with (j + 1) by lia. exact HP.
      + keptc_trans.
    - zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (IH P Rx lx Mx MD T p q n ncode (j + 1) cib (Bb - 3) (Hb / 2 ^ 3) fin (zfupd lf (order_f j) (Z.land Hb 7)) Hh) end;
        try zreg; try assumption; try lia.
      + intros R' M' j' B' H' lf'. intros. eapply (KX R' M' j' B' H' lf'); try eassumption; try lia.
        keptc_trans.
      + intros R' M' ci' B' H' lf'. intros. eapply (KD R' M' ci' B' H' lf'); try eassumption; try lia.
        keptc_trans. }
  destruct (Z_lt_dec 2 B) as [HB3 | HB3].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (BODY Rx ci H B) end; try zreg; try lia. keptc_close.
  - zbr Rfd false.
    destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
    + zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KX Rx Mx j B H lf) end;
        try zreg; try assumption; try lia. keptc_close.
    + zbr Rfd true.
      pose proof (Rfin ci ltac:(lia)) as Rb1.
      tld1 Hin ci Rfin.
      tstep1 Rfd.
      zstep Rfd.
      zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
      pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hpl0 Hpl1].
      zstep Rfd.
      zsetreg (B + 8) ltac:(symmetry; apply lor8_small; lia).
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (BODY Rx (ci + 1) (fin ci * 2 ^ B + H) (B + 8)) end;
        try zreg; try lia.
      keptc_close.
Qed.

Lemma fill_loop : forall (N : nat) (P : Z -> mem -> Prop) Rb l M MD T (p j jo : Z) (lf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kS6 = p + 168 -> zget_l Rb l kA0 = 4294967295 -> zget_l Rb l kA1 = A_ORDER + 2 * j -> zget_l Rb l kA5 = j + 1 ->
  19 - j <= Z.of_nat N -> 0 <= j -> j < 19 ->
  0 < p -> p + 7176 <= 140737488355328 -> ZSEP (p + 7176 <= 65536 \/ 135168 <= p) ->
  mem_wr R_segs M p 7176 -> mem_arr 2 R_segs M A_ORDER 19 order_f ->
  mem_arr 2 R_segs M (p + 168) 320 lf -> (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) ->
  (forall i, 0 <= i < j -> lf (order_f i) <= 7) ->
  P jo M ->
  (forall M' jo' (a v : Z), P jo' M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo' (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (forall R' M' (lf' : Z -> Z),
     zget R' kA2 = 19 ->
     mem_wr R_segs M' p 7176 -> mem_arr 2 R_segs M' A_ORDER 19 order_f ->
     mem_arr 2 R_segs M' (p + 168) 320 lf' -> (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) ->
     (forall i, 0 <= i < 19 -> lf' (order_f i) <= 7) -> P jo M' ->
     keptc Rb l R' KS_LF ->
     realizes R_segs (zcfg R_segs L_LL_FEND (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_LL_FLOOP (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T p j jo lf Hh L2 La0 La1 La5 HN Hj0 Hj1 Hp1 Hp2 SPR Wp Hord Hlens Rlf Hlf7 HP HPb K; [lia|].
  zkeys. unfold L_LL_FLOOP, L_LL_FEND, A_ORDER in *. pose proof two64_eq as TW64.
  pose proof (order_f_range j ltac:(lia)) as Ho. pose proof (order_f_lt j ltac:(lia)) as Ho2.
  assert (Rord : forall i, 0 <= i < 19 -> 0 <= order_f i < 65536) by (intros; apply order_f_lt; lia).
  tstep Rfd.
  zstep Rfd.
  zsetreg (j + 1) ltac:(symmetry; apply land_m32; lia).
  zstep Rfd.
  zstep Rfd.
  zsetreg (2 * order_f j) ltac:(rewrite shiftl_1m; reflexivity).
  zstep Rfd.
  tstore_arrP2 Rfd Hlens (order_f j) HP HPb.
  zstep Rfd.
  zstep Rfd.
  assert (Rlf1 : forall i, 0 <= i < 320 -> 0 <= zfupd lf (order_f j) 0 i < 65536).
  { intros i Hi. unfold zfupd. destruct (Z.eqb_spec i (order_f j)); [lia | apply Rlf; lia]. }
  assert (Hlf7' : forall i, 0 <= i < j + 1 -> zfupd lf (order_f j) 0 (order_f i) <= 7).
  { intros i Hi. unfold zfupd. destruct (Z.eqb_spec (order_f i) (order_f j)); [lia|]. apply Hlf7.
    destruct (Z.eq_dec i j); [subst; congruence | lia]. }
  destruct (Z.eq_dec j 18) as [Hlast | Hmore].
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx (zfupd lf (order_f j) 0)) end;
      try zreg; try assumption.
    + intros i Hi. apply Hlf7'. lia.
    + keptc_close.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH P Rx lx Mx MD T p (j + 1) jo (zfupd lf (order_f j) 0) Hh) end;
      try zreg; try assumption; try lia.
Qed.

Lemma table_loop : forall (k : nat) Rb l M MD T (q n cinj holdj j : Z) (fin : Z -> Z),
  m_halted MD = None -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  14 - 8 * Z.of_nat k <= j < 22 - 8 * Z.of_nat k -> (1 <= k <= 2)%nat -> 0 <= j ->
  0 <= cinj <= n -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 ->
  zget_l Rb l kS8 = j -> zget_l Rb l kA2 = j ->
  zget_l Rb l kS11 = q + cinj -> zget_l Rb l kS2 = n - cinj -> zget_l Rb l kS7 = holdj ->
  mem_arr 1 R_segs M q n fin ->
  (forall R' hold' j',
     zget R' kS11 = q + n -> zget R' kS2 = 0 -> zget R' kS7 = hold' -> zget R' kS8 = j' ->
     j' = j + 8 * (n - cinj) -> 0 <= hold' < 2 ^ j' -> n - cinj < Z.of_nat k ->
     keptc Rb l R' KS_TB ->
     realizes R_segs (zcfg R_segs L_LEAVE_LD (zupd R' []) M MD) T) ->
  (forall R' hold' j',
     zget R' kS10 = q + cinj + Z.of_nat k -> zget R' kS11 = q + cinj + Z.of_nat k ->
     zget R' kS2 = n - cinj - Z.of_nat k -> zget R' kS7 = hold' -> zget R' kS8 = j' ->
     j' = j + 8 * Z.of_nat k -> 0 <= hold' < 2 ^ j' -> Z.of_nat k <= n - cinj ->
     keptc Rb l R' KS_TB ->
     realizes R_segs (zcfg R_segs L_TAB_BODY (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_TAB_LOOP (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros Rb l M MD T q n cinj holdj j fin Hh Hfin Hj Hk Hj0 Hc Hhj Hjc Hq1 Hn26 Hq2 L9 L13 L27 L25 L24 Hin KLV KDN; [lia|].
  zkeys. unfold L_TAB_LOOP, L_TAB_BODY, L_LEAVE_LD in *. pose proof two64_eq as TW64.
  assert (Hj40 : 2 ^ j <= 2 ^ 21) by (apply Z.pow_le_mono_r; lia). change (2 ^ 21) with 2097152 in Hj40.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  -
    zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KLV R' holdj j) end; try zreg; try lia.
    all: first [ keptc_close | replace (j + 8 * (n - cinj)) with j by lia; lia ].
  - zbr Rfd true.
    pose proof (Hfin cinj ltac:(lia)) as Hb0.
    zstep Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (fin cinj * 2 ^ j) ltac:(rewrite (Z.mod_small j) by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (pullbyte_bound holdj j (fin cinj) ltac:(lia) Hhj Hb0) as Hpb.
    destruct k as [|k'].
    +
      zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KDN R' (fin cinj * 2 ^ j + holdj) (j + 8)) end; try zreg; try lia.
      keptc_close.
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') _ _) _ =>
        eapply (IH R' l' M MD T q n (cinj + 1) (fin cinj * 2 ^ j + holdj) (j + 8) fin Hh Hfin) end;
        [ lia | lia | lia | lia | lia | lia | lia | lia | lia | zreg .. | exact Hin | | ].
      * intros R' hold' j'. intros. eapply KLV; try eassumption; try lia.
      * intros R' hold' j'. intros. eapply KDN; try eassumption; try lia.
Qed.
End FXG.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InftreesCoverage InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require Import SBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require Import S_Type S_MatchL S_DistL S_TableL S_Table S_ClDefs S_CodelensL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition KS_CR : list positive := [2; 3; 4; 5; 9; 10; 11; 12; 13; 15; 16; 17; 20; 21; 22; 23; 26; 32]%positive.
Ltac keptc_closeR := cbv [keptc KS_CR KS_CP KS_CD KS_CF KS_CX]; split_conj; try exact I; zreg.
Ltac kopen HK := cbv [keptc KS_CR KS_CP KS_CD KS_CF KS_CX] in HK; destr_conj HK; zimps.
Ltac keptc_transC :=
  repeat match goal with H : keptc _ _ _ _ |- _ => cbv [keptc KS_CR KS_CP KS_CD KS_CF KS_CX] in H; destr_conj H end;
  cbv [keptc KS_CR KS_CP KS_CD KS_CF KS_CX]; split_conj; try exact I;
  rewrite ?zget_zupd in *; cbv [zget_l] in *; cbn [alookup Pos.eqb] in *;
  first [ assumption | reflexivity
        | etransitivity; [eassumption|]; first [assumption | reflexivity | symmetry; assumption] ].
Ltac kgoal := first [ zreg | assumption | OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ITac.zarith_goal; lia | etransitivity; [eassumption | solve [lia | symmetry; assumption]] | keptc_transC ].

Lemma cl_res {RCa1 : RunCtx}  : forall (P : Z -> mem -> Prop) Rb l M MD T (u p q n nlen nd lb lm nx c0 b0 j ci B H : Z) (fin cf lf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + -224 -> zget_l Rb l kS0 = p -> zget_l Rb l kS6 = p + 168 ->
  zget_l Rb l kA2 = nlen -> zget_l Rb l kA4 = nd -> zget_l Rb l kA5 = p + 1384 -> zget_l Rb l kA6 = lm ->
  zget_l Rb l kA3 = j -> zget_l Rb l kS11 = q + ci -> zget_l Rb l kS2 = n - ci -> zget_l Rb l kA7 = B ->
  zget_l Rb l kS8 = b0 -> zget_l Rb l kS7 = H ->
  zget_l Rb l kT0 = code_bits (cf (Z.land lm H)) -> zget_l Rb l kT3 = Z.land lm H ->
  zget_l Rb l kT4 = 30 -> zget_l Rb l kS9 = 67008 ->
  0 <= j -> j < nd -> nd <= 316 -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  code_bits (cf (Z.land lm H)) <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  lm = 2 ^ lb - 1 -> 1 <= lb -> lb <= 15 -> 0 <= nx -> nx <= 1444 -> tab_ok CODES (rdc cf (CDyn 0)) lb nx = true ->
  (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) -> (forall i, 0 <= i < j -> lf i <= 15) ->
  1 <= q -> 0 <= n -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 -> p + 8200 <= u -> u + 208 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 cf -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf ->
  P j M ->
  (forall M' (a v : Z), P j M' -> a = p + 156 -> 0 <= v < 4294967296 -> P v (wbytes M' (w64 a) (Z_to_le_bytes 4 v))) ->
  (forall M' (jo a v : Z), P jo M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (forall R' (ci' B' H' : Z),
     zget R' kS7 = H' -> zget R' kS2 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kA7 = B' -> zget R' kS8 = b0 ->
     ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ci) + B ->
     keptc Rb l R' KS_CR ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_A7 (zupd R' []) M MD) T) ->
  (forall (pc : Z) R' (ci' B' H' : Z),
     (pc = L_BADREP0 \/ pc = L_BADREP) ->
     zget R' kS7 = H' -> zget R' kS2 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kS10 = q + ci' -> zget R' kS8 = B' ->
     zget R' kT4 = 30 -> zget R' kS9 = 67008 ->
     ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ci) + B ->
     keptc Rb l R' KS_CR ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd R' []) M MD) T) ->
  (forall R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     zget R' kA3 = j' -> zget R' kS7 = H' -> zget R' kS2 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kS8 = B' ->
     zget R' kT4 = 30 -> zget R' kS9 = 67008 ->
     j < j' -> j' <= nd -> ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' + 1 <= 8 * (n - ci) + B ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> P j' M' ->
     keptc Rb l R' KS_CR ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_NEXT (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_RES (zupd Rb l) M MD) T.
Proof.
  intros P Rb l M MD T u p q n nlen nd lb lm nx c0 b0 j ci B H fin cf lf Hh
    Lsp Ls9 Lra La2 La4 La5 La6 La3 Ls10 Ls8 La7 Ls0 Ls7 Lt0 Lt3 Lt4 Lt5
    Hj0 Hj1 Hnd Hc0 Hc1 Hc2 Hb0 HB Hbe HB40 HH1 HH2 HBc Hdm Hlb1 Hlb2 Hnx1 Hnx2 TOK Rlf Hlf15
    Hq1 Hn0 Hn26 Hq2 Hp1 Hp2 Hpu Hu2 SPQ Wp Hin Rfin Hcodes Hlens HP HPa HPb KX KB KN.
  zkeys. unfold L_CL_RES, L_CL_NEXT, L_LEAVE_A7, L_BADREP0, L_BADREP, L_CL_P17, L_CL_X17, L_CL_P16, L_CL_X16, L_CL_P18, L_CL_X18,
    L_CL_CHK, L_CL_FILL, L_CL_FILLX in *.
  pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPlb.
  pose proof (land_mask_l H lb ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (ctab_bits cf lb nx (Z.land lm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits0 Hpow].
  set (e := cf (Z.land lm H)) in *.
  pose proof (code_bits_range e) as Rbe. pose proof (code_val_range e) as Rve.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  zstep Rfd.
  zsetreg (4 * Z.land lm H) ltac:(symmetry; apply shiftl_2).
  zstep Rfd.
  tld4_val Hcodes (Z.land lm H).
  fold e.
  zstep Rfd.
  assert (CHK : forall RC (ci' B' H' copy len : Z),
    zget RC kA7 = copy -> zget RC kT1 = len -> zget RC kS7 = H' -> zget RC kS8 = B' ->
    zget RC kS2 = n - ci' -> zget RC kS11 = q + ci' -> zget RC kS10 = q + ci' -> zget RC kA3 = j ->
    zget RC kT4 = 30 -> zget RC kS9 = 67008 -> zget RC kA4 = nd -> zget RC kS0 = p -> zget RC kS6 = p + 168 ->
    3 <= copy -> copy <= 138 -> 0 <= len -> len <= 15 ->
    ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
    8 * (n - ci') + B' + 1 <= 8 * (n - ci) + B ->
    keptc Rb l RC KS_CR ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 89160 (zupd RC []) M MD) T).
  { intros RC ci' B' H' copy len G18 G7 G24 G9 G25 G27 G28 G14 G30 G31 G15 G26 G2 Hcp1 Hcp2 Hln1 Hln2 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 HK.
    zkeys.
    tstep1 Rfd.
    destruct (Z_lt_dec nd (copy + j)) as [Hover | Hfit].
    - zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KB 93384 Rx ci' B' H') end;
        try (right; reflexivity). all: kgoal.
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        pose proof (fun M1 a1 v1 => HPb M1 j a1 v1) as HPbj;
        eapply (cl_fill (Z.to_nat 138) (P j) Rx lx Mx MD T u p q n j (copy + j) len fin cf lf Hh) end;
        try zreg; try lia; try eassumption.
      intros R' M' lf' G14' Wp' Hin' Hcodes' Hlens' HP' Hfill Hkeep HK'. unfold L_CL_FILLX. zimps. kopen HK'. zkeys.
      tstorePc Rfd HP' HPa.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KN Rx Mx (copy + j) ci' B' H' lf') end; try eassumption.
      all: first [ intros i Hi;
                   first [ destruct (Z_lt_dec i j) as [Hl|Hr]; [rewrite Hkeep by lia; apply Rlf; lia |];
                           destruct (Z_lt_dec i (copy + j)) as [Hm|Hx]; [rewrite Hfill by lia; lia | rewrite Hkeep by lia; apply Rlf; lia]
                         | destruct (Z_lt_dec i j) as [Hl|Hr]; [rewrite Hkeep by lia; apply Hlf15; lia | rewrite Hfill by lia; lia] ]
                 | kgoal ]. }
  destruct (Z_lt_dec 15 (code_val e)) as [Hrep | Hlit].
  2: {
    zbr Rfd false.
    zstep Rfd.
    zsetreg (H / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold H B); lia).
    pose proof (hold_shr_bound H B (code_bits e) ltac:(lia) ltac:(lia)) as HH'.
    tstep1 Rfd.
    zstep Rfd.
    tstep1 Rfd.
    tstorePc Rfd HP HPa.
    zstep Rfd.
    zsetreg (2 * j) ltac:(symmetry; apply zext32_shift31; lia).
    zstep Rfd.
    pose proof (fun M1 a1 v1 => HPb M1 (j + 1) a1 v1) as HPb1.
    tstore_arrPc Rfd Hlens j HP HPb1.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KN Rx Mx (j + 1) ci (B - code_bits e) (H / 2 ^ code_bits e) (zfupd lf j (code_val e))) end;
      try eassumption.
    all: first [ intros i Hi; unfold zfupd; destruct (Z.eqb_spec i j); [lia | first [apply Rlf; lia | apply Hlf15; lia]]
               | kgoal ]. }
  zbr Rfd true.
  zstep Rfd.
  destruct (Z.eq_dec (code_val e) 16) as [E16 | N16].
  -
    zbr Rfd true.
    zstep Rfd.
    assert (X16 : forall RX (ci' B' H' : Z),
      zget RX kS2 = n - ci' -> zget RX kS11 = q + ci' -> zget RX kS10 = q + ci' -> zget RX kA7 = B' -> zget RX kS7 = H' ->
      zget RX kT0 = code_bits e -> zget RX kA3 = j -> zget RX kS6 = p + 168 -> zget RX kT4 = 30 -> zget RX kS9 = 67008 ->
      zget RX kS0 = p -> zget RX kA4 = nd ->
      ci <= ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> code_bits e + 2 <= B' -> B' <= 40 ->
      0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
      keptc Rb l RX KS_CR ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 89072 (zupd RX []) M MD) T).
    { intros RX ci' B' H' G25 G27 G28 G18 G24 G6 G14 G2 G30 G31 G26 G15 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 HK. kopen HK. zkeys.
      pose proof (pow2_48 B' ltac:(lia)) as HPB'.
      zstep Rfd.
      zsetreg (H' / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold H' B'); lia).
      pose proof (hold_shr_bound H' B' (code_bits e) ltac:(lia) ltac:(lia)) as HS2.
      pose proof (pow2_48 (B' - code_bits e) ltac:(lia)) as HPd.
      set (H2 := H' / 2 ^ code_bits e) in *.
      tstep1 Rfd.
      destruct (Z.eq_dec j 0) as [Hj | Hj].
      +
        zbr Rfd false.
        zstep Rfd.
        pose proof (pow2_le (B' - code_bits e) B' ltac:(lia)) as HP2.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KB 93468 Rx ci' (B' - code_bits e) H2) end;
          try (left; reflexivity). all: kgoal.
      + zbr Rfd true.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zsetreg (2 * (j - 1)) ltac:(symmetry; apply zext32_shift31; lia).
        zstep Rfd.
        pose proof (Rlf (j - 1) ltac:(lia)) as Rlj. pose proof (Hlf15 (j - 1) ltac:(lia)) as Hlj.
        tstep Rfd.
        zstep Rfd.
        pose proof (land3_range H2) as Hcp.
        zstep Rfd.
        zstep Rfd.
        zsetreg (H2 / 2 ^ 2) ltac:(rewrite (Z.mod_small H2) by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
        pose proof (hold_shr_bound H2 (B' - code_bits e) 2 ltac:(lia) ltac:(lia)) as HS3.
        tstep1 Rfd.
        zstep Rfd.
        pose proof (pow2_le (B' - code_bits e - 2) (B' - code_bits e) ltac:(lia)) as HP3.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
          eapply (CHK Rx ci' (B' - code_bits e - 2) (H2 / 2 ^ 2) (Z.land H2 3 + 3) (lf (j - 1))) end.
        all: kgoal. }
    destruct (Z_lt_dec B (code_bits e + 2)) as [Hneed | Hhave].
    + zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (cl_pull (S (Z.to_nat (n - ci))) 88924 89072 Rx lx Mx MD T q n (code_bits e + 2) c0 b0 ci B H fin
                  ltac:(right; left; split; reflexivity) Hh) end;
        try zreg; try lia; try eassumption.
      * intros R' H' G24 G25 G27 G18 X1 X2 X3 X4 HK. zimps. kopen HK.
        eapply (KX R' n (b0 + 8 * (n - c0)) H'). all: kgoal.
      * intros R' ci' B' H' G25 G27 G28 G18 G8 G24 X1 X2 X3 X4 X5 X6 X7 X8 HK. zimps. kopen HK.
        eapply (X16 R' ci' B' H'). all: kgoal.
    + zbr Rfd true.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (X16 Rx ci B H) end. all: kgoal.
  - zbr Rfd false.
    zstep Rfd.
    assert (X1718 : forall (pcx k base : Z) RX (ci' B' H' : Z),
      ((pcx = 89036 /\ k = 3 /\ base = 3) \/ (pcx = 89132 /\ k = 7 /\ base = 11)) ->
      zget RX kS2 = n - ci' -> zget RX kS11 = q + ci' -> zget RX kS10 = q + ci' -> zget RX kA7 = B' -> zget RX kS7 = H' ->
      zget RX kT0 = code_bits e -> zget RX kA3 = j -> zget RX kS6 = p + 168 -> zget RX kT4 = 30 -> zget RX kS9 = 67008 ->
      zget RX kS0 = p -> zget RX kA4 = nd ->
      ci <= ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> code_bits e + k <= B' -> B' <= 40 ->
      0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
      keptc Rb l RX KS_CR ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pcx (zupd RX []) M MD) T).
    { intros pcx k base RX ci' B' H' Hpcx G25 G27 G28 G18 G24 G6 G14 G2 G30 G31 G26 G15 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 HK. kopen HK. zkeys.
      pose proof (pow2_48 B' ltac:(lia)) as HPB'.
      destruct Hpcx as [(-> & -> & ->) | (-> & -> & ->)].
      - zstep Rfd.
        zstep Rfd.
        zsetreg (H' / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold H' B'); lia).
        pose proof (hold_shr_bound H' B' (code_bits e) ltac:(lia) ltac:(lia)) as HS2.
        pose proof (pow2_48 (B' - code_bits e) ltac:(lia)) as HPd.
        set (H2 := H' / 2 ^ code_bits e) in *.
        tstep1 Rfd.
        zstep Rfd.
        pose proof (land7_range' H2) as Hcp.
        zstep Rfd.
        zsetreg (H2 / 2 ^ 3) ltac:(rewrite (Z.mod_small H2) by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
        pose proof (hold_shr_bound H2 (B' - code_bits e) 3 ltac:(lia) ltac:(lia)) as HS3.
        zstep Rfd.
        tstep1 Rfd.
        zstep Rfd.
        pose proof (pow2_le (B' - code_bits e - 3) (B' - code_bits e) ltac:(lia)) as HP3.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
          eapply (CHK Rx ci' (B' - code_bits e - 3) (H2 / 2 ^ 3) (Z.land H2 7 + 3) 0) end.
        all: kgoal.
      - zstep Rfd.
        zstep Rfd.
        zsetreg (H' / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold H' B'); lia).
        pose proof (hold_shr_bound H' B' (code_bits e) ltac:(lia) ltac:(lia)) as HS2.
        pose proof (pow2_48 (B' - code_bits e) ltac:(lia)) as HPd.
        set (H2 := H' / 2 ^ code_bits e) in *.
        tstep1 Rfd.
        zstep Rfd.
        pose proof (land127_range H2) as Hcp.
        zstep Rfd.
        zsetreg (H2 / 2 ^ 7) ltac:(rewrite (Z.mod_small H2) by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
        pose proof (hold_shr_bound H2 (B' - code_bits e) 7 ltac:(lia) ltac:(lia)) as HS3.
        zstep Rfd.
        tstep1 Rfd.
        pose proof (pow2_le (B' - code_bits e - 7) (B' - code_bits e) ltac:(lia)) as HP3.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
          eapply (CHK Rx ci' (B' - code_bits e - 7) (H2 / 2 ^ 7) (Z.land H2 127 + 11) 0) end.
        all: kgoal. }
    destruct (Z.eq_dec (code_val e) 17) as [E17 | N17].
    +
      zbr Rfd false.
      zstep Rfd.
      destruct (Z_lt_dec B (code_bits e + 3)) as [Hneed | Hhave].
      * zbr Rfd false.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (cl_pull (S (Z.to_nat (n - ci))) 88864 89036 Rx lx Mx MD T q n (code_bits e + 3) c0 b0 ci B H fin
                    ltac:(left; split; reflexivity) Hh) end;
          try zreg; try lia; try eassumption.
        -- intros R' H' G24 G25 G27 G18 X1 X2 X3 X4 HK. zimps. kopen HK.
           eapply (KX R' n (b0 + 8 * (n - c0)) H'). all: kgoal.
        -- intros R' ci' B' H' G25 G27 G28 G18 G8 G24 X1 X2 X3 X4 X5 X6 X7 X8 HK. zimps. kopen HK.
           eapply (X1718 89036 3 3 R' ci' B' H'); try (left; split_conj; reflexivity). all: kgoal.
      * zbr Rfd true.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (X1718 89036 3 3 Rx ci B H) end;
          try (left; split_conj; reflexivity). all: kgoal.
    +
      zbr Rfd true.
      zstep Rfd.
      destruct (Z_lt_dec B (code_bits e + 7)) as [Hneed | Hhave].
      * zbr Rfd false.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (cl_pull (S (Z.to_nat (n - ci))) 88984 89132 Rx lx Mx MD T q n (code_bits e + 7) c0 b0 ci B H fin
                    ltac:(right; right; split; reflexivity) Hh) end;
          try zreg; try lia; try eassumption.
        -- intros R' H' G24 G25 G27 G18 X1 X2 X3 X4 HK. zimps. kopen HK.
           eapply (KX R' n (b0 + 8 * (n - c0)) H'). all: kgoal.
        -- intros R' ci' B' H' G25 G27 G28 G18 G8 G24 X1 X2 X3 X4 X5 X6 X7 X8 HK. zimps. kopen HK.
           eapply (X1718 89132 7 11 R' ci' B' H'); try (right; split_conj; reflexivity). all: kgoal.
      * zbr Rfd true.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (X1718 89132 7 11 Rx ci B H) end;
          try (right; split_conj; reflexivity). all: kgoal.
Qed.

Lemma cl_loop {RCa1 : RunCtx}  : forall (N : nat) (P : Z -> mem -> Prop) Rb l M MD T (u p q n nlen nd lb lm nx ce Be j ci B H : Z) (fin cf lf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + -224 -> zget_l Rb l kS0 = p -> zget_l Rb l kS6 = p + 168 ->
  zget_l Rb l kA2 = nlen -> zget_l Rb l kA4 = nd -> zget_l Rb l kA5 = p + 1384 -> zget_l Rb l kA6 = lm ->
  zget_l Rb l kA3 = j -> zget_l Rb l kS11 = q + ci -> zget_l Rb l kT2 = q + ci -> zget_l Rb l kS2 = n - ci -> zget_l Rb l kT1 = n - ci ->
  zget_l Rb l kS8 = B -> zget_l Rb l kS7 = H -> zget_l Rb l kT4 = 30 -> zget_l Rb l kS9 = 67008 ->
  nd - j <= Z.of_nat N -> 0 <= j -> j < nd -> nd <= 316 ->
  ce <= ci -> ci <= n -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci -> 8 * (n - ci) + B <= 8 * (n - ce) + Be ->
  lm = 2 ^ lb - 1 -> 1 <= lb -> lb <= 15 -> 0 <= nx -> nx <= 1444 -> tab_ok CODES (rdc cf (CDyn 0)) lb nx = true ->
  (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) -> (forall i, 0 <= i < j -> lf i <= 15) ->
  1 <= q -> 0 <= n -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 -> p + 8200 <= u -> u + 208 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 cf -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf ->
  P j M ->
  (forall M' (jo a v : Z), P jo M' -> a = p + 156 -> 0 <= v < 4294967296 -> P v (wbytes M' (w64 a) (Z_to_le_bytes 4 v))) ->
  (forall M' (jo a v : Z), P jo M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (forall R' M' (j' ci0 B0 H' : Z) (lf' : Z -> Z),
     zget R' kS7 = H' -> zget R' kS2 = 0 -> zget R' kT1 = n - ci0 -> zget R' kT2 = q + ci0 -> zget R' kS8 = B0 ->
     ce <= ci0 -> ci0 <= n -> 0 <= B0 -> B0 + 8 * (n - ci0) <= 40 -> 0 <= H' -> H' < 2 ^ (B0 + 8 * (n - ci0)) ->
     B0 + 8 * (n - ci0) <= 8 * n -> B0 + 8 * (n - ci0) <= 8 * (n - ce) + Be ->
     j <= j' -> j' < nd ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> P j' M' ->
     keptc Rb l R' KS_CR ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_CL (zupd R' []) M' MD) T) ->
  (forall R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     zget R' kS7 = H' -> zget R' kS2 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kA7 = B' ->
     ce <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ce) + Be -> j <= j' -> j' < nd ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> P j' M' ->
     keptc Rb l R' KS_CR ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_A7 (zupd R' []) M' MD) T) ->
  (forall (pc : Z) R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     (pc = L_BADREP0 \/ pc = L_BADREP) ->
     zget R' kS7 = H' -> zget R' kS2 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kS10 = q + ci' -> zget R' kS8 = B' ->
     zget R' kT4 = 30 -> zget R' kS9 = 67008 ->
     ce <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ce) + Be -> j <= j' -> j' < nd ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> P j' M' ->
     keptc Rb l R' KS_CR ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd R' []) M' MD) T) ->
  (forall R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     zget R' kS7 = H' -> zget R' kS2 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kS8 = B' -> zget R' kA3 = j' ->
     zget R' kT4 = 30 -> zget R' kS9 = 67008 ->
     ce <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ce) + Be -> nd <= j' -> j' <= nd ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> P j' M' ->
     keptc Rb l R' KS_CR ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_DONE (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_LOOP (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T u p q n nlen nd lb lm nx ce Be j ci B H fin cf lf Hh
    Lsp Ls9 Lra La2 La4 La5 La6 La3 Ls10 Lt2 Ls8 Lt1 Ls0 Ls7 Lt4 Lt5
    HN Hj0 Hj1 Hnd Hce Hc2 HB0 HB40 HH1 HH2 HBc HW Hdm Hlb1 Hlb2 Hnx1 Hnx2 TOK Rlf Hlf15
    Hq1 Hn0 Hn26 Hq2 Hp1 Hp2 Hpu Hu2 SPQ Wp Hin Rfin Hcodes Hlens HP HPa HPb KXD KXA KBD KDN; [lia|].
  zkeys. unfold L_CL_LOOP, L_CL_DLOOP, L_CL_RES, L_CL_NEXT, L_CL_DONE, L_LVX_CL, L_LEAVE_A7, L_BADREP0, L_BADREP in *.
  pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPlb. pose proof (pow2_48 B ltac:(lia)) as HPB.
  pose proof (land_mask_l H lb ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (ctab_bits cf lb nx (Z.land lm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits0 Hpow].
  assert (RES : forall RR (ci1 B1 H1 : Z),
    zget RR kSP = u + -224 -> zget RR kS0 = p -> zget RR kS6 = p + 168 ->
    zget RR kA2 = nlen -> zget RR kA4 = nd -> zget RR kA5 = p + 1384 -> zget RR kA6 = lm ->
    zget RR kA3 = j -> zget RR kS11 = q + ci1 -> zget RR kS2 = n - ci1 -> zget RR kA7 = B1 ->
    zget RR kS8 = B -> zget RR kS7 = H1 -> zget RR kT0 = code_bits (cf (Z.land lm H1)) -> zget RR kT3 = Z.land lm H1 ->
    zget RR kT4 = 30 -> zget RR kS9 = 67008 -> zget RR kT1 = n - ci -> zget RR kT2 = q + ci ->
    ci <= ci1 -> ci1 <= n -> B1 = B + 8 * (ci1 - ci) -> code_bits (cf (Z.land lm H1)) <= B1 -> B1 <= 40 ->
    0 <= H1 -> H1 < 2 ^ B1 -> B1 <= 8 * ci1 ->
    keptc Rb l RR KS_CR ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 88780 (zupd RR []) M MD) T).
  { intros RR ci1 B1 H1. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
    eapply (cl_res P RR [] M MD T u p q n nlen nd lb lm nx ci B j ci1 B1 H1 fin cf lf Hh);
      try (cbv [zget_l alookup]; eassumption); try eassumption; try lia.
    - intros M1 a1 v1 X1 X2 X3. exact (HPa M1 j a1 v1 X1 X2 X3).
    -
      intros R' ci' B' H'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
      eapply (KXA R' M j ci' B' H' lf). all: kgoal.
    -
      intros pc R' ci' B' H' Hpc. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
      eapply (KBD pc R' M j ci' B' H' lf Hpc). all: kgoal.
    -
      intros R' M' j' ci' B' H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end. unfold L_CL_NEXT. zkeys.
      pose proof (pow2_48 B' ltac:(lia)) as HPB'.
      zstep Rfd.
      zstep Rfd.
      destruct (Z_lt_dec j' nd) as [Hlt | Hge].
      + zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (IH P Rx lx Mx MD T u p q n nlen nd lb lm nx ce Be j' ci' B' H' fin cf lf' Hh) end;
          try zreg; try lia; try eassumption.
        * intros RR9 MM9 jj9 cc9 BB9 HQ9 ll9. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
          eapply (KXD RR9 MM9 jj9 cc9 BB9 HQ9 ll9). all: kgoal.
        * intros RR9 MM9 jj9 cc9 BB9 HQ9 ll9. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
          eapply (KXA RR9 MM9 jj9 cc9 BB9 HQ9 ll9). all: kgoal.
        * intros pc RR9 MM9 jj9 cc9 BB9 HQ9 ll9 Hpc. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
          eapply (KBD pc RR9 MM9 jj9 cc9 BB9 HQ9 ll9 Hpc). all: kgoal.
        * intros RR9 MM9 jj9 cc9 BB9 HQ9 ll9. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
          eapply (KDN RR9 MM9 jj9 cc9 BB9 HQ9 ll9). all: kgoal.
      + zbr Rfd false.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KDN Rx Mx j' ci' B' H' lf') end. all: kgoal. }
  zstep Rfd.
  zstep Rfd.
  zsetreg (4 * Z.land lm H) ltac:(symmetry; apply shiftl_2).
  zstep Rfd.
  tld4_bits Hcodes (Z.land lm H).
  destruct (Z_lt_dec B (code_bits (cf (Z.land lm H)))) as [Hdec | Hres].
  -
    zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (cl_decode (S (Z.to_nat (n - ci))) Rx lx Mx MD T u p q n lb lm nx ci B ci B H fin cf Hh) end;
      try zreg; try lia; try eassumption.
    + intros R' H'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
      eapply (KXD R' M j ci B H' lf). all: kgoal.
    + intros R' ci' B' H'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
      eapply (RES R' ci' B' H'). all: kgoal.
  - zbr Rfd true.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (RES Rx ci B H) end. all: kgoal.
Qed.

Definition st_cl (st : ist) (ci H B j : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) ci (t_cout st) H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) j (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_cl : forall cx st lf cf ci H B j lf',
  sinv cx st lf cf -> t_mode st = CODELENS ->
  t_cin st <= ci -> ci <= c_n cx -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
  0 <= j -> j <= t_nlen st + t_ndist st ->
  (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j -> lf' i <= 15) ->
  sinv cx (st_cl st ci H B j) lf' cf /\ meas cx (st_cl st ci H B j) <= meas cx st.
Proof.
  intros cx st lf cf ci H B j lf' (R & W & P & Mo) Hm H1 H2 H3 H4 H5 H6 H7 H8 Hj0 Hj1 Rlf' Hlf'.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_cl, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. cbv [N_LENS N_CODES] in R. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (CODELENS = HEAD \/ CODELENS = BAD) /\ cout = 0) by mode_get Mo.
  assert (MC : CODELENS = CODELENS -> 257 <= nlen /\ nlen <= 286 /\ 1 <= ndist /\ ndist <= 30 /\ shave <= nlen + ndist /\
            (forall i, 0 <= i < shave -> lf i <= 15) /\
            ctable_live (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  specialize (MC eq_refl). dand MC as (A1 & A2 & A3 & A4 & _ & _ & CT). clear Mo.
  unfold ctable_live in CT. cbn [t_lc t_lb t_nx] in CT.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf CT. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3 H1 H8. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [mode_vacuous |].
    split; [intros _; split_conj; try assumption; unfold ctable_live; cbn [t_lc t_lb t_nx]; exact CT |].
    split_conj; mode_vacuous.
  - clear - H8. lia_std.
Qed.

Section CL.
Context {RCa1 : RunCtx}.
Hypothesis CLDONE : cldone_stmt.

Theorem clhead_s : clhead_stmt.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RG KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0. pose proof KM as KM0.
  open_K K. open_kmem KM. pose proof STD as STD0. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (MC : t_mode st = CODELENS -> 257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            t_shave st <= t_nlen st + t_ndist st /\ (forall i, 0 <= i < t_shave st -> lf i <= 15) /\ ctable_live st cf) by mode_get MODE_.
  specialize (MC Hm). dand MC as (Hnl1 & Hnl2 & Hnd1 & Hnd2 & Hsh & Hlf15 & CT). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold ctable_live in CT. cbn [t_lc t_lb t_nx] in CT. dand CT as (Hlc & Hlb & Hnx0 & Hnx1 & TOK). cbv [N_CODES] in Hnx1.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  unfold s_regs_cl, s_fix, s_vars in RG. icx_cbn. destr_conj RG.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof SREST as SR'. unfold st_rest in SR'. icx_cbn.
  dand SR' as (_ & _ & _ & _ & _ & _ & _ & C104 & _ & C120 & _ & _ & C132 & C136 & C140 & _).
  subst lc. cbv [cp_addr o_codes] in C104. icx_cbn.
  assert (Hshv : 0 <= shave) by (pose proof (Hlf15 0); lia).
  pose proof (PL_intro _ _ _ _ _ _ _ KM0) as [HP _]. cbn [t_shave] in HP.
  clear Ww CST HK Hmode SREST SRET SOUT.
  prune_rng.
  zkeysb. unfold L_CL_HEAD, L_CL_DONE, L_CL_LOOP, L_LVX_CL, L_LEAVE_A7, L_BADREP0, L_BADREP, L_BADMSG_S11, L_LEAVE, L_LEAVE_LD in *.
  cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  destruct (Z_lt_dec shave (nlen + ndist)) as [Hgo | Hdone0].
  2: {
    zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (CLDONE (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI0) end.
    - unfold s_regs_cld, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - exact KM0.
    - exact KA0. }
  zbr Rfd false.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zsetreg (2 ^ lb - 1) ltac:(symmetry; apply mask_not_sllw; lia).
  zstep Rfd.
  zstep Rfd.
  assert (KMX : forall M' (ci' H' B' j' : Z) (lf' : Z -> Z),
    PL (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
       (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) cf j' M' ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' ->
    k_mem (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
      (st_cl (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' j') lf' cf M').
  { intros M' ci' H' B' j' lf' HP' HL'. unfold st_cl. ist_cbn.
    pose proof (PL_kmem _ _ _ _ lf' _ _ _ HP' HL') as X. unfold st_sh in X. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in X.
    unfold k_mem in X |- *. dand X as (X1 & X2 & X3 & X3b & X4 & X5 & X6). split_conj; try assumption. }
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (cl_loop (S (Z.to_nat (nlen + ndist - shave)))
              (PL (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                  (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) cf)
              Rx lx Mx MD T u p q n nlen (nlen + ndist) lb (2 ^ lb - 1) nx cin bits shave cin bits hold fin cf lf Hh) end;
    try zreg; try lia; try eassumption; try reflexivity.
  - unfold ZSEP. pose proof (sep_p_q _ _ SEP) as D. cbn [c_p c_q c_n] in D. cbv [STATE_SIZE] in D. exact D.
  - intros M' jo a v HPj Ha Hv. apply (PL_store140 _ _ _ _ _ _ _ _ _ CX0 HPj); [icx_cbn; exact Ha | exact Hv].
  - intros M' jo a v HPj Ha1 Ha2. apply (PL_store_lens _ _ _ _ _ _ _ _ _ CX0 HPj); icx_cbn; lia.
  -
    intros R' M' j' ci0 B0 H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end. zkeys.
    match goal with HP' : PL _ _ _ _ _ j' M' |- _ =>
      dand HP' as (STD' & SAT' & SRET' & SOUT' & HC' & HAG'); unfold s_ret in SRET'; unfold st_sh in SAT'; icx_cbn end.
    eapply (stub_CL R' [] M' MD T q n ci0 B0 u ret Hh); try (cbv [zget_l alookup]; eassumption); try lia.
    intros R9 E9 E27 HK9. kopen HK9.
    pose proof (sinv_cl _ _ lf cf n H' (B0 + 8 * (n - ci0)) j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(assumption) ltac:(assumption)) as [SI1 ME1].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KLL Rx Mx _ lf' cf SI1) end.
    + unfold s_regs_leave_ld, st_cl; icx_cbn; zkeys; split_conj; kgoal.
    + exact STD'.
    + unfold st_cl; ist_cbn. exact SAT'.
    + unfold st_cl, s_ret in *; ist_cbn. exact SRET'.
    + unfold st_cl, s_out in *; ist_cbn. exact SOUT'.
    + assumption.
    + exact HC'.
    + exact HAG'.
  -
    intros R' M' j' ci' B' H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end. unfold L_LEAVE_A7. zkeys.
    match goal with HP' : PL _ _ _ _ _ j' M' |- _ =>
      dand HP' as (STD' & SAT' & SRET' & SOUT' & HC' & HAG'); unfold st_sh in SAT'; icx_cbn end.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_cl _ _ lf cf ci' H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(assumption) ltac:(assumption)) as [SI1 ME1].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KLL Rx Mx _ lf' cf SI1) end.
    + unfold s_regs_leave_ld, st_cl; icx_cbn; zkeys; split_conj; kgoal.
    + exact STD'.
    + unfold st_cl; ist_cbn. exact SAT'.
    + unfold st_cl, s_ret in *; ist_cbn. exact SRET'.
    + unfold st_cl, s_out in *; ist_cbn. exact SOUT'.
    + assumption.
    + exact HC'.
    + exact HAG'.
  -
    intros pc R' M' j' ci' B' H' lf' Hpc. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end. unfold L_BADREP0, L_BADREP in Hpc. zkeys.
    pose proof (sinv_cl _ _ lf cf ci' H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(assumption) ltac:(assumption)) as [SI1 ME1].
    pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (st_cl (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' j')) as MB.
    unfold st_cl in MB, SI1, ME1 |- *. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in MB, SI1, ME1 |- *. change (rank CODELENS) with 20 in MB.
    destruct Hpc as [-> | ->];
      (zstep Rfd; zstep Rfd; zlit;
       zstep Rfd;
       lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
         eapply (KB11 Rx Mx (IST CODELENS last flags ci' cout H' B' out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist j' nx whave wnext) lf' cf
                   (sinv_bad_of _ _ _ _ SI1)) end;
       [ clear - MB ME1; lia
       | unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; kgoal
       | lazymatch goal with |- 0 <= ?x < _ => first [ assert (EA2 : x = 66210) by zreg; rewrite EA2 | assert (EA2 : x = 66272) by zreg; rewrite EA2 ] end; lia
       | apply KMX; assumption ]).
  -
    intros R' M' j' ci' B' H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end. zkeys.
    assert (Ej : j' = nlen + ndist) by lia.
    pose proof (sinv_cl _ _ lf cf ci' H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(assumption) ltac:(assumption)) as [SI1 ME1].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (CLDONE (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (st_cl (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' j')
                lf' cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI1) end.
    + unfold s_regs_cld, s_fix, s_vars, st_cl; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; kgoal.
    + apply KMX; assumption.
    + eapply KALL_mono; [| exact KA0]. clear - ME1. unfold st_cl in ME1. exact ME1.
Qed.

Theorem arm_CODELENS_s0 : arm_stmt L_CODELENS CODELENS.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof KM as KM0. open_kmem KM. destruct SAT as [Hmode SREST].
  pose proof CX as CX0. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode] in Hm. subst mode.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  unfold st_rest in SREST. icx_cbn. dand SREST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C140 & _).
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & Mo). unfold RNG in RNG_. icx_cbn. destr_conj RNG_.
  assert (MC : CODELENS = CODELENS -> 257 <= nlen /\ nlen <= 286 /\ 1 <= ndist /\ ndist <= 30 /\ shave <= nlen + ndist /\
            (forall i, 0 <= i < shave -> lf i <= 15) /\
            ctable_live (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  specialize (MC eq_refl). dand MC as (MC1 & MC2 & MC3 & MC4 & MC5 & _). clear Mo.
  zkeysb. unfold L_CODELENS, L_CL_HEAD in *. pose proof two64_eq as TW64.
  tstep1 Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (clhead_s (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx lx Mx
              (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf CX0 Hh Hfin eq_refl SI) end.
  - unfold s_regs_cl, s_fix, s_vars; icx_cbn; zkeys; split_conj; zreg.
  - exact KM0.
  - exact K.
Qed.

End CL.

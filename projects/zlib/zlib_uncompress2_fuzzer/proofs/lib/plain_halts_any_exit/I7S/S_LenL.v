(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.IK.IConj.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.I7S Require Import SBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.I7S Require Import S_MatchL S_DistL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_LLOOP1 : Z := 92024.
Definition L_L40 : Z := 92096.
Definition L_LLOOP2 : Z := 92192.
Definition L_L700 : Z := 92296.

Definition KS_E1 : list positive := [2; 3; 4; 5; 9; 10; 11; 12; 16; 17; 19; 20; 21; 23; 25; 26; 28; 29; 30; 32]%positive.
Definition KS_E2 : list positive := [2; 3; 4; 5; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 23; 25; 26; 27; 28]%positive.
Ltac keptc_close ::= cbv [keptc KS_D1 KS_D2 KS_X KS_E1 KS_E2 KS_L1 KS_L2]; split_conj; try exact I; zreg.
Ltac keptc_chain HK ::= cbv [keptc KS_D1 KS_D2 KS_X KS_E1 KS_E2 KS_L1 KS_L2] in HK |- *; destr_conj HK; split_conj; try exact I;
  cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; first [assumption | reflexivity].

Lemma l_loop1 {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (q n la na lb lm c0 b0 ci B H : Z) (fin rdL : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA5 = la -> zget_l Rb l kA6 = lm -> zget_l Rb l kA2 = n - ci -> zget_l Rb l kT1 = q + ci ->
  zget_l Rb l kT0 = B -> zget_l Rb l kA3 = B -> zget_l Rb l kS7 = H ->
  zget_l Rb l kA4 = code_bits (rdL (Z.land lm H)) -> zget_l Rb l kA7 = la + 4 * Z.land lm H ->
  zget_l Rb l kS2 = n - c0 -> zget_l Rb l kS8 = b0 -> zget_l Rb l kS11 = q + c0 ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < code_bits (rdL (Z.land lm H)) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  lm = 2 ^ lb - 1 -> 1 <= lb -> lb <= 15 -> 2 ^ lb <= na -> tab_ok LENS rdL lb na = true ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 <= la -> la + 4 * na <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M la na rdL ->
  (forall R' (H' : Z),
     zget R' kS7 = H' -> 0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 14 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_E1 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_L1 (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     zget R' kS10 = q + ci' -> zget R' kA2 = n - ci' -> zget R' kA3 = B' -> zget R' kT0 = B' -> zget R' kS7 = H' ->
     zget R' kA4 = code_bits (rdL (Z.land lm H')) -> zget R' kA7 = la + 4 * Z.land lm H' ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> B' <= 22 -> code_bits (rdL (Z.land lm H')) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_E1 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_L40 (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LLOOP1 (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n la na lb lm c0 b0 ci B H fin rdL Hh La5 La6 La2 Lt1 Lt0 La3 Ls7 La4 La7 Ls8 Ls0 Ls10
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt HH1 HH2 HBc Hdm Hdb1 Hdb2 Hnd TOK Hq1 Hn26 Hq2 Hda1 Hda2 Hin Rfin Htab KX KD; [lia|].
  zkeys. unfold L_LLOOP1, L_L40, L_LVX_L1 in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPdb.
  pose proof (land_mask_l H lb ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (tab_root_entry LENS rdL lb na (Z.land lm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as (Hbits0 & _ & _ & _).
  assert (HB14 : B <= 14) by lia.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    - replace (b0 + 8 * (n - c0)) with B by lia. lia.
    - keptc_close. }
  zbr Rfd false.
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.
  zstep Rfd.
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  zstep Rfd.
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  set (H' := H + fin ci * 2 ^ B) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1.
  zstep Rfd.
  pose proof (land_mask_l H' lb ltac:(lia)) as Ri1. rewrite <- Hdm in Ri1.
  pose proof (tab_root_entry LENS rdL lb na (Z.land lm H') TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as (Hbits1 & _ & _ & _).
  zstep Rfd.
  zsetreg (4 * Z.land lm H') ltac:(symmetry; apply shiftl_2).
  zstep Rfd.
  tld4_bits Htab (Z.land lm H').
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  tstep1 Rfd.
  zstep Rfd.
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct (Z_lt_dec (B + 8) (code_bits (rdL (Z.land lm H')))) as [Hmore | Hdone].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T q n la na lb lm c0 b0 (ci + 1) (B + 8) H' fin rdL Hh) end;
      try zreg; try lia; try eassumption.
    + intros R' ci' B' H'' G28 G13 G14 G6 G24 G15 G17 X1 X2 X3 X4 X5 X6 X7 X8 HK.
      eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chain HK.
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) H') end;
      try zreg; try lia.
    all: keptc_close.
Qed.


Lemma l_loop2 {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (q n la na lb lo v m2 c1 b1 ci B H : Z) (fin rdL : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kT2 = m2 -> zget_l Rb l kA6 = lb -> zget_l Rb l kA7 = v -> zget_l Rb l kA5 = la ->
  zget_l Rb l kA2 = n - c1 -> zget_l Rb l kA3 = b1 -> zget_l Rb l kS10 = q + c1 ->
  zget_l Rb l kT0 = n - ci -> zget_l Rb l kS1 = q + ci -> zget_l Rb l kT4 = B -> zget_l Rb l kT1 = B -> zget_l Rb l kS7 = H ->
  zget_l Rb l kT5 = la + 4 * (v + Z.land H m2 / 2 ^ lb) -> zget_l Rb l kT3 = code_bits (rdL (v + Z.land H m2 / 2 ^ lb)) ->
  n - ci < Z.of_nat N -> 0 <= c1 -> c1 <= ci -> ci <= n -> 0 <= b1 -> B = b1 + 8 * (ci - c1) ->
  B < lb + code_bits (rdL (v + Z.land H m2 / 2 ^ lb)) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  m2 = 2 ^ (lb + lo) - 1 -> 1 <= lb -> lb <= 15 -> 1 <= lo -> lo <= 15 - lb -> 0 <= v -> v + 2 ^ lo <= na -> na <= 65536 ->
  (forall j, 0 <= j < 2 ^ lo -> is_linkop (code_op (rdL (v + j))) = false /\ term_ok LENS (15 - lb) (rdL (v + j)) = true) ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 <= la -> la + 4 * na <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M la na rdL ->
  (forall R' (H' : Z),
     zget R' kS7 = H' -> 0 <= H' -> H' < 2 ^ (b1 + 8 * (n - c1)) -> b1 + 8 * (n - c1) <= 29 -> b1 + 8 * (n - c1) <= 8 * n ->
     keptc Rb l R' KS_E2 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_L2 (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     zget R' kT6 = q + ci' -> zget R' kT0 = n - ci' -> zget R' kT1 = B' -> zget R' kT4 = B' -> zget R' kS7 = H' ->
     zget R' kT5 = la + 4 * (v + Z.land H' m2 / 2 ^ lb) -> zget R' kT3 = code_bits (rdL (v + Z.land H' m2 / 2 ^ lb)) ->
     ci < ci' -> ci' <= n -> B' = b1 + 8 * (ci' - c1) -> B' <= 37 -> lb + code_bits (rdL (v + Z.land H' m2 / 2 ^ lb)) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_E2 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_L700 (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LLOOP2 (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n la na lb lo v m2 c1 b1 ci B H fin rdL Hh Lt2 La6 La7 La5 La2 La3 Ls11
    Lt0 Ls0 Lt4 Lt1 Ls7 Lt5 Lt3 HN Hc0 Hc1 Hc2 Hb0 HB Hlt HH1 HH2 HBc Hm2 Hdb1 Hdb2 Hlo1 Hlo2 Hv1 Hv2 Hnd SUB
    Hq1 Hn26 Hq2 Hda1 Hda2 Hin Rfin Htab KX KD; [lia|].
  zkeys. unfold L_LLOOP2, L_L700, L_LVX_L2 in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPdb. pose proof (pow2_15 lo ltac:(lia)) as HPlo.
  assert (HPm : 1 <= 2 ^ (lb + lo) <= 32768) by (apply pow2_15; lia).
  assert (JR : forall Hx, 0 <= Z.land Hx m2 / 2 ^ lb < 2 ^ lo).
  { intros Hx. pose proof (land_mask_r Hx (lb + lo) ltac:(lia)) as A. rewrite <- Hm2 in A.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. exact (proj2 A). }
  pose proof (JR H) as Rj0.
  destruct (SUB _ Rj0) as [_ TM0]. apply term_ok_LENS in TM0 as [Hbits0 _].
  assert (HB29 : B <= 29) by lia.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    - replace (b1 + 8 * (n - c1)) with B by lia. lia.
    - keptc_close. }
  zbr Rfd false.
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.
  zstep Rfd.
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  zstep Rfd.
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  set (H' := H + fin ci * 2 ^ B) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1.
  zstep Rfd.
  pose proof (land_mask_r H' (lb + lo) ltac:(lia)) as Rm. rewrite <- Hm2 in Rm.
  zstep Rfd.
  zsetreg (Z.land H' m2 / 2 ^ lb) ltac:(symmetry; apply srlw_small; lia).
  pose proof (JR H') as Rj1.
  destruct (SUB _ Rj1) as [_ TM1]. apply term_ok_LENS in TM1 as [Hbits1 _].
  zstep Rfd.
  zsetreg (v + Z.land H' m2 / 2 ^ lb) ltac:(lia).
  zstep Rfd.
  zstep Rfd.
  zsetreg (4 * (v + Z.land H' m2 / 2 ^ lb)) ltac:(symmetry; apply zext32_shift30; lia).
  zstep Rfd.
  tld4_bits Htab (v + Z.land H' m2 / 2 ^ lb).
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct (Z_lt_dec (B + 8) (lb + code_bits (rdL (v + Z.land H' m2 / 2 ^ lb)))) as [Hmore | Hdone].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T q n la na lb lo v m2 c1 b1 (ci + 1) (B + 8) H' fin rdL Hh) end;
      try zreg; try lia; try eassumption.
    + intros R' ci' B' H'' G31 G18 G6 G30 G24 G29 G8 X1 X2 X3 X4 X5 X6 X7 X8 HK.
      eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chain HK.
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) H') end;
      try zreg; try lia.
    all: keptc_close.
Qed.


Definition st_le (st : ist) (m len ex : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      len (t_offset st) ex (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_len_set : forall cx st lf cf m len,
  sinv cx st lf cf -> t_mode st = LEN -> (m = LEN \/ m = LIT \/ m = TYPE) -> 0 <= len -> len < 4294967296 ->
  sinv cx (st_le st m len (t_extra st)) lf cf.
Proof.
  intros cx st lf cf m len SI Hm Hm' Hl1 Hl2.
  dand SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN = HEAD \/ LEN = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [| split; [exact W | split; [prog_transfer P|]]].
  - clear W P Mf Mlive. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear - Hm'; unfold reach; destruct Hm' as [-> | [-> | ->]]; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | destruct Hm' as [-> | [-> | ->]]; mode_vacuous ].
Qed.

Lemma sinv_to_lenext : forall cx st lf cf len ex,
  sinv cx st lf cf -> t_mode st = LEN -> 1 <= len -> len <= 32768 -> 0 <= ex -> ex <= 15 ->
  sinv cx (st_le st LENEXT len ex) lf cf /\ meas cx (st_le st LENEXT len ex) < meas cx st.
Proof.
  intros cx st lf cf len ex SI Hm Hl1 Hl2 He1 He2.
  dand SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN = HEAD \/ LEN = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [split; [| split; [exact W | split; [prog_transfer P|]]] |].
  - clear W P Mf Mlive. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | intros _; clear - Hl1 Hl2 He1 He2; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma sinv_to_dist : forall cx st lf cf len,
  sinv cx st lf cf -> t_mode st = LENEXT -> 1 <= len -> len < 65536 ->
  sinv cx (st_le st DIST len (t_extra st)) lf cf /\ meas cx (st_le st DIST len (t_extra st)) < meas cx st.
Proof.
  intros cx st lf cf len SI Hm Hl1 Hl2.
  dand SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LENEXT = HEAD \/ LENEXT = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LENEXT -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LENEXT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [split; [| split; [exact W | split; [prog_transfer P|]]] |].
  - clear W P Mf Mlive. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | intros _; clear - Hl1 Hl2; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma st_rest_le {RCa1 : RunCtx}  : forall cx st M m len ex,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_w3 st len (t_offset st) ex) M -> st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_le st m len ex) M.
Proof. intros cx st M m len ex H. destruct cx, st. exact H. Qed.

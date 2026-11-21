(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InftreesCoverage InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S Require Import SBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S Require Import S_Type S_MatchL S_DistL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.PropExec.FPState}.

Definition L_CL_LOOP : Z := 88664.
Definition L_CL_DLOOP : Z := 88700.
Definition L_CL_RES : Z := 88780.
Definition L_CL_P17 : Z := 88864.
Definition L_CL_X17 : Z := 89036.
Definition L_CL_P16 : Z := 88924.
Definition L_CL_X16 : Z := 89072.
Definition L_CL_P18 : Z := 88984.
Definition L_CL_X18 : Z := 89132.
Definition L_CL_CHK : Z := 89160.
Definition L_CL_FILL : Z := 89172.
Definition L_CL_FILLX : Z := 89196.
Definition L_CL_NEXT : Z := 89204.
Definition L_LVX_CL : Z := 93540.
Definition L_LEAVE_A7 : Z := 93632.
Definition L_BADREP0 : Z := 93468.
Definition L_BADREP : Z := 93384.

Lemma ctab_bits : forall cf lb nx i,
  tab_ok CODES (rdc cf (CDyn 0)) lb nx = true -> 0 <= i < 2 ^ lb -> 1 <= code_bits (cf i) <= lb /\ 2 ^ lb <= nx.
Proof.
  intros cf lb nx i T Hi. pose proof (tab_root_entry CODES (rdc cf (CDyn 0)) lb nx i T Hi) as (X & _ & Y & _).
  unfold rdc in X. rewrite Z.add_0_l in X. split; [exact X | exact Y].
Qed.
Lemma zext32_shift31 : forall x, 0 <= x < 4294967296 ->
  Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) (31 mod 64) = 2 * x.
Proof.
  intros x Hx. change (31 mod 64) with 31. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  change (2 ^ 32) with (2 * 2 ^ 31). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma land3_range : forall x, 0 <= Z.land x 3 < 4.
Proof. intros. apply land_ones_range with (k := 2). lia_std. Qed.
Lemma land7_range' : forall x, 0 <= Z.land x 7 < 8.
Proof. intros. apply land_ones_range with (k := 3). lia_std. Qed.
Lemma land127_range : forall x, 0 <= Z.land x 127 < 128.
Proof. intros. apply land_ones_range with (k := 7). lia_std. Qed.

Definition KS_CP : list positive := [2; 3; 4; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 25; 26; 30; 32]%positive.
Definition KS_CD : list positive := [2; 3; 4; 5; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 25; 26; 27; 32]%positive.
Definition KS_CF : list positive := [2; 3; 4; 5; 7; 8; 9; 10; 11; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 32]%positive.
Definition KS_CX : list positive := [2; 3; 4; 5; 6; 8; 9; 11; 12; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 26; 27; 29; 30; 32]%positive.
End FXG.
Ltac keptc_closeC := cbv [keptc KS_CP KS_CD KS_CF KS_CX]; split_conj; try exact I; zreg.
Ltac keptc_chainC HK := cbv [keptc KS_CP KS_CD KS_CF KS_CX] in HK |- *; destr_conj HK; split_conj; try exact I;
  cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; first [assumption | reflexivity].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.PropExec.FPState}.

Lemma cl_pull : forall (N : nat) (pc pcx : Z) Rb l M MD T (q n need c0 b0 ci B H : Z) (fin : Z -> Z),
  ((pc = L_CL_P17 /\ pcx = L_CL_X17) \/ (pc = L_CL_P16 /\ pcx = L_CL_X16) \/ (pc = L_CL_P18 /\ pcx = L_CL_X18)) ->
  m_halted MD = None ->
  zget_l Rb l kS2 = n - ci -> zget_l Rb l kS11 = q + ci -> zget_l Rb l kT2 = B -> zget_l Rb l kA7 = B ->
  zget_l Rb l kT1 = need -> zget_l Rb l kS7 = H ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < need -> need <= 22 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 ->
  mem_arr 1 R_segs M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  (forall R' (H' : Z),
     zget R' kS7 = H' -> zget R' kS2 = 0 -> zget R' kS11 = q + n -> zget R' kA7 = b0 + 8 * (n - c0) ->
     0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) < need -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_CP ->
     realizes R_segs (zcfg R_segs L_LEAVE_A7 (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     zget R' kS2 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kS10 = q + ci' -> zget R' kA7 = B' -> zget R' kT2 = B' -> zget R' kS7 = H' ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> need <= B' -> B' <= 29 ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_CP ->
     realizes R_segs (zcfg R_segs pcx (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs pc (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros pc pcx Rb l M MD T q n need c0 b0 ci B H fin Hpc Hh Ls8 Ls10 Lt2 La7 Lt1 Ls7
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt Hneed HH1 HH2 HBc Hq1 Hn26 Hq2 Hin Rfin KX KD; [lia|].
  zkeys. unfold L_CL_P17, L_CL_X17, L_CL_P16, L_CL_X16, L_CL_P18, L_CL_X18, L_LEAVE_A7 in *. pose proof two64_eq as TW64.
  pose proof (pow2_48 B ltac:(lia)) as HPB. pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct Hpc as [[-> ->] | [[-> ->] | [-> ->]]]; (
    destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz];
    [ zbr Rfd false; zstep Rfd;
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia;
      [ replace (b0 + 8 * (n - c0)) with B by lia; lia | keptc_closeC ]
    | zbr Rfd true;
      pose proof (Rfin ci ltac:(lia)) as Rb1;
      tld1 Hin ci Rfin;
      tstep1 Rfd;
      zstep Rfd;
      zstep Rfd;
      zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia);
      pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]; rewrite pow2_add8 in Hp1 by lia;
      zstep Rfd;
      zstep Rfd;
      zsetreg (H + fin ci * 2 ^ B) ltac:(lia);
      assert (HH' : 0 <= H + fin ci * 2 ^ B < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia);
      zstep Rfd;
      zstep Rfd;
      destruct (Z_lt_dec (B + 8) need) as [Hmore | Hdone];
      [ zbr Rfd true;
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx ?MDx) ?Tx =>
          eapply (IH _ _ Rx lx Mx MDx Tx q n need c0 b0 (ci + 1) (B + 8) (H + fin ci * 2 ^ B) fin) end;
        [ first [left; split; reflexivity | right; left; split; reflexivity | right; right; split; reflexivity] | ..];
        try zreg; try lia; try eassumption;
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? HK; eapply KD; try eassumption; try lia; keptc_chainC HK
      | zbr Rfd false;
        zstep Rfd;
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) (H + fin ci * 2 ^ B)) end;
        try zreg; try lia; keptc_closeC ] ]).
Qed.

Lemma cl_decode : forall (N : nat) Rb l M MD T (u p q n lb lm nx c0 b0 ci B H : Z) (fin cf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + -224 -> zget_l Rb l kS9 = 67008 -> zget_l Rb l kA5 = p + 1384 -> zget_l Rb l kA6 = lm ->
  zget_l Rb l kT5 = q + ci -> zget_l Rb l kS11 = q + ci -> zget_l Rb l kS2 = n - ci ->
  zget_l Rb l kT4 = B -> zget_l Rb l kA7 = B -> zget_l Rb l kS7 = H ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < code_bits (cf (Z.land lm H)) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  lm = 2 ^ lb - 1 -> 1 <= lb -> lb <= 15 -> 0 <= nx -> nx <= 1444 -> tab_ok CODES (rdc cf (CDyn 0)) lb nx = true ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 ->
  p + 8200 <= u -> u + 208 <= 140737488355328 ->
  mem_arr 1 R_segs M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 R_segs M (p + 1384) 1444 cf ->
  (forall R' (H' : Z),
     zget R' kS7 = H' -> zget R' kS2 = 0 ->
     0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 22 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_CD ->
     realizes R_segs (zcfg R_segs L_LVX_CL (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     zget R' kS11 = q + ci' -> zget R' kS2 = n - ci' -> zget R' kA7 = B' -> zget R' kS7 = H' ->
     zget R' kT0 = code_bits (cf (Z.land lm H')) -> zget R' kT3 = Z.land lm H' -> zget R' kT4 = 30 -> zget R' kS9 = 67008 ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> code_bits (cf (Z.land lm H')) <= B' -> B' <= 22 ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_CD ->
     realizes R_segs (zcfg R_segs L_CL_RES (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_CL_DLOOP (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T u p q n lb lm nx c0 b0 ci B H fin cf Hh Lsp Ls8j La5 La6 Lt5 Ls10 Ls8 Lt4 La7 Ls7
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt HH1 HH2 HBc Hdm Hlb1 Hlb2 Hnx1 Hnx2 TOK Hq1 Hn26 Hq2 Hp1 Hp2 Hu1 Hu2 Hin Rfin Hcodes KX KD; [lia|].
  zkeys. unfold L_CL_DLOOP, L_CL_RES, L_LVX_CL in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPlb.
  pose proof (land_mask_l H lb ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (ctab_bits cf lb nx (Z.land lm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits0 Hpow].
  assert (HB14 : B <= 14) by lia.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    all: first [replace (b0 + 8 * (n - c0)) with B by lia; lia | keptc_closeC]. }
  zbr Rfd true.
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.
  zstep Rfd.
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1']. rewrite pow2_add8 in Hp1' by lia.
  zstep Rfd.
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  set (H' := H + fin ci * 2 ^ B) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1'.
  zstep Rfd.
  pose proof (land_mask_l H' lb ltac:(lia)) as Ri1. rewrite <- Hdm in Ri1.
  pose proof (ctab_bits cf lb nx (Z.land lm H') TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits1 _].
  zstep Rfd.
  zsetreg (4 * Z.land lm H') ltac:(symmetry; apply shiftl_2).
  zstep Rfd.
  tld4_bits Hcodes (Z.land lm H').
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  tstep1 Rfd.
  zstep Rfd.
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct (Z_lt_dec (B + 8) (code_bits (cf (Z.land lm H')))) as [Hmore | Hdone].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T u p q n lb lm nx c0 b0 (ci + 1) (B + 8) H' fin cf Hh) end;
      try zreg; try lia; try eassumption.
    intros R' ci' B' H'' G27 G25 G18 G24 G6 G29 G30 G31 X1 X2 X3 X4 X5 X6 X7 X8 HK.
    eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chainC HK.
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) H') end;
      try zreg; try lia.
    all: keptc_closeC.
Qed.

Lemma stub_CL : forall Rb l M MD T (q n c0 b0 u rv : Z),
  m_halted MD = None ->
  zget_l Rb l kT1 = n - c0 -> zget_l Rb l kT2 = q + c0 -> zget_l Rb l kS8 = b0 -> zget_l Rb l kSP = u + -224 ->
  0 <= n - c0 -> n - c0 < 4294967296 -> mem_u64 R_segs M (u + -160) rv ->
  (forall R', zget R' kS8 = b0 + 8 * (n - c0) -> zget R' kS11 = q + n ->
     keptc Rb l R' KS_CX -> realizes R_segs (zcfg R_segs L_LEAVE_LD (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_LVX_CL (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T q n c0 b0 u rv Hh Lt1 Lt2 Ls0 Lsp H1 H2 Hrv K.
  zkeys. unfold L_LVX_CL, L_LEAVE_LD in *.
  zstep Rfd.
  zsetreg (8 * (n - c0)) ltac:(symmetry; apply shiftl_3).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zext32.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end; try zreg. keptc_closeC.
Qed.

End FXG.
Ltac zside1c := first [reflexivity | exact I | zlia].
Ltac tstore_arrPc fd Ha i HP HPres :=
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
          (let HP' := fresh in pose proof (HPres M a v HP ltac:(zside1c) ltac:(zside1c)) as HP'; clear HP; rename HP' into HP);
          repeat match goal with
          | H : mem_arr ?k' segs M ?base' ?n' ?f' |- _ =>
              first [ apply (mem_arr_frame segs k' M base' n' f' a (Z_to_le_bytes kk v)) in H; [|unfold zdisj; zlen_norm; zlia]
                    | idtac "tstore_arrPc: mem_arr fact dropped at array store" a; clear H ]
          end;
          zmem_post
      end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.PropExec.FPState}.
End FXG.
Ltac tstorePc fd HP HPres :=
  let pc := zpc in
  fd pc ltac:(fun F E D =>
    lazymatch type of D with
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply zu_sh; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply zu_sw; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply zu_sd; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    end);
  lazymatch goal with
  | |- realizes _ (zcfg _ _ _ (wbytes ?M (w64 ?a) (Z_to_le_bytes ?kk ?v)) _) _ =>
      (let HP' := fresh in pose proof (HPres M a v HP ltac:(zside1c) ltac:(zside1c)) as HP'; clear HP; rename HP' into HP);
      zmem_post_arr; zmem_post
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.PropExec.FPState}.

Lemma cl_fill : forall (N : nat) (P : mem -> Prop) Rb l M MD T (u p q n j je len : Z) (fin cf lf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA3 = j -> zget_l Rb l kA7 = je -> zget_l Rb l kT1 = len -> zget_l Rb l kS6 = p + 168 ->
  je - j <= Z.of_nat N -> 0 <= j -> j < je -> je <= 320 -> 0 <= len -> len < 65536 ->
  0 < p -> p + 7176 <= 140737488355328 -> 1 <= q -> 0 <= n -> q + n <= 140737488355328 -> p + 8200 <= u -> u + 208 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) ->
  mem_wr R_segs M p 7176 ->
  mem_arr 1 R_segs M q n fin -> mem_arr 4 R_segs M (p + 1384) 1444 cf -> mem_arr 2 R_segs M (p + 168) 320 lf ->
  P M ->
  (forall M' (a v : Z), P M' -> p + 168 <= a -> a + 2 <= p + 808 -> P (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (forall R' M' (lf' : Z -> Z),
     zget R' kA3 = je ->
     mem_wr R_segs M' p 7176 -> mem_arr 1 R_segs M' q n fin -> mem_arr 4 R_segs M' (p + 1384) 1444 cf ->
     mem_arr 2 R_segs M' (p + 168) 320 lf' -> P M' ->
     (forall i, 0 <= i < 320 -> j <= i < je -> lf' i = len) ->
     (forall i, 0 <= i < 320 -> ~ (j <= i < je) -> lf' i = lf i) ->
     keptc Rb l R' KS_CF ->
     realizes R_segs (zcfg R_segs L_CL_FILLX (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_CL_FILL (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T u p q n j je len fin cf lf Hh La3 La7 Lt1 Lra
    HN Hj0 Hj1 Hje Hl0 Hl1 Hp1 Hp2 Hq1 Hn0 Hq2 Hu1 Hu2 SPQ Wp Hin Hcodes Hlens HP HPb KD; [lia|].
  zkeys. unfold L_CL_FILL, L_CL_FILLX in *. pose proof two64_eq as TW64.
  zstep Rfd.
  tstep1 Rfd.
  zstep Rfd.
  zsetreg (2 * j) ltac:(symmetry; apply zext32_shift31; lia).
  zstep Rfd.
  tstore_arrPc Rfd Hlens j HP HPb.
  destruct (Z.eq_dec (j + 1) je) as [Hlast | Hmore].
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KD Rx Mx (zfupd lf j len)) end;
      try zreg; try eassumption.
    all: first [ intros i Hi Hij; unfold zfupd; destruct (Z.eqb_spec i j); first [reflexivity | lia] | keptc_closeC ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH P Rx lx Mx MD T u p q n (j + 1) je len fin cf _ Hh) end;
      try zreg; try lia; try eassumption.
    intros R' M' lf' G14 W' Hin' Hcodes' Hlens' HP' Hin_ Hout_ HK.
    eapply (KD R' M' lf'); try eassumption.
    all: first [ intros i Hi Hij;
                 first [ destruct (Z.eq_dec i j) as [-> | Hne];
                         [ rewrite Hout_ by lia; unfold zfupd; rewrite Z.eqb_refl; reflexivity | apply Hin_; lia ]
                       | rewrite Hout_ by lia; unfold zfupd; destruct (Z.eqb_spec i j); [lia | reflexivity] ]
               | keptc_chainC HK ].
Qed.
End FXG.

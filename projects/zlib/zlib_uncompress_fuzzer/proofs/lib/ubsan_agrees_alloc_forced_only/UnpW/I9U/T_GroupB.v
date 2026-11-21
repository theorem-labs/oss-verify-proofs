(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U Require TBase T_ClDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Inftrees InftreesCoverage ItCovIface InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require ItBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require S_Type S_MatchL S_DistL S_TableL S_Table.

Module T_TableL.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_DistL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_TableL.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition L_TAB_LOOP_T : Z := 87856.  (* [comment removed for export] *)
Definition L_TAB_BODY_T : Z := 88724.  (* [comment removed for export] *)
Definition L_LVX_TAB_T : Z := 95972.   (* [comment removed for export] *)
Definition L_LL_HEAD_T : Z := 88864.   (* [comment removed for export] *)
Definition L_LL_BODY_T : Z := 88920.   (* [comment removed for export] *)
Definition L_LVX_LL_T : Z := 96148.    (* [comment removed for export] *)
Definition L_LL_FILL_T : Z := 89024.   (* [comment removed for export] *)
Definition L_LL_FLOOP_T : Z := 89052.  (* [comment removed for export] *)
Definition L_LL_FEND_T : Z := 89116.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition KS_LLT : list positive := [2; 3; 4; 5; 9; 10; 11; 12; 14; 17; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32]%positive.
(* [comment removed for export] *)
Definition KS_TBT : list positive := [2; 3; 4; 5; 8; 9; 10; 11; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32]%positive.
(* [comment removed for export] *)
Definition KS_LFT : list positive := [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32]%positive.
Ltac keptc_close ::= cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF KS_LLT KS_TBT KS_LFT]; split_conj; try exact I; zreg.
Ltac keptc_chain HK ::= cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF KS_LLT KS_TBT KS_LFT] in HK |- *; destr_conj HK; split_conj; try exact I;
  cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; first [assumption | reflexivity].
Ltac keptc_trans ::=
  repeat match goal with H : keptc _ _ _ _ |- _ => cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF KS_LLT KS_TBT KS_LFT] in H; destr_conj H end;
  cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF KS_LLT KS_TBT KS_LFT]; split_conj; try exact I;
  rewrite ?zget_zupd in *; cbv [zget_l] in *; cbn [alookup Pos.eqb] in *;
  first [ assumption | reflexivity
        | etransitivity; [eassumption|]; first [assumption | reflexivity | symmetry; assumption] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac tld1 Ha i Hr :=
  lazymatch type of Ha with mem_arr 1 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr' (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | apply Hr; lia | ]); znorm end.

(* [comment removed for export] *)
Lemma mod64_wit : forall z, exists mv, z mod 18446744073709551616 = mv /\
  (0 <= z < 18446744073709551616 -> mv = z) /\ (-18446744073709551616 <= z < 0 -> mv = z + 18446744073709551616).
Proof.
  intros z. exists (z mod 18446744073709551616). split; [reflexivity|]. split; intros Hz.
  - apply Z.mod_small. exact Hz.
  - apply mod_u64_neg. exact Hz.
Qed.
(* [comment removed for export] *)
Lemma order_f_same : forall i, order_f i = I7S.Base.order_f i.
Proof. intros i. reflexivity. Qed.
Lemma order_f_ltT : forall i, 0 <= i < 19 -> 0 <= order_f i < 65536.
Proof. intros i Hi. pose proof (order_f_range i Hi). lia_std. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lenlens_loop_t {RCa1 : RunCtx}  : forall (N : nat) (P : Z -> mem -> Prop) Rb l M MD T
    (u p q n ncode j ci B H : Z) (fin lf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + -256 -> zget_l Rb l kS0 = p -> zget_l Rb l kA0 = A_ORDER -> zget_l Rb l kA1 = ncode ->
  zget_l Rb l kA3 = -19 -> zget_l Rb l kA6 = - ncode -> zget_l Rb l kA5 = j + 1 -> zget_l Rb l kA7 = 2 * j ->
  zget_l Rb l kA4 = q + ci -> zget_l Rb l kA2 = n - ci -> zget_l Rb l kS2 = B -> zget_l Rb l kS4 = H ->
  ncode - j <= Z.of_nat N -> 0 <= j -> j < ncode -> ncode <= 19 ->
  0 <= ci -> ci <= n -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 ->
  Z.max (p + 7176) (q + n) + 1024 <= u -> u + 208 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) -> ZSEP (p + 7176 <= 65536 \/ 139264 <= p) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M A_ORDER 19 order_f ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -136) (- (p + 168) + -1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -128) (p + 168) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf -> (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) ->
  (forall i, 0 <= i < j -> lf (order_f i) <= 7) ->
  P j M ->
  (forall M' jo (a v : Z), P jo M' -> a = p + 156 -> 0 <= v < 4294967296 -> P v (wbytes M' (w64 a) (Z_to_le_bytes 4 v))) ->
  (forall M' jo (a v : Z), P jo M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (* [comment removed for export] *)
  (forall R' M' (j' B' H' : Z) (lf' : Z -> Z),
     zget R' kS2 = B' -> zget R' kS4 = H' -> zget R' kA2 = 0 -> zget R' kA4 = q + n ->
     j <= j' -> j' < ncode -> 0 <= B' -> B' < 3 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * n ->
     B' + 3 * (j' - j) = 8 * (n - ci) + B ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' A_ORDER 19 order_f ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -136) (- (p + 168) + -1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -128) (p + 168) ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) ->
     (forall i, 0 <= i < j' -> lf' (order_f i) <= 7) -> P j' M' ->
     keptc Rb l R' KS_LLT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_LL_T (zupd R' []) M' MD) T) ->
  (* [comment removed for export] *)
  (forall R' M' (ci' B' H' : Z) (lf' : Z -> Z),
     zget R' kS2 = B' -> zget R' kS4 = H' -> zget R' kA2 = n - ci' -> zget R' kA4 = q + ci' -> zget R' kA7 = ncode ->
     zget R' kS0 = p -> zget R' kSP = u + -256 -> zget R' kA0 = A_ORDER ->
     ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' + 3 * (ncode - j) = 8 * (n - ci) + B ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' A_ORDER 19 order_f ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -136) (- (p + 168) + -1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -128) (p + 168) ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) ->
     (forall i, 0 <= i < ncode -> lf' (order_f i) <= 7) -> P ncode M' ->
     keptc Rb l R' KS_LLT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_FILL_T (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_HEAD_T (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T u p q n ncode j ci B H fin lf Hh L3 L28 L11 L12 L14 L17 L16 L18 L15 L13 L10 L20
    HN Hj0 Hj1 Hnc Hc0 Hc1 HB0 HB1 HH0 HH1 HBc Hq1 Hn26 Hq2 Hp1 Hp2 Hu1 Hu2 SPQ SPR Wp Hin Rfin Hord S136 S128 Hlens Rlf Hlf7 HP HPa HPb KX KD; [lia|].
  zkeys. unfold L_LL_HEAD_T, L_LL_FILL_T, L_LVX_LL_T, A_ORDER in *. pose proof two64_eq as TW64.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  pose proof (lnot_val_mod' (p + 168) ltac:(lia)) as Hnl.
  zstep Rfd.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (BODY : forall RJ (cib Hb Bb : Z),
    zget RJ kSP = u + -256 -> zget RJ kS0 = p -> zget RJ kA0 = 67132 -> zget RJ kA1 = ncode ->
    zget RJ kA3 = -19 -> zget RJ kA6 = - ncode -> zget RJ kA5 = j + 1 -> zget RJ kA7 = 2 * j ->
    zget RJ kA4 = q + cib -> zget RJ kA2 = n - cib -> zget RJ kS2 = Bb -> zget RJ kS4 = Hb ->
    ci <= cib -> cib <= n -> 3 <= Bb -> Bb <= 40 -> 0 <= Hb -> Hb < 2 ^ Bb -> Bb <= 8 * cib ->
    8 * (n - cib) + Bb = 8 * (n - ci) + B ->
    keptc Rb l RJ KS_LLT ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_BODY_T (zupd RJ []) M MD) T).
  { intros RJ cib Hb Bb G3 G28 G11 G12 G14 G17 G16 G18 G15 G13 G10 G20 X1 X2 X3 X4 X5 X6 X7 X8 HK.
    unfold L_LL_BODY_T. zkeys.
    pose proof (pow2_48 Bb ltac:(lia)) as HPBb.
    pose proof (land7_range Hb) as Hv.
    pose proof (order_f_range j ltac:(lia)) as Ho. pose proof (order_f_ltT j ltac:(lia)) as Ho2.
    assert (Rord : forall i, 0 <= i < 19 -> 0 <= order_f i < 65536) by (intros; apply order_f_ltT; lia).
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (j + -18) ltac:(symmetry; rewrite swrap32_small by lia; lia).
    zstep Rfd.                        (* [comment removed for export] *)
    tstoreP Rfd HP HPa.               (* [comment removed for export] *)
    dand (mod64_wit (j + -18)) as (mv1 & Hmv1 & Hmv1a & Hmv1b).
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd. znot.                  (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (2 * order_f j) ltac:(rewrite shiftl_1m; reflexivity).
    zstep Rfd.                        (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (Hb / 2 ^ 3) ltac:(symmetry; apply (srl_hold Hb Bb 3); lia).
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstore_arrP2 Rfd Hlens (order_f j) HP HPb. (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (j + 2 - ncode) ltac:(symmetry; rewrite swrap32_small by lia; lia).
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (drop3_bound Hb Bb ltac:(lia) ltac:(lia)) as Hd3.
    assert (Rlf1 : forall i, 0 <= i < 320 -> 0 <= zfupd lf (order_f j) (Z.land Hb 7) i < 65536).
    { intros i Hi. unfold zfupd. destruct (Z.eqb_spec i (order_f j)); [lia | apply Rlf; lia]. }
    assert (Hlf7' : forall i, 0 <= i < j + 1 -> zfupd lf (order_f j) (Z.land Hb 7) (order_f i) <= 7).
    { intros i Hi. unfold zfupd. destruct (Z.eqb_spec (order_f i) (order_f j)); [lia|]. apply Hlf7.
      destruct (Z.eq_dec i j); [subst; congruence | lia]. }
    dand (mod64_wit (j + 2 - ncode)) as (mv2 & Hmv2 & Hmv2a & Hmv2b).
    destruct (Z.eq_dec (ncode - j) 1) as [Hlast | Hmore].
    - zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KD Rx Mx cib (Bb - 3) (Hb / 2 ^ 3) (zfupd lf (order_f j) (Z.land Hb 7))) end;
        try zreg; try assumption; try lia.
      + intros i Hi. apply Hlf7'. lia.
      + replace ncode with (j + 1) by lia. exact HP.
      + keptc_trans.
    - zbr Rfd true.                   (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (IH P Rx lx Mx MD T u p q n ncode (j + 1) cib (Bb - 3) (Hb / 2 ^ 3) fin (zfupd lf (order_f j) (Z.land Hb 7)) Hh) end;
        try zreg; try assumption; try lia.
      + intros R' M' j' B' H' lf'. intros. eapply (KX R' M' j' B' H' lf'); try eassumption; try lia. keptc_trans.
      + intros R' M' ci' B' H' lf'. intros. eapply (KD R' M' ci' B' H' lf'); try eassumption; try lia. keptc_trans. }
  destruct (Z_lt_dec 2 B) as [HB3 | HB3].
  - zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (BODY Rx ci H B) end; try zreg; try lia. keptc_close.
  - zbr Rfd false.
    destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
    + zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KX Rx Mx j B H lf) end;
        try zreg; try assumption; try lia. keptc_close.
    + zbr Rfd true.                   (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zbr Rfd true.                   (* [comment removed for export] *)
      pose proof (Rfin ci ltac:(lia)) as Rb1.
      tld1 Hin ci Rfin.               (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
      pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hpl0 Hpl1].
      zstep Rfd.                      (* [comment removed for export] *)
      zsetreg (B + 8) ltac:(symmetry; apply lor8_small; lia).
      tstep1 Rfd.                     (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (BODY Rx (ci + 1) (fin ci * 2 ^ B + H) (B + 8)) end;
        try zreg; try lia.
      keptc_close.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fill_loop_t {RCa1 : RunCtx}  : forall (N : nat) (P : Z -> mem -> Prop) Rb l M MD T (u p j jo e6 : Z) (lf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + -256 -> zget_l Rb l kA0 = A_ORDER -> zget_l Rb l kA1 = 2 * j -> zget_l Rb l kA2 = A_ORDER + 2 * j ->
  zget_l Rb l kA6 = e6 ->
  19 - j <= Z.of_nat N -> 0 <= j -> j < 19 ->
  0 < p -> p + 7176 <= 140737488355328 -> p + 7176 + 1024 <= u -> u + 208 <= 140737488355328 ->
  ZSEP (p + 7176 <= 65536 \/ 139264 <= p) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M A_ORDER 19 order_f ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -136) (- (p + 168) + -1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -128) (p + 168) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf -> (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) ->
  (forall i, 0 <= i < j -> lf (order_f i) <= 7) ->
  P jo M ->
  (forall M' jo' (a v : Z), P jo' M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo' (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (forall R' M' (lf' : Z -> Z),
     zget R' kSP = u + -256 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' A_ORDER 19 order_f ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -136) (- (p + 168) + -1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -128) (p + 168) ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) ->
     (forall i, 0 <= i < 19 -> lf' (order_f i) <= 7) -> P jo M' ->
     keptc Rb l R' KS_LFT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_FEND_T (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_FLOOP_T (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T u p j jo e6 lf Hh L3 L11 L12 L13 L17 HN Hj0 Hj1 Hp1 Hp2 Hu1 Hu2 SPR Wp Hord S136 S128 Hlens Rlf Hlf7 HP HPb K; [lia|].
  zkeys. unfold L_LL_FLOOP_T, L_LL_FEND_T, A_ORDER in *. pose proof two64_eq as TW64.
  pose proof (order_f_range j ltac:(lia)) as Ho. pose proof (order_f_ltT j ltac:(lia)) as Ho2.
  assert (Rord : forall i, 0 <= i < 19 -> 0 <= order_f i < 65536) by (intros; apply order_f_ltT; lia).
  pose proof (lnot_val_mod' (p + 168) ltac:(lia)) as Hnl.
  zstep Rfd. znot.                    (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  tstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (2 * order_f j) ltac:(rewrite shiftl_1m; reflexivity).
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  tstore_arrP2 Rfd Hlens (order_f j) HP HPb. (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  assert (Rlf1 : forall i, 0 <= i < 320 -> 0 <= zfupd lf (order_f j) 0 i < 65536).
  { intros i Hi. unfold zfupd. destruct (Z.eqb_spec i (order_f j)); [lia | apply Rlf; lia]. }
  assert (Hlf7' : forall i, 0 <= i < j + 1 -> zfupd lf (order_f j) 0 (order_f i) <= 7).
  { intros i Hi. unfold zfupd. destruct (Z.eqb_spec (order_f i) (order_f j)); [lia|]. apply Hlf7.
    destruct (Z.eq_dec i j); [subst; congruence | lia]. }
  destruct (Z.eq_dec j 18) as [Hlast | Hmore].
  - zbr Rfd false.                    (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx (zfupd lf (order_f j) 0)) end;
      try zreg; try assumption.
    + intros i Hi. apply Hlf7'. lia.
    + keptc_close.
  - zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH P Rx lx Mx MD T u p (j + 1) jo (e6 + 1) (zfupd lf (order_f j) 0) Hh) end;
      try zreg; try assumption; try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma table_loop_t {RCa1 : RunCtx}  : forall (k : nat) Rb l M MD T (q n cinj holdj j stm : Z) (fin : Z -> Z),
  m_halted MD = None -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  14 - 8 * Z.of_nat k <= j < 22 - 8 * Z.of_nat k -> (1 <= k <= 2)%nat -> 0 <= j ->
  0 <= cinj <= n -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 ->
  zget_l Rb l kA1 = j -> zget_l Rb l kA7 = j -> zget_l Rb l kA2 = n - cinj ->
  zget_l Rb l kA5 = q + cinj -> zget_l Rb l kT0 = q + cinj -> zget_l Rb l kS4 = holdj ->
  zget_l Rb l kS1 = stm -> zget_l Rb l kA3 = stm ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin ->
  (forall R' hold' j',   (* [comment removed for export] *)
     zget R' kA2 = 0 -> zget R' kS4 = hold' -> zget R' kA3 = stm ->
     j' = j + 8 * (n - cinj) -> 0 <= hold' < 2 ^ j' -> n - cinj < Z.of_nat k ->
     keptc Rb l R' KS_TBT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_TAB_T (zupd R' []) M MD) T) ->
  (forall R' hold' j',   (* [comment removed for export] *)
     zget R' kA4 = q + cinj + Z.of_nat k -> zget R' kA2 = n - cinj - Z.of_nat k ->
     zget R' kA1 = j' -> zget R' kS4 = hold' -> zget R' kA3 = stm ->
     j' = j + 8 * Z.of_nat k -> 0 <= hold' < 2 ^ j' -> Z.of_nat k <= n - cinj ->
     keptc Rb l R' KS_TBT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TAB_BODY_T (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TAB_LOOP_T (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros Rb l M MD T q n cinj holdj j stm fin Hh Hfin Hj Hk Hj0 Hc Hhj Hjc Hq1 Hn26 Hq2 L12 L18 L13 L16 L6 L20 L9 L14 Hin KLV KDN; [lia|].
  zkeys. unfold L_TAB_LOOP_T, L_TAB_BODY_T, L_LVX_TAB_T in *. pose proof two64_eq as TW64.
  assert (Hj40 : 2 ^ j <= 2 ^ 21) by (apply Z.pow_le_mono_r; lia). change (2 ^ 21) with 2097152 in Hj40.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  - (* [comment removed for export] *)
    zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KLV R' holdj j) end; try zreg; try lia.
    all: first [ keptc_close | replace (j + 8 * (n - cinj)) with j by lia; lia ].
  - zbr Rfd true.                     (* [comment removed for export] *)
    pose proof (Hfin cinj ltac:(lia)) as Hb0.
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (fin cinj * 2 ^ j) ltac:(rewrite (Z.mod_small j) by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (pullbyte_bound holdj j (fin cinj) ltac:(lia) Hhj Hb0) as Hpb.
    destruct k as [|k'].
    + (* [comment removed for export] *)
      zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KDN R' (fin cinj * 2 ^ j + holdj) (j + 8)) end; try zreg; try lia.
      keptc_close.
    + zbr Rfd true.                   (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') _ _) _ =>
        eapply (IH R' l' M MD T q n (cinj + 1) (fin cinj * 2 ^ j + holdj) (j + 8) stm fin Hh Hfin) end;
        [ lia | lia | lia | lia | lia | lia | lia | lia | lia | zreg .. | exact Hin | | ].
      * intros R' hold' j'. intros. eapply KLV; try eassumption; try lia.
      * intros R' hold' j'. intros. eapply KDN; try eassumption; try lia.
Qed.
End T_TableL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require S_CodelensT.

Module T_CodelensT.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ItCovIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ItBridge.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_DistL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_CodelensT.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U.TBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U.T_ClDefs.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition L_LENS_RET_T : Z := 90256.  (* [comment removed for export] *)
Definition L_DTAB_T : Z := 90988.      (* [comment removed for export] *)
Definition L_DISTS_RET_T : Z := 91068. (* [comment removed for export] *)
Definition L_CL_OK_T : Z := 93548.     (* [comment removed for export] *)
Definition L_EOB_T : Z := 90820.       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mem_u64_eqv_t {RCa1 : RunCtx}  : forall M a v v', v = v' -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v'.
Proof. intros M a v v' <- H. exact H. Qed.
Lemma mem_u64_mod_t {RCa1 : RunCtx}  : forall M a v, mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a (v mod 18446744073709551616).
Proof. intros M a v H. unfold mem_u64 in *. change 18446744073709551616 with two64. rewrite Z_to_le_bytes_mod by lia_std. exact H. Qed.
Lemma work_arr_t {RCa1 : RunCtx}  : forall M p, mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> 0 <= p -> p + 7176 <= two64 ->
  exists wf, mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 808) 288 wf /\ (forall i, 0 <= i < 288 -> 0 <= wf i < 65536).
Proof.
  intros M p W Hp1 Hp2.
  destruct (mem_wr_readable (run_segments R_segs rc_inp rc_sp rc_mb) wr_rd_R M (p + 808) 576 ltac:(eapply mem_wr_sub; [exact W | lia_std | lia_std]) ltac:(lia_std)) as [bs [A B]].
  exists (le_cell 2 bs). split.
  - apply (mem_arr_of_bytes (run_segments R_segs rc_inp rc_sp rc_mb) 2 M (p + 808) 288 bs A); try lia_std.
  - intros i _. apply le_cell2_range.
Qed.
Lemma rom_it_tabs_t {RCa1 : RunCtx}  : forall M, rom_ok M ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M LBASE_ADDR 31 (arr_get lbase_a) /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M LEXT_ADDR 31 (arr_get lext_a) /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M DBASE_ADDR 32 (arr_get dbase_a) /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M DEXT_ADDR 32 (arr_get dext_a).
Proof.
  intros M H. cbv [LBASE_ADDR LEXT_ADDR DBASE_ADDR DEXT_ADDR]. split_conj.
  - eapply mem_arr_ext; [apply rom_lbase_arr; exact H | intros; apply lbase_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_lext_arr; exact H | intros; apply lext_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_dbase_arr; exact H | intros; apply dbase_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_dext_arr; exact H | intros; apply dext_f_model; assumption].
Qed.
(* [comment removed for export] *)
Lemma i_frame_slots_t {RCa1 : RunCtx}  : forall cx M, i_frame cx M ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -120) 0 /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -128) (c_p cx + 168) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -136) (- (c_p cx + 168) + -1) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -176) 16209 /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -216) (c_p cx + 160) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -224) (c_p cx + 808) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -232) (c_p cx + 1384) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -240) (c_p cx + 136) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -248) (c_p cx + 140).
Proof. intros cx M H. unfold i_frame in H. destr_conj H. split_conj; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CLT.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Hypothesis ITABLE : itable_spec_t.
Hypothesis LENU : lenu_stmt.

(* [comment removed for export] *)
Local Ltac itable_pre SEP AL Wstk LF15 :=
  first [ lazymatch goal with
       | |- zget_l _ _ _ = _ => cbv [cty o_lens o_next o_work o_lenbits o_distbits]; zreg
       | |- Z.land _ _ = _ => reflexivity
       | |- _ \/ _ => first [ left; cbv [o_lenbits]; reflexivity | right; cbv [o_distbits]; reflexivity ]
       | |- ZSEP _ => unfold ZSEP; pose proof (sep_p_rom _ _ SEP) as D; cbn [c_p] in D; cbv [STATE_SIZE ROM_LO_ALL DEXT_ADDR ROMHI_T] in D |- *; clear - D; lia
       | |- _ mod 16 = 0 => first [ exact (proj1 (proj2 AL)) | apply mod0_add; [lia | exact (proj1 AL) | reflexivity] ]
       | |- mem_wr _ _ _ _ => first [ assumption | cbv [FR_IT]; eapply mem_wr_sub; [exact Wstk | lia | lia] ]
       | |- mem_arr _ _ _ _ _ _ => assumption
       | |- mem_u64 _ _ _ _ => first [ assumption | eapply mem_u64_eqv_t; [| eassumption]; cbv [o_codes]; lia ]
       | |- mem_u32 _ _ _ _ => assumption
       | |- forall i : Z, _ -> _ <= _ < _ => assumption
       | |- _ = CODES -> _ => intros X; discriminate X
       | |- _ = DISTS -> _ => first [ intros X; discriminate X | intros _; lia ]
       | |- forall s : Z, _ -> _ <= 15 => intros s Hs; first [ replace (0 + s) with s by lia | idtac ]; apply LF15; lia
       | |- forall R' M', _ => idtac
       | |- _ => cbv [FRA STATE_SIZE N_LENS N_CODES FR_IT ENOUGH_LENS ENOUGH_DISTS DEXT_ADDR]; cbn [it_room]; cbv [ENOUGH_LENS ENOUGH_DISTS]; first [assumption | lia]
       end | match goal with |- ?G => idtac "ITFAIL" G end ].

Theorem cldone_t : cldone_stmt.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm Hhave SI RG KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (MC : t_mode st = CODELENS -> 257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            t_shave st <= t_nlen st + t_ndist st /\ (forall i, 0 <= i < t_shave st -> lf i <= 15) /\ ctable_live st cf) by mode_get MODE_.
  specialize (MC Hm). dand MC as (Hnl1 & Hnl2 & Hnd1 & Hnd2 & Hsh & Hlf15 & _). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  assert (LF15 : forall i, 0 <= i < nlen + ndist -> lf i <= 15) by (intros i Hi; apply Hlf15; lia). clear Hlf15 Hsh Hhave.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  match goal with H : forall i, _ -> 0 <= cf i < 4294967296 |- _ => rename H into Rcf end.
  pose proof (rng_dc _ _ _ _ SI0) as Hdc. cbn [t_dc] in Hdc. cbv [N_CODES] in Hdc.
  unfold s_regs_cld, s_vars in RG. icx_cbn. destr_conj RG.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (i_frame_slots_t _ _ FRM) as FS. icx_cbn.
  dand FS as (Q136 & Q128 & Q120 & Q80 & Q40 & Q32 & Q24 & Q16 & Q8).
  unfold st_rest in SREST. icx_cbn.
  dand SREST as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
  pose proof SRET as SRET'. unfold s_ret in SRET'. icx_cbn. clear SRET.
  assert (Rdb : 0 <= db < 4294967296) by lia. pose proof (Rlf 256 ltac:(lia)) as R256.
  prune_rng.
  zkeysb. unfold L_CL_DONE, L_LENS_RET_T, L_DTAB_T, L_DISTS_RET_T, L_CL_OK_T, L_EOB_T, L_BADMSG_A0, L_DISP, L_ITABLE, L_LEN_ in *.
  pose proof two64_eq as TW64.
  assert (Hm513 : (-513) mod 18446744073709551616 = 18446744073709551103) by reflexivity.
  pose proof (lnot_val_mod' (p + 168) ltac:(lia)) as Hnlens.
  fp_frame_from HP0.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  destruct (Z.eq_dec (lf 256) 0) as [Hz | Hnz].
  { (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd. zstep Rfd. zlit.       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB.
    cbn [t_mode] in MB. change (rank CODELENS) with 20 in MB.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KD Rx Mx (bad_of (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) lf cf
                (sinv_bad_of _ _ _ _ SI0)) end.
    - clear - MB. unfold bad_of. unfold SBase.bad_of in MB. cbn [t_mode] in *. lia_std.   (* [comment removed for export] *)
    - unfold s_regs_disp, s_fix, s_vars, bad_of; icx_cbn; zkeys; split_conj; zreg.
    - unfold k_mem, st_at, st_rest, s_ret, bad_of; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std.
      all: first [ cbv [BAD]; assumption | exact HAG | sbk ]. }
  (* [comment removed for export] *)
  zbr Rfd false.                      (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    destruct (work_arr_t Mx p Wp ltac:(lia) ltac:(rewrite TW64; lia)) as (wf & Hwork & Rwf);
    dand (rom_it_tabs_t Mx ROM) as (RT1 & RT2 & RT3 & RT4) end.
  lazymatch goal with H120 : mem_u32 _ ?Mx (p + 136) 9, H144 : mem_u64 _ ?Mx (p + 160) (p + 1384) |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    rename H120 into C120n; rename H144 into C144n end.
  pose proof ITABLE as ITABLE1. unfold itable_spec_t, itable_spec_at in ITABLE1.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (ITABLE1 Rx lx Mx MD T LENS p 0 nlen 0 9 (p + 136) (u + -256) 90256 zc lf cf wf Hh) end.
  all: itable_pre SEP AL Wstk LF15.
  clear ITABLE1.
  (* [comment removed for export] *)
  intros R' M' cf' wf' Hrv Hret3 Hcf' Hwf' Rcf' Rwf' HP Hlens' Hcodes' Hwork' Hnext' Hbits' KE.
  set (r := inflate_table _ _ _ _ _ _ _ _) in *.
  assert (BR : it_ret r = 0 ->
     tab_ok LENS (rdc cf' (CDyn 0)) (it_bits r) (it_table r - 0) = true /\ 1 <= it_bits r <= 15 /\
     0 + 2 ^ it_bits r <= it_table r <= 0 + it_room LENS /\ (forall i, 0 <= i < N_CODES -> ~ (0 <= i < it_table r) -> cf' i = cf i)).
  { intros Hr0. apply (tab_ok_of_itable LENS lf cf wf cf' 0 nlen 0 9); cbv [N_LENS N_CODES]; cbn [it_room]; cbv [ENOUGH_LENS]; try assumption; try lia.
    - intros s Hs. replace (0 + s) with s by lia. apply LF15. lia.
    - intros X; discriminate X.
    - intros X; discriminate X. }
  assert (FS1 : it_ret r <> 0 -> it_table r = 0 /\ it_bits r = 9).
  { intros Hne. exact (inflate_table_fail_shape LENS (arr_init N_LENS lf) 0 nlen (arr_init N_CODES cf) 0 9 (arr_init N_WORK wf) Hne). }
  clearbody r.
  unfold kept_eq in KE. zkeys. destr_conj KE. zimps.
  clear Hwork RT1 RT2 RT3 RT4 C120n C144n Hcodes Hlens.
  unfold it_fp in HP. cbv [o_next o_work o_codes o_lenbits N_WORK N_CODES FR_IT] in HP. zreattachL HP.
  cbv [o_lens o_codes o_work o_next o_lenbits N_LENS N_CODES N_WORK] in Hlens', Hcodes', Hwork', Hnext', Hbits'.
  cbv [N_CODES] in Rcf', BR. cbv [N_WORK] in Rwf'. cbn [it_room] in BR. cbv [ENOUGH_LENS] in BR.
  destruct (Z.eq_dec (it_ret r) 0) as [Hr0 | Hnz1].
  2: { (* [comment removed for export] *)
    destruct (FS1 Hnz1) as [Ht0 Hb9]. clear BR FS1.
    assert (Hrm : exists rm, it_ret r mod 18446744073709551616 = rm /\ rm <> 0 /\ 0 <= rm < 18446744073709551616).
    { exists (it_ret r mod 18446744073709551616). split; [reflexivity|].
      destruct Hret3 as [E | [E | E]]; [exfalso; exact (Hnz1 E) | rewrite E | rewrite E];
        [ rewrite Z.mod_small by lia_std; lia_std
        | replace ((-1) mod 18446744073709551616) with 18446744073709551615 by reflexivity; lia_std ]. }
    dand Hrm as (rm & Hrm & Hrm0 & Hrm1).
    zbr Rfd false.                    (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    lazymatch goal with H : mem_u64 _ ?Mx (u + -184) _ |- realizes _ (zcfg _ _ _ ?Mx _) _ =>   (* [comment removed for export] *)
      apply mem_u64_mod_t in H; rewrite Hrm in H end.
    zstep Rfd. zstep Rfd. zlit.       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (sinv_cl_bad _ _ lf cf cf' rm (it_bits r) dc db (it_table r) SI0 eq_refl (conj (proj1 Hrm1) (proj2 Hrm1))
                  ltac:(lia) ltac:(lia) Hdc ltac:(lia) ltac:(cbv [N_CODES]; lia) ltac:(cbv [N_CODES]; exact Rcf')) as [SI1 ME1].
    rewrite Ht0 in *. rewrite Hb9 in *.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KB0 Rx Mx (st_tab (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                                 CODELENS rm 9 dc db 0) lf cf') end.
    + unfold bad_of, st_tab; cbn. unfold st_tab in SI1; cbn in SI1. exact SI1.
    + unfold bad_of, st_tab; cbn. unfold st_tab in ME1; cbn in ME1. exact ME1.
    + zreg. + zreg. + zreg. + zreg. + zreg.
    + unfold st_tab; icx_cbn; zreg. + unfold st_tab; icx_cbn; zreg. + unfold st_tab; icx_cbn; zreg. + unfold st_tab; icx_cbn; zreg. + unfold st_tab; icx_cbn; zreg.
    + lazymatch goal with |- 0 <= ?x < _ => assert (EA0 : x = 66363) by zreg; rewrite EA0 end. lia.
    + unfold k_mem, st_at, st_rest, s_ret, st_tab; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [CODELENS]; assumption | exact HAG | sbk | eapply mem_u64_eqv_t; [| eassumption]; lia ]. }
  (* [comment removed for export] *)
  dand (BR Hr0) as (TOK1 & Hb15 & Htab1 & Hout1). clear BR FS1.
  rewrite Hr0 in Hrv. rewrite Z.sub_0_r in TOK1.
  pose proof (pow2_pos (it_bits r) ltac:(lia)) as Hpw1.
  zbr Rfd true.                       (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (2 * nlen) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 1) with 2; rewrite ?Z.mod_small by lia; lia).
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    dand (rom_it_tabs_t Mx ROM) as (RT1 & RT2 & RT3 & RT4) end.
  lazymatch goal with H124 : mem_u32 _ ?Mx (p + 140) 6, H112 : mem_u64 _ ?Mx (p + 128) _ |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    rename H124 into C124n; rename H112 into C112n end.
  pose proof ITABLE as ITABLE2. unfold itable_spec_t, itable_spec_at in ITABLE2.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (ITABLE2 Rx lx Mx MD T DISTS p nlen ndist (it_table r) 6 (p + 140) (u + -256) 91068 zc lf cf' wf' Hh) end.
  all: itable_pre SEP AL Wstk LF15.
  clear ITABLE2.
  (* [comment removed for export] *)
  intros R'' M'' cf'' wf'' Hrv2 Hret32 Hcf'' Hwf'' Rcf'' Rwf'' HP2 Hlens'' Hcodes'' Hwork'' Hnext'' Hbits'' KE2.
  set (r2 := inflate_table _ _ _ _ _ _ _ _) in *.
  assert (BR2 : it_ret r2 = 0 ->
     tab_ok DISTS (rdc cf'' (CDyn (it_table r))) (it_bits r2) (it_table r2 - it_table r) = true /\ 1 <= it_bits r2 <= 15 /\
     it_table r + 2 ^ it_bits r2 <= it_table r2 <= it_table r + it_room DISTS /\
     (forall i, 0 <= i < N_CODES -> ~ (it_table r <= i < it_table r2) -> cf'' i = cf' i)).
  { intros Hr0'. apply (tab_ok_of_itable DISTS lf cf' wf' cf'' nlen ndist (it_table r) 6); cbv [N_LENS N_CODES]; cbn [it_room]; cbv [ENOUGH_DISTS]; try assumption; try lia.
    - intros s Hs. apply LF15. lia.
    - intros X; discriminate X. }
  assert (FS2 : it_ret r2 <> 0 -> it_table r2 = it_table r /\ it_bits r2 = 6).
  { intros Hne. exact (inflate_table_fail_shape DISTS (arr_init N_LENS lf) nlen ndist (arr_init N_CODES cf') (it_table r) 6 (arr_init N_WORK wf') Hne). }
  clearbody r2.
  unfold kept_eq in KE2. zkeys. destr_conj KE2. zimps.
  clear RT1 RT2 RT3 RT4 C124n Hcodes' Hlens' Hwork' Hnext'.
  unfold it_fp in HP2. cbv [o_next o_work o_codes o_distbits N_WORK N_CODES FR_IT] in HP2. zreattachL HP2.
  cbv [o_lens o_codes o_work o_next o_distbits N_LENS N_CODES N_WORK] in Hlens'', Hcodes'', Hwork'', Hnext'', Hbits''.
  cbv [N_CODES] in Rcf'', BR2. cbn [it_room] in BR2. cbv [ENOUGH_DISTS] in BR2.
  tstep1 Rfd.                         (* [comment removed for export] *)
  destruct (Z.eq_dec (it_ret r2) 0) as [Hr20 | Hnz2].
  - (* [comment removed for export] *)
    dand (BR2 Hr20) as (TOK2 & Hb25 & Htab2 & Hout2). clear BR2 FS2.
    rewrite Hr20 in *.
    pose proof (pow2_pos (it_bits r2) ltac:(lia)) as Hpw2.
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd. zlit.                  (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zbr Rfd false.                    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (TOK1' : tab_ok LENS (rdc cf'' (CDyn 0)) (it_bits r) (it_table r) = true).
    { eapply tab_ok_ext_rd; [| exact TOK1]. intros i Hi. unfold rdc. apply Hout2; cbv [N_CODES]; lia. }
    pose proof (sinv_cl_len_ _ _ lf cf cf'' (it_bits r) (it_table r) (it_bits r2) (it_table r2) SI0 eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv [N_CODES]; lia)
                  TOK1' TOK2 ltac:(cbv [N_CODES]; exact Rcf'')) as [SI1 ME1].
    unfold st_tab in SI1, ME1. ist_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (LENU (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (IST LEN_ last flags cin cout hold bits out 0 length offset extra (CDyn 0) (CDyn (it_table r)) (it_bits r) (it_bits r2)
                     ncode nlen ndist shave (it_table r2) whave wnext)
                lf cf'' CX0 Hh Hfin eq_refl SI1) end.
    + unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys; split_conj; zreg.
    + unfold k_mem, st_at, st_rest, s_ret; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [LEN_]; assumption | exact HAG | sbk | eapply mem_u64_eqv_t; [| eassumption]; lia ].
    + eapply KALL_mono; [| exact KA0]. clear - ME1. lia.
  - (* [comment removed for export] *)
    destruct (FS2 Hnz2) as [Ht2 Hb6]. clear BR2 FS2.
    assert (Hrm : exists rm, it_ret r2 mod 18446744073709551616 = rm /\ rm <> 0 /\ 0 <= rm < 18446744073709551616).
    { exists (it_ret r2 mod 18446744073709551616). split; [reflexivity|].
      destruct Hret32 as [E | [E | E]]; [exfalso; exact (Hnz2 E) | rewrite E | rewrite E];
        [ rewrite Z.mod_small by lia_std; lia_std
        | replace ((-1) mod 18446744073709551616) with 18446744073709551615 by reflexivity; lia_std ]. }
    dand Hrm as (rm & Hrm & Hrm0 & Hrm1).
    lazymatch goal with H : mem_u64 _ ?Mx (u + -184) _ |- realizes _ (zcfg _ _ _ ?Mx _) _ =>   (* [comment removed for export] *)
      apply mem_u64_mod_t in H; rewrite Hrm in H end.
    zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd. zstep Rfd. zlit.       (* [comment removed for export] *)
    pose proof (sinv_cl_bad _ _ lf cf cf'' rm (it_bits r) (CDyn (it_table r)) (it_bits r2) (it_table r2) SI0 eq_refl (conj (proj1 Hrm1) (proj2 Hrm1))
                  ltac:(lia) ltac:(lia) ltac:(cbv [N_CODES]; lia) ltac:(lia) ltac:(cbv [N_CODES]; lia) ltac:(cbv [N_CODES]; exact Rcf'')) as [SI1 ME1].
    rewrite Ht2 in *. rewrite Hb6 in *.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KB0 Rx Mx (st_tab (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                                 CODELENS rm (it_bits r) (CDyn (it_table r)) 6 (it_table r)) lf cf'') end.
    + unfold bad_of, st_tab; cbn. unfold st_tab in SI1; cbn in SI1. exact SI1.
    + unfold bad_of, st_tab; cbn. unfold st_tab in ME1; cbn in ME1. exact ME1.
    + zreg. + zreg. + zreg. + zreg. + zreg.
    + unfold st_tab; icx_cbn; zreg. + unfold st_tab; icx_cbn; zreg. + unfold st_tab; icx_cbn; zreg. + unfold st_tab; icx_cbn; zreg. + unfold st_tab; icx_cbn; zreg.
    + lazymatch goal with |- 0 <= ?x < _ => assert (EA0 : x = 66740) by zreg; rewrite EA0 end. lia.
    + unfold k_mem, st_at, st_rest, s_ret, st_tab; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [CODELENS]; assumption | exact HAG | sbk | eapply mem_u64_eqv_t; [| eassumption]; lia ].
Qed.

End CLT.
End T_CodelensT.

Module T_Table.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ItCovIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ItBridge.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_DistL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_TableL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_Table.
Import T_TableL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U.T_ClDefs T_CodelensT OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition L_TAB_SKIP_T : Z := 88712.  (* [comment removed for export] *)
Definition L_LL_SETUP_T : Z := 88812.  (* [comment removed for export] *)
Definition L_LL_TABLE_T : Z := 89124.  (* [comment removed for export] *)
Definition L_LL_RET_T : Z := 89176.    (* [comment removed for export] *)
Definition L_BAD_TAB_T : Z := 90344.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac st_cell_tac Hp1 Hp2 :=
  lazymatch goal with
  | |- mem_u32 _ (wbytes _ (w64 ?a) _) ?a _ => apply mem_u32_stored; clear - Hp1 Hp2; lia_std
  | |- mem_u64 _ (wbytes _ (w64 ?a) _) ?a _ => apply mem_u64_stored; clear - Hp1 Hp2; lia_std
  | |- mem_u32 _ (wbytes _ _ _) _ _ => apply mem_u32_frame; [st_cell_tac Hp1 Hp2 | clear - Hp1 Hp2; unfold zdisj; rewrite length_Z_to_le_bytes'; cbn; lia_std]
  | |- mem_u64 _ (wbytes _ _ _) _ _ => apply mem_u64_frame; [st_cell_tac Hp1 Hp2 | clear - Hp1 Hp2; unfold zdisj; rewrite length_Z_to_le_bytes'; cbn; lia_std]
  | |- _ => assumption
  end.
Lemma st_rest_set140_t {RCa1 : RunCtx}  : forall cx st M v,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_sh st v) (wbytes M (w64 (c_p cx + 156)) (Z_to_le_bytes 4 v)).
Proof.
  intros cx st M v H Hp1 Hp2; destruct cx, st; unfold st_rest, st_sh in *; icx_cbn.
  pose proof two64_eq as TW64.
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  repeat split; st_cell_tac Hp1 Hp2.
Qed.
Lemma st_rest_llt_t {RCa1 : RunCtx}  : forall cx st M v,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_lt st v 0)
    (* a worker 1.4 UBSan: the distcode store (p+128) comes between lencode and lenbits (as plain S_GroupB) *)
    (wbytes (wbytes (wbytes (wbytes M (w64 (c_p cx + 120)) (Z_to_le_bytes 8 (c_p cx + 1384)))
                            (w64 (c_p cx + 128)) (Z_to_le_bytes 8 (c_p cx + 1384)))
                    (w64 (c_p cx + 136)) (Z_to_le_bytes 4 v))
            (w64 (c_p cx + 160)) (Z_to_le_bytes 8 (c_p cx + 1384))).
Proof.
  intros cx st M v H Hp1 Hp2; destruct cx, st; unfold st_rest, st_lt in *; icx_cbn. cbv [cp_addr o_codes]. icx_cbn.
  pose proof two64_eq as TW64.
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  rewrite Z.mul_0_r, Z.add_0_r.
  repeat split; st_cell_tac Hp1 Hp2.
Qed.
Lemma st_rest_tb3_t {RCa1 : RunCtx}  : forall cx st M vc vn vd,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_tb st (t_mode st) (t_cin st) (t_hold st) (t_bits st) vc vn vd (t_shave st))
    (wbytes (wbytes (wbytes M (w64 (c_p cx + 144)) (Z_to_le_bytes 4 vc))
                    (w64 (c_p cx + 148)) (Z_to_le_bytes 4 vn))
            (w64 (c_p cx + 152)) (Z_to_le_bytes 4 vd)).
Proof.
  intros cx st M vc vn vd H Hp1 Hp2; destruct cx, st; unfold st_rest, st_tb in *; icx_cbn.
  pose proof two64_eq as TW64.
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  repeat split; st_cell_tac Hp1 Hp2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PLT {RCa1 : RunCtx}  (cx : ictx) (fin : Z -> Z) (M0 : mem) (st : ist) (cf : Z -> Z) (j : Z) (M : mem) : Prop :=
  s_std cx fin M /\ st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_sh st j) M /\ s_ret cx st M /\ s_lo cx st M /\
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf /\ mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx) /\ s_bk cx st M.

Lemma PLT_store140 {RCa1 : RunCtx}  : forall cx fin M0 st cf jo M a v,
  ctx_ok ROMHI_T cx -> PLT cx fin M0 st cf jo M -> a = c_p cx + 156 -> 0 <= v < 4294967296 ->
  PLT cx fin M0 st cf v (wbytes M (w64 a) (Z_to_le_bytes 4 v)).
Proof.
  intros cx fin M0 st cf jo M a v CX H -> Hv.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  dand H as (STD & [Hmode SREST] & RET & SLO & HC & HP0 & SBK). open_std STD. unfold PLT. icx_cbn. cbv [N_LENS N_CODES] in *.
  cbv [ROMHI_T] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof (st_rest_set140_t _ _ _ v SREST ltac:(cbn; lia) ltac:(cbn; lia)) as SR1. clear SREST.
  unfold st_sh in SR1, Hmode |- *. cbn [c_p t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SR1, Hmode |- *.
  zmem_transport M (p + 156) (Z_to_le_bytes 4 v).
  split_conj; try assumption; try close_std; try exact HAG. split; assumption.
Qed.

Lemma PLT_store_lens {RCa1 : RunCtx}  : forall cx fin M0 st cf jo M a v,
  ctx_ok ROMHI_T cx -> PLT cx fin M0 st cf jo M -> c_p cx + 168 <= a -> a + 2 <= c_p cx + 808 ->
  PLT cx fin M0 st cf jo (wbytes M (w64 a) (Z_to_le_bytes 2 v)).
Proof.
  intros cx fin M0 st cf jo M a v CX H Ha1 Ha2.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  dand H as (STD & SAT & RET & SLO & HC & HP0 & SBK). open_std STD. unfold PLT. icx_cbn. cbv [N_LENS N_CODES] in *.
  cbv [ROMHI_T] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zmem_transport M a (Z_to_le_bytes 2 v).
  split_conj; try assumption; try close_std; try exact HAG.
Qed.

Lemma PLT_intro {RCa1 : RunCtx}  : forall cx fin M0 st lf cf M,
  k_mem cx fin M0 st lf cf M -> PLT cx fin M0 st cf (t_shave st) M /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf.
Proof.
  intros cx fin M0 st lf cf M H. open_kmem H. split; [| exact Hlens]. unfold PLT. destruct st. split_conj; assumption.
Qed.
Lemma PLT_kmem {RCa1 : RunCtx}  : forall cx fin M0 st lf cf j M,
  PLT cx fin M0 st cf j M -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> k_mem cx fin M0 (st_sh st j) lf cf M.
Proof.
  intros cx fin M0 st lf cf j M (A & B & C & D & E & F & G) HL. unfold k_mem. destruct st. split_conj; try assumption.
  all: dand G as (c & G1 & G2 & G3 & G4); exists c; split_conj; assumption.
Qed.

(* [comment removed for export] *)
Ltac zrange := zkeys; rewrite ?zget_zupd; cbv [zget_l]; cbn [alookup Pos.eqb]; lia.
(* [comment removed for export] *)
Ltac zval k :=
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ?l) _ _) _ =>
    let o := eval cbn [alookup Pos.eqb] in (alookup l k) in
    lazymatch o with Some ?v => v end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section TABLE_CODE_T.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Hypothesis ITABLE : itable_spec_t.
Hypothesis CLHEAD : clhead_stmt.

(* [comment removed for export] *)
Definition s_regs_lltT (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -256 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_p cx /\ zget_l Rb l kS1 = c_u cx /\
  s_vars cx st Rb l.

(* [comment removed for export] *)
Local Ltac itable_preT SEP AL Wstk L7 C144n :=
  first [ lazymatch goal with
       | |- zget_l _ _ _ = _ => cbv [cty o_lens o_next o_work o_lenbits]; zreg
       | |- Z.land _ _ = _ => reflexivity
       | |- _ \/ _ => left; cbv [o_lenbits]; reflexivity
       | |- ZSEP _ => unfold ZSEP; pose proof (sep_p_rom _ _ SEP) as D; cbn [c_p] in D; cbv [STATE_SIZE ROM_LO_ALL DEXT_ADDR ROMHI_T] in D |- *; clear - D; lia
       | |- _ mod 16 = 0 => first [ exact (proj1 (proj2 AL)) | apply mod0_add; [lia | exact (proj1 AL) | reflexivity] ]
       | |- mem_wr _ _ _ _ => first [ assumption | cbv [FR_IT]; eapply mem_wr_sub; [exact Wstk | lia | lia] ]
       | |- mem_arr _ _ _ _ _ _ => assumption
       | |- mem_u64 _ _ _ _ => first [ assumption | eapply mem_u64_eqv_t; [| exact C144n]; cbv [o_codes]; lia ]
       | |- mem_u32 _ _ _ _ => assumption
       | |- forall i : Z, _ -> _ <= _ < _ => assumption
       | |- _ = CODES -> _ => intros _; split; [lia | split; [reflexivity | intros s Hs; replace (0 + s) with s by lia; apply L7; lia]]
       | |- _ = DISTS -> _ => intros X; discriminate X
       | |- forall s : Z, _ -> _ <= 15 => intros s Hs; replace (0 + s) with s by lia; pose proof (L7 s Hs); lia
       | |- forall R' M', _ => idtac
       | |- _ => cbv [FRA STATE_SIZE N_LENS N_CODES FR_IT DEXT_ADDR]; cbn [it_room]; first [assumption | lia]
       end | match goal with |- ?G => idtac "ITFAIL" G end ].

(* [comment removed for export] *)
Lemma ll_table_t : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENLENS -> t_shave st = 19 -> sinv cx st lf cf ->
  s_regs_lltT cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_TABLE_T (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm Hsh SI RG KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). rewrite Hsh in ML. dand ML as (_ & _ & _ & Hnl1 & Hnl2 & Hnd1 & Hnd2 & Hlf7). clear MODE_.
  assert (L7 : forall i, 0 <= i < 19 -> lf i <= 7).
  { apply order_covers. intros j0 Hj0. rewrite I7S.Base.order_f_model by exact Hj0. apply Hlf7. exact Hj0. }
  clear Hlf7.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode shave. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  match goal with H : forall i, _ -> 0 <= cf i < 4294967296 |- _ => rename H into Rcf end.
  unfold s_regs_lltT, s_vars in RG. icx_cbn. destr_conj RG.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (i_frame_slots_t _ _ FRM) as FS. icx_cbn.
  dand FS as (S120 & S128 & S136 & S176 & S216 & S224 & S232 & S240 & S248).
  prune_rng.
  zkeysb. unfold L_LL_TABLE_T, L_LL_RET_T, L_BADMSG_A0, L_CODELENS, L_ITABLE in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  pose proof (st_rest_llt_t _ _ _ 7 SREST ltac:(cbn; lia) ltac:(cbn; lia)) as SR1.
  unfold st_lt in SR1. cbn [c_p t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SR1.
  clear SREST.
  zstep Rfd.                          (* sd a1,120(s0) *)
  zstep Rfd.                          (* sd a1,128(s0): the distcode store, 1.4 *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  rename SR1 into SREST.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    destruct (work_arr_t Mx p Wp ltac:(lia) ltac:(rewrite TW64; lia)) as (wf & Hwork & Rwf);
    dand (rom_it_tabs_t Mx ROM) as (RT1 & RT2 & RT3 & RT4) end.
  lazymatch goal with H120 : mem_u32 _ ?Mx (p + 136) 7, H144 : mem_u64 _ ?Mx (p + 160) (p + 1384) |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    rename H120 into C120n; rename H144 into C144n end.
  pose proof ITABLE as ITABLE1. unfold itable_spec_t, itable_spec_at in ITABLE1.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (ITABLE1 Rx lx Mx MD T CODES p 0 19 0 7 (p + 136) (u + -256) 89176 zc lf cf wf Hh) end.
  all: itable_preT SEP AL Wstk L7 C144n.
  clear ITABLE1.
  (* [comment removed for export] *)
  intros R' M' cf' wf' Hrv Hret3 Hcf' Hwf' Rcf' Rwf' HP Hlens' Hcodes' Hwork' Hnext' Hbits' KE.
  pose proof (tab_ok_of_itable CODES lf cf wf cf' 0 19 0 7) as BR0.
  pose proof (it_fail_shape CODES (arr_init N_LENS lf) 0 19 (arr_init N_CODES cf) 0 7 (arr_init N_WORK wf)) as FS0.
  set (r := inflate_table CODES (arr_init N_LENS lf) 0 19 (arr_init N_CODES cf) 0 7 (arr_init N_WORK wf)) in *.
  clearbody r. cbv zeta in BR0, FS0.
  assert (BR : it_ret r = 0 ->
     tab_ok CODES (rdc cf' (CDyn 0)) (it_bits r) (it_table r - 0) = true /\ 1 <= it_bits r <= 15 /\
     0 + 2 ^ it_bits r <= it_table r <= 0 + it_room CODES /\ (forall i, 0 <= i < N_CODES -> ~ (0 <= i < it_table r) -> cf' i = cf i)).
  { intros Hrz. apply BR0; cbv [N_LENS N_CODES]; cbn [it_room]; try assumption; try lia.
    - intros s Hs. replace (0 + s) with s by lia. pose proof (L7 s Hs). lia.
    - intros _. split; [lia | split; [reflexivity | intros s Hs; replace (0 + s) with s by lia; apply L7; lia]]. }
  assert (FS : it_ret r <> 0 -> it_table r = 0 /\ it_bits r = 7) by (intros Hnz; exact (FS0 Hnz)).
  clear BR0 FS0.
  unfold kept_eq in KE. zkeys. destr_conj KE. zimps.
  clear Hwork RT1 RT2 RT3 RT4 C120n C144n Hcodes.
  unfold st_rest in SREST. icx_cbn. cbv [cp_addr o_codes] in SREST. icx_cbn.
  dand SREST as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & _ & C124 & C128 & C132 & C136 & C140 & _).
  unfold it_fp in HP. cbv [o_next o_work o_codes N_WORK N_CODES FR_IT] in HP. zreattachL HP.
  cbv [N_CODES] in Rcf', BR. cbn [it_room] in BR. cbv [o_next o_codes] in Hnext'.
  destruct (Z.eq_dec (it_ret r) 0) as [Hr0 | Hnz].
  - (* [comment removed for export] *)
    dand (BR Hr0) as (TOK & Hb15 & Htab & Hout). clear BR FS.
    rewrite Hr0 in Hrv. rewrite Z.sub_0_r in TOK.
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    clear Hmode.
    zstep Rfd.                        (* [comment removed for export] *)
    clear C140.
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (sinv_ll_ct _ _ lf cf cf' (it_bits r) (it_table r) SI0 eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv [N_CODES]; lia) TOK ltac:(cbv [N_CODES]; exact Rcf')) as [SI1 ME1].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (CLHEAD (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (st_ct (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist 19 nx whave wnext)
                       CODELENS 0 (it_bits r) (it_table r) 0)
                lf cf' CX0 Hh Hfin eq_refl SI1) end.
    + unfold s_regs_clh, s_vars, st_ct; icx_cbn; zkeys; split_conj; zreg.
    + unfold k_mem, st_at, st_rest, s_ret, s_lo, st_ct; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [CODELENS]; assumption | exact HAG | sbk | eapply mem_u64_eqv_t; [| eassumption]; lia
                 | unfold s_lo in SLO; icx_cbn; destruct SLO as [SL1 SL2]; assumption ].
    + eapply KALL_mono; [| exact KA0]. clear - ME1. lia.
  - (* [comment removed for export] *)
    destruct (FS Hnz) as [Ht0 Hb7]. clear BR FS.
    assert (Hrm : exists rm, it_ret r mod 18446744073709551616 = rm /\ rm <> 0 /\ 0 <= rm < 18446744073709551616).
    { exists (it_ret r mod 18446744073709551616). split; [reflexivity|].
      destruct Hret3 as [E | [E | E]]; [exfalso; exact (Hnz E) | rewrite E | rewrite E]; clear;
        [ change (1 mod 18446744073709551616) with 1 | change ((-1) mod 18446744073709551616) with 18446744073709551615 ]; lia_std. }
    dand Hrm as (rm & Hrm & Hrm0 & Hrm1).
    zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with H : mem_u64 _ ?Mx (u + -184) _ |- realizes _ (zcfg _ _ _ ?Mx _) _ =>   (* [comment removed for export] *)
      apply mem_u64_mod_t in H; rewrite Hrm in H end.
    zstep Rfd. zstep Rfd. zlit.       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (sinv_ll_bad _ _ lf cf cf' rm SI0 eq_refl (conj (proj1 Hrm1) (proj2 Hrm1)) ltac:(cbv [N_CODES]; exact Rcf')) as [SI1 ME1].
    ist_cbn. rewrite Ht0 in Hnext'. rewrite Hb7 in Hbits'.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KB0 Rx Mx (st_ct (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist 19 nx whave wnext)
                            LENLENS rm 7 0 19) lf cf') end.
    + unfold bad_of, st_ct; cbn. unfold st_ct in SI1; cbn in SI1. exact SI1.
    + unfold bad_of, st_ct; cbn. unfold st_ct in ME1; cbn in ME1. exact ME1.
    + zreg. + zreg. + zreg. + zreg. + zreg.
    + unfold st_ct; icx_cbn; zreg. + unfold st_ct; icx_cbn; zreg. + unfold st_ct; icx_cbn; zreg. + unfold st_ct; icx_cbn; zreg. + unfold st_ct; icx_cbn; zreg.
    + zrange.
    + unfold k_mem, st_at, st_rest, s_ret, s_lo, st_ct; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [LENLENS]; assumption | exact HAG | sbk | eapply mem_u64_eqv_t; [| eassumption]; lia
                 | unfold s_lo in SLO; icx_cbn; destruct SLO as [SL1 SL2]; assumption ].
Qed.

(* [comment removed for export] *)
Lemma ll_fill_t : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENLENS -> t_ncode st <= t_shave st -> sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kS1 = c_u cx ->
  zget_l Rb l kA4 = c_q cx + t_cin st -> zget_l Rb l kA2 = c_n cx - t_cin st ->
  zget_l Rb l kS3 = c_ob cx + t_cout st -> zget_l Rb l kS4 = t_hold st -> zget_l Rb l kS2 = t_bits st ->
  zget_l Rb l kA7 = t_shave st -> zget_l Rb l kA0 = A_ORDER ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_FILL_T (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm Hsh SI L3 L4 L5 L28 L9 L15 L13 L19 L20 L10 L18 L11 KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  destruct (PLT_intro _ _ _ _ _ _ _ KM) as [HP HlensX]. open_kmem KM. open_std STD. clear SAT SRET HlensX SLO SBK.
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). dand ML as (Hnc1 & Hnc2 & Hsh19 & _ & _ & _ & _ & Hlf7). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (rom_order_arr _ ROM) as Hord.
  pose proof (i_frame_slots_t _ _ FRM) as FS. icx_cbn. dand FS as (S120 & S128 & S136 & _).
  prune_rng.
  zkeysb. unfold L_LL_FILL_T, L_LL_TABLE_T, L_LL_FLOOP_T, L_LL_FEND_T, A_ORDER in *. pose proof two64_eq as TW64.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  destruct (Z_lt_dec 18 shave) as [H19 | H18].
  - zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (ll_table_t _ fin MD T M0 Rx lx Mx
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI0) end.
    + unfold s_regs_lltT, s_vars; icx_cbn; zkeys; split_conj; zreg.
    + apply (PLT_kmem _ _ _ _ lf cf shave) in HP; [exact HP | exact Hlens].
    + exact KA0.
  - zbr Rfd false.
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (2 * shave) ltac:(rewrite shiftl_1m; reflexivity).
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fill_loop_t 19 (fun (_ : Z) Mq => PLT (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                 (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf shave Mq)
                Rx lx Mx MD T u p shave shave (shave + 1) lf Hh) end;
      try zreg; try assumption; try lia.
    + unfold ZSEP. exact (sep_p_rom _ _ SEP).
    + intros i Hi. rewrite order_f_same, I7S.Base.order_f_model by lia. apply Hlf7. lia.
    + intros M' jo' a v HP' Ha1 Ha2. eapply PLT_store_lens; [exact CX0 | exact HP' | cbn; lia | cbn; lia].
    + (* [comment removed for export] *)
      intros R' M' lf' G3 Wp' Hord' S136' S128' Hlens' Rlf' Hlf7' HP' HKC.
      cbv [keptc KS_LFT] in HKC. destr_conj HKC. zimps. zkeys. unfold L_LL_FEND_T in *.
      clear Hlens Hord Hin Wp Wstk Wob Ww ROM FRM CST HK Hcodes HP S136 S128.
      zstep Rfd.                      (* [comment removed for export] *)
      pose proof (fun M' jo a v => PLT_store140 (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                    (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    cf jo M' a v CX0) as HPa.
      tstoreP Rfd HP' HPa.            (* [comment removed for export] *)
      assert (Hlf7'' : forall i, 0 <= i < 19 -> lf' (I7S.Base.order_f i) <= 7) by (intros i Hi; rewrite <- order_f_same; apply Hlf7'; exact Hi).
      pose proof (sinv_ll _ _ lf cf cin hold bits 19 lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) Rlf' Hlf7'') as [SI1 ME1].
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (ll_table_t _ fin MD T M0 Rx lx Mx
                  (st_ll (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cin hold bits 19)
                  lf' cf CX0 Hh Hfin eq_refl eq_refl SI1) end.
      * unfold s_regs_lltT, s_vars, st_ll; icx_cbn; zkeys; split_conj; try zreg; keptc_trans.
      * apply (PLT_kmem _ _ _ _ lf' cf 19) in HP'; [exact HP' | exact Hlens'].
      * eapply KALL_mono; [| exact KA0]. exact ME1.
Qed.

(* [comment removed for export] *)
Lemma ll_setup_t : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENLENS -> sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kS1 = c_u cx ->
  zget_l Rb l kA4 = c_q cx + t_cin st -> zget_l Rb l kA2 = c_n cx - t_cin st ->
  zget_l Rb l kS3 = c_ob cx + t_cout st -> zget_l Rb l kS4 = t_hold st -> zget_l Rb l kS2 = t_bits st ->
  zget_l Rb l kA7 = t_shave st ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_SETUP_T (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI L3 L4 L5 L28 L9 L15 L13 L19 L20 L10 L18 KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0. pose proof KM as KM0. open_K K.
  destruct (PLT_intro _ _ _ _ _ _ _ KM) as [HP HlensX]. open_kmem KM. open_std STD. clear HlensX.
  destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). dand ML as (Hnc1 & Hnc2 & Hsh19 & _ & _ & _ & _ & Hlf7). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (rom_order_arr _ ROM) as Hord.
  pose proof (i_frame_slots_t _ _ FRM) as FS. icx_cbn. dand FS as (S120 & S128 & S136 & _).
  assert (C128 : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 144) ncode) by (unfold st_rest in SREST; icx_cbn; destr_conj SREST; assumption).
  clear SREST Hmode SRET.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  prune_rng.
  zkeysb. unfold L_LL_SETUP_T, L_LL_HEAD_T, L_LL_FILL_T, L_LVX_LL_T, L_LEAVE_LD2, A_ORDER in *.
  pose proof two64_eq as TW64.
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd. zstep Rfd. zlit.         (* [comment removed for export] *)
  destruct (Z_lt_dec shave ncode) as [Hlt | Hge].
  2: { zbr Rfd true.                  (* [comment removed for export] *)
       lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
         eapply (ll_fill_t _ fin MD T M0 Rx lx Mx
                   (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                   lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI0) end;
         [ (icx_cbn; zkeys; zreg) .. | exact KM0 | exact KA0 ]. }
  zbr Rfd false.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd false.                      (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (-19) ltac:(first [reflexivity | symmetry; apply swrap32_small; lia]).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (- ncode) ltac:(first [symmetry; rewrite swrap32_small by lia; lia | lia]).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (2 * shave) ltac:(symmetry; apply zext32_shift31; lia).
  pose proof (fun M' jo a v => PLT_store140 (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                cf jo M' a v CX0) as HPa.
  pose proof (fun M' jo a v => PLT_store_lens (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                cf jo M' a v CX0) as HPb.
  cbn [c_p] in HPa, HPb.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (lenlens_loop_t 19 (fun jo Mq => PLT (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
               (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf jo Mq)
              Rx lx Mx MD T u p q n ncode shave cin bits hold fin lf Hh) end;
    try zreg; try assumption; try lia.
  - unfold ZSEP. exact (sep_p_q _ _ SEP).
  - unfold ZSEP. exact (sep_p_rom _ _ SEP).
  - intros i Hi. rewrite order_f_same, I7S.Base.order_f_model by lia. apply Hlf7. lia.
  - (* [comment removed for export] *)
    intros R' M' j' B' H' lf' G10 G20 G13 G15 X1 X2 X3 X4 X5 X6 X7 X8 Wp' Hin' Hord' S136' S128' Hlens' Rlf' Hlf7' HP' HKC.
    cbv [keptc KS_LLT] in HKC. destr_conj HKC. zimps. zkeys. unfold L_LVX_LL_T in *.
    assert (Hlf7'' : forall i, 0 <= i < j' -> lf' (I7S.Base.order_f i) <= 7) by (intros i Hi; rewrite <- order_f_same; apply Hlf7'; exact Hi).
    pose proof (sinv_ll _ _ lf cf n H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) Rlf' Hlf7'') as [SI1 ME1].
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (PLT_kmem _ _ _ _ lf' cf j' _ HP' Hlens') as KM'. dand KM' as (STD' & SAT' & SRET' & SLO' & HL' & HC' & HP0' & SBK').
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KLL2 Rx Mx (st_ll (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) n H' B' j') lf' cf SI1) end.
    + unfold s_regs_leave_ld2, st_ll; icx_cbn; zkeys; split_conj; try zreg; try assumption. all: try lia.
    + exact STD'.
    + exact SAT'.
    + exact SRET'.
    + exact SLO'.
    + exact SBK'.
    + exact HL'.
    + exact HC'.
    + exact HP0'.
  - (* [comment removed for export] *)
    intros R' M' ci' B' H' lf' G10 G20 G13 G15 G18 G28 G3 G11 X1 X2 X3 X4 X5 X6 X7 X8 Wp' Hin' Hord' S136' S128' Hlens' Rlf' Hlf7' HP' HKC.
    cbv [keptc KS_LLT] in HKC. destr_conj HKC. zimps. zkeys. unfold L_LL_FILL_T in *.
    assert (Hlf7'' : forall i, 0 <= i < ncode -> lf' (I7S.Base.order_f i) <= 7) by (intros i Hi; rewrite <- order_f_same; apply Hlf7'; exact Hi).
    pose proof (sinv_ll _ _ lf cf ci' H' B' ncode lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) Rlf' Hlf7'') as [SI1 ME1].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (ll_fill_t _ fin MD T M0 Rx [] Mx
                (st_ll (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' ncode)
                lf' cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI1) end;
      [ (unfold st_ll; icx_cbn; zkeys; first [zreg | assumption]) ..
      | apply (PLT_kmem _ _ _ _ lf' cf ncode) in HP'; [exact HP' | exact Hlens']
      | eapply KALL_mono; [| exact KA0]; exact ME1 ].
Qed.

(* [comment removed for export] *)
Lemma table_body_t : forall cx fin MD T M0 Rb l M st lf cf (cin1 hold1 bits1 : Z),
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = TABLE -> sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kS1 = c_u cx -> zget_l Rb l kA3 = c_u cx -> zget_l Rb l kRA = 16209 ->
  zget_l Rb l kA4 = c_q cx + cin1 -> zget_l Rb l kA2 = c_n cx - cin1 ->
  zget_l Rb l kS3 = c_ob cx + t_cout st -> zget_l Rb l kS4 = hold1 -> zget_l Rb l kA1 = bits1 ->
  t_cin st <= cin1 -> cin1 <= c_n cx -> 14 <= bits1 -> bits1 <= 40 -> 0 <= hold1 -> hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
  8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TAB_BODY_T (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf cin1 hold1 bits1 CX Hh Hfin Hm SI L3 L4 L5 L28 L9 L14 L2 L15 L13 L19 L20 L12
         Hc1 Hc2 Hb1 Hb2 Hh1 Hh2 Hbc HW KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0. open_K K.
  open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (i_frame_slots_t _ _ FRM) as FS. icx_cbn. dand FS as (S120 & _).
  prune_rng.
  pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh64.
  zkeysb. unfold L_TAB_BODY_T, L_LL_SETUP_T, L_BAD_TAB_T, L_BADMSG_A5 in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (hold1 mod 32) ltac:(symmetry; apply land31_mod; lia).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (hold1 / 2 ^ 14) ltac:(rewrite (Z.mod_small hold1) by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg ((hold1 / 32) mod 32) ltac:(symmetry; apply bits_54_59; lia).
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg ((hold1 / 1024) mod 16) ltac:(symmetry; apply bits_50_60; lia).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  pose proof (mod_range hold1 32 ltac:(lia)) as R1. pose proof (mod_range (hold1 / 32) 32 ltac:(lia)) as R2.
  pose proof (mod_range (hold1 / 1024) 16 ltac:(lia)) as R3.
  pose proof (hold_shr_bound hold1 bits1 14 ltac:(lia) ltac:(lia)) as R4.
  let vc := zval 18%positive in let vn := zval 6%positive in let vd := zval 7%positive in
  pose proof (st_rest_tb3_t _ _ _ vc vn vd SREST ltac:(cbn; lia) ltac:(cbn; lia)) as SR1.
  unfold st_tb in SR1. cbn [c_p t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SR1.
  clear SREST.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  rename SR1 into SREST.
  zstep Rfd.                          (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (JB : forall RJ,
    zget RJ kSP = u + -256 -> zget RJ kGP = K0 kGP -> zget RJ kTP = K0 kTP -> zget RJ kS0 = p ->
    zget RJ kA3 = u -> zget RJ kS1 = u -> zget RJ kA1 = 0 -> zget RJ kRA = 16209 ->
    zget RJ kA4 = q + cin1 -> zget RJ kA2 = n - cin1 -> zget RJ kS3 = ob + cout ->
    zget RJ kS4 = hold1 / 2 ^ 14 -> zget RJ kS2 = bits1 - 14 ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 90344 (zupd RJ []) Mc MD) T) end.
  { intros RJ. intros. zkeys.
    zstep Rfd. zstep Rfd. zlit.       (* [comment removed for export] *)
    pose proof (sinv_tb_bad _ _ lf cf cin1 hold1 bits1 ((hold1 / 1024) mod 16 + 4) (hold1 mod 32 + 257) ((hold1 / 32) mod 32 + 1)
                  SI0 eq_refl Hc1 Hc2 Hb1 Hb2 Hh1 Hh2 Hbc HW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI1 ME1].
    ist_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KB5 Rx Mx _ lf cf SI1 ME1) end.
    - unfold s_fix; icx_cbn; zkeys; split_conj; zreg.
    - unfold st_tb; icx_cbn; zreg.
    - unfold st_tb; icx_cbn; zreg.
    - unfold st_tb; icx_cbn; zreg.
    - unfold st_tb; icx_cbn; zreg.
    - unfold st_tb; icx_cbn; zreg.
    - zrange.
    - unfold k_mem, st_at, st_tb, s_ret, s_lo; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
      all: first [cbv [TABLE]; assumption | exact HAG | sbk | unfold s_lo in SLO; icx_cbn; destruct SLO as [SL1 SL2]; assumption]. }
  destruct (Z_lt_dec 29 (hold1 mod 32)) as [Hn1 | Hn1].
  { zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => apply (JB Rx) end; zreg. }
  zbr Rfd false.
  zstep Rfd.                          (* [comment removed for export] *)
  destruct (Z_lt_dec ((hold1 / 32) mod 32) 30) as [Hn2 | Hn2].
  2: { zbr Rfd true.                  (* [comment removed for export] *)
       lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => apply (JB Rx) end; zreg. }
  zbr Rfd false.
  clear JB.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  clear Hmode.
  zstep Rfd.                          (* [comment removed for export] *)
  pose proof (st_rest_set140_t _ _ _ 0 SREST ltac:(cbn; lia) ltac:(cbn; lia)) as SR1.
  unfold st_sh in SR1. cbn [c_p t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SR1.
  clear SREST.
  zstep Rfd.                          (* [comment removed for export] *)
  rename SR1 into SREST.
  pose proof (sinv_tb _ _ lf cf cin1 hold1 bits1 ((hold1 / 1024) mod 16 + 4) (hold1 mod 32 + 257) ((hold1 / 32) mod 32 + 1)
                SI0 eq_refl Hc1 Hc2 Hb1 Hb2 Hh1 Hh2 Hbc HW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI1 ME1].
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (ll_setup_t _ fin MD T M0 Rx lx Mx
              (st_tb (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                     LENLENS cin1 (hold1 / 2 ^ 14) (bits1 - 14) ((hold1 / 1024) mod 16 + 4) (hold1 mod 32 + 257) ((hold1 / 32) mod 32 + 1) 0)
              lf cf CX0 Hh Hfin eq_refl SI1) end.
  all: try (unfold st_tb; icx_cbn; zkeys; zreg).
  - unfold k_mem, st_at, st_tb, s_ret, s_lo; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
    all: first [cbv [LENLENS]; assumption | exact HAG | sbk | unfold s_lo in SLO; icx_cbn; destruct SLO as [SL1 SL2]; assumption].
  - eapply KALL_mono; [| exact KA0]. clear - ME1. lia.
Qed.

Theorem arm_TABLE_t0 : arm_stmt L_TABLE TABLE.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof KM as KM0. pose proof K as KA0. open_K K. open_kmem KM. open_std STD.
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof RE as RE0. unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  pose proof (i_frame_slots_t _ _ FRM) as FS. icx_cbn. dand FS as (S120 & _).
  clear SAT Hlens Hcodes ROM Wstk Wp Wob Ww FRM CST HK SLO SBK.
  unfold s_ret in SRET. icx_cbn.
  prune_rng.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  zkeysb. unfold L_TABLE, L_TAB_LOOP_T, L_TAB_BODY_T, L_TAB_SKIP_T, L_LVX_TAB_T, L_LEAVE in *.
  pose proof two64_eq as TW64.
  zstep Rfd.                          (* [comment removed for export] *)
  destruct (Z_lt_dec 13 bits) as [Hb14 | Hb14].
  - zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (table_body_t _ fin MD T M0 Rx lx Mx
                (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf cin hold bits CX0 Hh Hfin eq_refl SI) end;
      [ (icx_cbn; zkeys; first [zreg | lia]) .. | exact KM0 | exact KA0 ].
  - zbr Rfd false.
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    assert (Hkk : exists k : nat, 14 - 8 * Z.of_nat k <= bits < 22 - 8 * Z.of_nat k /\ (1 <= k <= 2)%nat).
    { destruct (Z_lt_dec bits 6); [exists 2%nat | exists 1%nat]; cbn; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (table_loop_t k Rx lx Mx MD T q n cin hold bits (u) fin Hh Hfin Hk1 Hk2) end;
      [ lia | lia | lia | lia | lia | lia | lia | zreg .. | exact Hin | | ].
    + (* [comment removed for export] *)
      intros R' hold' j' G13 G20 G14 Hj' Hh' Hkn HKC. cbv [keptc KS_TBT] in HKC. destr_conj HKC. zimps. zkeys. unfold L_LVX_TAB_T in *.
      pose proof (sinv_pull _ _ lf cf n hold' j' SI ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 _].
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zsetreg (8 * (n - cin)) ltac:(symmetry; apply shiftl_3).
      zstep Rfd. zext32.              (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      dand KM0 as (STD' & SAT' & SRET' & SLO' & HL' & HC' & HP0' & SBK').
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KL Rx Mx (st_pull (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) n hold' j') ret lf cf SI1) end;
        [ unfold s_regs_leave, st_pull; icx_cbn; zkeys; split_conj; try zreg; try assumption; lia
        | exact STD' | exact SAT' | exact SLO' | exact SBK' | exact HL' | exact HC' | exact HP0' ].
    + (* [comment removed for export] *)
      intros R' hold' j' G15 G13 G12 G20 G14 Hj' Hh' Hkn HKC. cbv [keptc KS_TBT] in HKC. destr_conj HKC. zimps. zkeys. unfold L_TAB_BODY_T in *.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (table_body_t _ fin MD T M0 Rx [] Mx
                  (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  lf cf (cin + Z.of_nat k) hold' j' CX0 Hh Hfin eq_refl SI) end;
        [ (icx_cbn; zkeys; first [zreg | assumption | lia]) .. | exact KM0 | exact KA0 ].
Qed.

Theorem arm_LENLENS_t0 : arm_stmt L_LENLENS LENLENS.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof KM as KM0. open_kmem KM. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). dand ML as (Hnc1 & Hnc2 & Hsh19 & _). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof RE as RE0. unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  assert (C140 : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 156) shave) by (unfold st_rest in SREST; icx_cbn; destr_conj SREST; assumption).
  clear SREST Hmode STD SRET Hlens Hcodes HP0 SLO SBK.
  zkeysb. unfold L_LENLENS, L_LL_SETUP_T in *. pose proof two64_eq as TW64.
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (ll_setup_t _ fin MD T M0 Rx lx Mx
              (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf CX0 Hh Hfin eq_refl SI) end;
    [ (icx_cbn; zkeys; zreg) .. | exact KM0 | exact K ].
Qed.
End TABLE_CODE_T.

(* [comment removed for export] *)
End T_Table.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require S_CodelensL S_Codelens.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U Require T_DistL.

Module T_CodelensL.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_DistL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_TableL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_CodelensL.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U.T_DistL T_TableL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition L_CL_WHILE_T : Z := 89268.  (* [comment removed for export] *)
Definition L_CL_DLOOP_T : Z := 89356.  (* [comment removed for export] *)
Definition L_CL_RES_T : Z := 89500.    (* [comment removed for export] *)
Definition L_LVX_CLD_T : Z := 96004.   (* [comment removed for export] *)
Definition L_LVX_CLN_T : Z := 96248.   (* [comment removed for export] *)
Definition L_CL_P17_T : Z := 89644.    (* [comment removed for export] *)
Definition L_CL_X17_T : Z := 89904.    (* [comment removed for export] *)
Definition L_CL_P16_T : Z := 89732.    (* [comment removed for export] *)
Definition L_CL_X16_T : Z := 89956.    (* [comment removed for export] *)
Definition L_CL_P18_T : Z := 89820.    (* [comment removed for export] *)
Definition L_CL_X18_T : Z := 90056.    (* [comment removed for export] *)
Definition L_CL_FILL_T : Z := 90124.   (* [comment removed for export] *)
Definition L_CL_FILLX_T : Z := 90172.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_CPT : list positive := [2; 3; 4; 5; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 20; 23; 24; 26; 27; 28; 30; 31; 32]%positive.
(* [comment removed for export] *)
Definition KS_CDT : list positive := [2; 3; 4; 5; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 24; 26; 28; 32]%positive.
(* [comment removed for export] *)
Definition KS_CFT : list positive := [2; 3; 4; 5; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 31; 32]%positive.
(* [comment removed for export] *)
Definition KS_CXD : list positive := [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 28; 29; 30; 31]%positive.
Definition KS_CXN : list positive := [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 28; 29; 30; 31; 32]%positive.
Ltac keptc_closeU := cbv [keptc KS_CPT KS_CDT KS_CFT KS_CXD KS_CXN]; split_conj; try exact I; zreg.
Ltac keptc_transU :=
  repeat match goal with H : keptc _ _ _ _ |- _ => cbv [keptc KS_CPT KS_CDT KS_CFT KS_CXD KS_CXN] in H; destr_conj H end;
  cbv [keptc KS_CPT KS_CDT KS_CFT KS_CXD KS_CXN]; split_conj; try exact I;
  rewrite ?zget_zupd in *; cbv [zget_l] in *; cbn [alookup Pos.eqb] in *;
  first [ assumption | reflexivity
        | etransitivity; [eassumption|]; first [assumption | reflexivity | symmetry; assumption] ].

(* [comment removed for export] *)
Ltac tld1 Ha i Hr :=
  lazymatch type of Ha with mem_arr 1 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr' (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | apply Hr; lia | ]); znorm end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stub_CLd_t {RCa1 : RunCtx}  : forall Rb l M MD T (q n c0 b0 s6v : Z),
  m_halted MD = None ->
  zget_l Rb l kA7 = q + c0 -> zget_l Rb l kS7 = s6v ->   (* [comment removed for export] *) zget_l Rb l kT6 = n - c0 -> zget_l Rb l kS2 = b0 ->
  Z.shiftr (s6v mod 18446744073709551616) 32 = n - c0 -> 0 <= n - c0 -> n - c0 < 4294967296 ->
  (forall R', zget R' kS10 = q + n -> zget R' kS2 = b0 + 8 * (n - c0) ->
     keptc Rb l R' KS_CXD -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_LD2 (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_CLD_T (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T q n c0 b0 s6v Hh La7 Ls6 Lt6 Ls1 Hs6 H1 H2 K.
  zkeys. unfold L_LVX_CLD_T, L_LEAVE_LD2 in *.
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (n - c0) ltac:(symmetry; exact Hs6).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (8 * (n - c0)) ltac:(symmetry; first [apply shiftl_3 | apply shl_3]).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end; try zreg. keptc_closeU.
Qed.

(* [comment removed for export] *)
Lemma stub_CLn_t {RCa1 : RunCtx}  : forall Rb l M MD T (q n c1 B : Z),
  m_halted MD = None ->
  zget_l Rb l kS10 = q + c1 -> zget_l Rb l kT1 = n - c1 -> zget_l Rb l kT0 = B ->
  (forall R', zget R' kS10 = q + n -> zget R' kS2 = B ->
     keptc Rb l R' KS_CXN -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_LD2 (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_CLN_T (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T q n c1 B Hh Ls9 Lt1 Lt0 K.
  zkeys. unfold L_LVX_CLN_T, L_LEAVE_LD2 in *.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end; try zreg. keptc_closeU.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cl_pull_t {RCa1 : RunCtx}  : forall (N : nat) (pc pcx : Z) Rb l M MD T (q n need c1 b1 ci B H : Z) (fin : Z -> Z),
  ((pc = L_CL_P17_T /\ pcx = L_CL_X17_T) \/ (pc = L_CL_P16_T /\ pcx = L_CL_X16_T) \/ (pc = L_CL_P18_T /\ pcx = L_CL_X18_T)) ->
  m_halted MD = None ->
  zget_l Rb l kS8 = n - ci -> zget_l Rb l kS2 = q + ci -> zget_l Rb l kT3 = q + ci ->
  zget_l Rb l kT2 = B -> zget_l Rb l kT0 = B -> zget_l Rb l kT6 = need -> zget_l Rb l kS4 = H ->
  zget_l Rb l kS10 = q + c1 -> zget_l Rb l kT1 = n - c1 ->
  n - ci < Z.of_nat N -> 0 <= c1 -> c1 <= ci -> ci <= n -> 0 <= b1 -> B = b1 + 8 * (ci - c1) ->
  B < need -> need <= 22 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  (* [comment removed for export] *)
  (forall R' (H' : Z),
     zget R' kS4 = H' -> zget R' kS8 = 0 -> zget R' kT0 = b1 + 8 * (n - c1) -> zget R' kS10 = q + c1 -> zget R' kT1 = n - c1 ->
     0 <= H' -> H' < 2 ^ (b1 + 8 * (n - c1)) -> b1 + 8 * (n - c1) < need -> b1 + 8 * (n - c1) <= 8 * n ->
     keptc Rb l R' KS_CPT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_CLN_T (zupd R' []) M MD) T) ->
  (* [comment removed for export] *)
  (forall R' (ci' B' H' : Z),
     zget R' kS8 = n - ci' -> zget R' kS2 = q + ci' -> zget R' kA7 = q + ci' -> zget R' kT0 = B' -> zget R' kT2 = B' -> zget R' kS4 = H' ->
     zget R' kT6 = need ->
     ci < ci' -> ci' <= n -> B' = b1 + 8 * (ci' - c1) -> need <= B' -> B' <= 29 ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_CPT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pcx (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros pc pcx Rb l M MD T q n need c1 b1 ci B H fin Hpc Hh Ls7 Ls1 Lt3 Lt2 Lt0 Lt6 Ls3 Ls9 Lt1
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt Hneed HH1 HH2 HBc Hq1 Hn26 Hq2 Hin Rfin KX KD; [lia|].
  zkeys. unfold L_CL_P17_T, L_CL_X17_T, L_CL_P16_T, L_CL_X16_T, L_CL_P18_T, L_CL_X18_T, L_LVX_CLN_T in *. pose proof two64_eq as TW64.
  pose proof (pow2_48 B ltac:(lia)) as HPB. pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct Hpc as [[-> ->] | [[-> ->] | [-> ->]]]; (
    destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz];
    [ zbr Rfd false; zstep Rfd;
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia;
      first [ replace (b1 + 8 * (n - c1)) with B by lia; lia | keptc_closeU ]
    | zbr Rfd true;
      zstep Rfd;                        (* [comment removed for export] *)
      zstep Rfd;                        (* [comment removed for export] *)
      zbr Rfd true;                     (* [comment removed for export] *)
      zstep Rfd;                        (* [comment removed for export] *)
      zbr Rfd true;                     (* [comment removed for export] *)
      pose proof (Rfin ci ltac:(lia)) as Rb1;
      tld1 Hin ci Rfin;                 (* [comment removed for export] *)
      zstep Rfd;                        (* [comment removed for export] *)
      zstep Rfd;                        (* [comment removed for export] *)
      zstep Rfd;                        (* [comment removed for export] *)
      zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia);
      pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]; rewrite pow2_add8 in Hp1 by lia;
      zstep Rfd;                        (* [comment removed for export] *)
      zstep Rfd;                        (* [comment removed for export] *)
      zsetreg (H + fin ci * 2 ^ B) ltac:(lia);
      assert (HH' : 0 <= H + fin ci * 2 ^ B < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia);
      tstep1 Rfd;                       (* [comment removed for export] *)
      zstep Rfd;                        (* [comment removed for export] *)
      destruct (Z_lt_dec (B + 8) need) as [Hmore | Hdone];
      [ zbr Rfd true;
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx ?MDx) ?Tx =>
          eapply (IH _ _ Rx lx Mx MDx Tx q n need c1 b1 (ci + 1) (B + 8) (H + fin ci * 2 ^ B) fin) end;
        [ first [left; split; reflexivity | right; left; split; reflexivity | right; right; split; reflexivity] | ..];
        try zreg; try lia; try eassumption;
        (intros; first [eapply KD | eapply KX]; try eassumption; try lia; keptc_transU)
      | zbr Rfd false;
        zstep Rfd;                      (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) (H + fin ci * 2 ^ B)) end;
        try zreg; try lia; keptc_closeU ] ]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cl_decode_t {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (p q n lb lm nx c0 b0 ci B H : Z) (fin cf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA4 = p + 1384 -> zget_l Rb l kA5 = lm -> zget_l Rb l kS9 = 1 ->
  zget_l Rb l kT4 = Z.land lm H -> zget_l Rb l kS4 = H ->
  zget_l Rb l kT2 = B -> zget_l Rb l kT0 = B -> zget_l Rb l kS5 = - B ->
  zget_l Rb l kT3 = q + ci -> zget_l Rb l kS10 = q + ci -> zget_l Rb l kS8 = n - ci -> zget_l Rb l kT1 = n - ci ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  0 <= H -> H < 2 ^ B -> B <= 8 * ci -> B <= 40 -> (c0 < ci -> B <= 22) ->
  lm = 2 ^ lb - 1 -> 1 <= lb -> lb <= 15 -> 0 <= nx -> nx <= 1444 -> tab_ok CODES (rdc cf (CDyn 0)) lb nx = true ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 cf ->
  (* [comment removed for export] *)
  (forall R' (H' : Z),
     zget R' kS4 = H' -> zget R' kS8 = 0 ->
     0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 14 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_CDT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_CLD_T (zupd R' []) M MD) T) ->
  (* [comment removed for export] *)
  (forall R' (ci' B' H' : Z),
     zget R' kS10 = q + ci' -> zget R' kT3 = q + ci' -> zget R' kS8 = n - ci' -> zget R' kT1 = n - ci' ->
     zget R' kT2 = B' -> zget R' kT0 = B' -> zget R' kS5 = - B' -> zget R' kS4 = H' ->
     zget R' kS6 = cellv (cf (Z.land lm H')) -> zget R' kT5 = code_bits (cf (Z.land lm H')) ->
     zget R' kT4 = code_bits (cf (Z.land lm H')) + 256 * code_val (cf (Z.land lm H')) ->
     ci <= ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> code_bits (cf (Z.land lm H')) <= B' -> B' <= 40 -> (c0 < ci' -> B' <= 22) ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_CDT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_RES_T (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_DLOOP_T (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T p q n lb lm nx c0 b0 ci B H fin cf Hh La4 La5 Ls8 Lt4 Ls3 Lt2 Lt0 Ls4 Lt3 Ls9 Ls7 Lt1
    HN Hc0 Hc1 Hc2 Hb0 HB HH1 HH2 HBc HB40 HB22 Hdm Hlb1 Hlb2 Hnx1 Hnx2 TOK Hq1 Hn26 Hq2 Hp1 Hp2 Hin Rfin Hcodes KX KD; [lia|].
  zkeys. unfold L_CL_DLOOP_T, L_CL_RES_T, L_LVX_CLD_T in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPlb.
  pose proof (land_mask_l H lb ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (ctab_bits cf lb nx (Z.land lm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits0 Hpow].
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  pose proof (code_bits_range (cf (Z.land lm H))) as Rcb. pose proof (code_val_range (cf (Z.land lm H))) as Rcv.
  pose proof (cellv_range (cf (Z.land lm H))) as Rcell.
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (4 * Z.land lm H) ltac:(symmetry; first [apply shiftl_2 | apply shl_2]).
  zstep Rfd.                          (* [comment removed for export] *)
  tcell Hcodes (Z.land lm H).         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (code_bits (cf (Z.land lm H)) + 256 * code_val (cf (Z.land lm H))) ltac:(symmetry; apply cell_shr8).
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (code_bits (cf (Z.land lm H))) ltac:(symmetry; apply bits_and255).
  destruct (Z_lt_dec B (code_bits (cf (Z.land lm H)))) as [Hlt | Hge].
  2: { (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx ci B H) end; try zreg; try lia. keptc_closeU. }
  zbr Rfd false.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    all: first [replace (b0 + 8 * (n - c0)) with B by lia; lia | keptc_closeU]. }
  zbr Rfd true.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.                   (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1']. rewrite pow2_add8 in Hp1' by lia.
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  set (H' := H + fin ci * 2 ^ B) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1'.
  zstep Rfd.                          (* [comment removed for export] *)
  pose proof (land_mask_l H' lb ltac:(lia)) as Ri1. rewrite <- Hdm in Ri1.
  pose proof (ctab_bits cf lb nx (Z.land lm H') TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits1 _].
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (4 * Z.land lm H') ltac:(symmetry; first [apply shiftl_2 | apply shl_2]).
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd. zbool.                   (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg 1 ltac:(reflexivity).
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (IH Rx lx Mx MD T p q n lb lm nx c0 b0 (ci + 1) (B + 8) H' fin cf Hh) end;
    try zreg; try lia; try eassumption.
  all: intros; first [eapply KD | eapply KX]; try eassumption; try lia; keptc_transU.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cl_fill_t {RCa1 : RunCtx}  : forall (N : nat) (P : mem -> Prop) Rb l M MD T (u p q n j je len : Z) (fin cf lf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + -256 -> zget_l Rb l kA6 = j -> zget_l Rb l kT0 = je - j -> zget_l Rb l kT1 = len -> zget_l Rb l kT2 = 320 ->
  je - j <= Z.of_nat N -> 0 <= j -> j < je -> je <= 320 -> 0 <= len -> len < 65536 ->
  0 < p -> p + 7176 <= 140737488355328 -> 1 <= q -> 0 <= n -> q + n <= 140737488355328 ->
  Z.max (p + 7176) (q + n) + 1024 <= u -> u + 208 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 cf -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -136) (- (p + 168) + -1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -128) (p + 168) -> P M ->
  (forall M' (a v : Z), P M' -> p + 168 <= a -> a + 2 <= p + 808 -> P (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (forall R' M' (lf' : Z -> Z),
     zget R' kA6 = je -> zget R' kT0 = 0 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -136) (- (p + 168) + -1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -128) (p + 168) -> P M' ->
     (forall i, 0 <= i < 320 -> j <= i < je -> lf' i = len) ->
     (forall i, 0 <= i < 320 -> ~ (j <= i < je) -> lf' i = lf i) ->
     keptc Rb l R' KS_CFT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_FILLX_T (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_FILL_T (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T u p q n j je len fin cf lf Hh L3 L17 L6 L7 L8
    HN Hj0 Hj1 Hje Hl0 Hl1 Hp1 Hp2 Hq1 Hn0 Hq2 Hu1 Hu2 SPQ Wp Hin Hcodes Hlens S136 S128 HP HPb KD; [lia|].
  zkeys. unfold L_CL_FILL_T, L_CL_FILLX_T in *. pose proof two64_eq as TW64.
  pose proof (lnot_val_mod' (p + 168) ltac:(lia)) as Hnl.
  zbr Rfd true.                       (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (2 * j) ltac:(rewrite shiftl_1m; reflexivity).
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  tstore_arrPc Rfd Hlens j HP HPb.    (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  destruct (Z.eq_dec (j + 1) je) as [Hlast | Hmore].
  - zbr Rfd false.                    (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KD Rx Mx (zfupd lf j len)) end;
      try zreg; try eassumption; try lia.
    all: first [ intros i Hi Hij; unfold zfupd; destruct (Z.eqb_spec i j); first [reflexivity | lia] | keptc_closeU ].
  - zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH P Rx lx Mx MD T u p q n (j + 1) je len fin cf _ Hh) end;
      try zreg; try lia; try eassumption.
    intros R' M' lf' G17 G6 W' Hin' Hcodes' Hlens' S136' S128' HP' Hin_ Hout_ HK.
    eapply (KD R' M' lf'); try eassumption.
    all: first [ intros i Hi Hij;
                 first [ destruct (Z.eq_dec i j) as [-> | Hne];
                         [ rewrite Hout_ by lia; unfold zfupd; rewrite Z.eqb_refl; reflexivity | apply Hin_; lia ]
                       | rewrite Hout_ by lia; unfold zfupd; destruct (Z.eqb_spec i j); [lia | reflexivity] ]
               | keptc_transU ].
Qed.
End T_CodelensL.

Module T_Codelens.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_DistL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_TableL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_Table OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_CodelensL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_Codelens.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U.T_DistL T_TableL T_Table OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U.TBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U.T_ClDefs T_CodelensL T_CodelensT.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition L_CL_CHK_T : Z := 90096.    (* [comment removed for export] *)
Definition L_BADREP0_T : Z := 95868.   (* [comment removed for export] *)
Definition L_BADREP_T : Z := 95744.    (* a worker 1.4 UBSan: 0x1759c *)
Definition MSG_BADREP_T : Z := 66210.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cell_shr20 : forall e, Z.shiftr (cellv e mod 18446744073709551616) 20 = code_val e / 16.
Proof.
  intros e. pose proof (cellv_range e). pose proof (code_op_range e). pose proof (code_bits_range e). pose proof (code_val_range e).
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 20) with (65536 * 16). unfold cellv.
  rewrite <- Z.div_div by lia.
  replace (code_op e + 256 * code_bits e + 65536 * code_val e) with ((code_op e + 256 * code_bits e) + code_val e * 65536) by lia.
  rewrite Z.div_add by lia. rewrite (Z.div_small (code_op e + 256 * code_bits e)) by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma cell_shl48_shr56 : forall e, Z.shiftr (Z.shiftl (cellv e) 48 mod 18446744073709551616) 56 = code_bits e.
Proof.
  intros e. pose proof (cellv_range e). pose proof (code_op_range e). pose proof (code_bits_range e). pose proof (code_val_range e).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold cellv.
  replace ((code_op e + 256 * code_bits e + 65536 * code_val e) * 2 ^ 48)
    with ((code_op e + 256 * code_bits e) * 2 ^ 48 + code_val e * 18446744073709551616) by (change 18446744073709551616 with (65536 * 2 ^ 48); lia).
  rewrite Z.mod_add by lia. rewrite Z.mod_small by (change 18446744073709551616 with (65536 * 2 ^ 48); lia).
  change (2 ^ 56) with (2 ^ 48 * 256). rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia.
  replace (code_op e + 256 * code_bits e) with (code_op e + code_bits e * 256) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma srl_hold_cellC : forall hold bits e, 0 <= hold < 2 ^ bits -> 0 <= bits <= 63 -> code_bits e <= bits ->
  Z.shiftr (hold mod 18446744073709551616) ((code_bits e + 256 * code_val e) mod 64) = hold / 2 ^ code_bits e.
Proof.
  intros hold bits e Hh Hb He. pose proof (code_bits_range e). rewrite shamt_cell by lia.
  rewrite <- (Z.mod_small (code_bits e) 64) at 1 by lia. apply (srl_hold hold bits); lia.
Qed.

(* [comment removed for export] *)
Definition KS_CRT : list positive := [2; 3; 4; 5; 9; 10; 11; 12; 13; 14; 15; 16; 20; 28]%positive.
(* [comment removed for export] *)
Definition KS_CRB : list positive := [2; 3; 4; 5; 9; 10; 11; 13; 14; 15; 16; 20; 28]%positive.
Ltac keptc_closeR := cbv [keptc KS_CRT KS_CRB KS_CPT KS_CDT KS_CFT KS_CXD KS_CXN]; split_conj; try exact I; zreg.
(* [comment removed for export] *)
Ltac kopenT HK := cbv [keptc KS_CRT KS_CRB KS_CPT KS_CDT KS_CFT KS_CXD KS_CXN] in HK; destr_conj HK; zimps.
Ltac keptc_transR :=
  repeat match goal with H : keptc _ _ _ _ |- _ => cbv [keptc KS_CRT KS_CRB KS_CPT KS_CDT KS_CFT KS_CXD KS_CXN] in H; destr_conj H end;
  cbv [keptc KS_CRT KS_CRB KS_CPT KS_CDT KS_CFT KS_CXD KS_CXN]; split_conj; try exact I;
  rewrite ?zget_zupd in *; cbv [zget_l] in *; cbn [alookup Pos.eqb] in *;
  first [ assumption | reflexivity
        | etransitivity; [eassumption|]; first [assumption | reflexivity | symmetry; assumption]
        | zkept
        | etransitivity; [eassumption|]; etransitivity; [eassumption|]; first [assumption | reflexivity | symmetry; assumption] ].
Ltac ist_cbn := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
                     t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in *.
(* [comment removed for export] *)
Ltac kgoalT := first [ zreg | assumption | OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ITac.zarith_goal; lia | etransitivity; [eassumption | solve [lia | symmetry; assumption]] | keptc_transR ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cl_res_t {RCa1 : RunCtx}  : forall (P : Z -> mem -> Prop) Rb l M MD T (u p q n nd lb lm nx j ci B H : Z) (fin cf lf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + -256 -> zget_l Rb l kS0 = p -> zget_l Rb l kA1 = nd -> zget_l Rb l kA6 = j ->
  zget_l Rb l kS10 = q + ci -> zget_l Rb l kT3 = q + ci -> zget_l Rb l kS8 = n - ci -> zget_l Rb l kT1 = n - ci ->
  zget_l Rb l kT0 = B -> zget_l Rb l kT2 = B -> zget_l Rb l kS5 = - B -> zget_l Rb l kS4 = H ->
  zget_l Rb l kS6 = cellv (cf (Z.land lm H)) -> zget_l Rb l kT5 = code_bits (cf (Z.land lm H)) ->
  zget_l Rb l kT4 = code_bits (cf (Z.land lm H)) + 256 * code_val (cf (Z.land lm H)) ->
  0 <= j -> j < nd -> nd <= 316 -> 0 <= ci -> ci <= n -> 0 <= B ->
  code_bits (cf (Z.land lm H)) <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  lm = 2 ^ lb - 1 -> 1 <= lb -> lb <= 15 -> 0 <= nx -> nx <= 1444 -> tab_ok CODES (rdc cf (CDyn 0)) lb nx = true ->
  (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) -> (forall i, 0 <= i < j -> lf i <= 15) ->
  1 <= q -> 0 <= n -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 ->
  Z.max (p + 7176) (q + n) + 1024 <= u -> u + 208 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 cf -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -136) (- (p + 168) + -1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -128) (p + 168) ->
  P j M ->
  (forall M' (a v : Z), P j M' -> a = p + 156 -> 0 <= v < 4294967296 -> P v (wbytes M' (w64 a) (Z_to_le_bytes 4 v))) ->
  (forall M' (jo a v : Z), P jo M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (* [comment removed for export] *)
  (forall R' (B' H' : Z),
     zget R' kS10 = q + n -> zget R' kS8 = 0 -> zget R' kS2 = B' -> zget R' kS4 = H' ->
     0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * n -> B' <= 8 * (n - ci) + B ->
     keptc Rb l R' KS_CRT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_LD2 (zupd R' []) M MD) T) ->
  (* [comment removed for export] *)
  (forall R' (ci' B' H' : Z),
     zget R' kA7 = q + ci' -> zget R' kS8 = n - ci' -> zget R' kS2 = B' -> zget R' kS4 = H' -> zget R' kA1 = MSG_BADREP_T ->
     ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ci) + B ->
     keptc Rb l R' KS_CRB ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_BADMSG_A1 (zupd R' []) M MD) T) ->
  (* [comment removed for export] *)
  (forall R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     zget R' kA6 = j' -> zget R' kA7 = q + ci' -> zget R' kS10 = q + ci' -> zget R' kT6 = n - ci' -> zget R' kS8 = n - ci' ->
     zget R' kS2 = B' -> zget R' kS4 = H' ->
     j < j' -> j' < nd -> ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' + 1 <= 8 * (n - ci) + B ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -136) (- (p + 168) + -1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -128) (p + 168) -> P j' M' ->
     keptc Rb l R' KS_CRT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_WHILE_T (zupd R' []) M' MD) T) ->
  (* [comment removed for export] *)
  (forall R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     zget R' kS10 = q + ci' -> zget R' kS8 = n - ci' -> zget R' kS2 = B' -> zget R' kS4 = H' ->
     j < j' -> j' = nd -> ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' + 1 <= 8 * (n - ci) + B ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -136) (- (p + 168) + -1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -128) (p + 168) -> P j' M' ->
     keptc Rb l R' KS_CRT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_DONE (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_RES_T (zupd Rb l) M MD) T.
Proof.
  intros P Rb l M MD T u p q n nd lb lm nx j ci B H fin cf lf Hh
    Lsp Ls11 La1 La6 Ls9 Lt3 Ls7 Lt1 Lt0 Lt2 Ls4 Ls3 Ls5 Lt5 Lt4
    Hj0 Hj1 Hnd Hc0 Hc2 HB0 Hbe HB40 HH1 HH2 HBc Hdm Hlb1 Hlb2 Hnx1 Hnx2 TOK Rlf Hlf15
    Hq1 Hn0 Hn26 Hq2 Hp1 Hp2 Hu1 Hu2 SPQ Wp Hin Rfin Hcodes Hlens S136 S128 HP HPa HPb KX KB KW KDN.
  zkeys. unfold L_CL_RES_T, L_CL_WHILE_T, L_CL_DONE, L_LEAVE_LD2, L_BADMSG_A1, L_BADREP0_T, L_BADREP_T, MSG_BADREP_T,
    L_CL_P17_T, L_CL_X17_T, L_CL_P16_T, L_CL_X16_T, L_CL_P18_T, L_CL_X18_T, L_LVX_CLN_T, L_CL_CHK_T, L_CL_FILL_T, L_CL_FILLX_T in *.
  pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPlb.
  pose proof (land_mask_l H lb ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (ctab_bits cf lb nx (Z.land lm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits0 Hpow].
  set (e := cf (Z.land lm H)) in *.
  pose proof (code_bits_range e) as Rbe. pose proof (code_val_range e) as Rve. pose proof (cellv_range e) as Rce.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  pose proof (lnot_val_mod' (p + 168) ltac:(lia)) as Hnl.
  (* [comment removed for export] *)
  assert (CHK : forall RC (ci' B' H' copy len : Z),
    zget RC kT0 = copy -> zget RC kT1 = len -> zget RC kS4 = H' -> zget RC kS2 = B' ->
    zget RC kS8 = n - ci' -> zget RC kA7 = q + ci' -> zget RC kA6 = j -> zget RC kA1 = nd ->
    zget RC kSP = u + -256 -> zget RC kS0 = p ->
    3 <= copy -> copy <= 138 -> 0 <= len -> len <= 15 ->
    ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
    8 * (n - ci') + B' + 1 <= 8 * (n - ci) + B ->
    keptc Rb l RC KS_CRT ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 90096 (zupd RC []) M MD) T).
  { intros RC ci' B' H' copy len G6 G7 G20 G10 G24 G18 G17 G12 G3 G28 Hcp1 Hcp2 Hln1 Hln2 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 HK.
    zkeys.
    tstep1 Rfd.                       (* [comment removed for export] *)
    destruct (Z_lt_dec nd (copy + j)) as [Hover | Hfit].
    - zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd. zstep Rfd. zlit.     (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KB Rx ci' B' H') end. all: kgoalT.
    - zbr Rfd true.                   (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        pose proof (fun M1 a1 v1 => HPb M1 j a1 v1) as HPbj;
        eapply (cl_fill_t (Z.to_nat 138) (P j) Rx lx Mx MD T u p q n j (copy + j) len fin cf lf Hh) end;
        try zreg; try lia; try eassumption.
      intros R' M' lf' G17' G6' Wp' Hin' Hcodes' Hlens' S136' S128' HP' Hfill Hkeep HK'. unfold L_CL_FILLX_T. zimps. kopenT HK'. zkeys.
      tstorePc Rfd HP' HPa.           (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      destruct (Z_lt_dec (copy + j) nd) as [Hlt | Hge].
      + zbr Rfd true.                 (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
          eapply (KW Rx Mx (copy + j) ci' B' H' lf') end; try eassumption.
        all: first [ intros i Hi;
                     first [ destruct (Z_lt_dec i j) as [Hl|Hr]; [rewrite Hkeep by lia; apply Rlf; lia |];
                             destruct (Z_lt_dec i (copy + j)) as [Hm|Hx]; [rewrite Hfill by lia; lia | rewrite Hkeep by lia; apply Rlf; lia]
                           | destruct (Z_lt_dec i j) as [Hl|Hr]; [rewrite Hkeep by lia; apply Hlf15; lia | rewrite Hfill by lia; lia] ]
                   | kgoalT ].
      + zbr Rfd false.                (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
          eapply (KDN Rx Mx (copy + j) ci' B' H' lf') end; try eassumption.
        all: first [ intros i Hi;
                     first [ destruct (Z_lt_dec i j) as [Hl|Hr]; [rewrite Hkeep by lia; apply Rlf; lia |];
                             destruct (Z_lt_dec i (copy + j)) as [Hm|Hx]; [rewrite Hfill by lia; lia | rewrite Hkeep by lia; apply Rlf; lia]
                           | destruct (Z_lt_dec i j) as [Hl|Hr]; [rewrite Hkeep by lia; apply Hlf15; lia | rewrite Hfill by lia; lia] ]
                   | kgoalT ]. }
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (code_val e / 16) ltac:(symmetry; apply cell_shr20).
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (code_val e) ltac:(symmetry; apply cell_shr16).
  destruct (Z_lt_dec 15 (code_val e)) as [Hrep | Hlit].
  2: { (* [comment removed for export] *)
    assert (Hv16 : code_val e / 16 = 0) by (apply Z.div_small; lia_std).
    zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstorePc Rfd HP HPa.              (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (2 * j) ltac:(rewrite shiftl_1m; reflexivity).
    zstep Rfd.                        (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (H / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold_cellC H B e); lia).
    pose proof (hold_shr_bound H B (code_bits e) ltac:(lia) ltac:(lia)) as HH'.
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg B ltac:(first [symmetry; rewrite swrap32_small by lia; lia | lia | rewrite swrap32_small; lia]).
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (code_bits e) ltac:(symmetry; apply cell_shl48_shr56).
    tstep1 Rfd.                       (* [comment removed for export] *)
    pose proof (fun M1 a1 v1 => HPb M1 (j + 1) a1 v1) as HPb1.
    tstore_arrPc Rfd Hlens j HP HPb1. (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    destruct (Z_lt_dec (j + 1) nd) as [Hlt | Hge].
    - zbr Rfd true.                   (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KW Rx Mx (j + 1) ci (B - code_bits e) (H / 2 ^ code_bits e) (zfupd lf j (code_val e))) end;
        try eassumption.
      all: first [ intros i Hi; unfold zfupd; destruct (Z.eqb_spec i j); [lia | first [apply Rlf; lia | apply Hlf15; lia]]
                 | kgoalT ].
    - zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KDN Rx Mx (j + 1) ci (B - code_bits e) (H / 2 ^ code_bits e) (zfupd lf j (code_val e))) end;
        try eassumption.
      all: first [ intros i Hi; unfold zfupd; destruct (Z.eqb_spec i j); [lia | first [apply Rlf; lia | apply Hlf15; lia]]
                 | kgoalT ]. }
  (* [comment removed for export] *)
  assert (Hv16 : 1 <= code_val e / 16 /\ code_val e / 16 < 4096) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia_std).
  zbr Rfd true.                       (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg B ltac:(first [symmetry; rewrite swrap32_small by lia; lia | lia | rewrite swrap32_small; lia]).
  (* [comment removed for export] *)
  assert (X16 : forall RX (ci' B' H' : Z),
    zget RX kS8 = n - ci' -> zget RX kA7 = q + ci' -> zget RX kT0 = B' -> zget RX kS4 = H' ->
    zget RX kT5 = code_bits e -> zget RX kT4 = code_bits e + 256 * code_val e ->
    zget RX kA6 = j -> zget RX kA1 = nd -> zget RX kSP = u + -256 -> zget RX kS0 = p ->
    ci <= ci' -> ci' <= n -> code_bits e + 2 <= B' -> B' <= 40 ->
    0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' -> 8 * (n - ci') + B' <= 8 * (n - ci) + B ->
    keptc Rb l RX KS_CRT ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 89956 (zupd RX []) M MD) T).
  { intros RX ci' B' H' G24 G18 G6 G20 G31 G30 G17 G12 G3 G28 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 HK. kopenT HK. zkeys.
    pose proof (pow2_48 B' ltac:(lia)) as HPB'.
    zstep Rfd.                        (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (H' / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold_cellC H' B' e); lia).
    pose proof (hold_shr_bound H' B' (code_bits e) ltac:(lia) ltac:(lia)) as HS2.
    pose proof (pow2_48 (B' - code_bits e) ltac:(lia)) as HPd.
    set (H2 := H' / 2 ^ code_bits e) in *.
    tstep1 Rfd.                       (* [comment removed for export] *)
    destruct (Z.eq_dec j 0) as [Hj | Hj].
    - (* [comment removed for export] *)
      zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd. zstep Rfd. zlit.     (* [comment removed for export] *)
      pose proof (pow2_le (B' - code_bits e) B' ltac:(lia)) as HP2.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KB Rx ci' (B' - code_bits e) H2) end. all: kgoalT.
    - zbr Rfd true.                   (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zbr Rfd true.                   (* [comment removed for export] *)
      tstep1 Rfd.                     (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zsetreg (2 * (j - 1)) ltac:(rewrite shiftl_1m; reflexivity).
      zstep Rfd.                      (* [comment removed for export] *)
      zbr Rfd true.                   (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      pose proof (Rlf (j - 1) ltac:(lia)) as Rlj. pose proof (Hlf15 (j - 1) ltac:(lia)) as Hlj.
      tstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      pose proof (land3_range H2) as Hcp.
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zsetreg (H2 / 2 ^ 2) ltac:(rewrite (Z.mod_small H2) by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      pose proof (hold_shr_bound H2 (B' - code_bits e) 2 ltac:(lia) ltac:(lia)) as HS3.
      tstep1 Rfd.                     (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      pose proof (pow2_le (B' - code_bits e - 2) (B' - code_bits e) ltac:(lia)) as HP3.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (CHK Rx ci' (B' - code_bits e - 2) (H2 / 2 ^ 2) (Z.land H2 3 + 3) (lf (j - 1))) end.
      all: kgoalT. }
  (* [comment removed for export] *)
  assert (X1718 : forall (pcx k base : Z) RX (ci' B' H' : Z),
    ((pcx = 89904 /\ k = 3 /\ base = 3) \/ (pcx = 90056 /\ k = 7 /\ base = 11)) ->
    zget RX kS8 = n - ci' -> zget RX kA7 = q + ci' -> zget RX kT0 = B' -> zget RX kS4 = H' ->
    zget RX kT5 = code_bits e -> zget RX kT4 = code_bits e + 256 * code_val e ->
    zget RX kA6 = j -> zget RX kA1 = nd -> zget RX kSP = u + -256 -> zget RX kS0 = p ->
    ci <= ci' -> ci' <= n -> code_bits e + k <= B' -> B' <= 40 ->
    0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' -> 8 * (n - ci') + B' <= 8 * (n - ci) + B ->
    keptc Rb l RX KS_CRT ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pcx (zupd RX []) M MD) T).
  { intros pcx k base RX ci' B' H' Hpcx G24 G18 G6 G20 G31 G30 G17 G12 G3 G28 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 HK. kopenT HK. zkeys.
    pose proof (pow2_48 B' ltac:(lia)) as HPB'.
    destruct Hpcx as [(-> & -> & ->) | (-> & -> & ->)].
    - zstep Rfd.                      (* [comment removed for export] *)
      zbr Rfd true.                   (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zsetreg (H' / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold_cellC H' B' e); lia).
      pose proof (hold_shr_bound H' B' (code_bits e) ltac:(lia) ltac:(lia)) as HS2.
      pose proof (pow2_48 (B' - code_bits e) ltac:(lia)) as HPd.
      set (H2 := H' / 2 ^ code_bits e) in *.
      tstep1 Rfd.                     (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      pose proof (land7_range' H2) as Hcp.
      zstep Rfd.                      (* [comment removed for export] *)
      zsetreg (H2 / 2 ^ 3) ltac:(rewrite (Z.mod_small H2) by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      pose proof (hold_shr_bound H2 (B' - code_bits e) 3 ltac:(lia) ltac:(lia)) as HS3.
      zstep Rfd.                      (* [comment removed for export] *)
      tstep1 Rfd.                     (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      pose proof (pow2_le (B' - code_bits e - 3) (B' - code_bits e) ltac:(lia)) as HP3.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (CHK Rx ci' (B' - code_bits e - 3) (H2 / 2 ^ 3) (Z.land H2 7 + 3) 0) end.
      all: kgoalT.
    - zstep Rfd.                      (* [comment removed for export] *)
      zbr Rfd true.                   (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zsetreg (H' / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold_cellC H' B' e); lia).
      pose proof (hold_shr_bound H' B' (code_bits e) ltac:(lia) ltac:(lia)) as HS2.
      pose proof (pow2_48 (B' - code_bits e) ltac:(lia)) as HPd.
      set (H2 := H' / 2 ^ code_bits e) in *.
      tstep1 Rfd.                     (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      pose proof (land127_range H2) as Hcp.
      zstep Rfd.                      (* [comment removed for export] *)
      zsetreg (H2 / 2 ^ 7) ltac:(rewrite (Z.mod_small H2) by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      pose proof (hold_shr_bound H2 (B' - code_bits e) 7 ltac:(lia) ltac:(lia)) as HS3.
      zstep Rfd.                      (* [comment removed for export] *)
      tstep1 Rfd.                     (* [comment removed for export] *)
      pose proof (pow2_le (B' - code_bits e - 7) (B' - code_bits e) ltac:(lia)) as HP3.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (CHK Rx ci' (B' - code_bits e - 7) (H2 / 2 ^ 7) (Z.land H2 127 + 11) 0) end.
      all: kgoalT. }
  (* [comment removed for export] *)
  assert (PULL : forall (pc pcx k : Z) RP,
    ((pc = 89644 /\ pcx = 89904 /\ k = 3) \/ (pc = 89732 /\ pcx = 89956 /\ k = 2) \/ (pc = 89820 /\ pcx = 90056 /\ k = 7)) ->
    B < code_bits e + k ->
    zget RP kS8 = n - ci -> zget RP kS2 = q + ci -> zget RP kT3 = q + ci -> zget RP kT2 = B -> zget RP kT0 = B ->
    zget RP kT6 = code_bits e + k -> zget RP kS4 = H -> zget RP kS10 = q + ci -> zget RP kT1 = n - ci ->
    zget RP kT5 = code_bits e -> zget RP kT4 = code_bits e + 256 * code_val e ->
    zget RP kA6 = j -> zget RP kA1 = nd -> zget RP kSP = u + -256 -> zget RP kS0 = p ->
    keptc Rb l RP KS_CRT ->
    (forall RX (ci' B' H' : Z),
       zget RX kS8 = n - ci' -> zget RX kA7 = q + ci' -> zget RX kT0 = B' -> zget RX kS4 = H' ->
       zget RX kT5 = code_bits e -> zget RX kT4 = code_bits e + 256 * code_val e ->
       zget RX kA6 = j -> zget RX kA1 = nd -> zget RX kSP = u + -256 -> zget RX kS0 = p ->
       ci <= ci' -> ci' <= n -> code_bits e + k <= B' -> B' <= 40 ->
       0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' -> 8 * (n - ci') + B' <= 8 * (n - ci) + B ->
       keptc Rb l RX KS_CRT ->
       realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pcx (zupd RX []) M MD) T) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd RP []) M MD) T).
  { intros pc pcx k RP Hpc Hneed G24 G10 G29 G8 G6 G32 G20 G26 G7 G31 G30 G17 G12 G3 G28 HK KXD. kopenT HK.
    assert (Hk : 2 <= k <= 7) by (destruct Hpc as [(_ & _ & ->) | [(_ & _ & ->) | (_ & _ & ->)]]; lia).
    eapply (cl_pull_t (S (Z.to_nat (n - ci))) pc pcx RP [] M MD T q n (code_bits e + k) ci B ci B H fin);
      [ destruct Hpc as [(-> & -> & _) | [(-> & -> & _) | (-> & -> & _)]];
        [left; split; reflexivity | right; left; split; reflexivity | right; right; split; reflexivity]
      | exact Hh | .. ]; try (cbv [zget_l alookup]; eassumption); try eassumption; try lia.
    - (* [comment removed for export] *)
      intros R' H' E20 E24 E6 E26 E7 X1 X2 X3 X4 HK'. kopenT HK'.
      eapply (stub_CLn_t R' [] M MD T q n ci (B + 8 * (n - ci)) Hh); try (cbv [zget_l alookup]; first [eassumption | etransitivity; [eassumption|]; lia]).
      intros R'' E26' E10' HK''. kopenT HK''.
      eapply (KX R'' (B + 8 * (n - ci)) H'). all: kgoalT.
    - intros R' ci' B' H'. intros. eapply (KXD R' ci' B' H'). all: kgoalT. }
  destruct (Z.eq_dec (code_val e) 16) as [E16 | N16].
  - (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    destruct (Z_lt_dec B (code_bits e + 2)) as [Hneed | Hhave].
    + zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (PULL 89732 89956 2 Rx) end;
        [ right; left; split_conj; reflexivity | exact Hneed | .. ]; try zreg; try keptc_closeR; try exact X16.
    + zbr Rfd true.                   (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (X16 Rx ci B H) end. all: kgoalT.
  - zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    destruct (Z.eq_dec (code_val e) 17) as [E17 | N17].
    + (* [comment removed for export] *)
      zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      destruct (Z_lt_dec B (code_bits e + 3)) as [Hneed | Hhave].
      * zbr Rfd false.                (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (PULL 89644 89904 3 Rx) end;
          [ left; split_conj; reflexivity | exact Hneed | .. ]; try zreg; try keptc_closeR.
        intros RX ci' B' H'. intros. eapply (X1718 89904 3 3 RX ci' B' H'); [left; split_conj; reflexivity | ..]. all: kgoalT.
      * zbr Rfd true.                 (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (X1718 89904 3 3 Rx ci B H) end;
          [left; split_conj; reflexivity | ..]. all: kgoalT.
    + (* [comment removed for export] *)
      zbr Rfd true.                   (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      destruct (Z_lt_dec B (code_bits e + 7)) as [Hneed | Hhave].
      * zbr Rfd false.                (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (PULL 89820 90056 7 Rx) end;
          [ right; right; split_conj; reflexivity | exact Hneed | .. ]; try zreg; try keptc_closeR.
        intros RX ci' B' H'. intros. eapply (X1718 90056 7 11 RX ci' B' H'); [right; split_conj; reflexivity | ..]. all: kgoalT.
      * zbr Rfd true.                 (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (X1718 90056 7 11 Rx ci B H) end;
          [right; split_conj; reflexivity | ..]. all: kgoalT.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cl_loop_t {RCa1 : RunCtx}  : forall (N : nat) (P : Z -> mem -> Prop) Rb l M MD T (u p q n nlen nd lb lm nx ce Be j ci B H : Z) (fin cf lf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + -256 -> zget_l Rb l kS0 = p ->
  zget_l Rb l kA2 = nlen -> zget_l Rb l kA1 = nd -> zget_l Rb l kA3 = lb -> zget_l Rb l kA4 = p + 1384 -> zget_l Rb l kA5 = lm ->
  zget_l Rb l kA6 = j -> zget_l Rb l kA7 = q + ci -> zget_l Rb l kS10 = q + ci -> zget_l Rb l kT6 = n - ci -> zget_l Rb l kS8 = n - ci ->
  zget_l Rb l kS2 = B -> zget_l Rb l kS4 = H ->
  nd - j <= Z.of_nat N -> 0 <= j -> j < nd -> nd <= 316 ->
  ce <= ci -> ci <= n -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci -> 8 * (n - ci) + B <= 8 * (n - ce) + Be ->
  lm = 2 ^ lb - 1 -> 1 <= lb -> lb <= 15 -> 0 <= nx -> nx <= 1444 -> tab_ok CODES (rdc cf (CDyn 0)) lb nx = true ->
  (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) -> (forall i, 0 <= i < j -> lf i <= 15) ->
  1 <= q -> 0 <= n -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 ->
  Z.max (p + 7176) (q + n) + 1024 <= u -> u + 208 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 cf -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -136) (- (p + 168) + -1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -128) (p + 168) ->
  P j M ->
  (forall M' (jo a v : Z), P jo M' -> a = p + 156 -> 0 <= v < 4294967296 -> P v (wbytes M' (w64 a) (Z_to_le_bytes 4 v))) ->
  (forall M' (jo a v : Z), P jo M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (* [comment removed for export] *)
  (forall R' M' (j' B' H' : Z) (lf' : Z -> Z),
     zget R' kS10 = q + n -> zget R' kS8 = 0 -> zget R' kS2 = B' -> zget R' kS4 = H' ->
     0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * n -> B' <= 8 * (n - ce) + Be ->
     j <= j' -> j' < nd ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -136) (- (p + 168) + -1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -128) (p + 168) -> P j' M' ->
     keptc Rb l R' KS_CRT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_LD2 (zupd R' []) M' MD) T) ->
  (* [comment removed for export] *)
  (forall R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     zget R' kA7 = q + ci' -> zget R' kS8 = n - ci' -> zget R' kS2 = B' -> zget R' kS4 = H' -> zget R' kA1 = MSG_BADREP_T ->
     ce <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ce) + Be -> j <= j' -> j' < nd ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -136) (- (p + 168) + -1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -128) (p + 168) -> P j' M' ->
     keptc Rb l R' KS_CRB ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_BADMSG_A1 (zupd R' []) M' MD) T) ->
  (* [comment removed for export] *)
  (forall R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     zget R' kS10 = q + ci' -> zget R' kS8 = n - ci' -> zget R' kS2 = B' -> zget R' kS4 = H' ->
     ce <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ce) + Be -> j < j' -> j' = nd ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -136) (- (p + 168) + -1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -128) (p + 168) -> P j' M' ->
     keptc Rb l R' KS_CRT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_DONE (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_WHILE_T (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T u p q n nlen nd lb lm nx ce Be j ci B H fin cf lf Hh
    Lsp Ls11 La2 La1 La3 La4 La5 La6 La7 Ls9 Lt6 Ls7 Ls1 Ls3
    HN Hj0 Hj1 Hnd Hce Hc2 HB0 HB40 HH1 HH2 HBc HW Hdm Hlb1 Hlb2 Hnx1 Hnx2 TOK Rlf Hlf15
    Hq1 Hn0 Hn26 Hq2 Hp1 Hp2 Hu1 Hu2 SPQ Wp Hin Rfin Hcodes Hlens S136 S128 HP HPa HPb KXL KBD KDN; [lia|].
  zkeys. unfold L_CL_WHILE_T, L_CL_DLOOP_T, L_CL_RES_T, L_CL_DONE, L_LVX_CLD_T, L_LEAVE_LD2, L_BADMSG_A1, MSG_BADREP_T in *.
  pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPlb. pose proof (pow2_48 B ltac:(lia)) as HPB.
  pose proof (land_mask_l H lb ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (ctab_bits cf lb nx (Z.land lm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits0 Hpow].
  (* [comment removed for export] *)
  assert (RES : forall RR (ci1 B1 H1 : Z),
    zget RR kSP = u + -256 -> zget RR kS0 = p -> zget RR kA1 = nd -> zget RR kA6 = j ->
    zget RR kS10 = q + ci1 -> zget RR kT3 = q + ci1 -> zget RR kS8 = n - ci1 -> zget RR kT1 = n - ci1 ->
    zget RR kT0 = B1 -> zget RR kT2 = B1 -> zget RR kS5 = - B1 -> zget RR kS4 = H1 ->
    zget RR kS6 = cellv (cf (Z.land lm H1)) -> zget RR kT5 = code_bits (cf (Z.land lm H1)) ->
    zget RR kT4 = code_bits (cf (Z.land lm H1)) + 256 * code_val (cf (Z.land lm H1)) ->
    ci <= ci1 -> ci1 <= n -> B1 = B + 8 * (ci1 - ci) -> code_bits (cf (Z.land lm H1)) <= B1 -> B1 <= 40 ->
    0 <= H1 -> H1 < 2 ^ B1 -> B1 <= 8 * ci1 ->
    keptc Rb l RR KS_CRT ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 89500 (zupd RR []) M MD) T).
  { intros RR ci1 B1 H1. intros. match goal with HK : keptc _ _ _ _ |- _ => kopenT HK end.
    eapply (cl_res_t P RR [] M MD T u p q n nd lb lm nx j ci1 B1 H1 fin cf lf Hh);
      try (cbv [zget_l alookup]; eassumption); try eassumption; try lia.
    - intros M1 a1 v1 X1 X2 X3. exact (HPa M1 j a1 v1 X1 X2 X3).
    - (* [comment removed for export] *)
      intros R' B' H'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopenT HK end.
      eapply (KXL R' M j B' H' lf). all: kgoalT.
    - (* [comment removed for export] *)
      intros R' ci' B' H'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopenT HK end.
      eapply (KBD R' M j ci' B' H' lf). all: kgoalT.
    - (* [comment removed for export] *)
      intros R' M' j' ci' B' H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopenT HK end.
      pose proof (pow2_48 B' ltac:(lia)) as HPB'.
      eapply (IH P R' [] M' MD T u p q n nlen nd lb lm nx ce Be j' ci' B' H' fin cf lf' Hh);
        try (cbv [zget_l alookup]; first [eassumption | zkept]); try eassumption; try lia.
      + intros RR9 MM9 jj9 BB9 HQ9 ll9. intros. match goal with HK : keptc _ _ _ _ |- _ => kopenT HK end.
        eapply (KXL RR9 MM9 jj9 BB9 HQ9 ll9). all: kgoalT.
      + intros RR9 MM9 jj9 cc9 BB9 HQ9 ll9. intros. match goal with HK : keptc _ _ _ _ |- _ => kopenT HK end.
        eapply (KBD RR9 MM9 jj9 cc9 BB9 HQ9 ll9). all: kgoalT.
      + intros RR9 MM9 jj9 cc9 BB9 HQ9 ll9. intros. match goal with HK : keptc _ _ _ _ |- _ => kopenT HK end.
        eapply (KDN RR9 MM9 jj9 cc9 BB9 HQ9 ll9). all: kgoalT.
    - (* [comment removed for export] *)
      intros R' M' j' ci' B' H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopenT HK end.
      eapply (KDN R' M' j' ci' B' H' lf'). all: kgoalT. }
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (4 * Z.land lm H) ltac:(symmetry; first [apply shiftl_2 | apply shl_2]).
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  zstep Rfd. zbool.                   (* [comment removed for export] *)
  zstep Rfd. zbool.                   (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg 1 ltac:(reflexivity).
  zbr Rfd true.                       (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (- B) ltac:(first [symmetry; rewrite swrap32_small by lia; lia | lia | rewrite swrap32_small; lia]).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd. zext32.                  (* [comment removed for export] *)
  zstep Rfd. zext32.                  (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (cl_decode_t (S (Z.to_nat (n - ci))) Rx lx Mx MD T p q n lb lm nx ci B ci B H fin cf Hh) end;
    try zreg; try lia; try eassumption.
  - (* [comment removed for export] *)
    intros R' H'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopenT HK end.
    eapply (stub_CLd_t R' [] M MD T q n ci B (Z.shiftl (n - ci) 32) Hh); try (cbv [zget_l alookup]; first [eassumption | zkept]);
      try (apply zext32_shift; lia); try lia.
    intros R''. intros. match goal with HK : keptc _ _ _ _ |- _ => kopenT HK end.
    eapply (KXL R'' M j (B + 8 * (n - ci)) H' lf). all: kgoalT.
  - (* [comment removed for export] *)
    intros R' ci' B' H'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopenT HK end.
    eapply (RES R' ci' B' H'). all: kgoalT.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CL.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Hypothesis CLDONE : cldone_stmt.

Theorem clhead_t : clhead_stmt.
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
  unfold s_regs_clh, s_vars in RG. icx_cbn. destr_conj RG.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (i_frame_slots_t _ _ FRM) as FS. icx_cbn. dand FS as (_ & Q128 & Q120 & _).
  pose proof SREST as SR'. unfold st_rest in SR'. icx_cbn.
  dand SR' as (_ & _ & _ & _ & _ & _ & _ & C104 & _ & C120 & _ & _ & C132 & C136 & C140 & _).
  subst lc. cbv [cp_addr o_codes] in C104. icx_cbn.
  assert (Hshv : 0 <= shave) by lia.
  (* [comment removed for export] *)
  pose proof (PLT_intro _ _ _ _ _ _ _ KM0) as [HP _]. cbn [t_shave] in HP.
  clear Ww CST HK Hmode SREST SRET SLO SBK.
  prune_rng.
  zkeysb. unfold L_CODELENS, L_CL_DONE, L_CL_WHILE_T, L_LEAVE_LD2, L_BADMSG_A1, MSG_BADREP_T in *.
  pose proof two64_eq as TW64.
  tstep1 Rfd.                         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zsetreg (nlen + ndist) ltac:(lia).
  destruct (Z_lt_dec shave (nlen + ndist)) as [Hgo | Hdone0].
  2: { (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (CLDONE (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI0) end.
    - unfold s_regs_cld, s_vars; icx_cbn; zkeys; split_conj; zreg.
    - exact KM0.
    - exact KA0. }
  zbr Rfd false.                      (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (2 ^ lb - 1) ltac:(symmetry; apply mask_not_sllw; lia).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (KMX : forall M' (ci' H' B' j' : Z) (lf' : Z -> Z),
    PLT (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
        (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) cf j' M' ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' ->
    k_mem (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
      (st_cl (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' j') lf' cf M').
  { intros M' ci' H' B' j' lf' HP' HL'.
    pose proof (PLT_kmem _ _ _ _ lf' _ _ _ HP' HL') as X.
    unfold st_sh, st_cl in X |- *. unfold k_mem, st_at, st_rest, s_ret, s_lo, s_bk in X |- *.
    cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in X |- *.
    exact X. }
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (cl_loop_t (S (Z.to_nat (nlen + ndist - shave)))
              (PLT (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                   (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) cf)
              Rx lx Mx MD T u p q n nlen (nlen + ndist) lb (2 ^ lb - 1) nx cin bits shave cin bits hold fin cf lf Hh) end;
    try zreg; try lia; try eassumption; try reflexivity.
  - unfold ZSEP. pose proof (sep_p_q _ _ SEP) as D. cbn [c_p c_q c_n] in D. cbv [STATE_SIZE] in D. exact D.
  - intros M' jo a v HPj Ha Hv. apply (PLT_store140 _ _ _ _ _ _ _ _ _ CX0 HPj); [icx_cbn; exact Ha | exact Hv].
  - intros M' jo a v HPj Ha1 Ha2. apply (PLT_store_lens _ _ _ _ _ _ _ _ _ CX0 HPj); icx_cbn; lia.
  - (* [comment removed for export] *)
    intros R' M' j' B' H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopenT HK end. zkeys.
    pose proof (sinv_cl _ _ lf cf n H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(assumption) ltac:(assumption)) as [SI1 ME1].
    match goal with HP' : PLT _ _ _ _ _ j' M', HL' : mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' |- _ =>
      pose proof (KMX M' n H' B' j' lf' HP' HL') as KM' end.
    dand KM' as (STD' & SAT' & SRET' & SLO' & HLn' & HCd' & HP0' & SBK').
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KLL2 Rx Mx (st_cl (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) n H' B' j') lf' cf SI1) end.
    + unfold s_regs_leave_ld2, st_cl; icx_cbn; zkeys; split_conj; kgoalT.
    + exact STD'.
    + exact SAT'.
    + exact SRET'.
    + exact SLO'.
    + exact SBK'.
    + exact HLn'.
    + exact HCd'.
    + exact HP0'.
  - (* [comment removed for export] *)
    intros R' M' j' ci' B' H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopenT HK end. zkeys.
    pose proof (sinv_cl _ _ lf cf ci' H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(assumption) ltac:(assumption)) as [SI1 ME1].
    pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (st_cl (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' j')) as MB.
    unfold st_cl in MB, SI1, ME1 |- *. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in MB, SI1, ME1 |- *. change (rank CODELENS) with 20 in MB.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KB1 Rx Mx (IST CODELENS last flags ci' cout H' B' out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist j' nx whave wnext) lf' cf
                (sinv_bad_of _ _ _ _ SI1)) end.
    all: try (icx_cbn; zkeys; kgoalT).
    + clear - MB ME1. unfold bad_of. unfold SBase.bad_of in MB. cbn [t_mode] in *. lia_std.
    + lazymatch goal with |- 0 <= ?x < _ => assert (EA1 : x = 66210) by kgoalT; rewrite EA1 end. lia.
    + apply KMX; assumption.
  - (* [comment removed for export] *)
    intros R' M' j' ci' B' H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopenT HK end. zkeys.
    pose proof (sinv_cl _ _ lf cf ci' H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(assumption) ltac:(assumption)) as [SI1 ME1].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (CLDONE (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (st_cl (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' j')
                lf' cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI1) end.
    + unfold s_regs_cld, s_vars, st_cl; icx_cbn; zkeys; split_conj; kgoalT.
    + apply KMX; assumption.
    + eapply KALL_mono; [| exact KA0]. clear - ME1. unfold st_cl in ME1. exact ME1.
Qed.

(* [comment removed for export] *)
Theorem arm_CODELENS_t0 : arm_stmt L_CODELENS CODELENS.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  eapply (clhead_t cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI); [| exact KM | exact K].
  dand RE as (FIX & VARS & _). unfold s_fix in FIX. destr_conj FIX.
  unfold s_regs_clh. split_conj; assumption.
Qed.

End CL.
End T_Codelens.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U Require Import TBase T_ClDefs. Import T_Table. Import T_CodelensT. Import T_Codelens.
Import ListNotations.
Open Scope Z_scope.

Theorem arm_TABLE_t {RCa1 : RunCtx}  : itable_spec_t -> lenu_stmt -> arm_stmt L_TABLE TABLE.
Proof. intros IT LU. exact (arm_TABLE_t0 IT (clhead_t (cldone_t IT LU))). Qed.

Theorem arm_LENLENS_t {RCa1 : RunCtx}  : itable_spec_t -> lenu_stmt -> arm_stmt L_LENLENS LENLENS.
Proof. intros IT LU. exact (arm_LENLENS_t0 IT (clhead_t (cldone_t IT LU))). Qed.

Theorem arm_CODELENS_t {RCa1 : RunCtx}  : itable_spec_t -> lenu_stmt -> arm_stmt L_CODELENS CODELENS.
Proof. intros IT LU. exact (arm_CODELENS_t0 (cldone_t IT LU)). Qed.

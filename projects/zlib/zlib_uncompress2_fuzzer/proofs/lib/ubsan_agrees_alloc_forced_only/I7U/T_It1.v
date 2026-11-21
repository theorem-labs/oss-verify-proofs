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
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import
  ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U Require Import Base.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require Import ZTac ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require Import S_It0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.

Ltac zmem_transport_loop_T_It1 M a bs :=
  repeat match goal with
  | H : mem_arr ?k ?segs M ?base ?n ?f |- _ =>
      first [ apply (mem_arr_frame segs k M base n f a bs) in H; [|unfold zdisj; zlen_norm; zlia]
            | idtac "WARNING: mem_arr fact dropped at store" a base; clear H ]
  | H : mem_u64 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 8;
      first [ apply (mem_u64_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u32 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 4;
      first [ apply (mem_u32_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u16 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 2;
      first [ apply (mem_u16_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u8 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 1;
      first [ apply (mem_u8_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_is ?segs M ?a' ?bs' |- _ =>
      zrng_ensure a' (Z.of_nat (length bs'));
      first [ apply (mem_is_frame segs M a bs a' bs') in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_wr ?segs M ?a' ?len |- _ =>
      apply (mem_wr_frame segs M a bs a' len) in H
  | H : rom_ok M |- _ =>
      first [ apply (rom_ok_frame M a bs) in H; [| zlia | zlen_norm; zlia | unfold ROM_LO, ROM_HI; zdisj_tac]
            | idtac "WARNING: rom_ok dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stable ?Fr ?lo ?hi |- _ =>
      first [ apply (HS M a bs) in H; [|zlia|zlen_norm; zlia]
            | idtac "WARNING: framed fact dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stable2 ?Fr _ _ _ _ |- _ =>
      first [ apply (HS M a bs) in H; [|zlen_norm; zlia]
            | idtac "WARNING: framed2 fact dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stableL ?Fr _ |- _ =>
      first [ apply (HS M a bs) in H; [|zlen_norm; in_some_tac]
            | idtac "WARNING: framedL fact dropped at store" a; clear H ]
  | H : rdn ?segs M _ _ = Some _ |- _ => clear H
  end.
Ltac zmem_transport M a bs ::=
  zxfer_pre a bs;
  zmem_transport_loop_T_It1 M a bs;
  zxfer_post a.

Definition A_ITABLE_T : Z := 99036.

Lemma mem_arr2_zero16_t {RCa1 : RunCtx}  : forall M a,
  0 <= a -> a + 32 <= two64 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (a + 8) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (a + 16) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (a + 24) 0 ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M a 16 (fun _ => 0).
Proof.
  intros M a Ha Ha2 H0 H1 H2 H3.
  apply mem_arr_of_elems; [lia | lia | lia | lia |].
  intros i Hi. change (Z.to_nat 2) with 2%nat.
  assert (E : forall b j, mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M b 0 -> 0 <= j < 4 -> mem_is (run_segments R_segs rc_inp rc_sp rc_mb) M (b + 2 * j) (Z_to_le_bytes 2 0)).
  { intros b j Hb Hj. unfold mem_u64 in Hb.
    pose proof (mem_is_sub (run_segments R_segs rc_inp rc_sp rc_mb) M b (Z_to_le_bytes 8 0) (2 * j) 2 Hb ltac:(lia) ltac:(cbn; lia)) as X.
    unfold mem_is. cbn [length Z_to_le_bytes]. rewrite X.
    assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
    destruct J as [-> | [-> | [-> | ->]]]; reflexivity. }
  assert (C : i < 4 \/ (4 <= i < 8) \/ (8 <= i < 12) \/ 12 <= i) by lia.
  destruct C as [C | [C | [C | C]]].
  - apply (E a i H0). lia.
  - replace (a + 2 * i) with (a + 8 + 2 * (i - 4)) by lia. apply (E (a + 8) (i - 4) H1). lia.
  - replace (a + 2 * i) with (a + 16 + 2 * (i - 8)) by lia. apply (E (a + 16) (i - 8) H2). lia.
  - replace (a + 2 * i) with (a + 24 + 2 * (i - 12)) by lia. apply (E (a + 24) (i - 12) H3). lia.
Qed.

Section Prologue.
Context {RCa1 : RunCtx}.
Lemma it_prologue_t : forall Rb l M MD T (sp v1 v4 v5 v8 v9 v10 v11 v12 v13 v14 v15 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : Z),
  m_halted MD = None ->
  zget_l Rb l kSP = sp -> zget_l Rb l kRA = v1 -> zget_l Rb l kGP = v4 -> zget_l Rb l kTP = v5 ->
  zget_l Rb l kS0 = v8 -> zget_l Rb l kS1 = v9 ->
  zget_l Rb l kA0 = v10 -> zget_l Rb l kA1 = v11 -> zget_l Rb l kA2 = v12 -> zget_l Rb l kA3 = v13 ->
  zget_l Rb l kA4 = v14 -> zget_l Rb l kA5 = v15 ->
  zget_l Rb l kS2 = v18 -> zget_l Rb l kS3 = v19 ->
  zget_l Rb l kS4 = v20 -> zget_l Rb l kS5 = v21 -> zget_l Rb l kS6 = v22 -> zget_l Rb l kS7 = v23 ->
  zget_l Rb l kS8 = v24 -> zget_l Rb l kS9 = v25 -> zget_l Rb l kS10 = v26 -> zget_l Rb l kS11 = v27 ->
  208 <= sp -> sp <= 140737488355328 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - 208) 208 ->
  (forall R' M',
     zget_l R' [] kSP = sp + -208 -> zget_l R' [] kGP = v4 -> zget_l R' [] kTP = v5 ->
     zget_l R' [] kA0 = v10 -> zget_l R' [] kA1 = v11 -> zget_l R' [] kA2 = v12 -> zget_l R' [] kA3 = v13 ->
     zget_l R' [] kA4 = v14 -> zget_l R' [] kA5 = v15 ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -208) sp 0 0 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp - 208) 208 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -8) v1 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -16) v8 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -24) v9 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -32) v18 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -40) v19 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -48) v20 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -56) v21 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -64) v22 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -72) v23 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -80) v24 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -88) v25 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -96) v26 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -104) v27 ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -136) 16 (fun _ => 0) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99108 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99036 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T sp v1 v4 v5 v8 v9 v10 v11 v12 v13 v14 v15 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27
         Hh LSP LRA LGP LTP L8 L9 L10 L11 L12 L13 L14 L15 L18 L19 L20 L21 L22 L23 L24 L25 L26 L27 Hsp Hsp2 Wf K.
  zkeys. idtac.
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -208) sp 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (sp + -208) sp 0 0) M) by (apply mpost_refl).
  zrebase.
  zstep Rfd.
  do 13 (zstep Rfd).
  do 4 (zstep Rfd).
  lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ => eapply (K R Mx) end.
  all: try zreg.
  all: try assumption.
  apply mem_arr2_zero16_t; [lia | rewrite two64_eq; lia | assumption | | | ].
  all: match goal with |- mem_u64 _ _ ?a 0 => zfold; assumption end.
Qed.
End Prologue.

Definition pregs (p lens_ofs codes pb sp vgp vtp tyv : Z) (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kSP = sp + -208 /\ zget_l R l kGP = vgp /\ zget_l R l kTP = vtp /\
  zget_l R l kA0 = tyv /\ zget_l R l kA1 = p + 168 + 2 * lens_ofs /\ zget_l R l kA2 = codes /\
  zget_l R l kA3 = p + 160 /\ zget_l R l kA4 = pb /\ zget_l R l kA5 = p + 808.

Ltac open_pregs H := unfold pregs in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in let d := fresh "LA0" in
  let e := fresh "LA1" in let f := fresh "LA2" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in dand H as (a & b & c & d & e & f & g & h & i).
Ltac clear_regs := repeat match goal with H : zget _ _ = _ |- _ => clear H | H : zget_l _ _ _ = _ |- _ => clear H end.
Ltac close_pregs := unfold pregs; split_conj; zreg.

Section U7IT.
Context {RCa1 : RunCtx}.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 208 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cnt i := (arr_get (cntK lf lens_ofs i)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).

Lemma cA_range : forall j, 0 <= cA j <= codes.
Proof. intros j. pose proof C as C'. destruct C'. rewrite cntA_eq. pose proof (cntK_le lf lens_ofs codes j ltac:(lia_std) ltac:(lia_std)). lia_std. Qed.


Lemma count_loop_t : forall fuel i Rb l M MD T,
  (Z.to_nat (codes - i) <= fuel)%nat -> 0 <= i < codes ->
  m_halted MD = None -> PR Rb l ->
  zget_l Rb l kA6 = 2 * i -> zget_l Rb l kT5 = p + 168 + 2 * lens_ofs + 2 * i -> zget_l Rb l kT3 = 2 * codes ->
  zget_l Rb l kA7 = sp + -136 -> zget_l Rb l kT0 = 0 -> zget_l Rb l kT1 = - (p + 168 + 2 * lens_ofs) + -1 ->
  zget_l Rb l kT2 = - (sp + -136) + -1 -> zget_l Rb l kT4 = 16 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - 208) 208 ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 (cnt i) ->
  (forall R' M',
     PR R' [] -> zget_l R' [] kA7 = sp + -136 ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -136) (sp + -104) 0 0 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp - 208) 208 ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -136) 16 (cnt codes) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99204 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99152 (zupd Rb l) M MD) T.
Proof.
  induction fuel as [|fuel IH]; intros i Rb l M MD T Hfuel Hi Hh HP LA6 LT5 LT3 LA7 LT0 LT1 LT2 LT4 Wf Hlens Hcnt K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom.
  pose proof (Hlens15 i ltac:(lia)) as Hl15. pose proof (Hlf (lens_ofs + i) ltac:(lia)) as Hl16.
  assert (HCr1 : forall j, 0 <= j < 16 -> -32768 <= cnt i j < 32768).
  { intros j _. pose proof (cntK_le lf lens_ofs i j ltac:(lia) ltac:(lia)). lia. }
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) (sp + -104) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (sp + -136) (sp + -104) 0 0) M) by (apply mpost_refl).
  pose proof (lnot_val_mod' (p + 168 + 2 * lens_ofs) ltac:(lia)) as Hn1.
  pose proof (lnot_val_mod' (sp + -136) ltac:(lia)) as Hn2.
  zrebase.
  zbr Rfd false.
  zbr Rfd false.
  tstep Rfd.
  zbr Rfd false.
  tstep Rfd. zsetreg (2 * lf (lens_ofs + i)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zbr Rfd false.
  tstep Rfd.
  tstep Rfd.
  tstep Rfd.
  tstep Rfd.
  tstore_arr Rfd Hcnt (lf (lens_ofs + i)).
  apply mem_arr_arr_set in Hcnt; [|rewrite cntK_len; lia].
  rewrite <- (cntK_step lf lens_ofs i) in Hcnt by lia.
  zstep Rfd.
  destruct (Z.eq_dec (i + 1) codes) as [Hend|Hmore].
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ => eapply (K R Mx) end.
    all: try first [close_pregs | zreg | assumption].
    rewrite <- Hend. exact Hcnt.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH (i + 1) Rx [] Mx MD T) end.
    all: try first [lia | assumption | close_pregs | zreg].
    intros R' M'. intros. eapply K; try eassumption.
    eapply mpost_trans; [exact HAG | assumption].
Qed.

Lemma count_phase_t : forall Rb l M MD T,
  0 < codes -> m_halted MD = None -> PR Rb l ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - 208) 208 ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 (fun _ => 0) ->
  (forall R' M',
     PR R' [] -> zget_l R' [] kA7 = sp + -136 ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -136) (sp + -104) 0 0 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp - 208) 208 ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -136) 16 cA ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99204 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99108 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T Hc0 Hh HP Wf Hlens Hcnt K.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom.
  assert (Hcnt0 : mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 (cnt 0)).
  { eapply mem_arr_ext; [exact Hcnt|]. intros j Hj. cbn beta. unfold cntK. rewrite itm_count_k_0 by lia.
    rewrite it_zero_count_spec. reflexivity. }
  clear Hcnt. zrebase.
  zbr Rfd false.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zalign.
  zstep Rfd. znot.
  zstep Rfd.
  zstep Rfd. znot.
  zstep Rfd. zsetreg (2 * codes) ltac:(symmetry; apply zext32_x2; lia).
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
    eapply (count_loop_t (Z.to_nat codes) 0 Rx [] Mx MD T) end.
  all: try first [lia | assumption | close_pregs | zreg].
  all: intros; rewrite cntA_eq in K; eapply K; eassumption.
Qed.

Definition Kmax (bitsv : Z) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kA7 = bitsv -> zget_l R' [] kT0 = mx -> zget_l R' [] kT2 = cA 15 ->
    2 <= mx -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99440 (zupd R' []) M MD) T.
Definition Klow (bitsv : Z) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kA7 = bitsv -> zget_l R' [] kT2 = cA 15 -> (forall j, 2 <= j <= 15 -> cA j = 0) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101236 (zupd R' []) M MD) T.

Lemma max_stage_2 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 2 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99428 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 2) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 2) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KL Rx) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 2) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 2); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 2); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_3 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 3 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99412 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 3) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 3) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_2 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 3) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 3); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 3); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_4 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 4 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99396 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 4) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 4) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_3 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 4) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 4); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 4); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_5 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 5 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99380 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 5) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 5) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_4 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 5) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 5); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 5); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_6 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 6 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99364 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 6) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 6) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_5 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 6) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 6); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 6); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_7 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 7 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99348 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 7) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 7) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_6 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 7) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 7); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 7); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_8 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 8 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99332 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 8) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 8) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_7 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 8) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 8); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 8); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_9 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 9 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99316 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 9) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 9) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_8 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 9) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 9); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 9); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_10 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 10 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99300 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 10) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 10) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_9 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 10) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 10); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 10); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_11 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 11 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99284 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 11) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 11) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_10 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 11) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 11); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 11); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_12 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 12 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99268 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 12) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 12) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_11 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 12) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 12); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 12); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_13 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 13 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99252 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 13) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 13) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_12 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 13) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 13); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 13); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_14 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 14 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99236 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 14) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 14) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_13 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 14) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 14); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 14); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma pb_al : pb mod 2 ^ 2 = 0 /\ 0 < pb /\ pb + 4 <= p + 144 /\ p + 136 <= pb.
Proof.
  pose proof C as C'. open_itc C'. unfold ZSEP in Hpb.
  assert (D : exists q, p = 16 * q). { apply Z.mod_divide in Hpal; [|lia_std]. destruct Hpal as [q Hq]. exists q. lia_std. }
  destruct D as [q Hq]. change (2 ^ 2) with 4.
  destruct Hpb as [E|E]; rewrite E; (split; [rewrite Hq | lia_std]).
  - replace (16 * q + 136) with ((4 * q + 34) * 4) by lia_std. apply Z_mod_mult.   (* lenbits at 136 *)
  - replace (16 * q + 140) with ((4 * q + 35) * 4) by lia_std. apply Z_mod_mult.   (* distbits at 140 *)
Qed.

Lemma max_entry_t : forall Rb l M MD T av,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = av ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M pb bits ->
  Kmax bits M MD T -> Klow bits M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99204 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T av Hh HP LA7 Hcnt HB32 KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  pose proof pb_al as (PB4 & PB0 & PB1 & PB2).
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 15) as HRk.
  zrebase.
  zbr Rfd false.
  zstep Rfd. zsetreg 0 ltac:(symmetry; apply (land_mask0 pb 2); [lia_std | exact PB4]).
  zbr Rfd false.
  tstep Rfd.
  zstep Rfd. zsetreg bits ltac:(symmetry; apply swrap32_small; lia).
  destruct (Z.eq_dec (cA 15) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_14 Rx [] M MD T bits) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. replace jj with 15 by lia. exact Z0.
  - zbr Rfd false. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 15); [lia | intros; lia | exact NZ].
    + unfold mxA. rewrite (mx_found _ 15); [lia | lia | intros; lia | exact NZ].
Qed.

#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).

Definition Kleft (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
    zget_l R' [] kT3 = cA 1 -> zget_l R' [] kT4 = (if mx =? 1 then 0 else 1) -> zget_l R' [] kT2 = cA 15 -> 1 <= mx ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99504 (zupd R' []) M MD) T.
Definition Kmax0 (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> mx = 0 -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101268 (zupd R' []) M MD) T.

Lemma mxmn_facts : 1 <= mx -> 1 <= mn <= mx /\ mx <= 15 /\ 1 <= rt <= 15 /\ mn <= rt /\
  rt = (let r := (if bits <? mx then bits else mx) in if mn <? r then r else mn).
Proof.
  intros H1. pose proof C as C'. open_itc C'. pose proof (mx_range (cntA lf lens_ofs codes)) as MR.
  pose proof (mn_range (cntA lf lens_ofs codes) mx ltac:(unfold mxA in *; lia_std)) as NR.
  unfold rootA, itm_root. unfold mnA in *. unfold mxA in *.
  set (mxv := itm_max (cntA lf lens_ofs codes)) in *. set (mnv := itm_min (cntA lf lens_ofs codes) mxv) in *.
  destruct (Z.ltb_spec mxv bits); destruct (Z.ltb_spec bits mxv); try lia_std;
    destruct (Z.ltb_spec mxv mnv); destruct (Z.ltb_spec bits mnv); destruct (Z.ltb_spec mnv mxv); destruct (Z.ltb_spec mnv bits); cbv zeta; lia_std.
Qed.

Lemma min_loop_t : forall fuel m Rb l M MD T r7,
  (Z.to_nat (mx - m) <= fuel)%nat -> 1 <= m < mx -> 2 <= mx <= 15 ->
  (forall jj, 1 <= jj < m -> cA jj = 0) ->
  m_halted MD = None -> PR Rb l ->
  zget_l Rb l kT1 = m -> zget_l Rb l kA6 = sp + -136 + 2 * m -> zget_l Rb l kT3 = mx - m ->
  zget_l Rb l kT0 = mx -> zget_l Rb l kA7 = r7 -> zget_l Rb l kT2 = cA 15 ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  (forall R', PR R' [] -> zget_l R' [] kT1 = mn -> zget_l R' [] kT0 = mx -> zget_l R' [] kA7 = r7 ->
     zget_l R' [] kT2 = cA 15 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99488 (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99460 (zupd Rb l) M MD) T.
Proof.
  induction fuel as [|fuel IH]; intros m Rb l M MD T r7 Hfuel Hm Hmx2 Hz Hh HP LT1 LA6 LT3 LT0 LA7 LT2 Hcnt K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range m) as HRm.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA m) 0) as [Z0|NZ].
  - zbr Rfd false.
    zstep Rfd. zsetreg (m + 1) ltac:(symmetry; apply swrap32_small; lia).
    zstep Rfd. zstep Rfd.
    destruct (Z.eq_dec (m + 1) mx) as [Hlast|Hmore].
    + zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try first [assumption | close_pregs | zreg].
      zregv. symmetry. unfold mnA. apply mn_all; [lia|].
      intros jj Hjj. destruct (Z.eq_dec jj m) as [->|]; [exact Z0 | apply Hz; lia].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (IH (m + 1) Rx [] M MD T r7) end.
      all: try first [lia | assumption | close_pregs | zreg].
      intros jj Hjj. destruct (Z.eq_dec jj m) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try first [assumption | close_pregs | zreg].
    zregv. symmetry. unfold mnA. apply mn_found; [lia | lia | exact Hz | exact NZ].
Qed.

Lemma rootmin_t : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bits -> zget_l Rb l kT0 = mx -> zget_l Rb l kT2 = cA 15 ->
  2 <= mx ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kleft M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99440 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T Hh HP LA7 LT0 LT2 Hmx2 Hcnt KL.
  pose proof C as C'. open_itc C'. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 1) as HR1.
  pose proof (mxmn_facts ltac:(lia)) as (MN1 & MX15 & RT & MNRT & RTEQ).
  assert (STEP : forall r7, r7 = (if bits <? mx then bits else mx) -> 1 <= r7 <= 15 ->
    forall Rx lx, m_halted MD = None -> PR Rx lx -> zget_l Rx lx kA7 = r7 -> zget_l Rx lx kT0 = mx -> zget_l Rx lx kT2 = cA 15 ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99448 (zupd Rx lx) M MD) T).
  { intros r7 Hr7 Hr7b Rx lx Hh' HP' XA7 XT0 XT2. open_pregs HP'. zkeys. zrebase.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx' _ _) _ => eapply (min_loop_t (Z.to_nat mx) 1 Rx' [] M MD T r7) end.
    all: try first [lia | assumption | close_pregs | zreg].
    intros R' HP2 YT1 YT0 YA7 YT2. open_pregs HP2. zkeys. zrebase.
    tstep Rfd.
    zstep Rfd.
    destruct (Z.ltb_spec mn r7).
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Ry _ _) _ => eapply (KL Ry) end.
      all: try first [assumption | close_pregs | zreg].
      + zregv. rewrite RTEQ. cbv zeta. subst r7. destruct (Z.ltb_spec mn (if bits <? mx then bits else mx)); lia.
      + zregv. destruct (Z.eqb_spec mx 1); lia.
    - zbr Rfd false. zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Ry _ _) _ => eapply (KL Ry) end.
      all: try first [assumption | close_pregs | zreg].
      + zregv. rewrite RTEQ. cbv zeta. subst r7. destruct (Z.ltb_spec mn (if bits <? mx then bits else mx)); lia.
      + zregv. destruct (Z.eqb_spec mx 1); lia. }
  open_pregs HP. zkeys. zrebase.
  destruct (Z.ltb_spec bits mx).
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (STEP bits _ _ Rx []) end.
    all: try first [assumption | close_pregs | zreg].
    all: destruct (Z.ltb_spec bits mx); lia.
  - zbr Rfd false. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (STEP mx _ _ Rx []) end.
    all: try first [assumption | close_pregs | zreg].
    all: destruct (Z.ltb_spec bits mx); lia.
  Unshelve. all: lia.
Qed.

Lemma maxlow_t : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bits -> zget_l Rb l kT2 = cA 15 ->
  (forall jj, 2 <= jj <= 15 -> cA jj = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kleft M MD T -> Kmax0 M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101236 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T Hh HP LA7 LT2 Hz Hcnt KL K0.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 1) as HR1. pose proof (Hz 15 ltac:(lia)) as Z15.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 1) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K0 Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold mxA. apply mx_zero. intros jj Hjj. destruct (Z.eq_dec jj 1) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    assert (MX1 : mx = 1) by (unfold mxA; apply (mx_found _ 1); [lia | intros jj Hjj; apply Hz; lia | exact NZ]).
    pose proof (mxmn_facts ltac:(lia)) as (MN1 & MX15 & RT & MNRT & RTEQ).
    zstep Rfd.
    zstep Rfd. zbool.
    zstep Rfd. zstep Rfd.
    zbr Rfd true.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KL Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. rewrite RTEQ, MX1. cbv zeta. destruct (Z.ltb_spec bits 1); destruct (Z.ltb_spec mn 1); destruct (Z.ltb_spec mn bits); lia.
    + zregv. rewrite MX1. reflexivity.
Qed.

Lemma count_phase0_t : forall Rb l M MD T av,
  codes = 0 -> m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = av ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 (fun _ => 0) -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M pb bits ->
  Kmax0 M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99108 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T av Hc0 Hh HP LA7 Hcnt HB32 K0.
  pose proof C as C'. open_itc C'. clear HtyC HtyD Hprom Hpb.
  assert (ZALL : forall jj, cA jj = 0).
  { intros jj. rewrite cntA_eq, Hc0. unfold cntK. rewrite itm_count_k_0 by lia. apply it_zero_count_spec. }
  assert (MX0 : mx = 0) by (unfold mxA; apply mx_zero; intros; apply ZALL).
  assert (Hcnt' : mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA).
  { eapply mem_arr_ext; [exact Hcnt|]. intros jj Hjj. cbn beta. symmetry. apply ZALL. }
  open_pregs HP. zkeys. zrebase.
  zbr Rfd true.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_entry_t Rx [] M MD T av) end.
  all: try first [assumption | close_pregs | zreg].
  - intros R' _ _ _ _ Hmx. exfalso. lia.
  - intros R' HP' XA7 XT2 _. eapply maxlow_t; try eassumption.
    + intros; apply ZALL.
    + intros R'' _ _ _ _ _ _ _ Hmx. exfalso. lia.
Qed.
End U7IT.

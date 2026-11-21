(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZTac ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ModelRel ItCovIface ItCovMain.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZStep.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout S_It3Run.
Export OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_It3Run.

(* THE BRIDGE TEXT of the table-builder walk text, in the form for the hand text's old path: scaffolding
   until the texts above name the list-form items. It holds no run and no step. Each hand module's name
   holds the both-image text's module of the same name and then, word for word, the hand sentences that
   other texts name, each from its list-form twin. *)
Module S_It0.
Include OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_It3Run.S_It0.
End S_It0.

Module S_It1.
Include OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_It3Run.S_It1.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ITac.
Import S_It0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Definition A_ITABLE : Z := 95716.
Section Prologue.
Context {RCa1 : RunCtx}.

Lemma it_prologue_s : forall Rb l M MD T (sp v1 v4 v5 v8 v9 v10 v11 v12 v13 v14 v15 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : Z),
  m_halted MD = None ->
  zget_l Rb l kSP = sp -> zget_l Rb l kRA = v1 -> zget_l Rb l kGP = v4 -> zget_l Rb l kTP = v5 ->
  zget_l Rb l kS0 = v8 -> zget_l Rb l kS1 = v9 ->
  zget_l Rb l kA0 = v10 -> zget_l Rb l kA1 = v11 -> zget_l Rb l kA2 = v12 -> zget_l Rb l kA3 = v13 ->
  zget_l Rb l kA4 = v14 -> zget_l Rb l kA5 = v15 ->
  zget_l Rb l kS2 = v18 -> zget_l Rb l kS3 = v19 ->
  zget_l Rb l kS4 = v20 -> zget_l Rb l kS5 = v21 -> zget_l Rb l kS6 = v22 -> zget_l Rb l kS7 = v23 ->
  zget_l Rb l kS8 = v24 -> zget_l Rb l kS9 = v25 -> zget_l Rb l kS10 = v26 -> zget_l Rb l kS11 = v27 ->
  192 <= sp -> sp <= 140737488355328 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - 192) 192 ->
  (forall R' M',
     zget_l R' [] kSP = sp + -192 -> zget_l R' [] kGP = v4 -> zget_l R' [] kTP = v5 ->
     zget_l R' [] kA0 = v10 -> zget_l R' [] kA1 = v11 -> zget_l R' [] kA2 = v12 -> zget_l R' [] kA3 = v13 ->
     zget_l R' [] kA4 = v14 -> zget_l R' [] kA5 = v15 ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -192) sp 0 0 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp - 192) 192 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -8) v1 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -16) v8 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -24) v9 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -32) v18 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -40) v19 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -48) v20 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -56) v21 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -64) v22 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -72) v23 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -80) v24 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -88) v25 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -96) v26 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -104) v27 ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -136) 16 (fun _ => 0) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 95788 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 95716 (zupd Rb l) M MD) T.
Proof using.
  intros Rb l M MD T sp v1 v4 v5 v8 v9 v10 v11 v12 v13 v14 v15 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27
         Hh LSP LRA LGP LTP L8 L9 L10 L11 L12 L13 L14 L15 L18 L19 L20 L21 L22 L23 L24 L25 L26 L27 Hsp Hsp2 Wf K.
  pose proof (it_prologue_L Rb l M MD T sp v1 v4 v5 v8 v9 v10 v11 v12 v13 v14 v15 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hh) as BL.
  lay_it3. apply BL; clear BL;
    [ split_rvals; assumption
    | exact Hsp
    | exact Hsp2
    | exact Wf
    | intros R' M' HV'; open_rvals; intros; apply K; assumption ].
Qed.
End Prologue.

Definition pregs (p lens_ofs codes pb sp vgp vtp tyv : Z) (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kSP = sp + -192 /\ zget_l R l kGP = vgp /\ zget_l R l kTP = vtp /\
  zget_l R l kA0 = tyv /\ zget_l R l kA1 = p + 168 + 2 * lens_ofs /\ zget_l R l kA2 = codes /\
  zget_l R l kA3 = p + 160 /\ zget_l R l kA4 = pb /\ zget_l R l kA5 = p + 808.

Ltac open_pregs H := unfold pregs in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in let d := fresh "LA0" in
  let e := fresh "LA1" in let f := fresh "LA2" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in dand H as (a & b & c & d & e & f & g & h & i).
Ltac close_pregs := unfold pregs; split_conj; zreg.

Section S7IT.
Context {RCa1 : RunCtx}.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cnt i := (arr_get (cntK lf lens_ofs i)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
Lemma count_phase_s : forall Rb l M MD T,
  0 < codes -> m_halted MD = None -> PR Rb l ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - 192) 192 ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 (fun _ => 0) ->
  (forall R' M',
     PR R' [] -> zget_l R' [] kA7 = sp + -136 ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -136) (sp + -104) 0 0 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp - 192) 192 ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -136) 16 cA ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 95844 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 95788 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T Hc0 Hh HP Wf Hlens Hcnt K.
  pose proof (count_phase_L ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C Rb l M MD T Hc0 Hh) as BL.
  lay_it3. apply BL; clear BL;
    [ exact HP
    | exact Wf
    | exact Hlens
    | exact Hcnt
    | exact K ].
Qed.

Definition Kmax (bitsv : Z) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kA7 = bitsv -> zget_l R' [] kT0 = mx -> zget_l R' [] kT2 = cA 15 ->
    2 <= mx -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 96124 (zupd R' []) M MD) T.
Definition Klow (bitsv : Z) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kA7 = bitsv -> (forall j, 2 <= j <= 15 -> cA j = 0) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 97432 (zupd R' []) M MD) T.
Lemma max_entry_s : forall Rb l M MD T av,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = av ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M pb bits ->
  Kmax bits M MD T -> Klow bits M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 95844 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  intros Rb l M MD T av Hh HP LA7 Hcnt HB32 KF KL.
  pose proof (max_entry_L ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C Rb l M MD T av Hh) as BL.
  lay_it3. apply BL; clear BL;
    [ exact HP
    | exact LA7
    | exact Hcnt
    | exact HB32
    | intro R'; intros; lay_it3; open_rvals; apply KF; assumption
    | exact KL ].
Qed.

#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).

Definition Kleft (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
    zget_l R' [] kT3 = (if mx =? 1 then 0 else 1) -> zget_l R' [] kT2 = cA 15 -> 1 <= mx ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 96184 (zupd R' []) M MD) T.
Definition Kmax0 (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> mx = 0 -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 97468 (zupd R' []) M MD) T.
Lemma rootmin_s : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bits -> zget_l Rb l kT0 = mx -> zget_l Rb l kT2 = cA 15 ->
  2 <= mx ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kleft M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 96124 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  intros Rb l M MD T Hh HP LA7 LT0 LT2 Hmx2 Hcnt KL.
  pose proof (rootmin_L ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C Rb l M MD T Hh) as BL.
  lay_it3. apply BL; clear BL;
    [ exact HP
    | split_rvals; assumption
    | exact Hmx2
    | exact Hcnt
    | intro R'; intros; lay_it3; open_rvals; apply KL; assumption ].
Qed.
Lemma maxlow_s : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bits ->
  (forall jj, 2 <= jj <= 15 -> cA jj = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA ->
  Kleft M MD T -> Kmax0 M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 97432 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  intros Rb l M MD T Hh HP LA7 Hz Hcnt KL K0.
  pose proof (maxlow_L ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C Rb l M MD T Hh) as BL.
  lay_it3. apply BL; clear BL;
    [ exact HP
    | exact LA7
    | exact Hz
    | exact Hcnt
    | intro R'; intros; lay_it3; open_rvals; apply KL; assumption
    | exact K0 ].
Qed.
Lemma count_phase0_s : forall Rb l M MD T av,
  codes = 0 -> m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = av ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 (fun _ => 0) -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M pb bits ->
  Kmax0 M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 95788 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  intros Rb l M MD T av Hc0 Hh HP LA7 Hcnt HB32 K0.
  pose proof (count_phase0_L ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C Rb l M MD T av Hc0 Hh) as BL.
  lay_it3. apply BL; clear BL;
    [ exact HP
    | exact LA7
    | exact Hcnt
    | exact HB32
    | exact K0 ].
Qed.
End S7IT.
End S_It1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import
  ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import Base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require Import ZTac ZArr ZArr4 IDefs ISpecs ITac.
Import S_It0. Import S_It1.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.

Definition EXA (ty : codetype) (p : Z) : Z := match ty with CODES => p + 808 | LENS => 67232 | DISTS => 67358 end.
Definition BSA (ty : codetype) (p : Z) : Z := match ty with CODES => p + 808 | LENS => 67170 | DISTS => 67294 end.
Definition EXAn (ty : codetype) (p : Z) : Z := match ty with CODES => 0 | _ => EXA ty p end.
Definition BSAn (ty : codetype) (p : Z) : Z := match ty with CODES => 0 | _ => BSA ty p end.
Lemma EXAn_ne : forall ty p, ty <> CODES -> EXAn ty p = EXA ty p. Proof. intros [] p H; [congruence|reflexivity|reflexivity]. Qed.
Lemma BSAn_ne : forall ty p, ty <> CODES -> BSAn ty p = BSA ty p. Proof. intros [] p H; [congruence|reflexivity|reflexivity]. Qed.
(* EACH KEPT DEFINITION ABOVE IS EQUAL TO ITS LIST-FORM TWIN (the both-image text's definition, where the layout's
   fields hold the two tables' addresses) *)
Lemma EXA_twin : forall ty p, EXA ty p = EXA_l ty p. Proof. intros ty p. reflexivity. Qed.
Lemma BSA_twin : forall ty p, BSA ty p = BSA_l ty p. Proof. intros ty p. reflexivity. Qed.
Lemma EXAn_twin : forall ty p, EXAn ty p = EXAn_l ty p. Proof. intros ty p. reflexivity. Qed.
Lemma BSAn_twin : forall ty p, BSAn ty p = BSAn_l ty p. Proof. intros ty p. reflexivity. Qed.

Section S7IT3.
Context {RCa1 : RunCtx}.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).

Definition pregs6 (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kSP = sp + -192 /\ zget_l R l kGP = vgp /\ zget_l R l kTP = vtp /\
  zget_l R l kA1 = p + 168 + 2 * lens_ofs /\
  zget_l R l kA3 = p + 160 /\ zget_l R l kA4 = pb /\ zget_l R l kA5 = p + 808.

Definition cregs (R : tree Z) (l : list (positive * Z)) : Prop :=
  pregs6 R l /\ zget_l R l kA7 = rt /\ zget_l R l kT0 = mx /\ zget_l R l kA2 = it_match ty /\
  zget_l R l kT3 = EXA ty p /\ zget_l R l kT4 = BSA ty p /\ zget_l R l kS2 = 1 /\ zget_l R l kS3 = -1 /\
  zget_l R l kS4 = 2 ^ rt - 1 /\ zget_l R l kS5 = sp + -136.
Definition cregsN (R : tree Z) (l : list (positive * Z)) : Prop :=
  pregs6 R l /\ zget_l R l kA7 = rt /\ zget_l R l kT0 = mx /\ zget_l R l kA0 = it_match ty /\
  zget_l R l kT3 = EXAn ty p /\ zget_l R l kT2 = BSAn ty p /\ zget_l R l kS2 = 1 /\ zget_l R l kS3 = -1 /\
  zget_l R l kS4 = 2 ^ rt - 1 /\ zget_l R l kS5 = sp + -136.
Definition cregsB (R : tree Z) (l : list (positive * Z)) : Prop :=
  pregs6 R l /\ zget_l R l kA7 = rt /\ zget_l R l kT0 = mx /\
  zget_l R l kT3 = EXAn ty p /\ zget_l R l kT2 = BSAn ty p /\ zget_l R l kS2 = 1 /\ zget_l R l kS3 = -1 /\
  zget_l R l kS4 = 2 ^ rt - 1 /\ zget_l R l kS5 = sp + -136.
Definition sregs (st : ItSt) (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kT6 = t_sym st /\ zget_l R l kT1 = t_len st /\ zget_l R l kA6 = t_drop st /\ zget_l R l kT5 = t_used st /\
  zget_l R l kS1 = t_huff st /\ zget_l R l kS0 = p + 1384 + 4 * t_next st /\ zget_l R l kA2 = 2 ^ t_curr st /\
  zget_l R l kS7 = lowS (t_low st).
Definition cmem (M : mem) : Prop :=
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - 192) 192 /\ mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 808) 288 (arr_get work1Ar) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 160) (p + 1384 + 4 * nx) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -184) (isD ty) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -176) (isL ty) /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (EXA ty p) (NE ty) (it_extra ty work1Ar) /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (BSA ty p) (NE ty) (it_base ty work1Ar).
Definition smem (st : ItSt) (M : mem) : Prop :=
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 (arr_get (t_count st)) /\
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get (t_tbl st)).
Definition spure (st : ItSt) : Prop :=
  t_work st = work1Ar /\ ZSEP (t_low st = 4294967295 \/ 0 <= t_low st < 32768) /\ ZSEP (t_drop st = 0 \/ t_drop st = rt) /\
  0 <= t_next st /\ nx <= t_next st /\
  (forall j, 0 <= j < 16 -> 0 <= arr_get (t_count st) j < 65536) /\
  (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st) j < 4294967296) /\
  arr_len (t_count st) = 16 /\ arr_len (t_tbl st) = 1444.

(* EACH KEPT DEFINITION ABOVE AND ITS LIST-FORM TWIN (the both-image text's definition at this section's
   variables) SAY THE SAME: by unfolding and splitting only *)
Lemma spure_twin : forall st, spure st <-> spure_l lf lens_ofs codes nx bits wf st.
Proof. intros st. reflexivity. Qed.
Lemma cregsN_twin : forall Rb l, cregsN Rb l <-> cregsN_l ty lf lens_ofs codes bits p pb sp vgp vtp Rb l.
Proof.
  intros Rb l. cbv beta delta [cregsN pregs6].
  cbv [cregsN_l it3b_cvals OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_c].
  split; intro H; repeat match goal with H' : _ /\ _ |- _ => destr_conj H' end; split_conj; assumption.
Qed.
Lemma sregs_twin : forall st Rb l, sregs st Rb l <-> sregs_l p st Rb l.
Proof.
  intros st Rb l. cbv beta delta [sregs].
  cbv [sregs_l it3b_svals OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_s].
  split; intro H; repeat match goal with H' : _ /\ _ |- _ => destr_conj H' end; split_conj; assumption.
Qed.
Lemma cmem_twin : forall M, cmem M <-> cmem_l ty lf lens_ofs codes nx wf p sp M.
Proof.
  intros M. cbv beta delta [cmem].
  cbv [cmem_l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.fr_it3b_sl].
  split; intro H; repeat match goal with H' : _ /\ _ |- _ => destr_conj H' end; split_conj; assumption.
Qed.
Lemma smem_twin : forall st M, smem st M <-> smem_l p sp st M.
Proof. intros st M. reflexivity. Qed.

Lemma xaddr_facts :
  ZSEP (p + 7160 <= EXA ty p \/ EXA ty p + 2 * NE ty <= p + 1384) /\
  ZSEP (p + 7160 <= BSA ty p \/ BSA ty p + 2 * NE ty <= p + 1384) /\
  0 <= EXA ty p /\ EXA ty p + 2 * NE ty <= zc /\
  0 <= BSA ty p /\ BSA ty p + 2 * NE ty <= zc /\ 0 < NE ty <= 288.
Proof using C ret sp pb wf cf bits nx codes lens_ofs lf.
  (* THE BRIDGE: the sentence above stands word for word; its list form has the layout's fields for the two
     tables' addresses *)
  exact (xaddr_facts_l ty lf lens_ofs codes nx bits cf wf p pb sp ret zc C).
Qed.

Lemma here_s : forall st Rb l M MD T,
  m_halted MD = None -> cregsN Rb l -> sregs st Rb l -> cmem M -> spure st ->
  0 <= t_sym st < 288 -> 0 <= tr_w st < 65536 ->
  (it_match ty <= tr_w st -> tr_w st - it_match ty < NE ty) ->
  (ty = CODES -> tr_w st < it_match ty) ->
  (forall R', cregsN R' [] -> sregs st R' [] -> zget_l R' [] kS10 = tr_op X st -> zget_l R' [] kS9 = tr_val X st ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 96928 (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 96852 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  (* THE BRIDGE: the statement above stands word for word (another text names it); each premise of the list-form
     lemma is the hand premise taken through its `_twin` lemma, and its continuation is the hand continuation *)
  intros st Rb l M MD T Hh HC HS HM HU Hsym Hw Hwm HcB K.
  apply (here_l ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C st Rb l M MD T Hh
           (proj1 (cregsN_twin Rb l) HC) (proj1 (sregs_twin st Rb l) HS) (proj1 (cmem_twin M) HM)
           (proj1 (spure_twin st) HU) Hsym Hw Hwm HcB).
  intros R' HC' HS' HOV.
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_ov] in HOV.
  exact (K R' (proj2 (cregsN_twin R' []) HC') (proj2 (sregs_twin st R' []) HS') (proj1 HOV) (proj2 HOV)).
Qed.

Lemma fill_s : forall st Rb l M MD T,
  m_halted MD = None -> cregsN Rb l -> sregs st Rb l ->
  zget_l Rb l kS10 = tr_op X st -> zget_l Rb l kS9 = tr_val X st ->
  spure st -> it_trip_ok X 288 320 1444 st = true ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get (t_tbl st)) ->
  (forall R' M', cregsN R' [] -> sregs st R' [] -> zget_l R' [] kS8 = tr_hb st ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (p + 1384) (p + 7160) 0 0 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 ->
     mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 (arr_get (tr_tbl1 X st)) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 96988 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 96928 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  (* THE BRIDGE: the statement above stands word for word (another text names it); each premise of the list-form
     lemma is the hand premise taken through its `_twin` lemma (the two register facts are the meaning of the
     layout's two-register list), and its continuation is the hand continuation *)
  intros st Rb l M MD T Hh HC HS LS10 LS9 HU TOK Wp Htbl K.
  apply (fill_l ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C st Rb l M MD T Hh
           (proj1 (cregsN_twin Rb l) HC) (proj1 (sregs_twin st Rb l) HS) (conj LS10 LS9)
           (proj1 (spure_twin st) HU) TOK Wp Htbl).
  intros R' M' HC' HS' H8 HP HW HT.
  exact (K R' M' (proj2 (cregsN_twin R' []) HC') (proj2 (sregs_twin st R' []) HS') H8 HP HW HT).
Qed.

Definition Kst1 (pc : Z) (brk : bool) (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R' M', cregsN R' [] -> sregs (tr_st1 X st) R' [] -> zget_l R' [] kS8 = tr_hb st ->
    mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -136) (sp + -104) 0 0 -> cmem M' -> smem (tr_st1 X st) M' ->
    tr_brk X st = brk ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd R' []) M' MD) T.
Lemma Kst1_twin : forall pc brk st M MD T,
  Kst1 pc brk st M MD T <-> Kst1_l ty lf lens_ofs codes nx bits wf p pb sp vgp vtp pc brk st M MD T.
Proof.
  intros pc brk st M MD T. cbv beta delta [Kst1 cregsN pregs6 sregs cmem smem].
  cbv [Kst1_l cregsN_l sregs_l cmem_l smem_l it3b_cvals it3b_svals
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant nth fst snd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_c OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_s OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_hb
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.fr_it3b_sl].
  split; intro K; intros; repeat match goal with H' : _ /\ _ |- _ => destr_conj H' end; apply K; split_conj; assumption.
Qed.

Lemma count_s : forall st Rb l M MD T,
  m_halted MD = None -> cregsN Rb l -> sregs st Rb l -> zget_l Rb l kS8 = tr_hb st ->
  cmem M -> spure st -> it_trip_ok X 288 320 1444 st = true ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 (arr_get (t_count st)) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get (tr_tbl1 X st)) ->
  Kst1 97116 false st M MD T -> Kst1 97308 true st M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 96988 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  (* THE BRIDGE: the statement above stands word for word (another text names it); each premise of the list-form
     lemma is the hand premise taken through its `_twin` lemma (the one register fact is the meaning of the
     layout's one-register list); each of its two continuations is the hand continuation of the same place *)
  intros st Rb l M MD T Hh HC HS LS8 HM HU TOK Hcnt Htbl KS KB.
  exact (count_l ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C st Rb l M MD T Hh
           (proj1 (cregsN_twin Rb l) HC) (proj1 (sregs_twin st Rb l) HS) LS8
           (proj1 (cmem_twin M) HM) (proj1 (spure_twin st) HU) TOK Hcnt Htbl
           (proj1 (Kst1_twin _ _ st M MD T) KS) (proj1 (Kst1_twin _ _ st M MD T) KB)).
Qed.
End S7IT3.

Ltac open_pregs6 H := unfold pregs6 in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in
  let e := fresh "LA1" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in dand H as (a & b & c & e & g & h & i).
Ltac close_pregs6 := unfold pregs6; split_conj; zreg.
Ltac open_cregs H :=
  unfold cregsN in H;
  let hp := fresh "HP" in let a := fresh "LA7" in let b := fresh "LT0" in let c := fresh "LA2" in
  let d := fresh "LT3" in let e := fresh "LT4" in let f := fresh "LS2" in let g := fresh "LS3" in
  let h := fresh "LS4" in let i := fresh "LS5" in
  dand H as (hp & a & b & c & d & e & f & g & h & i); open_pregs6 hp.
Ltac open_sregs H :=
  unfold sregs in H;
  let a := fresh "LT6" in let b := fresh "LT1" in let c := fresh "LA6" in let d := fresh "LT5" in
  let e := fresh "LS1" in let f := fresh "LS0" in let g := fresh "LT2" in let h := fresh "LS7" in
  dand H as (a & b & c & d & e & f & g & h).
Ltac open_cmem H :=
  unfold cmem in H;
  let a := fresh "Wf" in let b := fresh "Wp" in let c := fresh "Hlens" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f := fresh "HslD" in let g := fresh "HslL" in let h := fresh "Hext" in let i := fresh "Hbase" in
  dand H as (a & b & c & d & e & f & g & h & i).
Ltac open_smem H :=
  unfold smem in H; let a := fresh "Hcnt" in let b := fresh "Htbl" in dand H as (a & b).
Ltac open_spure H :=
  unfold spure in H;
  let a := fresh "WK" in let b := fresh "LOWR" in let b2 := fresh "DROPR" in let c := fresh "NX0" in let d := fresh "NX1" in
  let e := fresh "HCr" in let f := fresh "HTr" in let g := fresh "CL" in let h := fresh "TL" in
  dand H as (a & b & b2 & c & d & e & f & g & h).
Ltac open_cregsB H :=
  unfold cregsB in H;
  let hp := fresh "HP" in let a := fresh "LA7" in let b := fresh "LT0" in
  let d := fresh "LT3" in let e := fresh "LT4" in let f := fresh "LS2" in let g := fresh "LS3" in
  let h := fresh "LS4" in let i := fresh "LS5" in
  dand H as (hp & a & b & d & e & f & g & h & i); open_pregs6 hp.
Ltac close_cregsB := unfold cregsB; split_conj; try close_pregs6; zreg.
Ltac close_cregs := unfold cregsN; split_conj; try close_pregs6; zreg.
Ltac close_sregs := unfold sregs; split_conj; zreg.
Ltac close_cmem := unfold cmem; split_conj; assumption.
Ltac close_smem := unfold smem; split_conj; assumption.
Ltac close_sregs1 EL := unfold sregs; cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]; rewrite ?EL; split_conj; zreg.
Ltac kauto := first
  [ assumption
  | lazymatch goal with
    | |- cregsN _ _ _ _ _ _ _ _ _ _ _ _ => close_cregs
    | |- cregsB _ _ _ _ _ _ _ _ _ _ _ _ => close_cregsB
    | |- sregs _ (tr_st1 _ _) _ _ => fail
    | |- sregs _ _ _ _ => close_sregs
    | |- pregs6 _ _ _ _ _ _ _ _ => close_pregs6
    | |- pregs _ _ _ _ _ _ _ _ _ _ => close_pregs
    | |- zget_l _ _ _ = _ => zreg
    | |- zget _ _ = _ => zreg
    | |- m_halted _ = _ => assumption
    end ].
Ltac trip_facts TOK :=
  pose proof (trip_ok_facts _ 288 320 1444 _ TOK) as (Fsym & Flen & Fdrop & Fcurr & Fhuff & Fnext & Fused & Fmin & Fw & Fwm & Ffit & Flook & Fcont);
  cbn [x_ty x_max x_lens x_lens_ofs x_table x_root x_mask itm_ctx] in Fsym, Flen, Fdrop, Fcurr, Fhuff, Fnext, Fused, Fmin, Fw, Fwm, Ffit, Flook, Fcont;
  rewrite <- ?NE_ext_len in Fwm; rewrite ?Z.shiftl_1_l in Ffit; box Fwm; box Flook; box Fcont.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.EvalMemo"; "mtab"; "mtab_ok"; "evalm"; "eval_f"; "mlook"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "prod"; "fst"; "pair"; "Some"; "cons"; "nil"; "option"; "snd"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
Import ListNotations.

Definition mtab := list (sv * word).
Fixpoint mlook (e : sv) (t : mtab) : option word :=
  match t with
  | [] => None
  | (s, v) :: r => if sv_eqb s e then Some v else mlook e r
  end.

Fixpoint evalm (rho : valuation) (e : sv) (t : mtab) : word * mtab :=
  match e with
  | SLit z => (Z_to_bv 64 z, t)
  | SVar i => (rw rho i, t)
  | SAlu op a b =>
      match mlook e t with
      | Some v => (v, t)
      | None => let '(va, t1) := evalm rho a t in let '(vb, t2) := evalm rho b t1 in
                let v := alu64 op va vb in (v, (e, v) :: t2)
      end
  | SAluW op a b =>
      match mlook e t with
      | Some v => (v, t)
      | None => let '(va, t1) := evalm rho a t in let '(vb, t2) := evalm rho b t1 in
                let v := sext 64 (alu32 op (low32 va) (low32 vb)) in (v, (e, v) :: t2)
      end
  | SMd op a b =>
      match mlook e t with
      | Some v => (v, t)
      | None => let '(va, t1) := evalm rho a t in let '(vb, t2) := evalm rho b t1 in
                let v := mul_div op va vb in (v, (e, v) :: t2)
      end
  | SMdW op a b =>
      match mlook e t with
      | Some v => (v, t)
      | None => let '(va, t1) := evalm rho a t in let '(vb, t2) := evalm rho b t1 in
                let v := sext 64 (mul_div op (low32 va) (low32 vb)) in (v, (e, v) :: t2)
      end
  | SExt sgn w a =>
      match mlook e t with
      | Some v => (v, t)
      | None => let '(va, t1) := evalm rho a t in
                let v := ext_low sgn w va in (v, (e, v) :: t1)
      end
  | SLBytes l i k =>
      let '(vi, t1) := evalm rho i t in (le_bytes_to_word (sublist (bv_unsigned vi) k (rl rho l)), t1)
  end.

Definition mtab_ok (rho : valuation) (t : mtab) : Prop := ltac2:(tb__ "0|1|
S0S8Q40A1M0S13SbS0G0A2SdS0G0R2R1A4Vt;A3S9G0R2S1Vrho;R3A2A3F_;Fv;Fs;").

Lemma mlook_ok : ltac2:(tb__ "0|1|
S2S0S3S8Q40A1M0S4R4R2A2S9S11G0A1S7R4R3A2SeG0R2A2A3S9G0R3S1R6R5A2A3F_;F_;Fv;Ft;Fe;Frho;").
Proof.
  intros rho e t. induction t as [|[s w] r IH]; intros v Ht H; cbn [mlook] in H; [discriminate|].
  destruct (sv_eqb s e) eqn:E.
  - injection H as <-. apply sv_eqb_sound in E. subst s. apply Ht. left. reflexivity.
  - apply IH; [|exact H]. intros s' v' Hin. apply Ht. right. exact Hin.
Qed.

Lemma mtab_ok_cons : ltac2:(tb__ "0|1|
S2S3S0S4R3R2A2S4R4SfSbS0S8Q40A1M0A2SdS0G0R2S1R4R2A2A4R3A3A2F_;Fe;Ft;Frho;").
Proof. intros rho t e Ht s v [H|H]; [injection H as <- <-; reflexivity | apply Ht; exact H]. Qed.

Theorem evalm_ok : ltac2:(tb__ "0|2|
S2S0S3S4R3R1A2SaS9S8Q40A1M0ScG0S3S5R4R3R2A3M1A3S1R4R3A2A3S4R4S12G0S3G1A3A2A2F_;Ft;Fe;Frho;").
Proof.
  intros rho. induction e as [z|i|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sgn w a IHa|l i IHi k];
    intros t Ht; cbn [evalm eval].
  - split; [reflexivity | exact Ht].
  - split; [reflexivity | exact Ht].
  - destruct (mlook (SAlu op a b) t) as [v|] eqn:L; [split; [exact (mlook_ok rho _ t v Ht L) | exact Ht]|].
    destruct (IHa t Ht) as [Ea Ha]. destruct (evalm rho a t) as [va t1]. cbn [fst snd] in Ea, Ha. subst va.
    destruct (IHb t1 Ha) as [Eb Hb]. destruct (evalm rho b t1) as [vb t2]. cbn [fst snd] in Eb, Hb. subst vb.
    cbn [fst snd]. split; [reflexivity | exact (mtab_ok_cons rho t2 (SAlu op a b) Hb)].
  - destruct (mlook (SAluW op a b) t) as [v|] eqn:L; [split; [exact (mlook_ok rho _ t v Ht L) | exact Ht]|].
    destruct (IHa t Ht) as [Ea Ha]. destruct (evalm rho a t) as [va t1]. cbn [fst snd] in Ea, Ha. subst va.
    destruct (IHb t1 Ha) as [Eb Hb]. destruct (evalm rho b t1) as [vb t2]. cbn [fst snd] in Eb, Hb. subst vb.
    cbn [fst snd]. split; [reflexivity | exact (mtab_ok_cons rho t2 (SAluW op a b) Hb)].
  - destruct (mlook (SMd op a b) t) as [v|] eqn:L; [split; [exact (mlook_ok rho _ t v Ht L) | exact Ht]|].
    destruct (IHa t Ht) as [Ea Ha]. destruct (evalm rho a t) as [va t1]. cbn [fst snd] in Ea, Ha. subst va.
    destruct (IHb t1 Ha) as [Eb Hb]. destruct (evalm rho b t1) as [vb t2]. cbn [fst snd] in Eb, Hb. subst vb.
    cbn [fst snd]. split; [reflexivity | exact (mtab_ok_cons rho t2 (SMd op a b) Hb)].
  - destruct (mlook (SMdW op a b) t) as [v|] eqn:L; [split; [exact (mlook_ok rho _ t v Ht L) | exact Ht]|].
    destruct (IHa t Ht) as [Ea Ha]. destruct (evalm rho a t) as [va t1]. cbn [fst snd] in Ea, Ha. subst va.
    destruct (IHb t1 Ha) as [Eb Hb]. destruct (evalm rho b t1) as [vb t2]. cbn [fst snd] in Eb, Hb. subst vb.
    cbn [fst snd]. split; [reflexivity | exact (mtab_ok_cons rho t2 (SMdW op a b) Hb)].
  - destruct (mlook (SExt sgn w a) t) as [v|] eqn:L; [split; [exact (mlook_ok rho _ t v Ht L) | exact Ht]|].
    destruct (IHa t Ht) as [Ea Ha]. destruct (evalm rho a t) as [va t1]. cbn [fst snd] in Ea, Ha. subst va.
    cbn [fst snd]. split; [reflexivity | exact (mtab_ok_cons rho t1 (SExt sgn w a) Ha)].
  - destruct (IHi t Ht) as [Ei Hi]. destruct (evalm rho i t) as [vi t1]. cbn [fst snd] in Ei, Hi. subst vi.
    cbn [fst snd]. split; [reflexivity | exact Hi].
Qed.

Definition eval_f (rho : valuation) (e : sv) : word := ltac2:(tb__ "0|1|
ScS8Q40A1M0S3S5Vrho;Ve;S10SbS0G0A2A1A3A3").
Theorem eval_f_eq : ltac2:(tb__ "0|0|
S2S0S9S8Q40A1S6R2R1A2S1R2R1A2A3Fe;Frho;").
Proof. intros rho e. unfold eval_f. apply evalm_ok. intros s v []. Qed.

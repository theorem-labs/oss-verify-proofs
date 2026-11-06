(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk SeqExec Hoare StreamSim
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section FPX. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

Fixpoint itab_of_ranges (rs : list (Z * nat)) (t : itab) : itab :=
  match rs with
  | [] => t
  | (lo, n) :: rs' => itab_of_ranges rs' (mk_itab_fuel segs n lo t)
  end.
Lemma itab_of_ranges_sound : forall rs t, itab_sound segs t -> itab_sound segs (itab_of_ranges rs t).
Proof. induction rs as [|[lo n] rs IH]; intros t Ht; cbn; [exact Ht|]. apply IH. apply mk_itab_fuel_sound. exact Ht. Qed.
Lemma itab_leaf_sound : itab_sound segs PTLeaf.
Proof. intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate. Qed.
Definition itab_of (rs : list (Z * nat)) : itab := itab_of_ranges rs PTLeaf.
Lemma itab_of_sound : forall rs, itab_sound segs (itab_of rs).
Proof. intros rs. apply itab_of_ranges_sound, itab_leaf_sound. Qed.
End WithSegs.

(* [comment removed for export] *)
Definition EnvR (R : bvmap 5 word) : env := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => []).
Lemma EnvR_regs_ok : forall R, regs_ok (EnvR R) sr_id R.
Proof. intros R. apply regs_ok_id. Qed.
Lemma EnvR_ev : forall R n, (n < 32)%nat -> ev (EnvR R) n = getr R (Z_to_bv 5 (Z.of_nat n)).
Proof. intros R n Hn. cbn [ev EnvR]. unfold reg_ev. apply Nat.ltb_lt in Hn. rewrite Hn. reflexivity. Qed.

Lemma u64_of_Z : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.

(* [comment removed for export] *)
Definition pres_check (sr' : list expr) (exc : list nat) : bool :=
  forallb (fun i => expr_eqb (nth i sr' (ELit 0)) (EVar i) || existsb (Nat.eqb i) exc)%bool (seq 0 32).

Lemma pres_check_sound : forall sr' exc E E' R R' b,
  pres_check sr' exc = true ->
  regs_ok E sr_id R -> regs_ok E' sr' R' -> env_agree b E E' -> (32 <= b)%nat ->
  forall r : reg, existsb (Nat.eqb (ridx r)) exc = false -> getr R' r = getr R r.
Proof.
  intros sr' exc E E' R R' b Hc HR HR' Hag Hb r Hr.
  rewrite (HR' r), (HR r). unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
  pose proof (ridx_range r) as Hlt.
  unfold pres_check in Hc. rewrite forallb_forall in Hc.
  specialize (Hc (ridx r)). rewrite Hr, orb_false_r in Hc.
  assert (Hin : In (ridx r) (seq 0 32)) by (apply in_seq; lia).
  specialize (Hc Hin). apply expr_eqb_eq in Hc. rewrite Hc.
  assert (Hid : nth (ridx r) sr_id (ELit 0) = EVar (ridx r)).
  { set (n := ridx r) in *. clearbody n. do 32 (destruct n as [|n]; [reflexivity|]). exfalso; lia. }
  rewrite Hid. cbn [edenot]. symmetry. apply (proj1 Hag). lia.
Qed.
End FPX.

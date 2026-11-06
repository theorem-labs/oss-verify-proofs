(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare BnModel BnMem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Export BnDefs.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsZX AsZXTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ZXA BM.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma reg_kept : forall regs vals rs regs' (r : reg),
  regs_ok (Eof regs vals) rs regs' -> zx_eqb (sr_get rs r) (ZV (ridx r)) = true ->
  getr regs' r = getr regs r.
Proof.
  intros regs vals rs regs' r Hr He. apply zx_eqb_eq in He.
  rewrite (Hr r), He. unfold wd. cbn [ev]. unfold Eof.
  pose proof (ridx_range r) as Hlt.
  replace (Nat.ltb (ridx r) 32) with true by (symmetry; apply Nat.ltb_lt; exact Hlt).
  rewrite ridx_roundtrip. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma reg_val : forall E rs regs' (r : reg) e,
  regs_ok E rs regs' -> sr_get rs r = e -> getr regs' r = Z_to_bv 64 (ev E e).
Proof. intros E rs regs' r e Hr <-. apply Hr. Qed.

(* [comment removed for export] *)
Lemma keeps_of_zx : forall l E rs0 regs rs regs',
  regs_ok E rs0 regs -> regs_ok E rs regs' ->
  forallb (fun r => zx_eqb (sr_get rs (Z_to_bv 5 r)) (sr_get rs0 (Z_to_bv 5 r))) l = true ->
  keeps l regs regs'.
Proof.
  intros l E rs0 regs rs regs' H0 H1 Hall r Hin.
  pose proof (proj1 (forallb_forall _ l) Hall r Hin) as He. apply zx_eqb_eq in He.
  rewrite (H1 (Z_to_bv 5 r)), (H0 (Z_to_bv 5 r)), He. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma reg_pin_of : forall E rs regs' (r : reg) e v,
  regs_ok E rs regs' -> sr_get rs r = e -> Z_to_bv 64 (ev E e) = v -> getr regs' r = v.
Proof. intros E rs regs' r e v Hr <- <-. apply Hr. Qed.
End WithFP.

(* [comment removed for export] *)
Ltac kc1 H := split; [apply (kc_intro _ _ _ _ _ _ _ _ _ H); zx_cbn; unfold zlen in *; zwidth; lia |].
(* [comment removed for export] *)
Ltac kw1 H :=
  lazymatch type of H with
  | RiscvSemantics.store_ok ?segs ?m (Z_to_bv 64 ?base) ?N = true =>
      lazymatch goal with
      | |- (0 <= ZXA.ev ?E ?b + ?lo /\ _) /\ _ =>
          split; [apply (kw_intro' segs E m b lo _ base N H); zx_cbn; zwidth; lia |]
      end
  end.

Section KwDef.
Context {fx : FPState}.
(* [comment removed for export] *)
Lemma kw_of_def : forall segs E (m : word -> option byte) b lo hi (base len : Z),
  (forall i, 0 <= i < len -> exists v, m (Z_to_bv 64 (base + i)) = Some v) ->
  (0 <= base /\ base + len <= M64 /\ base <= ev E b + lo /\ ev E b + hi <= base + len) ->
  0 <= ev E b + lo /\ ev E b + hi <= M64 /\
  forall k n, lo <= k -> k + Z.of_nat n <= hi -> RiscvSemantics.store_ok segs m (addr E b k) n = true.
Proof.
  intros segs E m b lo hi base len Hdef (H1 & H2 & H3 & H4). split; [lia|]. split; [lia|].
  intros k n Hk Hn. unfold addr.
  assert (GEN : forall j a, 0 <= a -> base <= a -> a + Z.of_nat j <= base + len ->
            RiscvSemantics.store_ok segs m (Z_to_bv 64 a) j = true).
  { induction j as [|j IH]; intros a Ha Hlo Hhi; [reflexivity|].
    cbn [RiscvSemantics.store_ok]. unfold wview.
    destruct (Hdef (a - base) ltac:(lia)) as [v Hv]. replace (base + (a - base)) with a in Hv by lia. rewrite Hv.
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
    2:{ symmetry. rewrite <- (Z_to_bv_bv_unsigned 64 (Z_to_bv 64 a + 1)). apply Z2bv_eqm.
        rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
        change (bv_unsigned (1%bv : word)) with 1. rewrite u_Z2bv64.
        rewrite Z.mod_mod by lia. rewrite Zplus_mod_idemp_l. reflexivity. }
    apply IH; lia. }
  apply GEN; lia.
Qed.
End KwDef.

(* [comment removed for export] *)
Ltac kwd H :=
  lazymatch goal with
  | |- (0 <= ZXA.ev ?E ?b + ?lo /\ _) /\ _ =>
      split; [apply (kw_of_def _ E _ b lo _ _ _ H); zx_cbn; zwidth; lia |]
  end.

(* [comment removed for export] *)
Tactic Notation "zx_reg" constr(ZR) constr(r) "as" ident(H) :=
  pose proof (ZR r) as H;
  lazymatch type of H with
  | getr _ _ = ZXA.wd _ (ZXA.sr_get ?rs ?rr) =>
      let e := eval vm_compute in (ZXA.sr_get rs rr) in change (ZXA.sr_get rs rr) with e in H
  end;
  zx_cbn_in H.

(* [comment removed for export] *)
Ltac zx_regv ZR :=
  lazymatch goal with |- getr _ _ = _ => idtac end;
  etransitivity; [apply ZR |];
  lazymatch goal with
  | |- ZXA.wd _ (ZXA.sr_get ?rs ?rr) = _ =>
      let e := eval vm_compute in (ZXA.sr_get rs rr) in change (ZXA.sr_get rs rr) with e
  end;
  unfold ZXA.wd; zx_cbn; first [reflexivity | f_equal; lia | rewrite Z_to_bv_bv_unsigned; first [reflexivity | assumption] | idtac].

(* [comment removed for export] *)
Ltac zx_use2 ZXB tacP tacV tacK tacW tacS :=
  lazymatch type of ZXB with
  | ?P1 -> ?P2 -> ?P3 -> ?P4 -> ?P5 -> _ =>
      let H1 := fresh "OP" in let H2 := fresh "OV" in let H3 := fresh "OK" in
      let H4 := fresh "OW" in let H5 := fresh "OS" in
      assert (H1 : P1); [clear ZXB; zx_cbn; tacP|
      assert (H2 : P2); [clear ZXB H1; zx_cbn; tacV|
      assert (H3 : P3); [clear ZXB H1 H2; cbn [kn_conj ZXA.c_kn]; tacK|
      assert (H4 : P4); [clear ZXB H1 H2 H3; cbn [kw_conj ZXA.c_kw]; tacW|
      assert (H5 : P5); [clear ZXB H1 H2 H3 H4; zx_cbn; tacS|
      specialize (ZXB H1 H2 H3 H4 H5); clear H1 H2 H3 H4 H5;
      let regs' := fresh "regs" in let ze := fresh "ZE" in let zr := fresh "ZR" in
      let zf := fresh "ZF" in let zm := fresh "ZM" in
      destruct ZXB as (ze & regs' & zr & zf & zm);
      zx_cbn_in zm; zx_cbn_in zf; cbn [ZXA.z_rs] in zr ]]]]]
  end.

(* [comment removed for export] *)
Ltac in_list := cbn; repeat (first [left; reflexivity | right]).

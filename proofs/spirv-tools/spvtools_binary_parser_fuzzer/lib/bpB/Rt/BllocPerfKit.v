(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics BllocWalkKit BW_LargeAlloc1 BW_PoisonRemap1 BllocTacX.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition out_img (W : list ivl) : Prop := Forall (fun r : ivl => snd r <= 65536 \/ 7241728 <= fst r) W.

Lemma out_img_nil : out_img []. Proof. constructor. Qed.
Lemma out_img_cons : forall lo hi W, (hi <= 65536 \/ 7241728 <= lo) -> out_img W -> out_img ((lo, hi) :: W).
Proof. intros lo hi W H HW. constructor; [exact H| exact HW]. Qed.

Lemma out_img_disjoint : forall W a n, out_img W -> 65536 <= a -> a + n <= 7241728 -> 0 <= n -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Ha Hn Hn0; [exact I|].
  inversion HW as [|r W' Hr HW']; subst. cbn [fst snd] in Hr. cbn [disjoint_from]. split; [| apply IH; assumption].
  destruct Hr as [Hr|Hr]; [right| left]; lia.
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Lemma renv_transport_img : forall g b m m' W,
    RENV g b m -> munch W m m' -> wmono asegs m m' -> out_img W -> RENV g b m'.
  Proof.
    intros g b m m' W E MU WM HW.
    apply (renv_transport g b m m' W E MU WM); apply (out_img_disjoint W _ _ HW); lia.
  Qed.

  Lemma senv_transport_img : forall tp TSD CTX TH m m' W,
    SENV tp TSD CTX TH m -> munch W m m' -> wmono asegs m m' -> out_img W ->
    65536 <= bv_unsigned tp + -88 -> bv_unsigned tp + -88 + 8 <= 7241728 ->
    65536 <= TSD -> TSD + 8 <= 7241728 ->
    disjoint_from W (CTX + 152) 8 ->
    SENV tp TSD CTX TH m'.
  Proof.
    intros tp TSD CTX TH m m' W E MU WM HW T1 T2 D1 D2 DC.
    apply (senv_transport tp TSD CTX TH m m' W E MU WM); try exact DC; apply (out_img_disjoint W _ _ HW); lia.
  Qed.
End HCW.

Ltac out_img_tac tac :=
  repeat first [ apply out_img_nil | apply out_img_cons; [ tac | ] ].

Ltac renv_img_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with BW_PoisonRemap1.RENV ?g ?b m =>
      assert (E' : BW_PoisonRemap1.RENV g b m');
      [ apply (renv_transport_img g b m m' W E MU WM); out_img_tac ltac:(cbn [fst snd]; region_decide) | ]
    end end.
Ltac senv_img_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with SENV ?tp ?TSD ?CTX ?TH m =>
      assert (E' : SENV tp TSD CTX TH m');
      [ apply (senv_transport_img tp TSD CTX TH m m' W E MU WM);
        [ out_img_tac ltac:(cbn [fst snd]; region_decide) | .. ]; cbn [disjoint_from]; region_decide | ]
    end end.

Definition parked (P : Prop) : Prop := P.
Lemma park : forall P : Prop, P -> parked P. Proof. intros P p. exact p. Qed.
Lemma unpark : forall P : Prop, parked P -> P. Proof. intros P p. exact p. Qed.
Global Opaque parked.

Ltac park_mem m keep :=
  repeat match goal with
  | H : rw_cells _ m _ _ |- _ => tryif constr_eq H keep then fail else apply park in H
  | H : ro_cells _ m _ _ |- _ => apply park in H
  | H : stk _ m _ _ |- _ => tryif constr_eq H keep then fail else apply park in H
  | H : u8arr _ m _ _ |- _ => apply park in H
  | H : u32arr _ m _ _ |- _ => apply park in H
  | H : u64arr _ m _ _ |- _ => apply park in H
  | H : u8ro _ m _ _ |- _ => apply park in H
  | H : bytes_at _ m _ _ |- _ => apply park in H
  | H : wr_at _ m _ _ |- _ => apply park in H
  end.
Ltac unpark_all := repeat match goal with H : parked _ |- _ => apply unpark in H end.

Ltac spill_block FR lo hi tac :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m0 _) =>
    let MUP := fresh "MUP" in let WMP := fresh "WMP" in
    pose proof (munch_refl [(lo, hi)] m0) as MUP; pose proof (wmono_refl segs m0) as WMP;
    park_mem m0 FR;
    tac;
    unpark_all;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      transport_after_call segs m0 m1 MUP WMP; clear MUP WMP
    end
  end.

Ltac spill_frame tac :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
    match goal with FRx : rw_cells _ m0 ?A [CB ?n _] |- _ =>
      let hi := lazymatch A with
                | (?b + ?k)%Z => let k' := eval vm_compute in (k + Z.of_nat n)%Z in constr:((b + k')%Z)
                | _ => constr:((A + Z.of_nat n)%Z)
                end in
      spill_block FRx A hi tac
    end
  end.

Ltac st1f := step; fix_lit_store; try (rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned by lia).

Ltac join_open JT JOIN := evar (JT : Prop); cut JT; [ intros JOIN | ].
Ltac join_here JT JOIN :=
  lazymatch goal with |- ?G => let e := eval unfold JT in JT in unify e G end; unfold JT in JOIN; exact JOIN.
Ltac join_here1 JT JOIN r :=
  lazymatch goal with |- evt ?s ?P (MS ?R ?F ?pc ?fc ?rv ?mm ?ro) =>
    let e := eval unfold JT in JT in
    unify e (forall x : word, evt s P (MS (bvmap_set r x R) F pc fc rv mm ro)) end;
  unfold JT in JOIN; eapply JOIN.
Ltac join_here3 JT JOIN r1 r2 r3 :=
  lazymatch goal with |- evt ?s ?P (MS ?R ?F ?pc ?fc ?rv ?mm ?ro) =>
    let e := eval unfold JT in JT in
    unify e (forall x y z : word, evt s P (MS (bvmap_set r1 x (bvmap_set r2 y (bvmap_set r3 z R))) F pc fc rv mm ro)) end;
  unfold JT in JOIN; eapply JOIN.
Ltac join_again JT JOIN := unfold JT in JOIN; first [ exact JOIN | eapply JOIN ].

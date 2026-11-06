(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim SymExec SymExec2X SymExec2SoundX SymRunX SymPackX RefMemcpyLib AgentLib.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells CellsX TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AXL_bridge.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AXL_snpDisc AXL_snpRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

(* [comment removed for export] *)
Lemma kword_of_bytes : forall E m a bs (o : nat) (w : nat) x v,
  bytes_at bsegs m a bs -> (o + w <= length bs)%nat -> (1 <= w <= 8)%nat ->
  x = a + Z.of_nat o -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  firstn w (skipn o bs) = word_to_le_bytes w (Z_to_bv 64 v) ->
  kentry_ok RSEGS E m (KWord (SA (ELit 0) x) w (ELit v)).
Proof.
  intros E m a bs o w x v B Hl Hw -> Ha Hs Hv.
  eapply (kword_intro RSEGS E m (ELit 0) (Z_to_bv 64 0) (a + Z.of_nat o) w (ELit v) (Z_to_bv 64 v)); [reflexivity | reflexivity | lia | lia | | | ].
  - change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
  - change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
  - change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_l. rewrite <- Hv. rewrite <- rdn_same, <- wa_eq.
    exact (Mem.bytes_at_rdn bsegs m a bs o w B Hl).
Qed.

Lemma Forall_flat_map_intro : forall {A B} (P : B -> Prop) (f : A -> list B) l,
  Forall (fun a => Forall P (f a)) l -> Forall P (flat_map f l).
Proof. intros A B P f l H. induction H as [|a l Ha _ IH]; cbn [flat_map]; [constructor | apply Forall_app; split; assumption]. Qed.

Ltac zc := vm_compute; first [reflexivity | discriminate | lia | (intro; discriminate)].
Ltac kw B :=
  lazymatch goal with
  | |- kentry_ok _ ?E ?m (KWord (SA (ELit 0) ?x) ?w (ELit ?v)) =>
      lazymatch type of B with
      | bytes_at _ _ ?a ?bs =>
          let o := eval vm_compute in (Z.to_nat (x - a)) in
          apply (kword_of_bytes E m a bs o w x v B); [zc | lia | zc | zc | zc | vm_compute; reflexivity]
      end
  end.
Ltac grp RC :=
  cbn [fst snd kn_of_cells] in *; destruct RC as [[_ B] _];
  repeat (apply Forall_cons; [ kw B |]); apply Forall_nil.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma cells_know : forall m, ACONST m -> forall E, know_ok RSEGS E m CELLS.
Proof.
  intros m AC E.
  assert (H : flat_map (fun ac : Z * list cell => kn_of_cells (fst ac) (snd ac)) aconst_cells = CELLS) by (vm_compute; reflexivity).
  destruct AC as [C _].
  unfold know_ok. rewrite <- H. apply Forall_flat_map_intro.
  unfold aconst_cells in C |- *.
  repeat (apply Forall_cons_iff in C; let RC := fresh "RC" in destruct C as [RC C];
          apply Forall_cons; [grp RC |]).
  apply Forall_nil.
Qed.

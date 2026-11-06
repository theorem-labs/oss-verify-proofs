(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem State.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem St.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module Ops.

Record opcomp := OpComp {
  oc_holds : list word -> (word -> option byte) -> Model -> Prop;
  oc_fp : list word -> list (Z * Z);
  oc_frame : forall args m m' model,
      (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (oc_fp args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
      (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
      oc_holds args m model -> oc_holds args m' model
}.

Definition oc_true : opcomp := OpComp (fun _ _ _ => True) (fun _ => []) (fun _ _ _ _ _ _ H => H).

Definition oc_pure (P : list word -> Model -> Prop) : opcomp :=
  OpComp (fun args _ model => P args model) (fun _ => []) (fun _ _ _ _ _ _ H => H).

Section Table.
Variables heap fd3 rstage fd3dir fdinit : opcomp.
Variable ext : int -> opcomp.

Definition comp_of (id : int) : opcomp :=
  if PrimInt63.eqb id 1%uint63 then heap
  else if PrimInt63.eqb id 2%uint63 then fd3
  else if PrimInt63.eqb id 3%uint63 then rstage
  else if PrimInt63.eqb id 4%uint63 then fd3dir
  else if PrimInt63.eqb id 5%uint63 then fdinit
  else ext id.

Definition comp_holds : int -> list word -> (word -> option byte) -> Model -> Prop := fun id => oc_holds (comp_of id).
Record tab_model := TabModel {
  tm_minv : Model -> Prop;
  tm_cov0 : Z -> Prop;
  tm_cov1 : int -> list word -> Z -> Prop;
  tm_halted : forall mo, tm_minv mo -> m_halted mo = None;
  tm_acc : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
      tm_minv mo ->
      Forall (fun o => comp_holds (fst o) (snd o) m mo) os ->
      (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> cov_of tm_cov0 tm_cov1 os (bv_unsigned a + j)) ->
      exists mo', materialize_model_accesses mo acc = Some mo' /\ tm_minv mo' /\
                  Forall (fun o => comp_holds (fst o) (snd o) m mo') os
}.
Definition plain_tm : tab_model :=
  TabModel mfacts (fun _ => True) (fun _ _ _ => False) mf_halted (plain_acc comp_holds).

Definition mk_optable_g (TM : tab_model) : optable :=
  OpTable comp_holds (fun id => oc_fp (comp_of id)) (fun id => oc_frame (comp_of id))
          (tm_minv TM) (tm_cov0 TM) (tm_cov1 TM) (tm_halted TM) (tm_acc TM).

Definition mk_optable : optable := mk_optable_g plain_tm.

Lemma mk_plain : plain_table mk_optable. Proof. split; [intros mo; reflexivity| intros a; exact I]. Qed.

Lemma mk_holds : forall TM id, op_holds (mk_optable_g TM) id = oc_holds (comp_of id). Proof. reflexivity. Qed.
Lemma mk_fp : forall TM id, op_fp (mk_optable_g TM) id = oc_fp (comp_of id). Proof. reflexivity. Qed.
Lemma mkg_minv : forall TM, op_minv (mk_optable_g TM) = tm_minv TM. Proof. reflexivity. Qed.
Lemma comp_1 : comp_of 1%uint63 = heap. Proof. reflexivity. Qed.
Lemma comp_2 : comp_of 2%uint63 = fd3. Proof. reflexivity. Qed.
Lemma comp_3 : comp_of 3%uint63 = rstage. Proof. reflexivity. Qed.
Lemma comp_4 : comp_of 4%uint63 = fd3dir. Proof. reflexivity. Qed.
Lemma comp_5 : comp_of 5%uint63 = fdinit. Proof. reflexivity. Qed.
Lemma comp_ext : forall id, PrimInt63.eqb id 1%uint63 = false -> PrimInt63.eqb id 2%uint63 = false -> PrimInt63.eqb id 3%uint63 = false ->
  PrimInt63.eqb id 4%uint63 = false -> PrimInt63.eqb id 5%uint63 = false -> comp_of id = ext id.
Proof. intros id H1 H2 H3 H4 H5. unfold comp_of. rewrite H1, H2, H3, H4, H5. reflexivity. Qed.
End Table.

Definition FD3_ID : int := 2%uint63.
Definition RSTAGE_ID : int := 3%uint63.
Definition FD3DIR_ID : int := 4%uint63.
Definition FDINIT_ID : int := 5%uint63.

Definition FDS0 : list (word * FdEntry) :=
  [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].

Definition fd3 : word := Z_to_bv 64 3.

Section Driver.
Variable p1 : list byte.
Variable file : list byte.
Variable RS : Z.
Definition RS_LEN : Z := 65536.

Definition fsize : Z := Z.min (Z.of_nat (length file)) (2 ^ 62).

Definition fd3_holds (args : list word) (model : Model) : Prop :=
  match args with
  | [off] => m_fds model = (fd3, FdFile p1 off) :: FDS0 /\ bv_unsigned off <= fsize
  | _ => False
  end.
Definition FD3 : opcomp := oc_pure fd3_holds.

Definition fd3dir_holds (args : list word) (model : Model) : Prop :=
  match args with [] => m_fds model = (fd3, FdDir) :: FDS0 | _ => False end.
Definition FD3DIR : opcomp := oc_pure fd3dir_holds.

Definition fdinit_holds (args : list word) (model : Model) : Prop :=
  match args with [] => m_fds model = FDS0 | _ => False end.
Definition FDINIT : opcomp := oc_pure fdinit_holds.

Definition rstage_holds (args : list word) (m : word -> option byte) (model : Model) : Prop :=
  match args with
  | [off; n] => bv_unsigned off + bv_unsigned n <= Z.of_nat (length file) /\ bv_unsigned n <= RS_LEN /\
               forall i, 0 <= i < bv_unsigned n ->
                 m (Z_to_bv 64 (RS + i)) = Some (nth (Z.to_nat (bv_unsigned off + i)) file (Z_to_bv 8 0))
  | _ => False
  end.
Definition rstage_fp (args : list word) : list (Z * Z) := [(RS, RS + RS_LEN)].

Hypothesis RS_range : 0 <= RS /\ RS + RS_LEN <= two64.

Lemma rstage_frame : forall args m m' model,
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (rstage_fp args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  rstage_holds args m model -> rstage_holds args m' model.
Proof.
  intros args m m' model AG _ H. destruct args as [|off [|n [|? ?]]]; cbn [rstage_holds] in *; try exact H.
  destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite <- (AG (RS + i)); [apply H3; exact Hi| unfold RS_LEN in *; lia |].
  constructor. cbn [fst snd]. unfold RS_LEN in *. lia.
Qed.

Definition RSTAGE : opcomp := OpComp rstage_holds rstage_fp rstage_frame.
End Driver.

End Ops.

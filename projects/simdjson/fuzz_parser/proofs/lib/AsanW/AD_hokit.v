(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import MainExport MainFactsAsan.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ARepInit_kit F_module_dtor_pre AD_handoff_md.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition scell := (nat * zexp)%type.
Definition sc_cell (V : nat -> Z) (sc : scell) : cell := cellw (fst sc) (zv V (snd sc)).
Definition sc_size (sc : scell) : Z := Z.of_nat (csize (cellw (fst sc) 0)).

Definition sc_factb (A : Z) (sc : scell) (f : mfact) : bool :=
  match f with
  | MCell (ZLit a) w v => (a =? A) && Nat.eqb w (fst sc) && zexp_eqb v (snd sc)
  | _ => false
  end.
Definition sc_imgb (l : list mfact) (A : Z) (sc : scell) : bool :=
  match snd sc with ZLit z => img_okb l A [cellw (fst sc) z] | _ => false end.
(* [comment removed for export] *)
Definition sc_zerob (l : list mfact) (A : Z) (sc : scell) : bool :=
  match snd sc with
  | ZLit 0 => existsb (fun f => match f with MZeroC (ZLit a) n => (a <=? A) && (A + sc_size sc <=? a + n) | _ => false end) l
  | _ => false
  end.
(* [comment removed for export] *)
Fixpoint lzeqb (x y : list Z) : bool :=
  match x, y with [], [] => true | a :: x', b :: y' => (a =? b) && lzeqb x' y' | _, _ => false end.
Definition sc_recutb (l : list mfact) (A : Z) (sc : scell) : bool :=
  match snd sc with
  | ZLit z =>
      existsb (fun f => match f with
                        | MCell (ZLit a) w' (ZLit v) =>
                            (* [comment removed for export] *)
                            if (a <=? A) && (A + sc_size sc <=? a + Z.of_nat (csize (cellw w' 0)))
                            then lzeqb (map bv_unsigned (firstn (csize (cellw (fst sc) 0)) (skipn (Z.to_nat (A - a)) (cbytes (cellw w' v)))))
                                       (map bv_unsigned (cbytes (cellw (fst sc) z)))
                            else false
                        | _ => false end) l
  | _ => false
  end.
Definition sc_okb (l : list mfact) (A : Z) (sc : scell) : bool :=
  if existsb (sc_factb A sc) l then true else if sc_zerob l A sc then true else if sc_recutb l A sc then true else sc_imgb l A sc.   (* [comment removed for export] *)
Fixpoint scs_okb (l : list mfact) (A : Z) (scs : list scell) : bool :=
  match scs with [] => true | sc :: tl => sc_okb l A sc && scs_okb l (A + sc_size sc) tl end.

Lemma cellw_zero_bytes : forall w, cbytes (cellw w 0) = repeat (Z_to_bv 8 0) (csize (cellw w 0)).
Proof. intros w. do 9 (destruct w as [|w]; [vm_compute; reflexivity|]). vm_compute. reflexivity. Qed.

Lemma zeroc_sub : forall (m : mem) a n A w, rw_cells asegs m a [CB (Z.to_nat n) (zeros n)] ->
  a <= A -> A + Z.of_nat (csize (cellw w 0)) <= a + n -> rw_cells asegs m A [cellw w 0].
Proof.
  intros m a n A w [[WF (B0 & B1 & B)] (W0 & W1 & W)] H1 H2.
  cbn [cells_bytes cbytes cells_size csize] in B0, B1, B, W0, W1, W. rewrite app_nil_r in B1, B. unfold zeros in B1, B. rewrite repeat_length in B1, B. rewrite Nat.add_0_r in W1, W.
  assert (SZ : (0 < csize (cellw w 0))%nat) by (do 9 (destruct w as [|w]; [cbn; lia|]); cbn; lia).
  split; [split|].
  - cbn. split; [| exact I]. do 9 (destruct w as [|w]; [exact I|]). exact I.
  - cbn [cells_bytes]. rewrite app_nil_r, cellw_zero_bytes. unfold bytes_at. rewrite repeat_length. split; [lia|]. split; [lia|].
    intros i Hi. specialize (B (Z.to_nat (A - a) + i)%nat ltac:(lia)).
    replace (a + Z.of_nat (Z.to_nat (A - a) + i)) with (A + Z.of_nat i) in B by lia. rewrite B.
    rewrite !nth_error_repeat by lia. reflexivity.
  - cbn [cells_size]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + i) with (a + (A - a + i)) by lia. apply W. lia.
Qed.

Lemma lzeqb_eq : forall x y, lzeqb x y = true -> x = y.
Proof. induction x as [|a x IH]; intros [|b y] H; cbn in H; try discriminate; [reflexivity|]. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; auto. Qed.
Lemma bytes_eq_of_unsigned' : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.
Lemma wf_cellw : forall w v, cells_wf [cellw w v].
Proof. intros w v. cbn. split; [| exact I]. do 9 (destruct w as [|w]; [exact I|]). exact I. Qed.
Lemma recut_cell : forall (m : mem) a (c : cell) A (c' : cell), rw_cells asegs m a [c] -> cell_wf c' ->
  a <= A -> A + Z.of_nat (csize c') <= a + Z.of_nat (csize c) ->
  firstn (csize c') (skipn (Z.to_nat (A - a)) (cbytes c)) = cbytes c' ->
  rw_cells asegs m A [c'].
Proof.
  intros m a c A c' [[WF (B0 & B1 & B)] (W0 & W1 & W)] WF' H1 H2 E.
  cbn [cells_bytes cells_size] in *. rewrite app_nil_r in *. rewrite Nat.add_0_r in *.
  destruct WF as [WFc _]. pose proof (cbytes_length c WFc) as LC. pose proof (cbytes_length c' WF') as LC'.
  split; [split|].
  - cbn. split; [exact WF'| exact I].
  - cbn [cells_bytes]. rewrite app_nil_r. unfold bytes_at. rewrite LC'. split; [lia|]. split; [lia|].
    intros i Hi. rewrite <- E. rewrite nth_error_firstn. destruct (Nat.ltb_spec i (csize c')); [|lia].
    rewrite nth_error_skipn. rewrite <- B by lia. f_equal. f_equal. lia.
  - cbn [cells_size]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + i) with (a + (A - a + i)) by lia. apply W. lia.
Qed.

Lemma sc_ok_fact : forall V (m : mem) l A sc, Forall (mfact_ok asegs V m) l -> existsb (sc_factb A sc) l = true -> rw_cells asegs m A [sc_cell V sc].
Proof.
  intros V m l A [w e] HF H.
  apply existsb_exists in H as (f & Hf & E). destruct f as [a w' v| | | | | | | | |]; try discriminate. destruct a as [z| | | | |]; try discriminate.
  cbn [sc_factb fst snd] in E. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply Z.eqb_eq in E1. apply Nat.eqb_eq in E2. apply zexp_eqb_eq in E3. subst.
  exact (proj1 (Forall_forall _ _) HF _ Hf).
Qed.
Lemma sc_ok_img : forall V (m : mem) l A sc, Forall (mfact_ok asegs V m) l -> sc_imgb l A sc = true -> rw_cells asegs m A [sc_cell V sc].
Proof.
  intros V m l A [w e] HF H. unfold sc_imgb in H. cbn [fst snd] in H. destruct e as [z| | | | |]; try discriminate.
  unfold sc_cell. cbn [fst snd zv]. eapply img_ok; [exact HF | apply wf_cellw | exact H].
Qed.
Lemma sc_ok_zero : forall V (m : mem) l A sc, Forall (mfact_ok asegs V m) l -> sc_zerob l A sc = true -> rw_cells asegs m A [sc_cell V sc].
Proof.
  intros V m l A [w e] HF H. unfold sc_zerob in H. cbn [fst snd] in H. destruct e as [z| | | | |]; try discriminate. destruct z; try discriminate.
  apply existsb_exists in H as (f & Hf & E). destruct f as [|a n| | | | | | | |]; try discriminate. destruct a as [z| | | | |]; try discriminate.
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. unfold sc_size in E2. cbn [fst] in E2.
  unfold sc_cell. cbn [fst snd zv]. eapply zeroc_sub; [exact (proj1 (Forall_forall _ _) HF _ Hf) | exact E1 | exact E2].
Qed.
Lemma sc_ok_recut : forall V (m : mem) l A sc, Forall (mfact_ok asegs V m) l -> sc_recutb l A sc = true -> rw_cells asegs m A [sc_cell V sc].
Proof.
  intros V m l A [w e] HF H. unfold sc_recutb in H. cbn [fst snd] in H. destruct e as [z| | | | |]; try discriminate.
  apply existsb_exists in H as (f & Hf & E). destruct f as [a w' v| | | | | | | | |]; try discriminate.
  destruct a as [a| | | | |]; try discriminate. destruct v as [v| | | | |]; try discriminate.
  destruct ((a <=? A) && (A + sc_size (w, ZLit z) <=? a + Z.of_nat (csize (cellw w' 0)))) eqn:E0; [|discriminate]. rename E into E3.
  apply andb_prop in E0 as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  apply lzeqb_eq in E3. apply bytes_eq_of_unsigned' in E3. unfold sc_size in E2. cbn [fst] in E2.
  pose proof (proj1 (Forall_forall _ _) HF _ Hf) as K. cbn [mfact_ok zv] in K.
  unfold sc_cell. cbn [fst snd zv].
  eapply (recut_cell m a (cellw w' v) A (cellw w z) K).
  + destruct (wf_cellw w z) as [X _]. exact X.
  + exact E1.
  + rewrite (csize_cellw w z), (csize_cellw w' v). exact E2.
  + rewrite (csize_cellw w z). exact E3.
Qed.
Lemma sc_ok : forall V (m : mem) l A sc, Forall (mfact_ok asegs V m) l -> sc_okb l A sc = true -> rw_cells asegs m A [sc_cell V sc].
Proof.
  intros V m l A sc HF H. unfold sc_okb in H.
  destruct (existsb (sc_factb A sc) l) eqn:H1; [eapply sc_ok_fact; eassumption|].
  destruct (sc_zerob l A sc) eqn:H2; [eapply sc_ok_zero; eassumption|].
  destruct (sc_recutb l A sc) eqn:H3; [eapply sc_ok_recut; eassumption|].
  eapply sc_ok_img; eassumption.
Qed.

Lemma scs_ok : forall V (m : mem) l, Forall (mfact_ok asegs V m) l ->
  forall scs A, scs <> [] -> scs_okb l A scs = true -> rw_cells asegs m A (map (sc_cell V) scs).
Proof.
  intros V m l HF scs. induction scs as [|sc tl IH]; intros A NE H; [congruence|].
  cbn [scs_okb] in H. apply andb_prop in H as [H1 H2]. cbn [map].
  destruct tl as [|sc' tl'].
  - eapply sc_ok; eassumption.
  - apply rw_cells_cons; [eapply sc_ok; eassumption|].
    replace (Z.of_nat (csize (sc_cell V sc))) with (sc_size sc) by (unfold sc_size, sc_cell; rewrite (csize_cellw (fst sc) (zv V (snd sc))); reflexivity).
    apply IH; [discriminate | exact H2].
Qed.
End CANSEC1.

(* [comment removed for export] *)
Ltac ho_reify_z V z :=
  lazymatch z with
  | V ?k => constr:(ZV k)
  | _ => let v := eval vm_compute in z in constr:(ZLit v)
  end.
Ltac ho_reify_cell V c :=
  lazymatch c with
  | C8 (Z_to_bv 64 ?z) => let e := ho_reify_z V z in constr:((8%nat, e))
  | C4 (Z_to_bv 64 ?z) => let e := ho_reify_z V z in constr:((4%nat, e))
  | C2 (Z_to_bv 64 ?z) => let e := ho_reify_z V z in constr:((2%nat, e))
  | C1 (Z_to_bv 8 ?z) => let e := ho_reify_z V z in constr:((1%nat, e))
  end.
Ltac ho_reify_cells V cs :=
  lazymatch cs with
  | nil => constr:(@nil scell)
  | cons ?c ?tl => let sc := ho_reify_cell V c in let r := ho_reify_cells V tl in constr:(cons sc r)
  end.
Ltac ho_cells V m HM :=
  lazymatch goal with
  | |- rw_cells asegs m ?A ?cs =>
      let a := eval vm_compute in A in
      let scs := ho_reify_cells V cs in
      change (rw_cells asegs m a (map (sc_cell V) scs));
      apply (scs_ok V m _ HM); [discriminate | vm_compute; reflexivity]
  end.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma ho_selftest : forall V m, Forall (mfact_ok asegs V m) asan_mem_facts ->
     rw_cells asegs m 0x662ec0 [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0x10c440 [C8 (Z_to_bv 64 1)].
Proof. intros V m HM. repeat match goal with |- _ /\ _ => split end; ho_cells V m HM. Qed.
End CANSEC2.

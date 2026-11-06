(* Model facts of m_rx for receive's walks (lib/Prog/T/receive.v, lib/U/Prog/T/receive.v), build-independent:
   m_rx returns 0 or 1 (fuzz/fuzz_transport.c:280-375: return 0 / return 1). The proof is that of
   TSim/RxOpLib.v rxop_m_rx_01, restated here in TModel; that m_rx keeps
   the world's g_fail_next byte is TIoRecv.v's m_rx_gk. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TSess0 TCb.
Import ListNotations.
Open Scope Z_scope.

Definition rx_t01 (o : option (list byte * Z)) : Prop := forall Bx t, o = Some (Bx, t) -> t = 0 \/ t = 1.

Lemma rx_t01_none : rx_t01 None.
Proof. intros Bx t H. discriminate H. Qed.
Lemma rx_t01_0 : forall B, rx_t01 (Some (B, 0)).
Proof. intros B Bx t H. injection H as E1 E2. subst t. left. reflexivity. Qed.
Lemma rx_t01_1 : forall B, rx_t01 (Some (B, 1)).
Proof. intros B Bx t H. injection H as E1 E2. subst t. right. reflexivity. Qed.
Lemma rx_t01_if : forall (b : bool) o1 o2, rx_t01 o1 -> rx_t01 o2 -> rx_t01 (if b then o1 else o2).
Proof. intros [|] o1 o2 H1 H2; [exact H1 | exact H2]. Qed.
Lemma rx_t01_bind : forall (A : Type) (o : option A) (f : A -> option (list byte * Z)),
  (forall x, rx_t01 (f x)) -> rx_t01 (match o with Some x => f x | None => None end).
Proof. intros A [x|] f H; [exact (H x) | exact rx_t01_none]. Qed.
Lemma rx_t01_pair : forall (A C : Type) (p : A * C) (f : A -> C -> option (list byte * Z)),
  (forall x y, rx_t01 (f x y)) -> rx_t01 (match p with (x, y) => f x y end).
Proof. intros A C [x y] f H. exact (H x y). Qed.

Lemma m_rx_m_01 : forall I F B n Bx t, m_rx_m I F B n = Some (Bx, t) -> t = 0 \/ t = 1.
Proof.
  intros I F B n. change (rx_t01 (m_rx_m I F B n)).
  unfold m_rx_m. destruct F as [fr|]; [|exact rx_t01_none].
  cbv beta zeta.
  repeat first [ apply rx_t01_if | apply rx_t01_bind | apply rx_t01_pair | apply rx_t01_none
               | apply rx_t01_0 | apply rx_t01_1 | lazymatch goal with |- forall _, _ => intro end ].
Qed.

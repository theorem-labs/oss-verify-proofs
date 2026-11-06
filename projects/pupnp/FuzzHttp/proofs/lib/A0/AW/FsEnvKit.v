(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
Import ListNotations.
Open Scope Z_scope.

Section FE.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

#[using="Type"] Lemma fcls_stack : forall lo q, alloc_ceiling <= lo -> fsenv_cls (FSB FI) (lo, q).
Proof. intros lo q H. left. exact H. Qed.
#[using="Type"] Lemma fcls_in_fs : forall a b, FSB FI <= a -> b <= FSB FI + A0_FS_SIZE -> fsenv_cls (FSB FI) (a, b).
Proof. intros a b H1 H2. right; left. cbn [fst snd]. split; assumption. Qed.
#[using="Type"] Lemma fcls_fs : fsenv_cls (FSB FI) (FSB FI, FSB FI + A0_FS_SIZE).
Proof. apply fcls_in_fs; lia. Qed.
#[using="Type"] Lemma fcls_shadow : forall a b, 0x7fff7000 <= a -> b <= 0x10007fff8000 -> fsenv_cls (FSB FI) (a, b).
Proof. intros a b H1 H2. right; right; left. cbn [fst snd]. split; assumption. Qed.
#[using="Type"] Lemma fcls_fssh : fsenv_cls (FSB FI) (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE).
Proof.
  pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & _). pose proof alloc_ceiling_bounds as ACR.
  apply fcls_shadow; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia.
Qed.

#[using="Type"] Lemma fcls_errno : forall a b, 0x5e68c8 <= a -> b <= 0x5e68d0 -> fsenv_cls (FSB FI) (a, b).
Proof.
  intros a b H1 H2. right; right; right. cbn [fst snd]. split; [lia|]. split; [lia|].
  unfold env_safe. apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil].
Qed.

#[using="Type"] Lemma fcls_lb : forall st m a n, RFAKE FI st m -> lb (fs_live FI st) a n -> fsenv_cls (FSB FI) (a, a + n).
Proof.
  intros st m a n RF (g & Hg & G1 & G2). pose proof (live_wf FI st m RF) as WF. rewrite Forall_forall in WF.
  destruct (WF g Hg) as (_ & W1 & W2 & _). apply fcls_in_fs; lia.
Qed.

#[using="Type"] Lemma fcls_wx : forall st m (Wx : list ivl), RFAKE FI st m ->
  Forall (fun iv : ivl => fst iv <= snd iv /\ (lb (fs_live FI st) (fst iv) (snd iv - fst iv) \/ (0x5e68c8 <= fst iv /\ snd iv <= 0x5e68d0))) Wx ->
  Forall (fsenv_cls (FSB FI)) Wx.
Proof.
  intros st m Wx RF H. induction H as [|[a b] W [LE [LB|ER]] _ IH]; constructor; try exact IH; cbn [fst snd] in *.
  - replace b with (a + (b - a)) by lia. exact (fcls_lb st m a (b - a) RF LB).
  - apply fcls_errno; lia.
Qed.

#[using="Type"] Lemma fsenv_FSIV : forall (W : list ivl) lo q m m',
  FSENV FI m -> munch ((lo, q) :: FSIV W) m m' -> alloc_ceiling <= lo -> Forall (fsenv_cls (FSB FI)) W -> FSENV FI m'.
Proof.
  intros W lo q m m' FE MU HLO HW. eapply (fsenv_frame FI); [exact FE| exact MU|].
  constructor; [apply fcls_stack; exact HLO|]. constructor; [apply fcls_fs|]. constructor; [apply fcls_fssh| exact HW].
Qed.
#[using="Type"] Lemma fsenv_munch : forall (W : list ivl) m m', FSENV FI m -> munch W m m' -> Forall (fsenv_cls (FSB FI)) W -> FSENV FI m'.
Proof. intros W m m' FE MU HW. exact (fsenv_frame FI m m' W FE MU HW). Qed.
End FE.

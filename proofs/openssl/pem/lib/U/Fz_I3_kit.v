(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma cstate_seg_e : forall Wseg s LBall LB L m m' sp sp' tp lo B hi (e : word),
  cstate s LBall LB L m sp tp lo B -> munch Wseg m m' -> wmono usegs m m' -> mem_inv usegs m' ->
  Forall (fun iv => cwin LBall lo hi iv \/ (errno_addr tp <= fst iv /\ snd iv <= errno_addr tp + 4)) Wseg -> lo <= hi -> hi <= B -> disjoint_from Wseg LX_FLAGS 1 ->
  rw_cells usegs m' (errno_addr tp) [C4 e] ->
  stk usegs m' lo (bv_unsigned sp') -> bv_unsigned sp' <= B ->
  cstate s LBall LB L m' sp' tp lo B.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Wseg s LBall LB L m m' sp sp' tp lo B hi e (HP & OWN & (errv & AV & HB & ST & LO & ERR & MI & TP) & LXS & (lb & LATCH) & RELRO & GLO)
         MU WM MI' HW LH HHI DL ERR' ST' SPB'.
  assert (ETP : errno_addr tp = 3344580) by (unfold errno_addr; rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  rewrite ETP in HW, ERR'.
  assert (BR : forall b, In b LBall -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; exact (RHEAP_block_range_proof _ _ _ b HP Hb)).
  unfold GLOBALS_TOP in GLO. unfold ceil_window in *.
  assert (OUT : forall a, (hi <= a \/ (0x10000 <= a < 0x31d4d0) \/ (0x31d4d8 <= a < 0x31dda0) \/ (0x3308c8 <= a < 0x3308d0) \/ (0x330918 <= a < 0x351010) \/ (0x3520d0 <= a < 0x353000)
                          \/ (0x32e030 <= a < 0x32e038)) -> outside Wseg a).
  { intros a Ha. clear MU DL. induction HW as [|[x y] W0 X HW IH]; cbn [outside]; [exact I|]. split; [| exact IH].
    intros Hin. cbn [fst snd] in X. destruct X as [X|X]; [| lia]. unfold cwin in X. cbn [fst snd] in X.
    destruct X as [X|[X|[X|[X|[X|(b & Hb & X1 & X2)]]]]]; try lia.
    destruct (BR b Hb) as (_ & _ & _ & BC1 & BC2). lia. }
  pose proof (agree_on_of_munch Wseg m m' MU WM) as AG.
  split. { eapply (RHEAP_frame_proof s LBall m m' Wseg HP MU WM). eapply Forall_impl; [| exact HW]. intros [x y] X. cbn [fst snd] in X.
           destruct X as [X|X].
           - eapply (Forall_inv (l := [])). eapply cwin_write_ok; [exact LO|]. constructor; [exact X| constructor].
           - unfold rclient_write_ok, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. cbn [fst snd]. right; left. lia. }
  split; [exact OWN|].
  split. { exists e. unfold cenv. split.
    { eapply rauxv_ok_agree; [exact AG| | | exact AV].
      - intros a Ha. apply OUT. left. lia.
      - unfold RMallocRep.RAUXV_CELL. intros a Ha. apply OUT. right; right; right; right; left. lia. }
    split; [exact SPB'|]. split; [exact ST'|]. split; [exact LO|]. split; [rewrite ETP; exact ERR'|]. split; [exact MI'| exact TP]. }
  split. { eapply lx_statics_agree; [exact AG| | exact LXS]. intros a Ha. apply OUT.
           unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN in Ha. lia. }
  split. { exists lb. eapply rw_cells_transport; [exact LATCH| exact MU| exact WM| exact DL]. }
  split; [| unfold GLOBALS_TOP; exact GLO].
  intros a Ha. rewrite (MU a); [exact (RELRO a Ha)|]. apply OUT. unfold cimg_addr in Ha. lia.
Qed.

(* [comment removed for export] *)
Lemma cframe_seg_e : forall T W SP s0 LB0 L0 m0 s LBc Lc m Wseg m',
  cframe T W SP s0 LB0 L0 m0 s LBc Lc m -> munch Wseg m m' -> wmono usegs m m' ->
  RHEAP s LBc m -> alloc_ceiling <= SP -> Forall (fun iv => cseg_ok T W SP LB0 LBc iv \/ (RERRNO <= fst iv /\ snd iv <= RERRNO + 4)) Wseg ->
  cframe T W SP s0 LB0 L0 m0 s LBc Lc m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros T W SP s0 LB0 L0 m0 s LBc Lc m Wseg m' (F1 & [K1 K1'] & SO1 & FA1) MU WM HP HSP HW.
  split; [| split; [split; assumption| split; assumption]].
  eapply agree_on_trans; [exact F1|]. eapply agree_on_mono; [exact (agree_on_of_munch Wseg m m' MU WM)|].
  intros a CA. cbv beta. unfold cfr_addr in CA. clear MU. induction HW as [|[x y] W0 H HW IH]; cbn [outside]; [exact I|]. split; [| exact IH].
  intros Hin. cbn [fst snd] in H. unfold ceil_window, LX_FLAGS in *.
  assert (BR : forall b0, In b0 LB0 -> ~ T (blk_id b0) -> rblock_range (blk_addr b0) (blk_size b0))
    by (intros b0 Hb0 NT; exact (RHEAP_block_range_proof _ _ _ b0 HP (K1 b0 Hb0 NT))).
  destruct H as [H|[E1 E2]].
  2:{ unfold RMallocRep.RERRNO in E1, E2. destruct CA as [CA|[(b0 & Hb0 & NT & Hr)|(C1 & C2 & C3 & C4)]]; [lia| |].
      - destruct (BR b0 Hb0 NT) as (_ & _ & _ & _ & BC). lia.
      - apply C2. unfold ralloc_static, RMallocRep.RERRNO. lia. }
  unfold cseg_ok in H. cbn [fst snd] in H. unfold LX_FLAGS in H.
  destruct H as [[H1 H2]|[(H0 & H1 & H)|[[H1 H2]|(b & Hb & FR & H1 & H2)]]].
  - destruct CA as [CA|[(b0 & Hb0 & NT & Hr)|(C1 & _)]]; [lia| | lia].
    destruct (BR b0 Hb0 NT) as (_ & _ & _ & BC & _). lia.
  - destruct CA as [CA|[(b0 & Hb0 & NT & Hr)|(C1 & C2 & C3 & C4)]]; [lia| | exact (C4 (H a Hin))].
    destruct (BR b0 Hb0 NT) as (_ & _ & _ & _ & BC). lia.
  - destruct CA as [CA|[(b0 & Hb0 & NT & Hr)|(C1 & C2 & C3 & C4)]]; [lia| | lia].
    destruct (BR b0 Hb0 NT) as (_ & _ & _ & _ & BC). lia.
  - destruct (RHEAP_block_range_proof _ _ _ b HP Hb) as (_ & _ & _ & BC1 & BC2).
    destruct CA as [CA|[(b0 & Hb0 & NT & Hr)|(C1 & C2 & C3 & C4)]]; [lia| | lia].
    destruct (RHEAP_blocks_disjoint_proof _ _ _ b0 b HP (K1 b0 Hb0 NT) Hb (FR b0 Hb0 NT)); lia.
Qed.
End WithCeiling0.

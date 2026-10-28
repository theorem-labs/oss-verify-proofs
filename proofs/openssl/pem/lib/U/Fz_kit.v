(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMallocKit_A RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_iface Driver_iface Drv_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition climpl (f : nat) (L : @clist bptr) (s : PState) (ms : machine_state)
    (POST : nat -> @clist bptr -> PState -> machine_state -> Prop) : Prop :=
  forall (A : Type) (K : @clist bptr -> M PState A) (Q : A -> PState -> machine_state -> Prop),
    (forall f' L' s' ms', POST f' L' s' ms' -> implM usegs (mbind (client_any lops f' L') K) s' Q ms') ->
    implM usegs (mbind (client_any lops f L) K) s Q ms.

Lemma climpl_done : forall f L s ms (POST : nat -> @clist bptr -> PState -> machine_state -> Prop), POST f L s ms -> climpl f L s ms POST.
Proof. intros f L s ms POST H A K Q HK. exact (HK _ _ _ _ H). Qed.

Lemma climpl_mono : forall f L s ms (P1 P2 : nat -> @clist bptr -> PState -> machine_state -> Prop),
  climpl f L s ms P1 -> (forall f' L' s' ms', P1 f' L' s' ms' -> P2 f' L' s' ms') -> climpl f L s ms P2.
Proof. intros f L s ms P1 P2 H HP A K Q HK. apply H. intros f' L' s' ms' H1. apply HK, HP, H1. Qed.

(* [comment removed for export] *)
Lemma climpl_seq : forall f L s ms (P1 POST : nat -> @clist bptr -> PState -> machine_state -> Prop),
  climpl f L s ms P1 -> (forall f' L' s' ms', P1 f' L' s' ms' -> climpl f' L' s' ms' POST) -> climpl f L s ms POST.
Proof. intros f L s ms P1 POST H H2 A K Q HK. apply H. intros f' L' s' ms' H1. exact (H2 _ _ _ _ H1 A K Q HK). Qed.

(* [comment removed for export] *)
Lemma climpl_from_evt : forall f L s ms POST, evt usegs (fun ms' => climpl f L s ms' POST) ms -> climpl f L s ms POST.
Proof.
  intros f L s ms POST H A K Q HK. eapply implM_evt; [exact H|]. cbv beta. intros ms' H'. exact (H' A K Q HK).
Qed.

(* [comment removed for export] *)
Lemma climpl_evt : forall f L s ms (P : machine_state -> Prop) POST,
  evt usegs P ms -> (forall ms', P ms' -> climpl f L s ms' POST) -> climpl f L s ms POST.
Proof. intros f L s ms P POST H HP. apply climpl_from_evt. eapply evt_mono; [exact H| exact HP]. Qed.

(* [comment removed for export] *)
Lemma client_any_stop : forall {A} f (L : @clist bptr) (K : @clist bptr -> M PState A) s Q ms,
  implM usegs (K L) s Q ms -> implM usegs (mbind (client_any lops f L) K) s Q ms.
Proof.
  intros A f L K s Q ms H. destruct f as [|f]; cbn [client_any].
  - exact H.
  - cbn [bind ret choose lops Target.ops]. apply implM_bind_assoc. apply implM_choicek. apply evt_done.
    exists (Cho 0 0 0). split; [exact I|]. exact H.
Qed.

Lemma implM_bind_ret_inv : forall {A} (c : M PState A) s (Q : A -> PState -> machine_state -> Prop) ms,
  implM usegs (mbind c (fun x => mret x)) s Q ms -> implM usegs c s Q ms.
Proof.
  intros A c s Q ms. unfold implM, mbind, mret, ebind. generalize (c s). intros t. revert ms.
  induction t as [[|[a s1]]|n k IH|v k IH]; intros ms H; cbn [ITree.bind] in H.
  - exact H.
  - exact H.
  - cbn [impl] in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
  - cbn [impl] in H |- *. eapply evt_mono; [exact H|]. intros ms1 (a & Hv & Ha). exists a. split; [exact Hv|]. apply IH. exact Ha.
Qed.

Lemma climpl_close : forall f L s ms POST (Q : @clist bptr -> PState -> machine_state -> Prop),
  climpl f L s ms POST -> (forall f' L' s' ms', POST f' L' s' ms' -> Q L' s' ms') ->
  implM usegs (client_any lops f L) s Q ms.
Proof.
  intros f L s ms POST Q H HQ. apply implM_bind_ret_inv. apply H. intros f' L' s' ms' HP.
  apply client_any_stop. apply implM_ret. apply evt_done. exact (HQ _ _ _ _ HP).
Qed.

(* [comment removed for export] *)
Lemma climpl_close_bind : forall {A} f L s ms POST (K : @clist bptr -> M PState A) (Q : A -> PState -> machine_state -> Prop),
  climpl f L s ms POST -> (forall f' L' s' ms', POST f' L' s' ms' -> implM usegs (K L') s' Q ms') ->
  implM usegs (mbind (client_any lops f L) K) s Q ms.
Proof. intros A f L s ms POST K Q H HQ. apply H. intros f' L' s' ms' HP. apply client_any_stop. exact (HQ _ _ _ _ HP). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cenv (m : mem) (sp tp : word) (lo B : Z) (errv : word) : Prop :=
  rauxv_ok m B /\ bv_unsigned sp <= B
  /\ stk usegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo
  /\ rw_cells usegs m (errno_addr tp) [C4 errv] /\ mem_inv usegs m /\ tp = Z_to_bv 64 RATP.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cstate (s : PState) (LBall LB : list block) (L : @clist bptr) (m : mem) (sp tp : word) (lo B : Z) : Prop :=
  RHEAP s LBall m /\ cl_own LBall LB L /\ (exists errv, cenv m sp tp lo B errv)
  /\ lx_statics m /\ (exists b : byte, rw_cells usegs m LX_FLAGS [C1 b]) /\ cimg m /\ GLOBALS_TOP <= lo.

Lemma cimg_seg : forall W m m', cimg m -> munch W m m' -> (forall a, cimg_addr a -> outside W a) -> cimg m'.
Proof. intros W m m' C MU H a Ha. rewrite (MU a); [exact (C a Ha)| exact (H _ Ha)]. Qed.

Lemma cstate_B : forall s LBall LB L m sp tp lo B, cstate s LBall LB L m sp tp lo B -> bv_unsigned sp <= B /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo.
Proof. intros s LBall LB L m sp tp lo B (_ & _ & (errv & _ & HB & _ & LO & _) & _ & _ & _ & GLO). auto. Qed.
Lemma cstate_nodup : forall s LBall LB L m sp tp lo B, cstate s LBall LB L m sp tp lo B -> List.NoDup (map blk_id LBall) /\ List.NoDup (map fst L).
Proof.
  intros s LBall LB L m sp tp lo B (HP & OWN & _). pose proof (RHEAP_blocks_nodup_proof _ _ _ HP) as ND.
  split; [exact ND| exact (cl_own_nodup _ _ _ OWN ND)].
Qed.

Lemma cstate_range : forall s LBall LB L m sp tp lo B p A n, cstate s LBall LB L m sp tp lo B -> In (p, A, n) LBall -> rblock_range A n.
Proof. intros s LBall LB L m sp tp lo B p A n (HP & _) H. exact (RHEAP_block_range_proof _ _ _ _ HP H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cfr_addr (T : bptr -> Prop) (W : list (Z * Z)) (SP : Z) (LBall : list block) (a : Z) : Prop :=
  SP <= a
  \/ (exists b, In b LBall /\ ~ T (blk_id b) /\ blk_addr b <= a < blk_addr b + blk_size b)
  \/ (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS /\ ~ rin_ivs W a).
Definition cfr (T : bptr -> Prop) (W : list (Z * Z)) (SP : Z) (LBall : list block) (m m' : mem) : Prop := agree_on (cfr_addr T W SP LBall) m m'.
Definition ckeep (T : bptr -> Prop) (LBall : list block) (L : @clist bptr) (LBall' : list block) (L' : @clist bptr) : Prop :=
  (forall b, In b LBall -> ~ T (blk_id b) -> In b LBall') /\ (forall q nm, In (q, nm) L -> ~ T q -> In (q, nm) L').
Definition cframe (T : bptr -> Prop) (W : list (Z * Z)) (SP : Z) (s : PState) (LBall : list block) (L : @clist bptr) (m : mem)
    (s' : PState) (LBall' : list block) (L' : @clist bptr) (m' : mem) : Prop :=
  cfr T W SP LBall m m' /\ ckeep T LBall L LBall' L' /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s.

Lemma cframe_refl : forall T W SP s LBall L m, cframe T W SP s LBall L m s LBall L m.
Proof. intros. split; [apply agree_on_refl|]. split; [split; auto| auto]. Qed.

(* [comment removed for export] *)
Lemma cframe_call : forall T W SP s0 LB0 L0 m0 s1 LB1 L1 m1 T' W' SP' s2 LB2 L2 m2,
  cframe T W SP s0 LB0 L0 m0 s1 LB1 L1 m1 -> cframe T' W' SP' s1 LB1 L1 m1 s2 LB2 L2 m2 ->
  SP' <= SP -> (forall a, rin_ivs W' a -> rin_ivs W a) ->
  (forall q, In q (map blk_id LB0) \/ In q (map fst L0) -> ~ T q -> ~ T' q) ->
  cframe T W SP s0 LB0 L0 m0 s2 LB2 L2 m2.
Proof.
  intros T W SP s0 LB0 L0 m0 s1 LB1 L1 m1 T' W' SP' s2 LB2 L2 m2 (F1 & [K1 K1'] & SO1 & FA1) (F2 & [K2 K2'] & SO2 & FA2) HSP HW HT.
  split; [| split; [split|split; congruence]].
  - eapply agree_on_trans; [exact F1|]. eapply agree_on_mono; [exact F2|]. intros a [H|[(b & Hb & NT & Hr)|(H1 & H2 & H3 & H4)]].
    + left. lia.
    + right; left. exists b. split; [apply K1; assumption|]. split; [| exact Hr]. apply HT; [left; apply in_map; exact Hb| exact NT].
    + right; right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. intros X. apply H4, HW, X.
  - intros b Hb NT. apply K2; [apply K1; assumption|]. apply HT; [left; apply in_map; exact Hb| exact NT].
  - intros q nm Hq NT. apply K2'; [apply K1'; assumption|]. apply HT; [right; apply in_map_iff; exists (q, nm); auto| exact NT].
Qed.

(* [comment removed for export] *)
Definition cseg_ok (T : bptr -> Prop) (W : list (Z * Z)) (SP : Z) (LB0 LBc : list block) (iv : Z * Z) : Prop :=
  (alloc_ceiling <= fst iv /\ snd iv <= SP)
  \/ (0x2c0000 <= fst iv /\ snd iv <= 0x353000 /\ forall a, fst iv <= a < snd iv -> rin_ivs W a)
  \/ (LX_FLAGS <= fst iv /\ snd iv <= LX_FLAGS + 1)
  \/ (exists b, In b LBc /\ (forall b0, In b0 LB0 -> ~ T (blk_id b0) -> blk_id b0 <> blk_id b)
                /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Lemma cseg_ok_stack : forall T W SP LB0 LBc x y, alloc_ceiling <= x -> y <= SP -> cseg_ok T W SP LB0 LBc (x, y).
Proof. intros. unfold cseg_ok. cbn [fst snd]. left. lia. Qed.
Lemma cseg_ok_block : forall T W SP LB0 LBc b x y, In b LBc -> (forall b0, In b0 LB0 -> ~ T (blk_id b0) -> blk_id b0 <> blk_id b) ->
  blk_addr b <= x -> y <= blk_addr b + blk_size b -> cseg_ok T W SP LB0 LBc (x, y).
Proof. intros T W SP LB0 LBc b x y Hb HF H1 H2. unfold cseg_ok. cbn [fst snd]. do 3 right. exists b. auto. Qed.
Lemma cseg_ok_static : forall T W SP LB0 LBc x y, 0x2c0000 <= x -> y <= 0x353000 -> (forall a, x <= a < y -> rin_ivs W a) -> cseg_ok T W SP LB0 LBc (x, y).
Proof. intros. unfold cseg_ok. cbn [fst snd]. right; left. auto. Qed.

Lemma cframe_seg : forall T W SP s0 LB0 L0 m0 s LBc Lc m Wseg m',
  cframe T W SP s0 LB0 L0 m0 s LBc Lc m -> munch Wseg m m' -> wmono usegs m m' ->
  RHEAP s LBc m -> alloc_ceiling <= SP -> Forall (cseg_ok T W SP LB0 LBc) Wseg ->
  cframe T W SP s0 LB0 L0 m0 s LBc Lc m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros T W SP s0 LB0 L0 m0 s LBc Lc m Wseg m' (F1 & [K1 K1'] & SO1 & FA1) MU WM HP HSP HW.
  split; [| split; [split; assumption| split; assumption]].
  eapply agree_on_trans; [exact F1|]. eapply agree_on_mono; [exact (agree_on_of_munch Wseg m m' MU WM)|].
  intros a CA. cbv beta. unfold cfr_addr in CA. clear MU. induction HW as [|[x y] W0 H HW IH]; cbn [outside]; [exact I|]. split; [| exact IH].
  intros Hin. unfold cseg_ok in H. cbn [fst snd] in H. unfold ceil_window, LX_FLAGS in *.
  assert (BR : forall b0, In b0 LB0 -> ~ T (blk_id b0) -> rblock_range (blk_addr b0) (blk_size b0))
    by (intros b0 Hb0 NT; exact (RHEAP_block_range_proof _ _ _ b0 HP (K1 b0 Hb0 NT))).
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

(* [comment removed for export] *)
Lemma cfresh_new : forall T LB0 L0 LBc Lc (b : block), ckeep T LB0 L0 LBc Lc -> List.NoDup (map blk_id (b :: LBc)) ->
  forall b0, In b0 LB0 -> ~ T (blk_id b0) -> blk_id b0 <> blk_id b.
Proof.
  intros T LB0 L0 LBc Lc b [K _] ND b0 Hb0 NT E. cbn [map] in ND. inversion ND as [|x l NI _]; subst. apply NI. rewrite <- E. apply in_map. exact (K b0 Hb0 NT).
Qed.

(* [comment removed for export] *)
Lemma cfr_cells_stack : forall T W SP LBall m m' A cs, cfr T W SP LBall m m' -> rw_cells usegs m A cs -> SP <= A -> rw_cells usegs m' A cs.
Proof. intros T W SP LBall m m' A cs H C HA. eapply rw_cells_agree; [exact H| exact C|]. intros a Ha. left. lia. Qed.
Lemma cfr_cells_block : forall T W SP LBall m m' A cs b, cfr T W SP LBall m m' -> rw_cells usegs m A cs ->
  In b LBall -> ~ T (blk_id b) -> blk_addr b <= A -> A + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b -> rw_cells usegs m' A cs.
Proof. intros T W SP LBall m m' A cs b H C Hb NT H1 H2. eapply rw_cells_agree; [exact H| exact C|]. intros a Ha. right; left. exists b. repeat split; auto; lia. Qed.
Lemma cfr_cells_static : forall T W SP LBall m m' A cs, cfr T W SP LBall m m' -> rw_cells usegs m A cs ->
  0x2c0000 <= A -> A + Z.of_nat (cells_size cs) <= 0x353000 ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ ralloc_static a /\ a <> LX_FLAGS /\ ~ rin_ivs W a) -> rw_cells usegs m' A cs.
Proof. intros T W SP LBall m m' A cs H C H1 H2 H3. eapply rw_cells_agree; [exact H| exact C|]. intros a Ha. right; right. split; [lia|]. apply H3. exact Ha. Qed.
Lemma cfr_bytes_stack : forall T W SP LBall m m' A bs, cfr T W SP LBall m m' -> bytes_at usegs m A bs -> SP <= A -> bytes_at usegs m' A bs.
Proof. intros T W SP LBall m m' A bs H C HA. eapply bytes_at_agree; [exact H| exact C|]. intros a Ha. left. lia. Qed.
Lemma cfr_bytes_block : forall T W SP LBall m m' A bs b, cfr T W SP LBall m m' -> bytes_at usegs m A bs ->
  In b LBall -> ~ T (blk_id b) -> blk_addr b <= A -> A + Z.of_nat (length bs) <= blk_addr b + blk_size b -> bytes_at usegs m' A bs.
Proof. intros T W SP LBall m m' A bs b H C Hb NT H1 H2. eapply bytes_at_agree; [exact H| exact C|]. intros a Ha. right; left. exists b. repeat split; auto; lia. Qed.
Lemma cfr_bytes_static : forall T W SP LBall m m' A bs, cfr T W SP LBall m m' -> bytes_at usegs m A bs ->
  0x2c0000 <= A -> A + Z.of_nat (length bs) <= 0x353000 ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> ~ ralloc_static a /\ a <> LX_FLAGS /\ ~ rin_ivs W a) -> bytes_at usegs m' A bs.
Proof. intros T W SP LBall m m' A bs H C H1 H2 H3. eapply bytes_at_agree; [exact H| exact C|]. intros a Ha. right; right. split; [lia|]. apply H3. exact Ha. Qed.

(* [comment removed for export] *)
Lemma cfr_lx_pres : forall T W SP LBall LB X m m', cfr T W SP LBall m m' ->
  (forall b, In b LB -> In b LBall /\ ~ T (blk_id b)) -> (forall a, rin_ivs W a \/ a = LX_FLAGS -> rin_ivs X a) -> lx_pres LB SP X m m'.
Proof.
  intros T W SP LBall LB X m m' H HB HX a Ha [NX CA]. apply H; [exact Ha|].
  destruct CA as [CA|[(b & Hb & Hr)|(C1 & C2)]]; [left; exact CA| right; left| right; right].
  - destruct (HB b Hb) as [I1 NT]. exists b. auto.
  - split; [exact C1|]. split; [exact C2|]. split; intros E; apply NX, HX; [right; exact E| left; exact E].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cwin (LBall : list block) (lo hi : Z) (iv : Z * Z) : Prop :=
  (0x31d4d0 <= fst iv /\ snd iv <= 0x31d4d8) \/ (0x31dda0 <= fst iv /\ snd iv <= 0x3308c4 /\ (snd iv <= 0x32e030 \/ 0x32e038 <= fst iv))
  \/ (0x3308d0 <= fst iv /\ snd iv <= 0x330918)
  \/ (0x351010 <= fst iv /\ snd iv <= 0x3520d0)
  \/ (lo <= fst iv /\ snd iv <= hi)
  \/ (exists b, In b LBall /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Lemma cwin_stack : forall LBall lo hi x y, lo <= x -> y <= hi -> cwin LBall lo hi (x, y).
Proof. intros. unfold cwin. cbn [fst snd]. do 4 right. left. lia. Qed.
Lemma cwin_block : forall LBall lo hi b x y, In b LBall -> blk_addr b <= x -> y <= blk_addr b + blk_size b -> cwin LBall lo hi (x, y).
Proof. intros LBall lo hi b x y Hb H1 H2. unfold cwin. cbn [fst snd]. do 5 right. exists b. auto. Qed.
Lemma cwin_bss : forall LBall lo hi x y, 0x31dda0 <= x -> y <= 0x3308c4 -> (y <= 0x32e030 \/ 0x32e038 <= x) -> cwin LBall lo hi (x, y).
Proof. intros. unfold cwin. cbn [fst snd]. right; left. lia. Qed.

Lemma cwin_write_ok : forall LBall lo hi W, alloc_ceiling <= lo -> Forall (cwin LBall lo hi) W -> Forall (rclient_write_ok LBall) W.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros LBall lo hi W LO H. eapply Forall_impl; [| exact H]. intros [a b] X; unfold cwin in X; cbn [fst snd] in *.
  unfold rclient_write_ok, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. cbn [fst snd].
  destruct X as [X|[X|[X|[X|[X|X]]]]]; [right; left; lia| right; left; lia| right; left; lia| right; left; lia| left; lia| right; right; exact X].
Qed.

Lemma cwin_outside : forall LBall lo hi W a, Forall (cwin LBall lo hi) W -> (forall b, In b LBall -> rblock_range (blk_addr b) (blk_size b)) -> alloc_ceiling <= lo -> lo <= hi ->
  (hi <= a \/ (0x10000 <= a < 0x31d4d0) \/ (0x31d4d8 <= a < 0x31dda0) \/ (0x3308c4 <= a < 0x3308d0) \/ (0x330918 <= a < 0x351010) \/ (0x3520d0 <= a < 0x353000)
   \/ (0x32e030 <= a < 0x32e038)) ->
  outside W a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros LBall lo hi W a H HB LO LH Ha. induction H as [|[x y] W0 X H IH]; cbn [outside]; [exact I|]. split; [| exact IH].
  intros Hin. unfold cwin in X. cbn [fst snd] in X. unfold ceil_window in *. destruct X as [X|[X|[X|[X|[X|(b & Hb & X1 & X2)]]]]]; try lia.
  destruct (HB b Hb) as (_ & _ & _ & BC1 & BC2). lia.
Qed.

Lemma cstate_seg' : forall Wseg s LBall LB L m m' sp sp' tp lo B hi,
  cstate s LBall LB L m sp tp lo B -> munch Wseg m m' -> wmono usegs m m' -> mem_inv usegs m' ->
  Forall (cwin LBall lo hi) Wseg -> lo <= hi -> hi <= B -> (exists b : byte, rw_cells usegs m' LX_FLAGS [C1 b]) ->
  stk usegs m' lo (bv_unsigned sp') -> bv_unsigned sp' <= B ->
  cstate s LBall LB L m' sp' tp lo B.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Wseg s LBall LB L m m' sp sp' tp lo B hi (HP & OWN & (errv & AV & HB & ST & LO & ERR & MI & TP) & LXS & _ & RELRO & GLO)
         MU WM MI' HW LH HHI LATCH' ST' SPB'.
  assert (BR : forall b, In b LBall -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; exact (RHEAP_block_range_proof _ _ _ b HP Hb)).
  pose proof (fun a => cwin_outside LBall lo hi Wseg a HW BR LO LH) as OUT.
  pose proof (agree_on_of_munch Wseg m m' MU WM) as AG.
  assert (ETP : errno_addr tp = 3344580) by (unfold errno_addr; rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  split; [exact (RHEAP_frame_proof s LBall m m' Wseg HP MU WM (cwin_write_ok LBall lo hi Wseg LO HW))|]. split; [exact OWN|].
  split. { exists errv. unfold cenv. split.
    { eapply rauxv_ok_agree; [exact AG| | | exact AV].
      - intros a Ha. apply OUT. left. lia.
      - unfold RMallocRep.RAUXV_CELL. intros a Ha. apply OUT. right; right; right; right; left. lia. }
    split; [exact SPB'|]. split; [exact ST'|]. split; [exact LO|].
    split. { eapply rw_cells_agree; [exact AG| exact ERR|]. rewrite ETP. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
             intros a Ha. apply OUT. right; right; right; left. lia. }
    split; [exact MI'| exact TP]. }
  split. { eapply lx_statics_agree; [exact AG| | exact LXS]. intros a Ha. apply OUT.
           unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN in Ha. lia. }
  split; [exact LATCH'|]. split; [| exact GLO].
  intros a Ha. rewrite (MU a); [exact (RELRO a Ha)|]. apply OUT. unfold cimg_addr in Ha. lia.
Qed.

Lemma cstate_seg : forall Wseg s LBall LB L m m' sp sp' tp lo B hi,
  cstate s LBall LB L m sp tp lo B -> munch Wseg m m' -> wmono usegs m m' -> mem_inv usegs m' ->
  Forall (cwin LBall lo hi) Wseg -> lo <= hi -> hi <= B -> disjoint_from Wseg LX_FLAGS 1 ->
  stk usegs m' lo (bv_unsigned sp') -> bv_unsigned sp' <= B ->
  cstate s LBall LB L m' sp' tp lo B.
Proof.
  intros Wseg s LBall LB L m m' sp sp' tp lo B hi CST MU WM MI' HW LH HHI DL ST' SPB'.
  eapply cstate_seg'; try eassumption. destruct CST as (_ & _ & _ & _ & (lb & LATCH) & _).
  exists lb. eapply rw_cells_transport; [exact LATCH| exact MU| exact WM| exact DL].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cret (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (v : word) (m' : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs).

(* [comment removed for export] *)
Definition cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (m : mem) (lo B : Z)
    (T : bptr -> Prop) (W : list (Z * Z)) (EV : nat) (da db dbig : Z)
    (R : word -> list block -> @clist bptr -> mem -> Prop) : nat -> @clist bptr -> PState -> machine_state -> Prop :=
  fun f' L' s' ms' => exists v m' LBall',
    cret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v m' ms'
    /\ (f - EV <= f')%nat /\ cgrow L L' da db dbig
    /\ cstate s' LBall' LB L' m' sp tp lo B
    /\ cframe T W (bv_unsigned sp) s LBall L m s' LBall' L' m'
    /\ R v LBall' L' m'.

(* [comment removed for export] *)
Lemma cpost_rebase : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (m m1 : mem) (lo B : Z) T W T' W' EV da db dbig R f' L' s' ms',
  cframe T W (bv_unsigned sp) s LBall L m s LBall L m1 ->
  (forall a, rin_ivs W' a -> rin_ivs W a) -> (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> ~ T q -> ~ T' q) ->
  cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m1 lo B T' W' EV da db dbig R f' L' s' ms' ->
  cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B T W EV da db dbig R f' L' s' ms'.
Proof.
  intros until ms'. intros FR0 HW HT (v & m2 & LB1 & RET & FU & GR & CST1 & FRM1 & RES).
  exists v, m2, LB1. split; [exact RET|]. split; [exact FU|]. split; [exact GR|]. split; [exact CST1|]. split; [| exact RES].
  eapply cframe_call; [exact FR0| exact FRM1| lia| exact HW| exact HT].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rheap_pres_cfr : forall LBall SP m m', rheap_pres LBall SP m m' -> cfr (fun _ => False) [] SP LBall m m'.
Proof.
  intros LBall SP m m' H a Ha CA. apply H; [exact Ha|]. destruct CA as [CA|[(b & Hb & _ & Hr)|(C1 & C2 & _)]].
  - left. exact CA.
  - right; right. exists b. auto.
  - right; left. auto.
Qed.

Lemma cstate_after : forall s s' LBall LBall' LB L L' m m' sp tp lo B (errv' : word) LBp,
  cstate s LBall LB L m sp tp lo B -> rheap_pres LBp (bv_unsigned sp) m m' ->
  RHEAP s' LBall' m' -> cl_own LBall' LB L' -> mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) ->
  rw_cells usegs m' (errno_addr tp) [C4 errv'] -> rauxv_ok m' B ->
  cstate s' LBall' LB L' m' sp tp lo B.
Proof.
  intros s s' LBall LBall' LB L L' m m' sp tp lo B errv' LBp (HP & OWN & (errv & AV & HB & ST & LO & ERR & MI & TP) & LXS & (lb & LATCH) & RELRO & GLO)
         PR HP' OWN' MI' ST' ERR' AV'.
  split; [exact HP'|]. split; [exact OWN'|]. split; [exists errv'; unfold cenv; auto 10|].
  pose proof (agree_of_heap_pres _ _ _ _ PR) as AG.
  split. { eapply lx_statics_agree; [exact AG| | exact LXS]. intros a Ha. right; left.
           unfold lxs_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP,
             LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN in *. lia. }
  split. { exists lb. eapply rw_cells_agree; [exact AG| exact LATCH|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. right; left.
           unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS in *. lia. }
  split; [| exact GLO].
  intros a Ha. pose proof (bv_unsigned_in_range _ a) as AR. change (bv_modulus 64) with (2^64) in AR.
  destruct (PR (bv_unsigned a) AR) as [E _].
  { right; left. unfold cimg_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia. }
  rewrite wa_unsigned_id in E. rewrite E. exact (RELRO a Ha).
Qed.

(* [comment removed for export] *)
Definition cs_malloc_res (n : Z) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists p A junk, v = Z_to_bv 64 A /\ LBall' = (p, A, n) :: LBall /\ L' = (p, n) :: L
                                     /\ rblock_range A n /\ rw_cells usegs m' A [CB (Z.to_nat n) junk].

Lemma cs_malloc : rmalloc_stmt ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (n lo B : Z),
  (1 <= f)%nat -> croom L (wA n) (wB n) (wBig n) -> 0 <= n < 2^31 ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - RMALLOC_STACK -> a0 = Z_to_bv 64 n ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 1 (wA n) (wB n) (wBig n)
                (cs_malloc_res n LBall L)).
Proof.
  intros MAL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f n lo B
         Hf ROOM N CST SLO A0 A K Q HQ.
  pose proof CST as (HP & OWN & (errv & AV & HB & ST & LO & ERR & MI & TP) & _).
  destruct f as [|f1]; [lia|].
  cbn [client_any]. cbn [bind ret choose lib_malloc unreachable lops Target.ops].
  apply implM_bind_assoc. apply implM_choicek. apply evt_done. exists (Cho 1 n 0).
  split; [apply croom_cvalid; [exact ROOM| unfold SZ_MAX; lia]|].
  apply implM_bind_assoc.
  eapply implM_bind.
  { eapply (MAL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall n lo B errv); try eassumption. lia. }
  cbv beta. intros r s' ms' PO. destruct r as [p|].
  2:{ unfold implM, mbind, munr, ebind. cbn [ITree.bind]. apply impl_ret_unr. }
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> & MI' & ST' & ERR' & AV' & PR & FA & SO
                  & A1 & junk & -> & RNG & HP' & BLK & _).
  apply HQ. exists (Z_to_bv 64 A1), m', ((p, A1, n) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [apply cgrow_cons|].
  split. { eapply cstate_after; try eassumption. apply cl_own_cons. exact OWN. }
  split. { split; [apply rheap_pres_cfr; exact PR|]. split; [split; intros; right; assumption| split; assumption]. }
  exists p, A1, junk. auto 6.
Qed.

Lemma cremove_keep : forall (L : @clist bptr) i p nm0 q nm, nth_error L i = Some (p, nm0) -> In (q, nm) L -> q <> p -> In (q, nm) (cremove i L).
Proof.
  intros L i p nm0 q nm HN H2 NE. destruct (cremove_split L i _ HN) as (l1 & l2 & EL & _ & EC). rewrite EC. rewrite EL in H2.
  apply in_app_or in H2. apply in_or_app. destruct H2 as [H2|[H2|H2]]; [left; exact H2| | right; exact H2].
  exfalso. apply NE. inversion H2. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cs_free : rfree_stmt ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (p : bptr) (A n nm lo B : Z),
  (1 <= f)%nat -> cown LBall L p A n nm ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - RFREE_STACK -> a0 = Z_to_bv 64 A ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq p) [] 1 (- wA nm) (- wB nm) (- wBig nm)
                (fun _ LBall' L' _ => LBall' = lb_remove p LBall /\ exists i, nth_error L i = Some (p, nm) /\ L' = cremove i L)).
Proof.
  intros FRE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f p A n nm lo B
         Hf OWNp CST SLO A0 A' K Q HQ.
  pose proof CST as (HP & OWN & (errv & AV & HB & ST & LO & ERR & MI & TP) & _).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST) as [ND NDL].
  destruct (cown_nth _ _ _ _ _ _ OWNp) as [i HN]. destruct OWNp as [INB INL].
  destruct f as [|f1]; [lia|].
  cbn [client_any]. cbn [bind ret choose lib_free unreachable lops Target.ops].
  apply implM_bind_assoc. apply implM_choicek. apply evt_done. exists (Cho 2 (Z.of_nat i) 0).
  split. { cbn [cvalid]. split; [lia|]. apply Nat2Z.inj_lt. apply nth_error_Some. rewrite HN. discriminate. }
  rewrite Nat2Z.id, HN. cbn [lib_free_opt]. apply implM_bind_assoc.
  eapply implM_bind.
  { eapply (FRE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall p A n lo B errv); eassumption. }
  cbv beta. intros [] s' ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & ERR' & AV' & PR & FA & SO & HP').
  apply HQ. exists a0', m', (lb_remove p LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [exact (cgrow_remove L i p nm HN)|].
  split. { eapply cstate_after; try eassumption. exact (cl_own_remove _ _ _ _ _ _ OWN ND HN). }
  split. { split.
    - intros a Ha CA. apply PR; [exact Ha|]. destruct CA as [CA|[(b & Hb & NT & Hr)|(C1 & C2 & _)]].
      + left. exact CA.
      + right; right. exists b. split; [| exact Hr]. apply lb_remove_In. split; [exact Hb|]. intros E. apply NT. symmetry. exact E.
      + right; left. auto.
    - split; [split|split; assumption].
      + intros b Hb NT. apply lb_remove_In. split; [exact Hb|]. intros E. apply NT. symmetry. exact E.
      + intros q nm' Hq NT. eapply cremove_keep; [exact HN| exact Hq|]. intros E. apply NT. symmetry. exact E. }
  split; [reflexivity|]. exists i. auto.
Qed.
End WithCeiling0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac cimg_cell CIMG m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nbs := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells usegs m A cs);
  [ apply (rw_cells_recast usegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 usegs m A bs);
      [ intros a Ha; apply CIMG; change (Z.of_nat (length bs)) with nbs in Ha; unfold cimg_addr, RMallocRep.RGOT_SSP; lia
      | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nbs; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

(* [comment removed for export] *)
Tactic Notation "calle" tactic3(APP) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ APP; repeat (rewrite unsigned_lit by lia); try eassumption; try reflexivity
      | let ms' := fresh "ms'" in let PO := fresh "POST" in
        intros ms' PO; hnf in PO; repeat (rewrite unsigned_lit in PO by lia); revert ms' PO; post_call segs mm ]
  end.

Ltac cprefix := apply climpl_from_evt.
Ltac chere := apply evt_done; cbv beta.

(* [comment removed for export] *)
Ltac cret_lit :=
  lazymatch goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(* [comment removed for export] *)
Ltac cfix_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac cstep := step; cfix_store.

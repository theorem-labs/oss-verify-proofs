(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RMalloc_impl RF_realloc_frame RF_realloc_spec RF_realloc_mid RF_aligned_frame RF_aligned_spec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition rmalloc_stmt_at (E : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM usegs (raw_malloc n) s
        (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 E) fc None m (seg_rom usegs)).
Definition rfree_stmt_at (E : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
  RHEAP s LB m -> In (p, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 A ->
  implM usegs (raw_free p) s
        (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 E) fc None m (seg_rom usegs)).
Lemma rmalloc_impl_at : rmalloc_impl_stmt -> rmalloc_stmt_at rmalloc_entry.  Proof. intros H. exact H. Qed.
Lemma rfree_impl_at : rfree_impl_stmt -> rfree_stmt_at rfree_entry.  Proof. intros H. exact H. Qed.

Lemma cs_malloc_at : forall ENT : Z, rmalloc_stmt_at ENT ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (n lo B : Z),
  (1 <= f)%nat -> croom L (wA n) (wB n) (wBig n) -> 0 <= n < 2^31 ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - RMALLOC_STACK -> a0 = Z_to_bv 64 n ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 ENT) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 1 (wA n) (wB n) (wBig n)
                (cs_malloc_res n LBall L)).
Proof.
  intros ENT MAL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f n lo B
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


(* [comment removed for export] *)
Lemma cs_free_at : forall ENT : Z, rfree_stmt_at ENT ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (p : bptr) (A n nm lo B : Z),
  (1 <= f)%nat -> cown LBall L p A n nm ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - RFREE_STACK -> a0 = Z_to_bv 64 A ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 ENT) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq p) [] 1 (- wA nm) (- wB nm) (- wBig nm)
                (fun _ LBall' L' _ => LBall' = lb_remove p LBall /\ exists i, nth_error L i = Some (p, nm) /\ L' = cremove i L)).
Proof.
  intros ENT FRE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f p A n nm lo B
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

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_at_inj : forall m a bs1 bs2, bytes_at usegs m a bs1 -> bytes_at usegs m a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
Proof.
  intros m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) LEN. apply List.nth_error_ext. intros i.
  destruct (Nat.ltb_spec0 i (length bs1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs1 i)) by lia. rewrite (proj2 (nth_error_None bs2 i)) by lia. reflexivity.
Qed.

Lemma firstn_min_length : forall {X} (l : list X) n, firstn n l = firstn (Nat.min n (length l)) l.
Proof.
  intros X l n. destruct (Nat.le_gt_cases n (length l)) as [H|H].
  - rewrite Nat.min_l by lia. reflexivity.
  - rewrite Nat.min_r by lia. rewrite firstn_all. apply firstn_all2. lia.
Qed.

(* [comment removed for export] *)
Lemma kept_prefix : forall m m' A (n n0 : nat) src junk,
  rw_cells usegs m A [CB n0 src] -> rw_cells usegs m' A [CB n junk] ->
  (forall bs, bytes_at usegs m A bs -> (length bs <= Nat.min n n0)%nat -> bytes_at usegs m' A bs) ->
  exists tail, rw_cells usegs m' A [CB n (firstn n src ++ tail)].
Proof.
  intros m m' A n n0 src junk OLD NEW KEEP.
  pose proof (rw_cells_CB_length usegs m A _ _ OLD) as LS. pose proof (rw_cells_CB_length usegs m' A _ _ NEW) as LJ.
  set (k := Nat.min n n0).
  pose proof (rw_cells_bytes_at usegs m A _ OLD) as BO. cbn [cells_bytes cbytes] in BO. rewrite app_nil_r in BO.
  pose proof (rw_cells_bytes_at usegs m' A _ NEW) as BN. cbn [cells_bytes cbytes] in BN. rewrite app_nil_r in BN.
  rewrite <- (firstn_skipn k src) in BO. apply bytes_at_app in BO. destruct BO as [BO _].
  rewrite <- (firstn_skipn k junk) in BN. apply bytes_at_app in BN. destruct BN as [BN _].
  assert (E : firstn k junk = firstn k src).
  { apply (bytes_at_inj m' A); [exact BN| apply KEEP; [exact BO| rewrite firstn_length; unfold k; lia]|]. rewrite !firstn_length. unfold k. lia. }
  exists (skipn k junk). rewrite (firstn_min_length src n), LS. fold k. rewrite <- E, firstn_skipn. exact NEW.
Qed.

Lemma w_nonneg : forall n, 0 <= wA n /\ 0 <= wB n /\ 0 <= wBig n.
Proof. intros n. unfold wA, wB, wBig, TIER_A_MAX. destruct (Z.leb_spec n 236); destruct (Z.ltb_spec 236 n); lia. Qed.

Definition RREALLOC_STACK : Z := 64 + RMALLOC_STACK.

Definition cs_realloc_res (p : bptr) (A nm n : Z) (src : list byte) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists q A' tail, v = Z_to_bv 64 A' /\ LBall' = (q, A', n) :: lb_remove p LBall /\ rblock_range A' n
      /\ rw_cells usegs m' A' [CB (Z.to_nat n) (firstn (Z.to_nat n) src ++ tail)]
      /\ ((q = p /\ A' = A /\ L' = L) \/ (exists i, nth_error L i = Some (p, nm) /\ L' = (q, n) :: cremove i L)).

Lemma cs_realloc : rrealloc_prefix_stmt -> rmalloc_impl_stmt -> rfree_impl_stmt ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (p : bptr) (A n0 nm n lo B : Z) (src : list byte),
  (2 <= f)%nat -> croom L (wA n) (wB n) (wBig n) -> 0 < n < MMAP_THRESHOLD ->
  cown LBall L p A n0 nm -> rw_cells usegs m A [CB (Z.to_nat n0) src] ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - RREALLOC_STACK -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq p) [] 2 (wA n) (wB n) (wBig n)
                (cs_realloc_res p A nm n src LBall L)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros PRE MAL FRE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f p A n0 nm n lo B src
         Hf ROOM N OWNp BLK CST SLO A0 A1.
  pose proof CST as (HP & OWN & (errv & AV & HB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNp)) as (PA0 & _ & PN0 & PAC & PAIMG).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST) as [ND NDL].
  unfold RREALLOC_STACK, RMALLOC_STACK, MMAP_THRESHOLD in *.
  pose proof (w_bounds n ltac:(lia)) as WB.
  eapply climpl_evt.
  { eapply (PRE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall p A n0 n lo B errv);
      try eassumption; [exact (proj1 OWNp)| lia| unfold MMAP_THRESHOLD; lia]. }
  intros ms1 [GROW|INPL].
  2:{ (* [comment removed for export] *)
    destruct INPL as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & jk & -> & MI1 & ST1 & ERR1 & AV1 & PR1 & HP1 & NEW).
    apply climpl_done. exists (Z_to_bv 64 A), m1, ((p, A, n) :: lb_remove p LBall).
    assert (INN : In (p, A, n) ((p, A, n) :: lb_remove p LBall)) by (left; reflexivity).
    assert (OWN1 : cl_own ((p, A, n) :: lb_remove p LBall) LB L).
    { destruct (in_split _ _ (proj1 OWNp)) as (l1 & l2 & EL). rewrite EL in ND |- *. rewrite (lb_remove_split p l1 (p, A, n0) l2 eq_refl ND).
      rewrite EL in OWN.
      assert (OWN' : cl_own ((p, A, n0) :: l1 ++ l2) LB L).
      { destruct OWN as (CLB & PERM & MAP). exists CLB. split; [| exact MAP]. eapply Permutation_trans; [| exact PERM]. apply Permutation_middle. }
      eapply cl_own_relist; [exact OWN'| | exact (proj2 OWNp)].
      eapply Permutation.Permutation_NoDup; [| exact ND]. apply Permutation_map. apply Permutation_sym. apply Permutation_middle. }
    split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [unfold cgrow; lia|].
    split. { eapply cstate_after; try eassumption. }
    split. { split; [| split; [split| split; reflexivity]].
      - intros a Ha CA. apply PR1; [exact Ha|]. destruct CA as [CA|[(b & Hb & NT & Hr)|(C1 & C2 & _)]].
        + left. exact CA.
        + right; right. exists b. split; [| exact Hr]. right. apply lb_remove_In. split; [exact Hb|]. intros E. apply NT. symmetry. exact E.
        + right; left. auto.
      - intros b Hb NT. right. apply lb_remove_In. split; [exact Hb|]. intros E. apply NT. symmetry. exact E.
      - intros q nm' Hq _. exact Hq. }
    destruct (kept_prefix m m1 A (Z.to_nat n) (Z.to_nat n0) src jk BLK NEW) as [tail KP].
    { intros bs Hbs Hlen. eapply rheap_pres_bytes_at; [exact PR1| exact Hbs|]. right; right. exists (p, A, n). split; [exact INN|].
      unfold blk_addr, blk_size. cbn [fst snd]. lia. }
    exists p, A, tail. split; [reflexivity|]. split; [reflexivity|]. split; [exact (RHEAP_block_range_proof _ _ _ _ HP1 INN)|]. split; [exact KP|]. left. auto. }
  (* [comment removed for export] *)
  destruct GROW as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ma & -> & FRa & STa & MUa & WMa & MIa & HPa).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -64)) tp lo B).
  { eapply (cstate_seg _ s LBall LB L m ma sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - constructor; [apply cwin_stack; lia| constructor].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS, GLOBALS_TOP in *. lia.
    - rewrite unsigned_lit by lia. exact STa.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (eq p) [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MUa| exact WMa| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  assert (BLKa : rw_cells usegs ma A [CB (Z.to_nat n0) src]).
  { eapply rw_cells_transport; [exact BLK| exact MUa| exact WMa|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  eapply climpl_seq.
  { eapply (cs_malloc_at rmalloc_entry (rmalloc_impl_at MAL)) with (n := n); [lia| exact ROOM| lia| exact CSTa| rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (q & A' & jk & -> & -> & -> & RNG & NEW)).
  destruct RET as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & ->).
  unfold RREALLOC_MID. cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRa ltac:(lia)) as FR1.
  assert (BLK1 : rw_cells usegs m1 A [CB (Z.to_nat n0) src]).
  { eapply (cfr_cells_block _ _ _ _ _ _ _ _ (p, A, n0) CFR1); [exact BLKa| exact (proj1 OWNp)| intros X; exact X| |]; unfold blk_addr, blk_size; cbn [fst snd cells_size csize]; lia. }
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (A'0 & _ & _ & A'C & A'IMG).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  assert (QP : q <> p).
  { intros E. cbn [map blk_id fst] in ND1. inversion ND1 as [|x l NI _]; subst. apply NI. apply in_map_iff. exists (p, A, n0). split; [reflexivity| exact (proj1 OWNp)]. }
  assert (APART : A + n0 <= A' \/ A' + n <= A).
  { pose proof (RHEAP_blocks_disjoint_proof _ _ _ (p, A, n0) (q, A', n) HP1 (or_intror (proj1 OWNp)) (or_introl eq_refl)) as D.
    unfold blk_id, blk_addr, blk_size in D. cbn [fst snd] in D. apply D. intros E. apply QP. symmetry. exact E. }
  set (k := Z.min n n0).
  destruct (rw_cells_CB_split_at usegs m1 A' (Z.to_nat n) jk (Z.to_nat k) ltac:(unfold k; lia) NEW) as [NEWa NEWb].
  pose proof (rw_cells_CB_length usegs m1 A _ _ BLK1) as LSRC.
  pose proof (rw_cells_bytes_at usegs m1 A _ BLK1) as SRC1. cbn [cells_bytes cbytes] in SRC1. rewrite app_nil_r in SRC1.
  rewrite <- (firstn_skipn (Z.to_nat k) src) in SRC1. apply bytes_at_app in SRC1. destruct SRC1 as [SRC1 _].
  (* [comment removed for export] *)
  eapply climpl_evt.
  { eapply (rrealloc_mid _ _ gp tp _ _ _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 A' A n n0 (firstn (Z.to_nat k) src) (firstn (Z.to_nat k) jk));
      [lia| lia| lia| lia| lia| exact SRC1| rewrite firstn_length, LSRC; unfold k; lia| exact NEWa| unfold k; lia| exact MI1]. }
  intros ms2 (x0 & x1 & x2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & x3 & x4 & x5 & x6 & m2 & -> & MU2 & WM2 & MI2 & DST2 & SRC2).
  fold k in MU2, DST2.
  assert (INQ : In (q, A', n) ((q, A', n) :: LBall)) by (left; reflexivity).
  assert (CST2 : cstate st1 ((q, A', n) :: LBall) LB ((q, n) :: L) m2 (Z_to_bv 64 (bv_unsigned sp + -64)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m1 m2 _ _ tp lo B (bv_unsigned sp)); [exact CST1| exact MU2| exact WM2| exact MI2| | lia| lia| | |].
    - constructor; [| constructor]. apply (cwin_block _ _ _ (q, A', n)); [exact INQ| |]; unfold blk_addr, blk_size; cbn [fst snd]; unfold k; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold k. lia.
    - rewrite unsigned_lit by lia. eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2|]. cbn [disjoint_from]. unfold k. lia.
    - rewrite unsigned_lit by lia. lia. }
  assert (FRb : cframe (eq p) [] (bv_unsigned sp) s LBall L m st1 ((q, A', n) :: LBall) ((q, n) :: L) m2).
  { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ _ X; exact X]| exact MU2| exact WM2| exact HP1| lia|].
    constructor; [| constructor]. apply (cseg_ok_block _ _ _ _ _ (q, A', n)); [exact INQ| | |]; unfold blk_addr, blk_size; cbn [fst snd]; unfold k; try lia.
    destruct FR0 as (_ & KP0 & _). exact (cfresh_new _ _ _ _ _ _ KP0 ND1). }
  assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) (rr_frame ra s0 s1 s2 s3 s4 s5 s6)).
  { eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add rr_frame]. unfold k. lia. }
  assert (NEWb2 : rw_cells usegs m2 (A' + Z.of_nat (Z.to_nat k)) [CB (Z.to_nat n - Z.to_nat k) (skipn (Z.to_nat k) jk)]).
  { eapply rw_cells_transport; [exact NEWb| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. unfold k. lia. }
  eapply climpl_seq.
  { eapply (cs_free_at rfree_entry (rfree_impl_at FRE)) with (p := p) (A := A) (n := n0) (nm := nm);
      [lia| apply cown_cons; exact OWNp| exact CST2| rewrite unsigned_lit by lia; unfold RFREE_STACK; lia| reflexivity]. }
  intros f2 L2 st2 ms2 (v2 & m3 & LB2 & RET2 & FU2 & GR2 & CST3 & FRM2 & (-> & i & HN & ->)).
  destruct RET2 as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  destruct i as [|i]; [cbn in HN; exfalso; apply QP; congruence|]. cbn [nth_error] in HN. cbn [cremove] in *.
  rewrite (lb_remove_cons_ne p (q, A', n) LBall) in * by (unfold blk_id; cbn [fst]; exact QP).
  pose proof FRM2 as (CFR2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR2 ltac:(lia)) as FR3.
  assert (NQ : ~ p = blk_id (q, A', n)) by (unfold blk_id; cbn [fst]; intros E; apply QP; symmetry; exact E).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q, A', n) CFR2 DST2 INQ NQ
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize]; unfold k; lia)) as DST3.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q, A', n) CFR2 NEWb2 INQ NQ
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize]; unfold k; lia)) as NEWb3.
  pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _).
  rewrite unsigned_lit in ST3 by lia.
  (* [comment removed for export] *)
  eapply climpl_evt.
  { eapply (rrealloc_tail _ ra sp gp tp _ _ _ s0 s1 s2 s3 s4 s5 s6); [exact FR3| exact ST3| lia| exact MI3]. }
  intros ms4 (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & -> & ST4).
  apply climpl_done. exists (Z_to_bv 64 A'), m3, ((q, A', n) :: lb_remove p LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split. { pose proof (w_nonneg nm). eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2)| lia| lia| lia]. }
  split. { eapply (cstate_seg [] _ _ _ _ m3 m3 _ sp tp lo B (bv_unsigned sp)); [exact CST3| apply munch_refl| apply wmono_refl| exact MI3| apply Forall_nil| lia| lia| exact I| exact ST4| exact HB]. }
  split. { eapply cframe_call; [exact FRb| exact FRM2| lia| intros a X; exact X| intros q0 _ X; exact X]. }
  exists q, A', (skipn (Z.to_nat k) jk). split; [reflexivity|]. split; [reflexivity|]. split; [exact RNG|]. split; [| right; exists i; auto].
  pose proof (rw_cells_CB_join usegs m3 A' _ _ _ _ DST3 NEWb3) as J.
  replace (Z.to_nat k + (Z.to_nat n - Z.to_nat k))%nat with (Z.to_nat n) in J by (unfold k; lia).
  rewrite (firstn_min_length src (Z.to_nat n)), LSRC. replace (Nat.min (Z.to_nat n) (Z.to_nat n0)) with (Z.to_nat k) by (unfold k; lia). exact J.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cstate_after' : forall s s' LBall LBall' LB L L' m m' sp tp lo B (errv' : word),
  cstate s LBall LB L m sp tp lo B -> agree_on (fun a => 0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a) m m' ->
  RHEAP s' LBall' m' -> cl_own LBall' LB L' -> mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) ->
  rw_cells usegs m' (errno_addr tp) [C4 errv'] -> rauxv_ok m' B ->
  cstate s' LBall' LB L' m' sp tp lo B.
Proof.
  intros s s' LBall LBall' LB L L' m m' sp tp lo B errv' (HP & OWN & (errv & AV & HB & ST & LO & ERR & MI & TP) & LXS & (lb & LATCH) & CIMG & GLO)
         AG HP' OWN' MI' ST' ERR' AV'.
  split; [exact HP'|]. split; [exact OWN'|]. split; [exists errv'; unfold cenv; auto 10|].
  split. { eapply lx_statics_agree; [exact AG| | exact LXS]. intros a Ha.
           unfold lxs_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP,
             LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN in *. lia. }
  split. { exists lb. eapply rw_cells_agree; [exact AG| exact LATCH|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha.
           unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS in *. lia. }
  split; [| exact GLO].
  intros a Ha. pose proof (bv_unsigned_in_range _ a) as AR. change (bv_modulus 64) with (2^64) in AR.
  destruct (AG (bv_unsigned a) AR) as [E _].
  { unfold cimg_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia. }
  rewrite wa_unsigned_id in E. rewrite E. exact (CIMG a Ha).
Qed.

Definition RMEMALIGN_STACK : Z := 48 + RMALLOC_STACK.

(* [comment removed for export] *)
Definition cs_memalign_res (len res : Z) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists p A' junk, v = Z_to_bv 64 0 /\ LBall' = (p, A', len) :: LBall /\ L' = (p, len + 48) :: L
      /\ rblock_range A' len /\ A' mod 64 = 0 /\ rw_cells usegs m' A' [CB (Z.to_nat len) junk] /\ rw_cells usegs m' res [C8 (Z_to_bv 64 A')].

(* [comment removed for export] *)
Lemma cs_memalign : rmemalign_prefix_stmt -> rmalloc_impl_stmt2 -> rmemalign_tail_stmt ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (len res lo B : Z) (old : word),
  (1 <= f)%nat -> croom L (wA (len + 48)) (wB (len + 48)) (wBig (len + 48)) -> 0 <= len -> len + 48 < MMAP_THRESHOLD ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - RMEMALIGN_STACK ->
  rw_cells usegs m RMALLOC_REPLACED [C4 (Z_to_bv 64 0)] ->
  rw_cells usegs m res [C8 old] -> bv_unsigned sp <= res -> res + 8 <= B ->
  a0 = Z_to_bv 64 res -> a1 = Z_to_bv 64 64 -> a2 = Z_to_bv 64 len ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 RMEMALIGN_SYM) fc None m (seg_rom usegs))
         (fun f' L' s' ms' => exists v m' LBall',
            cret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v m' ms'
            /\ (f - 1 <= f')%nat /\ cgrow L L' (wA (len + 48)) (wB (len + 48)) (wBig (len + 48))
            /\ cstate s' LBall' LB L' m' sp tp lo B
            /\ cframe (fun _ => False) [] (res + 8) s LBall L m s' LBall' L' m'
            /\ cs_memalign_res len res LBall L v LBall' L' m').
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros PRE MAL2 TAILS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f len res lo B old
         Hf ROOM LEN0 LTH CST SLO REPL RES RLO RHI A0 A1 A2 X K Q HQ.
  pose proof CST as (HP & OWN & (errv & AV & HB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold RMEMALIGN_STACK, RMALLOC_STACK, MMAP_THRESHOLD, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  assert (RESB : res < 2^64) by (destruct AV as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & _ & BAV & AVB & _); lia).
  eapply implM_evt.
  { eapply (PRE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall len lo); try eassumption; lia. }
  cbv beta. intros ms1 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ma & j8 & E1 & FRP & FRA & STa & MUa & WMa & MIa & HPa).
  cbv zeta in E1, FRA, STa. rewrite !unsigned_lit in * by lia. subst ms1.
  replace (bv_unsigned sp + -16 + -32) with (bv_unsigned sp + -48) in * by lia.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ s LBall LB L m ma sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - constructor; [apply cwin_stack; lia| constructor].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS in *. lia.
    - rewrite unsigned_lit by lia. exact STa.
    - rewrite unsigned_lit by lia. lia. }
  pose proof CSTa as (_ & _ & (errva & AVa & _ & _ & _ & ERRa & _ & _) & _).
  (* [comment removed for export] *)
  destruct f as [|f1]; [lia|].
  cbn [client_any]. cbn [bind ret choose lib_malloc unreachable lops Target.ops].
  apply implM_bind_assoc. apply implM_choicek. apply evt_done. exists (Cho 1 (len + 48) 0).
  split; [apply croom_cvalid; [exact ROOM| unfold SZ_MAX; lia]|].
  apply implM_bind_assoc.
  eapply implM_bind.
  { eapply (MAL2 _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc ma s LBall (len + 48) lo B errva);
      rewrite ?unsigned_lit by lia; try eassumption; try reflexivity; unfold RMALLOC_STACK; lia. }
  cbv beta. intros r st1 ms1 PO. destruct r as [p|].
  2:{ unfold implM, mbind, munr, ebind. cbn [ITree.bind]. apply impl_ret_unr. }
  destruct PO as (w0 & w1 & w2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & mb & errvb & -> & MIb & STb & ERRb & AVb & PRb & FAb & SOb
                  & A1' & junk & -> & RNG & HPb & BLKb & _ & FRESH).
  rewrite unsigned_lit in * by lia.
  unfold RALIGNED_MID. replace (ret_pc (Z_to_bv 64 2827468)) with (Z_to_bv 64 2827468) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* [comment removed for export] *)
  assert (FRPb : rw_cells usegs mb (bv_unsigned sp + -16) [C8 s0; C8 ra]).
  { eapply rheap_pres_rw_cells; [exact PRb| exact FRP|]. left. lia. }
  assert (FRAb : rw_cells usegs mb (bv_unsigned sp + -48) (ra_frame j8 (Z_to_bv 64 RMEMALIGN_MID) a0 s1)).
  { eapply rheap_pres_rw_cells; [exact PRb| exact FRA| left; lia]. }
  assert (RESb : rw_cells usegs mb res [C8 old]).
  { eapply rheap_pres_rw_cells; [exact PRb| | left; lia]. eapply rw_cells_transport; [exact RES| exact MUa| exact WMa|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  replace (Z_to_bv 64 (bv_unsigned sp + -48)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) + -32)) by (rewrite unsigned_lit by lia; f_equal; lia).
  eapply implM_evt.
  { eapply (TAILS _ ra sp gp tp _ _ _ s0 s1 (Z_to_bv 64 64) (Z_to_bv 64 len) (Z_to_bv 64 A1') _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ a0
              F fc mb st1 LBall p A1' len lo B errvb old j8);
      cbv zeta; rewrite ?unsigned_lit by lia; replace (bv_unsigned sp + -16 + -32) with (bv_unsigned sp + -48) by lia;
      try eassumption; try reflexivity; try (subst a0; rewrite ?unsigned_lit by lia; first [eassumption | lia]); try lia; try (unfold MMAP_THRESHOLD; lia). }
  cbv beta. intros ms2 (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & m1 & m2 & A' & jk & -> & MU2 & WM2 & MI2 & ST2 & RES2 & ERR2 & AV2
                        & AL & ARNG & PR2 & HP2 & BLK2).
  subst a0. rewrite unsigned_lit in * by lia.
  apply HQ. exists (Z_to_bv 64 0), m2, ((p, A', len) :: LBall).
  assert (INN : In (p, A', len) ((p, A', len) :: LBall)) by (left; reflexivity).
  (* [comment removed for export] *)
  assert (AG2 : agree_on (fun a => res + 8 <= a \/ in_block LBall a \/ (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a)) m m2).
  { intros a Ha CA.
    assert (C0 : outside [(bv_unsigned sp - 48, bv_unsigned sp)]%Z a).
    { cbn [outside]. split; [| exact I]. intros Hin. destruct CA as [CA|[(b & Hb & Hr)|(C1 & _)]]; [lia| | lia].
      destruct (RHEAP_block_range_proof _ _ _ b HP Hb) as (_ & _ & _ & BC & _). lia. }
    assert (C3 : outside [(res, res + 8)]%Z a).
    { cbn [outside]. split; [| exact I]. intros Hin. destruct CA as [CA|[(b & Hb & Hr)|(C1 & _)]]; [lia| | lia].
      destruct (RHEAP_block_range_proof _ _ _ b HP Hb) as (_ & _ & _ & BC & _). lia. }
    destruct (agree_on_of_munch _ _ _ MUa WMa a Ha C0) as [Ea Wa].
    destruct (PRb a Ha) as [Eb Wb]. { destruct CA as [CA|[CA|CA]]; [left; lia| right; right; exact CA| right; left; exact CA]. }
    destruct (PR2 a Ha) as [E1' W1']. { destruct CA as [CA|[(b & Hb & Hr)|CA]]; [left; lia| right; right; exists b; split; [right; exact Hb| exact Hr]| right; left; exact CA]. }
    destruct (agree_on_of_munch _ _ _ MU2 WM2 a Ha C3) as [E2 W2].
    split; [congruence| auto]. }
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [apply cgrow_cons|].
  split. { eapply (cstate_after' s st1 LBall _ LB L _ m m2 sp tp lo B errvb); [exact CST| | exact HP2| apply cl_own_cons; exact OWN| exact MI2| exact ST2| exact ERR2| exact AV2].
           eapply agree_on_mono; [exact AG2|]. intros a Ha. right; right. exact Ha. }
  split. { split; [| split; [split; intros; right; assumption| split; assumption]].
    eapply agree_on_mono; [exact AG2|]. intros a [CA|[(b & Hb & _ & Hr)|(C1 & C2 & _)]]; [left; exact CA| right; left; exists b; auto| right; right; auto]. }
  exists p, A', jk. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact (RHEAP_block_range_proof _ _ _ _ HP2 INN)|]. split; [exact AL|]. split; [exact BLK2| exact RES2].
Qed.
End WithCeiling0.

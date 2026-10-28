(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Exit Printf_wfile F_memcpy F_memset Lib_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition agree_on (P : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> P a ->
    m' (wa a) = m (wa a) /\ (wview ctusegs m (wa a) <> None -> wview ctusegs m' (wa a) <> None).

Lemma agree_on_refl : forall P m, agree_on P m m.
Proof. intros P m a _ _. auto. Qed.
Lemma agree_on_trans : forall P m1 m2 m3, agree_on P m1 m2 -> agree_on P m2 m3 -> agree_on P m1 m3.
Proof. intros P m1 m2 m3 H1 H2 a Ha HP. destruct (H1 a Ha HP) as [E1 W1]. destruct (H2 a Ha HP) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma agree_on_mono : forall (P P' : Z -> Prop) m m', agree_on P m m' -> (forall a, P' a -> P a) -> agree_on P' m m'.
Proof. intros P P' m m' H HP a Ha Hp. apply H; auto. Qed.

Lemma agree_on_of_munch : forall W m m', munch W m m' -> wmono ctusegs m m' -> agree_on (fun a => outside W a) m m'.
Proof.
  intros W m m' MU WM a Ha Ho. split; [| intros H; apply WM; exact H].
  apply MU. unfold wa. rewrite unsigned_lit by lia. exact Ho.
Qed.

(* [comment removed for export] *)
Lemma agree_of_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> agree_on (rclient_addr LB SP) m m'.
Proof. intros LB SP m m' H. exact H. Qed.
Lemma agree_of_lx_pres : forall LB SP X m m', lx_pres LB SP X m m' -> agree_on (lx_client LB SP X) m m'.
Proof. intros LB SP X m m' H. exact H. Qed.

Lemma bytes_at_agree : forall P m m' A bs,
  agree_on P m m' -> bytes_at ctusegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) ->
  bytes_at ctusegs m' A bs.
Proof.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma wr_at_agree : forall P m m' A n,
  agree_on P m m' -> wr_at ctusegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at ctusegs m' A n.
Proof.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.

Lemma rw_cells_agree : forall P m m' A cs,
  agree_on P m m' -> rw_cells ctusegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  rw_cells ctusegs m' A cs.
Proof.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply wr_at_agree; eauto.
Qed.

Lemma stk_agree : forall P m m' lo hi,
  agree_on P m m' -> stk ctusegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk ctusegs m' lo hi.
Proof.
  intros P m m' lo hi HP ST HR. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(apply HR; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
Definition stdout_addr (a : Z) : Prop := (RSTDOUT <= a < RSTDOUT + 232) \/ (RSTDOUT_BUF <= a < RSTDOUT_BUF + 1024).
Definition stderr_addr (a : Z) : Prop := RSTDERR <= a < RSTDERR + 232.
Definition ssp_addr (a : Z) : Prop := (got_ssp <= a < got_ssp + 8) \/ (ssp_guard <= a < ssp_guard + 8).
Definition lxs_addr (a : Z) : Prop :=
  (LX_GOT_STDERR <= a < LX_GOT_STDERR + 8) \/ (LX_STDERR_PTR <= a < LX_STDERR_PTR + 8).

Lemma stdout_file_agree : forall P m m' so,
  agree_on P m m' -> (forall a, stdout_addr a -> P a) -> stdout_file m so -> stdout_file m' so.
Proof.
  intros P m m' so AG HP (flags & mode & tail & bufb & FC & FL & BUF & BP & BL & INA).
  exists flags, mode, tail, bufb. split; [| split; [exact FL| split; [| auto]]].
  - eapply rw_cells_agree; [exact AG| exact FC|]. intros a Ha. apply HP. left. unfold file_cells in Ha. cbn in Ha. lia.
  - eapply rw_cells_agree; [exact AG| exact BUF|]. intros a Ha. apply HP. right. cbn in Ha. lia.
Qed.

Lemma stderr_wfile_agree : forall P m m',
  agree_on P m m' -> (forall a, stderr_addr a -> P a) -> stderr_wfile m -> stderr_wfile m'.
Proof.
  intros P m m' AG HP (flags & mode & e & wend & tail & FC & FL). exists flags, mode, e, wend, tail. split; [| exact FL].
  eapply rw_cells_agree; [exact AG| exact FC|]. intros a Ha. apply HP. unfold stderr_addr. unfold file_cells in Ha. cbn in Ha. lia.
Qed.

Lemma ssp_cells_agree : forall P m m' c,
  agree_on P m m' -> (forall a, ssp_addr a -> P a) -> ssp_cells m c -> ssp_cells m' c.
Proof.
  intros P m m' c AG HP [H1 H2]. unfold ssp_cells, ssp_addr, got_ssp, ssp_guard in *. split.
  - eapply rw_cells_agree; [exact AG| exact H1|]. intros a Ha. apply HP. cbn in Ha. lia.
  - eapply rw_cells_agree; [exact AG| exact H2|]. intros a Ha. apply HP. cbn in Ha. lia.
Qed.

Lemma lx_statics_agree : forall P m m',
  agree_on P m m' -> (forall a, lxs_addr a -> P a) -> lx_statics m -> lx_statics m'.
Proof.
  intros P m m' AG HP (A1 & A2). unfold lx_statics.
  unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR in *.
  Ltac tr AG HP A := eapply rw_cells_agree; [exact AG| exact A| intros a Ha; apply HP; cbn in Ha; lia].
  split; [tr AG HP A1| tr AG HP A2].
Qed.

Lemma rauxv_ok_agree : forall P m m' B,
  agree_on P m m' -> (forall a, B <= a -> P a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> P a) ->
  rauxv_ok m B -> rauxv_ok m' B.
Proof.
  intros P m m' B AG HP HC (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C & A1 & A2 & H).
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rw_cells_agree; [exact AG| exact C|]. intros a Ha. apply HC. cbn in Ha. lia.
  - eapply bytes_at_agree; [exact AG| exact A1|]. intros a Ha. apply HP. lia.
  - eapply bytes_at_agree; [exact AG| exact A2|]. intros a Ha. apply HP. cbn in Ha. lia.
Qed.

(* [comment removed for export] *)
Lemma stdout_addr_client : forall LB SP X a, stdout_addr a -> ~ rin_ivs X a -> lx_client LB SP X a.
Proof.
  intros LB SP X a Ha Hx. split; [exact Hx|]. right; right. unfold stdout_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia.
Qed.
Lemma stderr_addr_client : forall LB SP X a, stderr_addr a -> ~ rin_ivs X a -> lx_client LB SP X a.
Proof.
  intros LB SP X a Ha Hx. split; [exact Hx|]. right; right. unfold stderr_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia.
Qed.
Lemma lxs_addr_client : forall LB SP X a, lxs_addr a -> ~ rin_ivs X a -> lx_client LB SP X a.
Proof.
  intros LB SP X a Ha Hx. split; [exact Hx|]. right; right. unfold lxs_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP,
    LX_GOT_STDERR, LX_STDERR_PTR in *. lia.
Qed.
Lemma stack_client : forall LB SP X a, SP <= a -> ~ rin_ivs X a -> lx_client LB SP X a.
Proof. intros LB SP X a Ha Hx. split; [exact Hx| left; exact Ha]. Qed.
Lemma block_client : forall LB SP X b a, In b LB -> blk_addr b <= a < blk_addr b + blk_size b -> ~ rin_ivs X a -> lx_client LB SP X a.
Proof. intros LB SP X b a Hb Ha Hx. split; [exact Hx| right; left]. exists b. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma implM_get_bind : forall {A} (f : PState -> M PState A) s Q ms,
  implM ctusegs (f s) s Q ms -> implM ctusegs (mbind mget f) s Q ms.
Proof. intros A f s Q ms H. unfold implM, mbind, mget in *. cbn. exact H. Qed.
Lemma implM_ret_bind : forall {A B} (a : A) (f : A -> M PState B) s Q ms,
  implM ctusegs (f a) s Q ms -> implM ctusegs (mbind (mret a) f) s Q ms.
Proof. intros A B a f s Q ms H. unfold implM, mbind, mret in *. cbn. exact H. Qed.
Lemma implM_upd_bind : forall {A} (g : PState -> PState) (k : unit -> M PState A) s Q ms,
  implM ctusegs (k tt) (g s) Q ms -> implM ctusegs (mbind (mupd g) k) s Q ms.
Proof. intros A g k s Q ms H. unfold implM, mbind, mupd in *. cbn. exact H. Qed.
Lemma implM_if : forall {A} (b : bool) (t e : M PState A) s Q ms,
  (b = true -> implM ctusegs t s Q ms) -> (b = false -> implM ctusegs e s Q ms) -> implM ctusegs (if b then t else e) s Q ms.
Proof. intros A b t e s Q ms Ht He. destruct b; auto. Qed.

(* [comment removed for export] *)
Lemma implM_frame_pure : forall {A} (c : M PState A) s Q (phi : Prop) ms,
  phi -> implM ctusegs c s Q ms -> implM ctusegs c s (fun a s' ms' => phi /\ Q a s' ms') ms.
Proof. intros A c s Q phi ms Hphi H. eapply implM_mono; [exact H|]. intros; split; auto. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma LH_block_range : forall s LB m b, RHEAP s LB m -> In b LB -> rblock_range (blk_addr b) (blk_size b).
Proof. intros. eapply RMalloc_ifaceP.RHEAP_block_range_proof; eauto. Qed.

Lemma LH_nodup : forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).
Proof. intros. eapply RMalloc_ifaceP.RHEAP_blocks_nodup_proof; eauto. Qed.

Lemma LH_disjoint : forall s LB m b1 b2,
  RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof. intros. eapply RMalloc_ifaceP.RHEAP_blocks_disjoint_proof; eauto. Qed.

(* [comment removed for export] *)
Lemma LH_frame : forall s LB m m' W,
  RHEAP s LB m -> munch W m m' -> wmono ctusegs m m' -> Forall (rclient_write_ok LB) W -> RHEAP s LB m'.
Proof. intros. eapply RMalloc_ifaceP.RHEAP_frame_proof; eauto. Qed.

Lemma W_ok_stack : forall LB lo hi, alloc_ceiling <= lo -> rclient_write_ok LB (lo, hi).
Proof. intros LB lo hi H. left. cbn. exact H. Qed.

Lemma W_ok_block : forall LB b lo hi, In b LB -> blk_addr b <= lo -> hi <= blk_addr b + blk_size b ->
  rclient_write_ok LB (lo, hi).
Proof. intros LB b lo hi Hb H1 H2. right; right. exists b. cbn. auto. Qed.

(* [comment removed for export] *)
Lemma bptr_eqb_refl : forall p, bptr_eqb p p = true.
Proof. intros [[r o] z]. unfold bptr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, !Z.eqb_refl. reflexivity. Qed.

Lemma bptr_eqb_eq : forall p q, bptr_eqb p q = true -> p = q.
Proof.
  intros [[r o] z] [[r' o'] z'] H. unfold bptr_eqb, aptr_eqb in H. cbn in H.
  apply andb_true_iff in H. destruct H as [H1 H2]. apply andb_true_iff in H1. destruct H1 as [H0 H1].
  apply N.eqb_eq in H0. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma lb_remove_notin : forall p LB, ~ In p (map blk_id LB) -> lb_remove p LB = LB.
Proof.
  intros p LB. unfold lb_remove. induction LB as [|b LB IH]; intros H; [reflexivity|].
  rewrite filter_cons. cbn [map In] in H. destruct (decide _) as [Y|N].
  - rewrite IH; [reflexivity|]. intros H'. apply H. right. exact H'.
  - exfalso. destruct (bptr_eqb (blk_id b) p) eqn:E.
    + apply H. left. apply bptr_eqb_eq in E. exact E.
    + apply N. cbn [negb]. exact I.
Qed.

Lemma lb_remove_head : forall b LB, List.NoDup (map blk_id (b :: LB)) -> lb_remove (blk_id b) (b :: LB) = LB.
Proof.
  intros b LB ND. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
  unfold lb_remove. rewrite filter_cons, bptr_eqb_refl. destruct (decide _) as [Y|N]; [exfalso; exact Y|].
  apply (lb_remove_notin (blk_id b) LB). exact NI.
Qed.

Lemma lb_remove_hd : forall p A n LB, List.NoDup (map blk_id ((p, A, n) :: LB)) -> lb_remove p ((p, A, n) :: LB) = LB.
Proof. intros p A n LB ND. apply (lb_remove_head (p, A, n) LB ND). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma outside_of_X : forall X a, ~ rin_ivs X a -> outside X a.
Proof.
  intros X a. induction X as [|[lo hi] X IH]; intros H; cbn in *; [exact I|].
  split; [lia|]. apply IH. tauto.
Qed.

(* [comment removed for export] *)
Lemma lx_pres_of_munch : forall LB SP X W m m',
  munch W m m' -> wmono ctusegs m m' ->
  (forall a, 0 <= a < 2^64 -> lx_client LB SP X a -> outside W a) ->
  lx_pres LB SP X m m'.
Proof.
  intros LB SP X W m m' MU WM HW a Ha Hc. split; [| intros H; apply WM; exact H].
  apply MU. unfold wa. rewrite unsigned_lit by lia. apply HW; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma impl_post_evt : forall {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  impl ctusegs (at_node ctusegs) t Q ms -> (forall r ms', Q r ms' -> evt ctusegs (Q' r) ms') ->
  impl ctusegs (at_node ctusegs) t Q' ms.
Proof.
  induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Lemma implM_post_evt : forall {A} (c : M PState A) s Q Q' ms,
  implM ctusegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt ctusegs (Q' a s') ms') ->
  implM ctusegs c s Q' ms.
Proof.
  intros A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt; [exact H|].
  intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact I| apply HQ; exact H'].
Qed.

(* [comment removed for export] *)
Lemma impl_ebind_assoc : forall {A B C} (t : itree node (exc A)) (f : A -> itree node (exc B)) (g : B -> itree node (exc C)) Q ms,
  impl ctusegs (at_node ctusegs) (ebind t (fun a => ebind (f a) g)) Q ms ->
  impl ctusegs (at_node ctusegs) (ebind (ebind t f) g) Q ms.
Proof.
  induction t as [[|a]|n k IH]; intros f g Q ms H; cbn in *; try exact H.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
Qed.

Lemma implM_bind_assoc : forall {A B C} (c : M PState A) (f : A -> M PState B) (g : B -> M PState C) s Q ms,
  implM ctusegs (mbind c (fun x => mbind (f x) g)) s Q ms -> implM ctusegs (mbind (mbind c f) g) s Q ms.
Proof. intros A B C c f g s Q ms H. unfold implM, mbind in *. apply impl_ebind_assoc. exact H. Qed.

(* [comment removed for export] *)
Lemma heap_pres_of_munch : forall LB SP W m m',
  munch W m m' -> wmono ctusegs m m' ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a) ->
  rheap_pres LB SP m m'.
Proof.
  intros LB SP W m m' MU WM HW a Ha Hc. split; [| intros H; apply WM; exact H].
  apply MU. unfold wa. rewrite unsigned_lit by lia. apply HW; assumption.
Qed.

Lemma rclient_addr_cases : forall LB SP a,
  rclient_addr LB SP a -> SP <= a \/ (0x2c2000 <= a < 0x355000) \/ (exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b).
Proof. intros LB SP a [H|[[H _]|H]]; [left| right; left| right; right]; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_at_skipn : forall m A (bs : list byte) k,
  bytes_at ctusegs m A bs -> (k <= length bs)%nat -> bytes_at ctusegs m (A + Z.of_nat k) (skipn k bs).
Proof.
  intros m A bs k H Hk. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length, Nat.min_l in H by lia. exact H.
Qed.

Lemma bytes_at_firstn : forall m A (bs : list byte) k,
  bytes_at ctusegs m A bs -> bytes_at ctusegs m A (firstn k bs).
Proof.
  intros m A bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma rw_cells_recast : forall m A cs cs',
  rw_cells ctusegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells ctusegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LX_ERRNO : Z := RATP - 164.

Definition malloc_postZ (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo q
    /\ rw_cells ctusegs m' LX_ERRNO [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB q m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
       | Some p => exists A junk,
           a0 = Z_to_bv 64 A /\ rblock_range A n
           /\ RHEAP s' ((p, A, n) :: LB) m'
           /\ rw_cells ctusegs m' A [CB (Z.to_nat n) junk]
       end.

Lemma malloc_callZ : rmalloc_stmt ->
  forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> q <= B ->
  stk ctusegs m lo q -> alloc_ceiling <= lo -> lo <= q - RMALLOC_STACK ->
  rw_cells ctusegs m LX_ERRNO [C4 errv] ->
  mem_inv ctusegs m -> 0 <= q < 2^64 -> 0 <= n < 2^32 ->
  implM ctusegs (raw_malloc n) s
        (malloc_postZ ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom ctusegs)).
Proof.
  intros HM. intros until errv. intros HEAP AUX QB ST CEIL LO ERR MI Hq Hn.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Et : bv_unsigned (Z_to_bv 64 RATP) + -164 = LX_ERRNO) by (unfold LX_ERRNO, RATP; rewrite unsigned_lit by lia; lia).
  eapply implM_mono.
  { eapply HM with (B := B) (lo := lo); rewrite ?Eq, ?Et; try eassumption; try reflexivity; try lia. }
  cbv beta. intros r s' ms' PO. unfold rmalloc_post in PO. unfold malloc_postZ. rewrite !Eq, !Et in PO.
  destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & errv' & E & REST).
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, m', errv'. split; [exact E|].
  destruct REST as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). repeat (split; [assumption|]).
  destruct r as [p|]; [| exact A8].
  destruct A8 as (A & junk & B1 & B2 & B3 & B4 & _). exists A, junk. auto.
Qed.

Definition free_postZ (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo q
    /\ rw_cells ctusegs m' LX_ERRNO [C4 errv]
    /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p LB) q m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (lb_remove p LB) m'.

Lemma free_callZ : rfree_stmt ->
  forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (p : bptr) (q A n lo B : Z) (errv : word),
  RHEAP s LB m -> In (p, A, n) LB ->
  rauxv_ok m B -> q <= B ->
  stk ctusegs m lo q -> alloc_ceiling <= lo -> lo <= q - RFREE_STACK ->
  rw_cells ctusegs m LX_ERRNO [C4 errv] ->
  mem_inv ctusegs m -> 0 <= q < 2^64 ->
  implM ctusegs (raw_free p) s
        (free_postZ ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom ctusegs)).
Proof.
  intros HF. intros until errv. intros HEAP IN AUX QB ST CEIL LO ERR MI Hq.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Et : bv_unsigned (Z_to_bv 64 RATP) + -164 = LX_ERRNO) by (unfold LX_ERRNO, RATP; rewrite unsigned_lit by lia; lia).
  eapply implM_mono.
  { eapply HF with (B := B) (lo := lo); rewrite ?Eq, ?Et; try eassumption; try reflexivity; try lia. }
  cbv beta. intros r s' ms' PO. unfold rfree_post in PO. unfold free_postZ. rewrite !Eq, !Et in PO. exact PO.
Qed.

(* [comment removed for export] *)
Definition memcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ rw_cells ctusegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at ctusegs m' Src src.
Lemma memcpy_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
  bytes_at ctusegs m Src src -> length src = Z.to_nat N -> rw_cells ctusegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv ctusegs m ->
  evt ctusegs (memcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2bd77c) fc None m (seg_rom ctusegs)).
Proof.
  intros until junk. intros BA LEN DC SEP HN HS HD MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply F_memcpy.memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
  intros ms' P. unfold F_memcpy.memcpy_post, memcpy_postZ in *. rewrite ED, ES, EN in P. exact P.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lxs_addr_lt : forall a, lxs_addr a -> 0x2c2000 <= a < GLOBALS_TOP /\ ~ ralloc_static a.
Proof.
  intros a Ha. unfold lxs_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, GLOBALS_TOP,
    LX_GOT_STDERR, LX_STDERR_PTR in *. lia.
Qed.
Lemma stderr_addr_lt : forall a, stderr_addr a -> 0x2c2000 <= a < GLOBALS_TOP /\ ~ ralloc_static a.
Proof. intros a Ha. unfold stderr_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, GLOBALS_TOP in *. lia. Qed.
Lemma ssp_addr_lt : forall a, ssp_addr a -> 0x2c2000 <= a < GLOBALS_TOP /\ (~ ralloc_static a \/ (RMallocRep.RSSP_GUARD <= a < RMallocRep.RSSP_GUARD + 8) \/ (RMallocRep.RGOT_SSP <= a < RMallocRep.RGOT_SSP + 8)).
Proof. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, GLOBALS_TOP in *. lia. Qed.

(* [comment removed for export] *)
Lemma statics_heap : forall LB SP m m' ,
  rheap_pres LB SP m m' -> GLOBALS_TOP <= SP ->
  (lx_statics m -> lx_statics m') /\ (stderr_wfile m -> stderr_wfile m').
Proof.
  intros LB SP m m' HP HS. pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
  split.
  - intros H. eapply lx_statics_agree; [exact AG| |exact H]. intros a Ha. pose proof (lxs_addr_lt a Ha) as [R1 R2]. right; left. unfold GLOBALS_TOP in R1. split; [lia| exact R2].
  - intros H. eapply stderr_wfile_agree; [exact AG| |exact H]. intros a Ha. pose proof (stderr_addr_lt a Ha) as [R1 R2]. right; left. unfold GLOBALS_TOP in R1. split; [lia| exact R2].
Qed.

(* [comment removed for export] *)
Lemma statics_munch : forall W m m' c,
  munch W m m' -> wmono ctusegs m m' ->
  (forall a, 0x2c2000 <= a < GLOBALS_TOP -> outside W a) ->
  (lx_statics m -> lx_statics m') /\ (stderr_wfile m -> stderr_wfile m')
  /\ (ssp_cells m c -> ssp_cells m' c).
Proof.
  intros W m m' c MU WM HW. pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  split; [|split].
  - intros H. eapply lx_statics_agree; [exact AG| |exact H]. intros a Ha. pose proof (lxs_addr_lt a Ha) as [R1 R2]. apply HW. unfold GLOBALS_TOP in *. lia.
  - intros H. eapply stderr_wfile_agree; [exact AG| |exact H]. intros a Ha. pose proof (stderr_addr_lt a Ha) as [R1 R2]. apply HW. unfold GLOBALS_TOP in *. lia.
  - intros H. eapply ssp_cells_agree; [exact AG| |exact H]. intros a Ha. pose proof (ssp_addr_lt a Ha) as [R1 R2]. apply HW. unfold GLOBALS_TOP in *. lia.
Qed.

(* [comment removed for export] *)
Lemma RHEAP_ssp : forall s LB m, RHEAP s LB m -> ssp_cells m rr_guard.
Proof.
  intros s LB m (st & LB0 & _ & _ & MR & _). destruct MR as (_ & _ & (G1 & G2 & G3 & G4 & G5 & _) & _).
  unfold ssp_cells, got_ssp, ssp_guard. unfold RMallocRep.RGOT_SSP, RMallocRep.RSSP_GUARD in G4, G5. split; [exact G4| exact G5].
Qed.

Lemma bytes_at_same : forall m A (bs bs' : list byte),
  bytes_at ctusegs m A bs -> bytes_at ctusegs m A bs' -> length bs = length bs' -> bs = bs'.
Proof.
  intros m A bs bs' (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by lia. rewrite (proj2 (nth_error_None _ _)) by lia. reflexivity.
Qed.

Lemma ssp_canary_0 : forall s LB m c, RHEAP s LB m -> ssp_cells m c -> c = rr_guard.
Proof.
  intros s LB m c HR [_ H2]. pose proof (RHEAP_ssp _ _ _ HR) as [_ G2].
  destruct H2 as [[_ B2] _]. destruct G2 as [[_ C2] _]. cbn [cells_bytes cbytes app] in B2, C2. rewrite app_nil_r in B2, C2.
  pose proof (bytes_at_same _ _ _ _ B2 C2 ltac:(rewrite !length_le8; reflexivity)) as E.
  rewrite <- (le_bytes_to_word_le8 c), <- (le_bytes_to_word_le8 rr_guard), E. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma to_bytes_length : forall l, length (to_bytes l) = length l.
Proof. intros l. unfold to_bytes. apply length_map. Qed.
Lemma zlength_to_bytes : forall l, Z.of_nat (length (to_bytes l)) = zlength l.
Proof. intros l. rewrite to_bytes_length. reflexivity. Qed.

Lemma payload_ok_agree : forall P m m' LB D d,
  agree_on P m m' -> payload_ok m LB D d ->
  (forall b a, In b LB -> blk_addr b <= a < blk_addr b + blk_size b -> P a) ->
  payload_ok m' LB D d.
Proof.
  intros P m m' LB D d AG (BY & HF & HD & HD63 & HD31 & HB) HP.
  split; [| split; [exact HF| split; [exact HD| split; [exact HD63| split; [exact HD31| exact HB]]]]].
  destruct HB as [->|(b & Hb & Hb1 & Hb2)].
  - destruct BY as (B1 & B2 & _). split; [exact B1|]. split; [exact B2|]. intros i Hi. cbn in Hi. lia.
  - eapply bytes_at_agree; [exact AG| exact BY|]. intros a Ha. rewrite to_bytes_length in Ha. unfold zlength in Hb2.
    apply (HP b); [exact Hb| lia].
Qed.

Lemma payload_ok_heap : forall LB SP m m' D d,
  rheap_pres LB SP m m' -> payload_ok m LB D d -> payload_ok m' LB D d.
Proof.
  intros LB SP m m' D d HP PL. eapply payload_ok_agree; [apply agree_of_heap_pres; exact HP| exact PL|].
  intros b a Hb Ha. right; right. exists b. auto.
Qed.
End WithCeiling0.

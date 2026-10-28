(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit Driver_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation bgusegs := ImageBg.bgusegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

Definition BN_B1 : Z := 0x330e98.
Definition BN_STATICS : Z := 0x330e98.

Definition CR_MALLOC_IMPL : Z := 0x31db10.
Definition CR_FREE_IMPL : Z := 0x31db20.
Definition CR_GOT_MALLOC : Z := 0x31c6a8.
Definition CR_GOT_FREE : Z := 0x31c6b8.
Definition CR_MEMSET_FUNC : Z := 0x31db28.
Definition CR_NO_CUSTOMIZE : Z := 0x32e658.
Definition CRYPTO_MALLOC : Z := 0xe9138.
Definition CRYPTO_FREE : Z := 0xe94dc.
Definition MEMSET : Z := 0x2bbae4.

Definition OI_STOPPED : Z := 0x32e458.
Definition OI_OPTSDONE : Z := 0x32e4b0.
Definition OI_BASE_ONCE : Z := 0x32e470.
Definition TL_MASTER_ONCE : Z := 0x32e4d4.
Definition TCB_TSD : Z := 0x330f40.
Definition TSD_MAIN : Z := 0x352300.

Definition LIBW_bn : list (Z * Z) := [(0x2c0c80, 0x2c11b8); (0x3151a8, 0x31ae30); (0x31c6a8, 0x31c6c0); (0x31db00, 0x31e0e0); (0x32e440, 0x330ec8); (0x330f02, 0x330f03); (0x330f38, 0x330f48); (0x351ec0, 0x352318)].

Definition bn_cells (D : Z) (b : bignum bptr) : list cell :=
  [C8 (wz D); C4 (wz (Z.of_nat (bn_top b))); C4 (wz (Z.of_nat (bn_dmax b))); C4 (wz (Z.b2z (bn_neg b))); C4 (wz (bn_flags b))].

Definition bn_arr (m : mem) (OW : list block) (D : Z) (b : bignum bptr) : Prop :=
  match bn_d b with
  | None => D = 0 /\ bn_buf b = []
  | Some p => In (p, D, 8 * Z.of_nat (bn_dmax b)) OW /\ u64arr bgusegs m D (wlimbs (bn_buf b))
  end.

Definition bn_rep (m : mem) (OW : list block) (a : Z) (b : bignum bptr) : Prop :=
  exists D, rw_cells bgusegs m a (bn_cells D b) /\ bn_arr m OW D b.

Definition bnR : Type := Z -> bignum bptr -> bnref -> Prop.
Definition repR (m : mem) (OW : list block) : bnR := fun a b _ => bn_rep m OW a b.
Definition holeR (hs : list bnref) (m : mem) (OW : list block) : bnR := fun a b r => In r hs \/ bn_rep m OW a b.

Fixpoint bns_gen (R : bnR) (a : Z) (l : list (bignum bptr)) (i : nat) : Prop :=
  match l with
  | [] => True
  | b :: l' => R a b (RPool i) /\ bns_gen R (a + 24) l' (S i)
  end.

Definition ctx_cells (H Cu I : Z) (c : bn_ctx bptr) : list cell :=
  [C8 (wz H); C8 (wz Cu); C8 (wz H);
   C4 (wz (Z.of_nat (cx_pused c))); C4 (wz (Z.of_nat (cx_psize c)));
   C8 (wz I); C4 (wz (Z.of_nat (length (cx_frames c)))); C4 (wz (Z.of_nat (cx_ssize c)));
   C4 (wz (Z.of_nat (cx_used c))); C4 (wz (Z.of_nat (cx_err_stack c))); C4 (wz (Z.b2z (cx_too_many c)));
   C4 (wz 0); C8 (wz 0)].

Definition pool_mem (m : mem) (H Cu : Z) (c : bn_ctx bptr) : Prop :=
  match cx_head c with
  | None => Cu = 0 /\ cx_current c = None
  | Some p => rw_cells bgusegs m (H + 384) [C8 (wz 0); C8 (wz 0)]
              /\ ((cx_current c = None /\ Cu = 0) \/ (cx_current c = Some p /\ Cu = H))
  end.

Definition pool_gen (R : bnR) (cxo : bool) (m : mem) (OW : list block) (H Cu : Z) (c : bn_ctx bptr) : Prop :=
  match cx_head c with
  | None => H = 0 /\ cx_vals c = []
  | Some p => In (p, H, 400) OW /\ length (cx_vals c) = 16%nat /\ bns_gen R H (cx_vals c) 0
  end /\ (cxo = false -> pool_mem m H Cu c).

Definition stack_rep (m : mem) (OW : list block) (I : Z) (c : bn_ctx bptr) : Prop :=
  match cx_indexes c with
  | None => I = 0 /\ cx_ssize c = 0%nat /\ cx_frames c = []
  | Some q => In (q, I, 128) OW /\ cx_ssize c = 32%nat
              /\ exists stale : list word,
                   (length (cx_frames c) + length stale = 32)%nat
                   /\ u32arr bgusegs m I (map (fun k => wz (Z.of_nat k)) (cx_frames c) ++ stale)
  end.

Definition ctx_gen (R : bnR) (cxo : bool) (m : mem) (OW : list block) (a : Z) (c : bn_ctx bptr) : Prop :=
  exists H Cu I, (cxo = false -> rw_cells bgusegs m a (ctx_cells H Cu I c) /\ stack_rep m OW I c) /\ pool_gen R cxo m OW H Cu c.

Record bn_addrs : Type := mkAD {
  ad_b1 : Z; ad_b2 : Z; ad_b3 : Z; ad_b4 : Z; ad_b5 : Z; ad_ctx : Z;
  ad_p1 : bptr; ad_p2 : bptr; ad_p3 : bptr; ad_p4 : bptr; ad_p5 : bptr; ad_pc : bptr }.

Definition ad_cells (AD : bn_addrs) : list cell :=
  [C8 (wz (ad_b1 AD)); C8 (wz (ad_b2 AD)); C8 (wz (ad_b3 AD)); C8 (wz (ad_b4 AD)); C8 (wz (ad_b5 AD)); C8 (wz (ad_ctx AD))].

Definition ad_ids (AD : bn_addrs) : list bptr := [ad_p1 AD; ad_p2 AD; ad_p3 AD; ad_p4 AD; ad_p5 AD; ad_pc AD].

Definition ad_blocks (OW : list block) (AD : bn_addrs) : Prop :=
  In (ad_p1 AD, ad_b1 AD, 24) OW /\ In (ad_p2 AD, ad_b2 AD, 24) OW /\ In (ad_p3 AD, ad_b3 AD, 24) OW
  /\ In (ad_p4 AD, ad_b4 AD, 24) OW /\ In (ad_p5 AD, ad_b5 AD, 24) OW /\ In (ad_pc AD, ad_ctx AD, 72) OW.

Definition bn_mem_gen (R : bnR) (cxo : bool) (ls : lstate bptr) (m : mem) (OW : list block) (AD : bn_addrs) : Prop :=
  ro_cells bgusegs m BN_STATICS (ad_cells AD) /\ ad_blocks OW AD
  /\ R (ad_b1 AD) (ls_b1 ls) RB1 /\ R (ad_b2 AD) (ls_b2 ls) RB2 /\ R (ad_b3 AD) (ls_b3 ls) RB3
  /\ R (ad_b4 AD) (ls_b4 ls) RB4 /\ R (ad_b5 AD) (ls_b5 ls) RB5
  /\ ctx_gen R cxo m OW (ad_ctx AD) (ls_ctx ls).

Definition bn_mem (ls : lstate bptr) (m : mem) (OW : list block) (AD : bn_addrs) : Prop := bn_mem_gen (repR m OW) false ls m OW AD.

Definition ref_at (ls : lstate bptr) (OW : list block) (AD : bn_addrs) (r : bnref) (a : Z) : Prop :=
  match r with
  | RB1 => a = ad_b1 AD | RB2 => a = ad_b2 AD | RB3 => a = ad_b3 AD | RB4 => a = ad_b4 AD | RB5 => a = ad_b5 AD
  | RPool i => exists p H, cx_head (ls_ctx ls) = Some p /\ In (p, H, 400) OW /\ (i < 16)%nat /\ a = H + 24 * Z.of_nat i
  end.

Definition crypto_statics (m : mem) : Prop :=
  ro_cells bgusegs m CR_GOT_MALLOC [C8 (wz CRYPTO_MALLOC)]
  /\ ro_cells bgusegs m CR_GOT_FREE [C8 (wz CRYPTO_FREE)]
  /\ ro_cells bgusegs m CR_MEMSET_FUNC [C8 (wz MEMSET)]
  /\ ro_cells bgusegs m CR_MALLOC_IMPL [C8 (wz CRYPTO_MALLOC)]
  /\ ro_cells bgusegs m CR_FREE_IMPL [C8 (wz CRYPTO_FREE)]
  /\ ro_cells bgusegs m CR_NO_CUSTOMIZE [C1 (Z_to_bv 8 1)].

Definition ES_CLEARED : list byte :=
  repeat (Z_to_bv 8 0) 704 ++ repeat (Z_to_bv 8 255) 64 ++ repeat (Z_to_bv 8 0) 136.

Record err_addrs : Type := mkEA {
  ea_MK : Z; ea_SA : Z; ea_ND : Z; ea_ES : Z;
  ea_pk : bptr; ea_ps : bptr; ea_pn : bptr; ea_pe : bptr }.

Definition ea_ids (EA : err_addrs) : list bptr := [ea_pk EA; ea_ps EA; ea_pn EA; ea_pe EA].

Definition err_statics (m : mem) : Prop :=
  ro_cells bgusegs m OI_STOPPED [C1 (Z_to_bv 8 0)]
  /\ ro_cells bgusegs m OI_OPTSDONE [C8 (wz 2)]
  /\ ro_cells bgusegs m OI_BASE_ONCE [C4 (wz 2); C4 (wz 1)]
  /\ ro_cells bgusegs m TL_MASTER_ONCE [C4 (wz 2); C4 (wz 2)]
  /\ ro_cells bgusegs m TCB_TSD [C8 (wz TSD_MAIN)].

Definition err_mem (m : mem) (OW : list block) (EA : err_addrs) : Prop :=
  In (ea_pk EA, ea_MK EA, 72) OW /\ In (ea_ps EA, ea_SA EA, 32) OW /\ In (ea_pn EA, ea_ND EA, 128) OW /\ In (ea_pe EA, ea_ES EA, 904) OW
  /\ ro_cells bgusegs m (TSD_MAIN + 16) [C8 (wz (ea_MK EA))]
  /\ ro_cells bgusegs m (ea_MK EA + 24) [C8 (wz (ea_SA EA))]
  /\ (exists pad : list byte,
        ro_cells bgusegs m (ea_SA EA) [C4 (wz 1); CB 4 pad; C8 (wz 0); C8 (wz 1); C8 (wz (ea_ND EA))])
  /\ ro_cells bgusegs m (ea_ND EA) [C8 (wz (ea_ES EA))]
  /\ rw_cells bgusegs m (ea_ES EA) [CB 904 ES_CLEARED].

Definition err_inv (m : mem) (OW : list block) (EA : err_addrs) : Prop := err_statics m /\ err_mem m OW EA.

Definition bn_state_hc (cxo : bool) (hs : list bnref) (ls : lstate bptr) (m : mem) (OW : list block) (AD : bn_addrs) (EA : err_addrs) : Prop :=
  st_okm ls /\ List.NoDup (ad_ids AD ++ ea_ids EA ++ map fst (blocks_of ls)) /\ bn_mem_gen (holeR hs m OW) cxo ls m OW AD.

Definition lib_state_hc (cxo : bool) (hs : list bnref) (ls : lstate bptr) (m : mem) (OW : list block) (AD : bn_addrs) (EA : err_addrs) : Prop :=
  crypto_statics m /\ err_inv m OW EA /\ ossl_exit_cells m /\ bn_state_hc cxo hs ls m OW AD EA.

Notation lib_state_h := (lib_state_hc false).
Notation bn_state_h := (bn_state_hc false).
Definition bn_state := bn_state_hc false [].
Definition lib_state := lib_state_hc false [].

Definition lib_inv_bn (ls : lstate bptr) (m : mem) (OW : list block) : Prop :=
  exists AD EA, lib_state ls m OW AD EA.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma ro_cells_agree : forall P m m' A cs,
  agree_on P m m' -> ro_cells bgusegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  ro_cells bgusegs m' A cs.
Proof.
  intros P m m' A cs HP [Hwf HB] HR. split; [exact Hwf|].
  eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HR.
Qed.

Lemma u64arr_agree : forall P m m' A ws,
  agree_on P m m' -> u64arr bgusegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> P a) ->
  u64arr bgusegs m' A ws.
Proof.
  intros P m m' A ws HP [HB HW] HR. split.
  - eapply bytes_at_agree; eauto. rewrite u64s_length. intros a Ha. apply HR. lia.
  - eapply wr_at_agree; eauto.
Qed.

Lemma u32arr_agree : forall P m m' A ws,
  agree_on P m m' -> u32arr bgusegs m A ws -> (forall a, A <= a < A + 4 * Z.of_nat (length ws) -> P a) ->
  u32arr bgusegs m' A ws.
Proof.
  intros P m m' A ws HP [HB HW] HR. split.
  - eapply bytes_at_agree; eauto. rewrite u32s_length. intros a Ha. apply HR. lia.
  - eapply wr_at_agree; eauto.
Qed.

Lemma in_block_intro : forall (OW : list block) p A n a, In (p, A, n) OW -> A <= a < A + n -> in_block OW a.
Proof. intros OW p A n a H Ha. exists (p, A, n). split; [exact H|]. exact Ha. Qed.

Lemma wlimbs_length : forall l, length (wlimbs l) = length l.
Proof. intros. unfold wlimbs. apply length_map. Qed.

Definition bn_fp (OW : list block) (a : Z) (b : bignum bptr) (x : Z) : Prop :=
  (a <= x < a + 24)
  \/ (exists p D, bn_d b = Some p /\ In (p, D, 8 * Z.of_nat (bn_dmax b)) OW /\ D <= x < D + 8 * Z.of_nat (bn_dmax b)).

Lemma bn_rep_transport : forall P m m' OW OW' a b,
  agree_on P m m' -> (forall x, bn_fp OW a b x -> P x) ->
  (forall p D, bn_d b = Some p -> In (p, D, 8 * Z.of_nat (bn_dmax b)) OW -> In (p, D, 8 * Z.of_nat (bn_dmax b)) OW') ->
  bn_rep m OW a b -> bn_rep m' OW' a b.
Proof.
  intros P m m' OW OW' a b AG HP HOW (D & HC & HA). exists D. split.
  - eapply rw_cells_agree; [exact AG| exact HC|]. intros x Hx. apply HP. left. cbn in Hx. lia.
  - unfold bn_arr in *. destruct (bn_d b) as [p|] eqn:E; [|exact HA]. destruct HA as [Hin Harr]. split; [apply HOW; [reflexivity| exact Hin]|].
    eapply u64arr_agree; [exact AG| exact Harr|]. intros x Hx. apply HP. right. exists p, D. rewrite wlimbs_length in Hx.
    split; [exact E|]. split; [exact Hin|]. unfold bn_dmax. lia.
Qed.

Lemma bns_gen_impl : forall (R R' : bnR) l a i,
  (forall j b, nth_error l j = Some b -> R (a + 24 * Z.of_nat j) b (RPool (i + j)) -> R' (a + 24 * Z.of_nat j) b (RPool (i + j))) ->
  bns_gen R a l i -> bns_gen R' a l i.
Proof.
  intros R R' l. induction l as [|b l IH]; intros a i H HG; [exact I|].
  cbn [bns_gen] in *. destruct HG as [H1 H2]. split.
  - specialize (H 0%nat b eq_refl). rewrite Z.mul_0_r, Z.add_0_r, Nat.add_0_r in H. apply H. exact H1.
  - apply IH; [|exact H2]. intros j b' Hj HR. specialize (H (S j) b' Hj).
    replace (a + 24 * Z.of_nat (S j)) with (a + 24 + 24 * Z.of_nat j) in H by lia.
    replace (i + S j)%nat with (S i + j)%nat in H by lia. apply H. exact HR.
Qed.

Lemma bns_gen_nth : forall (R : bnR) l a i j d, bns_gen R a l i -> (j < length l)%nat ->
  R (a + 24 * Z.of_nat j) (nth j l d) (RPool (i + j)).
Proof.
  intros R l. induction l as [|b l IH]; intros a i j d HG Hj; cbn in Hj; [lia|].
  cbn [bns_gen] in HG. destruct HG as [H1 H2]. destruct j as [|j].
  - cbn [nth]. rewrite Z.mul_0_r, Z.add_0_r, Nat.add_0_r. exact H1.
  - cbn [nth]. replace (a + 24 * Z.of_nat (S j)) with (a + 24 + 24 * Z.of_nat j) by lia.
    replace (i + S j)%nat with (S i + j)%nat by lia. apply IH; [exact H2| lia].
Qed.

Lemma bns_gen_set : forall (R : bnR) l a i j b', bns_gen R a l i -> (j < length l)%nat ->
  R (a + 24 * Z.of_nat j) b' (RPool (i + j)) -> bns_gen R a (list_set l j b') i.
Proof.
  intros R l. induction l as [|b l IH]; intros a i j b' HG Hj HR; cbn in Hj; [lia|].
  cbn [bns_gen] in HG. destruct HG as [H1 H2]. destruct j as [|j]; cbn [list_set bns_gen].
  - rewrite Z.mul_0_r, Z.add_0_r, Nat.add_0_r in HR. split; assumption.
  - split; [exact H1|]. apply IH; [exact H2| lia|].
    replace (a + 24 + 24 * Z.of_nat j) with (a + 24 * Z.of_nat (S j)) by lia.
    replace (S i + j)%nat with (i + S j)%nat by lia. exact HR.
Qed.

Lemma nth_error_nth_d : forall {A} (l : list A) j b d, nth_error l j = Some b -> nth j l d = b.
Proof. intros A l j b d H. apply nth_error_nth. exact H. Qed.

Lemma gen_impl : forall (R R' : bnR) cxo ls m OW AD,
  (forall r a, ref_at ls OW AD r a -> valid_refm r ls -> R a (getbn r ls) r -> R' a (getbn r ls) r) ->
  bn_mem_gen R cxo ls m OW AD -> bn_mem_gen R' cxo ls m OW AD.
Proof.
  intros R R' cxo ls m OW AD HR (H0 & HB & H1 & H2 & H3 & H4 & H5 & HC).
  split; [exact H0|]. split; [exact HB|].
  split; [apply (HR RB1); [reflexivity| exact I| exact H1]|]. split; [apply (HR RB2); [reflexivity| exact I| exact H2]|].
  split; [apply (HR RB3); [reflexivity| exact I| exact H3]|]. split; [apply (HR RB4); [reflexivity| exact I| exact H4]|].
  split; [apply (HR RB5); [reflexivity| exact I| exact H5]|].
  destruct HC as (H & Cu & Ix & HCe & HPool & HPm). exists H, Cu, Ix. split; [exact HCe|]. split; [|exact HPm].
  destruct (cx_head (ls_ctx ls)) as [p|] eqn:Eh; [|exact HPool].
  destruct HPool as (Hin & Hlen & Hbns). split; [exact Hin|]. split; [exact Hlen|].
  eapply bns_gen_impl; [|exact Hbns]. intros j b Hj HRj. cbn [Nat.add] in *.
  assert (Hj16 : (j < 16)%nat) by (rewrite <- Hlen; apply nth_error_Some; congruence).
  pose proof (HR (RPool j) (H + 24 * Z.of_nat j)) as HRp. cbn [getbn] in HRp.
  rewrite (nth_error_nth_d _ _ _ (bn_nil 0) Hj) in HRp. apply HRp; [|cbn [valid_refm]; lia| exact HRj].
  exists p, H. auto.
Qed.

Lemma gen_get : forall (R : bnR) cxo ls m OW AD r a,
  bn_mem_gen R cxo ls m OW AD -> List.NoDup (map blk_id OW) -> ref_at ls OW AD r a -> R a (getbn r ls) r.
Proof.
  intros R cxo ls m OW AD r a (H0 & HB & H1 & H2 & H3 & H4 & H5 & HC) ND HA.
  destruct r as [| | | | |i]; cbn [ref_at getbn] in *; subst; try assumption.
  destruct HA as (p & H & Eh & Hin & Hi & ->). destruct HC as (H' & Cu & Ix & _ & HPool & _).
  rewrite Eh in HPool. destruct HPool as (Hin' & Hlen & Hbns).
  destruct (RH_addr_unique OW p H 400 H' 400 ND Hin Hin') as [-> _].
  apply (bns_gen_nth R _ H' 0%nat i (bn_nil 0) Hbns). lia.
Qed.

Lemma ctx_cells_set_vals : forall H Cu I c v, ctx_cells H Cu I (ctx_set_vals c v) = ctx_cells H Cu I c.
Proof. reflexivity. Qed.

Lemma pool_mem_set_vals : forall m H Cu c v, pool_mem m H Cu (ctx_set_vals c v) = pool_mem m H Cu c.
Proof. reflexivity. Qed.

Lemma stack_rep_set_vals : forall m OW I c v, stack_rep m OW I (ctx_set_vals c v) = stack_rep m OW I c.
Proof. reflexivity. Qed.

Lemma gen_set : forall (R : bnR) cxo ls m OW AD r a b',
  bn_mem_gen R cxo ls m OW AD -> List.NoDup (map blk_id OW) -> ref_at ls OW AD r a -> R a b' r ->
  bn_mem_gen R cxo (setbn r b' ls) m OW AD.
Proof.
  intros R cxo ls m OW AD r a b' (H0 & HB & H1 & H2 & H3 & H4 & H5 & HC) ND HA HR.
  destruct r as [| | | | |i]; cbn [ref_at] in HA; subst;
    try (unfold bn_mem_gen; cbn [setbn ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx]; tauto).
  destruct HA as (p & H & Eh & Hin & Hi & ->). destruct HC as (H' & Cu & Ix & HCe & HPool & HPm).
  unfold bn_mem_gen. cbn [setbn set_ctx ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx].
  repeat (split; [assumption|]). exists H', Cu, Ix. rewrite ctx_cells_set_vals, stack_rep_set_vals. split; [exact HCe|].
  unfold pool_gen. rewrite pool_mem_set_vals. split; [|exact HPm].
  cbn [ctx_set_vals cx_head cx_vals cx_current]. rewrite Eh in *.
  destruct HPool as (Hin' & Hlen & Hbns).
  destruct (RH_addr_unique OW p H 400 H' 400 ND Hin Hin') as [-> _].
  split; [exact Hin'|]. split; [rewrite list_set_length; exact Hlen|].
  apply bns_gen_set; [exact Hbns| lia| exact HR].
Qed.

Lemma ref_at_setbn : forall ls OW AD r b r' a, ref_at (setbn r b ls) OW AD r' a <-> ref_at ls OW AD r' a.
Proof.
  intros ls OW AD r b r' a. destruct r' as [| | | | |j]; cbn [ref_at]; try tauto.
  destruct (ctx_same_setbn r b ls) as (A1 & _). rewrite A1. tauto.
Qed.

End WithCeiling0.

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition libw (a : Z) : Prop := rin_ivs LIBW_bn a.

Definition err_fp (OW : list block) (EA : err_addrs) (x : Z) : Prop :=
  (ea_MK EA <= x < ea_MK EA + 72) \/ (ea_SA EA <= x < ea_SA EA + 32) \/ (ea_ND EA <= x < ea_ND EA + 128) \/ (ea_ES EA <= x < ea_ES EA + 904).

Definition cx_fp (ls : lstate bptr) (OW : list block) (AD : bn_addrs) (x : Z) : Prop :=
  (ad_ctx AD <= x < ad_ctx AD + 72)
  \/ (exists p H, cx_head (ls_ctx ls) = Some p /\ In (p, H, 400) OW /\ H + 384 <= x < H + 400)
  \/ (exists q I, cx_indexes (ls_ctx ls) = Some q /\ In (q, I, 128) OW /\ I <= x < I + 128).

Definition own_fpc (cxo : bool) (hs : list bnref) (ls : lstate bptr) (OW : list block) (AD : bn_addrs) (EA : err_addrs) (x : Z) : Prop :=
  libw x
  \/ (exists r a, ref_at ls OW AD r a /\ valid_refm r ls /\ ~ In r hs /\ bn_fp OW a (getbn r ls) x)
  \/ (cxo = false /\ cx_fp ls OW AD x)
  \/ err_fp OW EA x.

Ltac in_libw := intros ? ?; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; cbn in *; lia.

Lemma crypto_statics_agree : forall P m m', agree_on P m m' -> (forall a, libw a -> P a) -> crypto_statics m -> crypto_statics m'.
Proof.
  intros P m m' AG HP (H1 & H2 & H3 & H4 & H5 & H6).
  unfold crypto_statics, CR_GOT_MALLOC, CR_GOT_FREE, CR_MEMSET_FUNC, CR_MALLOC_IMPL, CR_FREE_IMPL, CR_NO_CUSTOMIZE in *.
  repeat split; (eapply ro_cells_agree; [exact AG| eassumption|]); intros a Ha; apply HP; revert a Ha; in_libw.
Qed.

Lemma err_statics_agree : forall P m m', agree_on P m m' -> (forall a, libw a -> P a) -> err_statics m -> err_statics m'.
Proof.
  intros P m m' AG HP (H1 & H2 & H3 & H4 & H5).
  unfold err_statics, OI_STOPPED, OI_OPTSDONE, OI_BASE_ONCE, TL_MASTER_ONCE, TCB_TSD in *.
  repeat split; (eapply ro_cells_agree; [exact AG| eassumption|]); intros a Ha; apply HP; revert a Ha; in_libw.
Qed.

Lemma err_mem_agree : forall P m m' OW OW' EA,
  agree_on P m m' -> (forall a, libw a -> P a) -> (forall x, err_fp OW EA x -> P x) ->
  (forall q A n, In q (ea_ids EA) -> In (q, A, n) OW -> In (q, A, n) OW') ->
  err_mem m OW EA -> err_mem m' OW' EA.
Proof.
  intros P m m' OW OW' EA AG HL HP HOW (I1 & I2 & I3 & I4 & H1 & H2 & (pad & H3) & H4 & H5).
  unfold err_mem, err_fp, ea_ids in *.
  split; [apply HOW; [cbn; tauto| exact I1]|]. split; [apply HOW; [cbn; tauto| exact I2]|].
  split; [apply HOW; [cbn; tauto| exact I3]|]. split; [apply HOW; [cbn; tauto| exact I4]|].
  split. { eapply ro_cells_agree; [exact AG| exact H1|]. intros a Ha. apply HL. revert a Ha. unfold TSD_MAIN. in_libw. }
  split. { eapply ro_cells_agree; [exact AG| exact H2|]. intros a Ha. apply HP. cbn in Ha. lia. }
  split. { exists pad. eapply ro_cells_agree; [exact AG| exact H3|]. intros a Ha. apply HP. cbn in Ha. lia. }
  split. { eapply ro_cells_agree; [exact AG| exact H4|]. intros a Ha. apply HP. cbn in Ha. lia. }
  eapply rw_cells_agree; [exact AG| exact H5|]. intros a Ha. apply HP. cbn in Ha. lia.
Qed.

Lemma ossl_exit_cells_agree : forall P m m', agree_on P m m' -> (forall a, libw a -> P a) -> ossl_exit_cells m -> ossl_exit_cells m'.
Proof.
  intros P m m' AG HP (b0 & H1 & H2). exists b0. unfold OSSL_BASE_INITED, OSSL_DO_GLOBAL_CLEANUP in *.
  split; (eapply rw_cells_agree; [exact AG| eassumption|]); intros a Ha; apply HP; revert a Ha; in_libw.
Qed.

Lemma gen_transport : forall P (R R' : bnR) cxo ls m m' OW OW' AD,
  bn_mem_gen R cxo ls m OW AD -> agree_on P m m' ->
  (forall x, libw x -> P x) ->
  (cxo = false -> forall x, ad_ctx AD <= x < ad_ctx AD + 72 -> P x) ->
  (forall p H, cx_head (ls_ctx ls) = Some p -> In (p, H, 400) OW -> In (p, H, 400) OW' /\ (cxo = false -> forall x, H + 384 <= x < H + 400 -> P x)) ->
  (cxo = false -> forall q I, cx_indexes (ls_ctx ls) = Some q -> In (q, I, 128) OW -> In (q, I, 128) OW' /\ forall x, I <= x < I + 128 -> P x) ->
  ad_blocks OW' AD ->
  (forall r a, ref_at ls OW AD r a -> valid_refm r ls -> R a (getbn r ls) r -> R' a (getbn r ls) r) ->
  bn_mem_gen R' cxo ls m' OW' AD.
Proof.
  intros P R R' cxo ls m m' OW OW' AD HG AG HL HCx HHd HIx HB' HR.
  apply (gen_impl R R' cxo ls m OW AD HR) in HG. destruct HG as (H0 & HB & H1 & H2 & H3 & H4 & H5 & HC).
  split. { eapply ro_cells_agree; [exact AG| exact H0|]. intros x Hx. apply HL. revert x Hx. unfold BN_STATICS. in_libw. }
  split; [exact HB'|]. repeat (split; [assumption|]).
  destruct HC as (H & Cu & Ix & HCe & HPool & HPm). exists H, Cu, Ix. split; [|split].
  - intros Ec. destruct (HCe Ec) as [HCe1 HSt]. split.
    + eapply rw_cells_agree; [exact AG| exact HCe1|]. intros x Hx. apply (HCx Ec). cbn in Hx. lia.
    + unfold stack_rep in *. destruct (cx_indexes (ls_ctx ls)) as [q|] eqn:Eq; [|exact HSt].
      destruct HSt as (Hin & Hsz & stale & Hlen & Harr). destruct (HIx Ec q Ix eq_refl Hin) as [Hin' HPi].
      split; [exact Hin'|]. split; [exact Hsz|]. exists stale. split; [exact Hlen|].
      eapply u32arr_agree; [exact AG| exact Harr|]. intros x Hx. apply HPi. rewrite length_app, length_map in Hx. lia.
  - destruct (cx_head (ls_ctx ls)) as [p|] eqn:Eh; [|exact HPool].
    destruct HPool as (Hin & Hlen & Hbns). destruct (HHd p H eq_refl Hin) as [Hin' _]. split; [exact Hin'|]. split; assumption.
  - intros Ec. specialize (HPm Ec). unfold pool_mem in *. destruct (cx_head (ls_ctx ls)) as [p|] eqn:Eh; [|exact HPm].
    destruct HPm as (Hpn & Hcur). split; [|exact Hcur].
    destruct HPool as (Hin & _). destruct (HHd p H eq_refl Hin) as [_ HPt].
    eapply rw_cells_agree; [exact AG| exact Hpn|]. intros x Hx. apply (HPt Ec). cbn in Hx. lia.
Qed.

Theorem lib_state_hc_agree : forall cxo hs ls m m' OW AD EA,
  lib_state_hc cxo hs ls m OW AD EA -> agree_on (own_fpc cxo hs ls OW AD EA) m m' -> lib_state_hc cxo hs ls m' OW AD EA.
Proof.
  intros cxo hs ls m m' OW AD EA (HC & (HE1 & HE2) & HO & (S1 & S3 & HM)) AG.
  assert (HL : forall a, libw a -> own_fpc cxo hs ls OW AD EA a) by (intros a Ha; left; exact Ha).
  split; [eapply crypto_statics_agree; eauto|].
  split. { split; [eapply err_statics_agree; eauto|]. eapply err_mem_agree; [exact AG| exact HL| | | exact HE2]; [|auto].
           intros x Hx. do 3 right. exact Hx. }
  split; [eapply ossl_exit_cells_agree; eauto|]. split; [exact S1|]. split; [exact S3|].
  pose proof HM as (_ & HB & _).
  eapply gen_transport; [exact HM| exact AG| exact HL| | | | exact HB|].
  - intros Ec x Hx. right; right; left. split; [exact Ec|]. left. exact Hx.
  - intros p H Eh Hin. split; [exact Hin|]. intros Ec x Hx. right; right; left. split; [exact Ec|]. right; left. exists p, H. auto.
  - intros Ec q I Eq Hin. split; [exact Hin|]. intros x Hx. right; right; left. split; [exact Ec|]. right; right. exists q, I. auto.
  - intros r a HA HV [Hh|HRp]; [left; exact Hh|]. destruct (in_dec_bnref r hs) as [Hi|Hn]; [left; exact Hi|]. right.
    eapply bn_rep_transport; [exact AG| | | exact HRp]; [|auto].
    intros x Hx. right; left. exists r, a. auto.
Qed.

Definition lib_state_h_agree := lib_state_hc_agree false.

End WithCeiling1.
Notation own_fp := (own_fpc false).

Section WithCeiling2. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition ids_ok (ls : lstate bptr) (AD : bn_addrs) (EA : err_addrs) : Prop :=
  List.NoDup (ad_ids AD ++ ea_ids EA ++ map fst (blocks_of ls)).

Definition ref_sid (ls : lstate bptr) (AD : bn_addrs) (r : bnref) : option bptr :=
  match r with
  | RB1 => Some (ad_p1 AD) | RB2 => Some (ad_p2 AD) | RB3 => Some (ad_p3 AD) | RB4 => Some (ad_p4 AD) | RB5 => Some (ad_p5 AD)
  | RPool _ => cx_head (ls_ctx ls)
  end.

Lemma ref_at_inb : forall ls OW AD r a, ad_blocks OW AD -> ref_at ls OW AD r a ->
  exists q A n, ref_sid ls AD r = Some q /\ In (q, A, n) OW /\ A <= a /\ a + 24 <= A + n.
Proof.
  intros ls OW AD r a (B1 & B2 & B3 & B4 & B5 & BC) HA. destruct r as [| | | | |i]; cbn [ref_at ref_sid] in *; subst.
  - exists (ad_p1 AD), (ad_b1 AD), 24. split; [reflexivity|]. split; [exact B1| lia].
  - exists (ad_p2 AD), (ad_b2 AD), 24. split; [reflexivity|]. split; [exact B2| lia].
  - exists (ad_p3 AD), (ad_b3 AD), 24. split; [reflexivity|]. split; [exact B3| lia].
  - exists (ad_p4 AD), (ad_b4 AD), 24. split; [reflexivity|]. split; [exact B4| lia].
  - exists (ad_p5 AD), (ad_b5 AD), 24. split; [reflexivity|]. split; [exact B5| lia].
  - destruct HA as (p & H & Eh & Hin & Hi & ->). exists p, H, 400. split; [exact Eh|]. split; [exact Hin| lia].
Qed.

Lemma ref_sid_cases : forall ls AD r q, ref_sid ls AD r = Some q ->
  (In q [ad_p1 AD; ad_p2 AD; ad_p3 AD; ad_p4 AD; ad_p5 AD] /\ (forall i, r <> RPool i)) \/ (cx_head (ls_ctx ls) = Some q /\ exists i, r = RPool i).
Proof.
  intros ls AD r q H. destruct r as [| | | | |i]; cbn [ref_sid] in H; try (injection H as <-; left; split; [cbn; tauto| congruence]).
  right. split; [exact H| exists i; reflexivity].
Qed.

Lemma ref_sid_inj : forall ls AD r r' q, List.NoDup (ad_ids AD) -> ref_sid ls AD r = Some q -> ref_sid ls AD r' = Some q ->
  (forall i, r <> RPool i) -> (forall i, r' <> RPool i) -> r = r'.
Proof.
  intros ls AD r r' q ND E E' Hn Hn'. unfold ad_ids in ND.
  assert (N : ad_p1 AD <> ad_p2 AD /\ ad_p1 AD <> ad_p3 AD /\ ad_p1 AD <> ad_p4 AD /\ ad_p1 AD <> ad_p5 AD
              /\ ad_p2 AD <> ad_p3 AD /\ ad_p2 AD <> ad_p4 AD /\ ad_p2 AD <> ad_p5 AD
              /\ ad_p3 AD <> ad_p4 AD /\ ad_p3 AD <> ad_p5 AD /\ ad_p4 AD <> ad_p5 AD).
  { repeat (apply NoDup_cons_iff in ND; destruct ND as [? ND]). cbn [In] in *. clear - H H0 H1 H2 H3. intuition congruence. }
  clear ND. destruct N as (N12 & N13 & N14 & N15 & N23 & N24 & N25 & N34 & N35 & N45).
  destruct r as [| | | | |j]; try (exfalso; eapply Hn; reflexivity); destruct r' as [| | | | |j']; try (exfalso; eapply Hn'; reflexivity);
    try reflexivity; cbn [ref_sid] in E, E'; exfalso; clear Hn Hn'; congruence.
Qed.

Lemma ids_ad_ea : forall ls AD EA q q', ids_ok ls AD EA -> In q (ad_ids AD) -> In q' (ea_ids EA) -> q <> q'.
Proof.
  intros ls AD EA q q' ND H1 H2 E. subst q'. unfold ids_ok in ND.
  eapply (nodup_app_disj _ _ q ND H1). apply in_or_app. left. exact H2.
Qed.
Lemma ids_ad_m : forall ls AD EA q q', ids_ok ls AD EA -> In q (ad_ids AD) -> In q' (map fst (blocks_of ls)) -> q <> q'.
Proof.
  intros ls AD EA q q' ND H1 H2 E. subst q'. unfold ids_ok in ND.
  eapply (nodup_app_disj _ _ q ND H1). apply in_or_app. right. exact H2.
Qed.
Lemma ids_ea_m : forall ls AD EA q q', ids_ok ls AD EA -> In q (ea_ids EA) -> In q' (map fst (blocks_of ls)) -> q <> q'.
Proof.
  intros ls AD EA q q' ND H1 H2 E. subst q'. unfold ids_ok in ND. apply nodup_app_r in ND.
  eapply (nodup_app_disj _ _ q ND H1). exact H2.
Qed.
Lemma ids_m_nodup : forall ls AD EA, ids_ok ls AD EA -> List.NoDup (map fst (blocks_of ls)).
Proof. intros ls AD EA ND. unfold ids_ok in ND. apply nodup_app_r in ND. apply nodup_app_r in ND. exact ND. Qed.
Lemma ids_ad_nodup : forall ls AD EA, ids_ok ls AD EA -> List.NoDup (ad_ids AD).
Proof. intros ls AD EA ND. unfold ids_ok in ND. apply nodup_app_l in ND. exact ND. Qed.

Lemma in5_ad : forall AD q, In q [ad_p1 AD; ad_p2 AD; ad_p3 AD; ad_p4 AD; ad_p5 AD] -> In q (ad_ids AD).
Proof. intros AD q H. unfold ad_ids. cbn in *. tauto. Qed.

Lemma in5_neq_pc : forall ls AD EA q, ids_ok ls AD EA -> In q [ad_p1 AD; ad_p2 AD; ad_p3 AD; ad_p4 AD; ad_p5 AD] -> q <> ad_pc AD.
Proof.
  intros ls AD EA q ND H E. apply ids_ad_nodup in ND. unfold ad_ids in ND.
  change [ad_p1 AD; ad_p2 AD; ad_p3 AD; ad_p4 AD; ad_p5 AD; ad_pc AD] with ([ad_p1 AD; ad_p2 AD; ad_p3 AD; ad_p4 AD; ad_p5 AD] ++ [ad_pc AD]) in ND.
  eapply (nodup_app_disj _ _ q ND H). left. symmetry. exact E.
Qed.

Lemma head_in_m : forall (ls : lstate bptr) h, cx_head (ls_ctx ls) = Some h -> In h (map fst (blocks_of ls)).
Proof. intros ls h H. apply blocks_of_In_head in H. apply (in_map fst) in H. exact H. Qed.
Lemma idx_in_m : forall (ls : lstate bptr) q, cx_indexes (ls_ctx ls) = Some q -> In q (map fst (blocks_of ls)).
Proof. intros ls q H. apply blocks_of_In_idx in H. apply (in_map fst) in H. exact H. Qed.
Lemma bn_in_m : forall r (ls : lstate bptr) p, valid_refm r ls -> bn_d (getbn r ls) = Some p -> In p (map fst (blocks_of ls)).
Proof. intros r ls p Hv H. apply (blocks_of_In_bn r ls p Hv) in H. apply (in_map fst) in H. exact H. Qed.

Section Disj.
  Variables (s : PState) (OW LB : list block) (m : mem).
  Hypothesis HEAP : RHEAP s (OW ++ LB) m.

  Lemma blk_excl : forall q1 A1 n1 q2 A2 n2 x,
    In (q1, A1, n1) OW -> In (q2, A2, n2) OW -> q1 <> q2 -> A1 <= x < A1 + n1 -> A2 <= x < A2 + n2 -> False.
  Proof. intros q1 A1 n1 q2 A2 n2 x H1 H2 NE R1 R2. pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP H1 H2 NE). lia. Qed.

  Lemma blk_not_libw : forall q A n x, In (q, A, n) OW -> A <= x < A + n -> libw x -> False.
  Proof.
    intros q A n x Hin Hx HL. pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & _ & _ & _ & BI).
    revert HL. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia.
  Qed.

  Lemma blk_below_ceiling : forall q A n x, In (q, A, n) OW -> A <= x < A + n -> x < alloc_ceiling.
  Proof. intros q A n x Hin Hx. pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & _ & _ & BC & _). lia. Qed.

  Variables (ls : lstate bptr) (AD : bn_addrs) (EA : err_addrs).
  Hypothesis IDS : ids_ok ls AD EA.
  Hypothesis ADB : ad_blocks OW AD.

  Lemma struct_disj : forall r r' a a', r <> r' -> ref_at ls OW AD r a -> ref_at ls OW AD r' a' -> a + 24 <= a' \/ a' + 24 <= a.
  Proof.
    intros r r' a a' NE HA HA'.
    destruct (ref_at_inb _ _ _ _ _ ADB HA) as (q & A & n & Eq & Hin & R1 & R2).
    destruct (ref_at_inb _ _ _ _ _ ADB HA') as (q' & A' & n' & Eq' & Hin' & R1' & R2').
    destruct (decide (q = q')) as [E|NEq].
    2:{ pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP Hin Hin' NEq). lia. }
    subst q'. destruct (ref_sid_cases _ _ _ _ Eq) as [[H5 Hnp]|[Hh [i ->]]], (ref_sid_cases _ _ _ _ Eq') as [[H5' Hnp']|[Hh' [i' ->]]].
    -
      exfalso. apply NE. eapply ref_sid_inj; [eapply ids_ad_nodup; exact IDS| exact Eq| exact Eq'| exact Hnp| exact Hnp'].
    - exfalso. eapply (ids_ad_m _ _ _ q q IDS); [apply in5_ad; exact H5| apply head_in_m; exact Hh'| reflexivity].
    - exfalso. eapply (ids_ad_m _ _ _ q q IDS); [apply in5_ad; exact H5'| apply head_in_m; exact Hh| reflexivity].
    - cbn [ref_at] in HA, HA'. destruct HA as (p1 & H1 & E1 & I1 & L1 & ->), HA' as (p2 & H2 & E2 & I2 & L2 & ->).
      rewrite E1 in E2. injection E2 as <-. pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
      destruct (RH_addr_unique OW p1 H1 400 H2 400 ND I1 I2) as [<- _].
      assert (i <> i') by congruence. lia.
  Qed.

  Lemma struct_limbs_disj : forall r r' a p D n, ref_at ls OW AD r a -> valid_refm r' ls -> bn_d (getbn r' ls) = Some p ->
    In (p, D, n) OW -> a + 24 <= D \/ D + n <= a.
  Proof.
    intros r r' a p D n HA HV' Ed Hin.
    destruct (ref_at_inb _ _ _ _ _ ADB HA) as (q & A & nq & Eq & HinA & R1 & R2).
    assert (NE : q <> p).
    { pose proof (bn_in_m r' ls p HV' Ed) as Hm. destruct (ref_sid_cases _ _ _ _ Eq) as [[H5 _]|[Hh _]].
      - eapply ids_ad_m; eauto using in5_ad.
      - intros ->. eapply (ids_bn_head_neq r' ls p p); eauto using ids_m_nodup. }
    pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP HinA Hin NE). lia.
  Qed.

  Lemma limbs_limbs_disj : forall r r' p D n p' D' n', r <> r' -> valid_refm r ls -> valid_refm r' ls ->
    bn_d (getbn r ls) = Some p -> bn_d (getbn r' ls) = Some p' -> In (p, D, n) OW -> In (p', D', n') OW ->
    D + n <= D' \/ D' + n' <= D.
  Proof.
    intros r r' p D n p' D' n' NE HV HV' Ed Ed' Hin Hin'.
    assert (NEp : p <> p') by (eapply (ids_bn_neq r r' ls p p'); eauto using ids_m_nodup).
    exact (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP Hin Hin' NEp).
  Qed.

  Inductive w_okc (cxo : bool) (hs : list bnref) (iv : Z * Z) : Prop :=
  | w_stack : alloc_ceiling <= fst iv -> w_okc cxo hs iv
  | w_struct : forall r a, In r hs -> ref_at ls OW AD r a -> a <= fst iv -> snd iv <= a + 24 -> w_okc cxo hs iv
  | w_limbs : forall r p D, In r hs -> valid_refm r ls -> bn_d (getbn r ls) = Some p ->
                In (p, D, 8 * Z.of_nat (bn_dmax (getbn r ls))) OW -> D <= fst iv -> snd iv <= D + 8 * Z.of_nat (bn_dmax (getbn r ls)) ->
                w_okc cxo hs iv
  | w_foreign : forall q A n, In (q, A, n) (OW ++ LB) -> ~ In q (ad_ids AD ++ ea_ids EA ++ map fst (blocks_of ls)) ->
                A <= fst iv -> snd iv <= A + n -> w_okc cxo hs iv
  | w_cx : cxo = true -> (forall x, fst iv <= x < snd iv -> cx_fp ls OW AD x) -> w_okc cxo hs iv.

  Hypothesis ERRB : In (ea_pk EA, ea_MK EA, 72) OW /\ In (ea_ps EA, ea_SA EA, 32) OW /\ In (ea_pn EA, ea_ND EA, 128) OW /\ In (ea_pe EA, ea_ES EA, 904) OW.

  Lemma cx_fp_block : forall x, cx_fp ls OW AD x ->
    exists q A n, In (q, A, n) OW /\ A <= x < A + n /\ In q (ad_ids AD ++ ea_ids EA ++ map fst (blocks_of ls)).
  Proof.
    intros x [Hc|[(p & H & Eh & Hin & Hx)|(q & I & Eq & Hin & Hx)]].
    - destruct ADB as (_ & _ & _ & _ & _ & BC). exists (ad_pc AD), (ad_ctx AD), 72. split; [exact BC|]. split; [exact Hc|].
      apply in_or_app; left. unfold ad_ids. cbn. tauto.
    - exists p, H, 400. split; [exact Hin|]. split; [lia|]. apply in_or_app; right; apply in_or_app; right. apply head_in_m. exact Eh.
    - exists q, I, 128. split; [exact Hin|]. split; [exact Hx|]. apply in_or_app; right; apply in_or_app; right. apply idx_in_m. exact Eq.
  Qed.

  Lemma own_fp_block : forall cxo hs x, own_fpc cxo hs ls OW AD EA x ->
    libw x \/ exists q A n, In (q, A, n) OW /\ A <= x < A + n /\ In q (ad_ids AD ++ ea_ids EA ++ map fst (blocks_of ls)).
  Proof.
    intros cxo hs x [HL|[(r & a & HA & HV & Hn & [Hs|(p & D & Ed & Hin & Hx)])|[[_ Hc]|He]]].
    - left. exact HL.
    - right. destruct (ref_at_inb _ _ _ _ _ ADB HA) as (q & A & n & Eq & Hin & R1 & R2). exists q, A, n. split; [exact Hin|]. split; [lia|].
      destruct (ref_sid_cases _ _ _ _ Eq) as [[H5 _]|[Hh _]]; [apply in_or_app; left; apply in5_ad; exact H5|].
      apply in_or_app; right; apply in_or_app; right. apply head_in_m. exact Hh.
    - right. exists p, D, (8 * Z.of_nat (bn_dmax (getbn r ls))). split; [exact Hin|]. split; [exact Hx|].
      apply in_or_app; right; apply in_or_app; right. eapply bn_in_m; eauto.
    - right. apply cx_fp_block. exact Hc.
    - right. destruct ERRB as (E1 & E2 & E3 & E4). unfold err_fp in He.
      destruct He as [He|[He|[He|He]]]; [exists (ea_pk EA), (ea_MK EA), 72| exists (ea_ps EA), (ea_SA EA), 32| exists (ea_pn EA), (ea_ND EA), 128| exists (ea_pe EA), (ea_ES EA), 904];
        (split; [assumption|]); (split; [exact He|]); apply in_or_app; right; apply in_or_app; left; unfold ea_ids; cbn; tauto.
  Qed.

  Local Ltac std_lia__ := lia.
  Local Ltac clia := pose proof alloc_ceiling_range as CEIL_RANGE__; std_lia__.

  Lemma struct_not_cx : forall r a x, ref_at ls OW AD r a -> a <= x < a + 24 -> cx_fp ls OW AD x -> False.
  Proof.
    intros r a x HA Hx HC.
    destruct (ref_at_inb _ _ _ _ _ ADB HA) as (q & A & n & Eq & Hin & R1 & R2).
    assert (Hxb : A <= x < A + n) by lia.
    assert (Hq : In q (ad_ids AD) /\ q <> ad_pc AD /\ (forall i, r <> RPool i) \/ cx_head (ls_ctx ls) = Some q /\ exists i, r = RPool i).
    { destruct (ref_sid_cases _ _ _ _ Eq) as [[H5 Hnp]|Hh]; [left| right; exact Hh].
      split; [apply in5_ad; exact H5|]. split; [eapply in5_neq_pc; eauto| exact Hnp]. }
    destruct HC as [Hc|[(h & H & Eh & HinH & HxH)|(qi & I & Eqi & HinI & HxI)]].
    - destruct ADB as (_ & _ & _ & _ & _ & BC). eapply (blk_excl q A n (ad_pc AD) (ad_ctx AD) 72 x Hin BC); [|exact Hxb| exact Hc].
      destruct Hq as [(_ & Hne & _)|(Hh & _)]; [exact Hne|]. intros E. subst q.
      eapply (ids_ad_m _ _ _ (ad_pc AD) (ad_pc AD) IDS); [unfold ad_ids; cbn; tauto| apply head_in_m; exact Hh| reflexivity].
    - destruct Hq as [(Ha & _)|(Hh & i & ->)].
      + eapply (blk_excl q A n h H 400 x Hin HinH); [|exact Hxb| lia]. eapply ids_ad_m; eauto using head_in_m.
      + cbn [ref_at] in HA. destruct HA as (p1 & H1 & E1 & I1 & L1 & ->). rewrite E1 in Eh. injection Eh as <-.
        pose proof (RH_nodup_l _ _ _ _ HEAP) as ND. destruct (RH_addr_unique OW p1 H1 400 H 400 ND I1 HinH) as [<- _]. lia.
    - eapply (blk_excl q A n qi I 128 x Hin HinI); [|exact Hxb| exact HxI].
      destruct Hq as [(Ha & _)|(Hh & _)]; [eapply ids_ad_m; eauto using idx_in_m|].
      eapply ids_head_idx_neq; eauto using ids_m_nodup.
  Qed.

  Lemma limbs_not_cx : forall r p D x, valid_refm r ls -> bn_d (getbn r ls) = Some p ->
    In (p, D, 8 * Z.of_nat (bn_dmax (getbn r ls))) OW -> D <= x < D + 8 * Z.of_nat (bn_dmax (getbn r ls)) -> cx_fp ls OW AD x -> False.
  Proof.
    intros r p D x HV Ed Hin Hx HC.
    pose proof (bn_in_m r ls p HV Ed) as Hm. pose proof (ids_m_nodup _ _ _ IDS) as NDm.
    destruct HC as [Hc|[(h & H & Eh & HinH & HxH)|(qi & I & Eqi & HinI & HxI)]].
    - destruct ADB as (_ & _ & _ & _ & _ & BC). eapply (blk_excl p D _ (ad_pc AD) (ad_ctx AD) 72 x Hin BC); [|exact Hx| exact Hc].
      intros E. eapply (ids_ad_m _ _ _ (ad_pc AD) p IDS); [unfold ad_ids; cbn; tauto| exact Hm| congruence].
    - eapply (blk_excl p D _ h H 400 x Hin HinH); [|exact Hx| lia]. eapply (ids_bn_head_neq r ls p h); eauto.
    - eapply (blk_excl p D _ qi I 128 x Hin HinI); [|exact Hx| exact HxI]. eapply (ids_bn_idx_neq r ls p qi); eauto.
  Qed.

  Lemma err_not_block : forall q A n x, In (q, A, n) OW -> A <= x < A + n -> (forall q', In q' (ea_ids EA) -> q <> q') -> err_fp OW EA x -> False.
  Proof.
    intros q A n x Hin Hxb NEe He. destruct ERRB as (E1 & E2 & E3 & E4). unfold err_fp in He.
    destruct He as [He|[He|[He|He]]].
    - eapply (blk_excl q A n _ _ _ x Hin E1); [apply NEe; unfold ea_ids; cbn; tauto| exact Hxb| exact He].
    - eapply (blk_excl q A n _ _ _ x Hin E2); [apply NEe; unfold ea_ids; cbn; tauto| exact Hxb| exact He].
    - eapply (blk_excl q A n _ _ _ x Hin E3); [apply NEe; unfold ea_ids; cbn; tauto| exact Hxb| exact He].
    - eapply (blk_excl q A n _ _ _ x Hin E4); [apply NEe; unfold ea_ids; cbn; tauto| exact Hxb| exact He].
  Qed.

  Lemma own_fp_not_struct : forall cxo hs x r a, In r hs -> ref_at ls OW AD r a -> own_fpc cxo hs ls OW AD EA x -> a <= x < a + 24 -> False.
  Proof.
    intros cxo hs x r a Hr HA HO Hx.
    destruct (ref_at_inb _ _ _ _ _ ADB HA) as (q & A & n & Eq & Hin & R1 & R2).
    assert (Hxb : A <= x < A + n) by lia.
    destruct HO as [HL|[(r' & a' & HA' & HV' & Hn' & [Hs|(p' & D' & Ed' & Hin' & Hx')])|[[_ HC]|He]]].
    - eapply blk_not_libw; eauto.
    - assert (NE : r <> r') by (intros ->; contradiction). pose proof (struct_disj r r' a a' NE HA HA'). lia.
    - pose proof (struct_limbs_disj r r' a p' D' _ HA HV' Ed' Hin'). lia.
    - eapply struct_not_cx; eauto.
    - eapply (err_not_block q A n x Hin Hxb); [|exact He]. intros q' Hq'.
      destruct (ref_sid_cases _ _ _ _ Eq) as [[H5 _]|[Hh _]]; [eapply ids_ad_ea; eauto using in5_ad|].
      intros E. subst q'. eapply (ids_ea_m _ _ _ q q IDS); [exact Hq'| apply head_in_m; exact Hh| reflexivity].
  Qed.

  Lemma own_fp_not_limbs : forall cxo hs x r p D, In r hs -> valid_refm r ls -> bn_d (getbn r ls) = Some p ->
    In (p, D, 8 * Z.of_nat (bn_dmax (getbn r ls))) OW -> own_fpc cxo hs ls OW AD EA x ->
    D <= x < D + 8 * Z.of_nat (bn_dmax (getbn r ls)) -> False.
  Proof.
    intros cxo hs x r p D Hr HV Ed Hin HO Hx.
    pose proof (bn_in_m r ls p HV Ed) as Hm. pose proof (ids_m_nodup _ _ _ IDS) as NDm.
    destruct HO as [HL|[(r' & a' & HA' & HV' & Hn' & [Hs|(p' & D' & Ed' & Hin' & Hx')])|[[_ HC]|He]]].
    - eapply blk_not_libw; eauto.
    - pose proof (struct_limbs_disj r' r a' p D _ HA' HV Ed Hin). lia.
    - assert (NE : r <> r') by (intros ->; contradiction).
      pose proof (limbs_limbs_disj r r' p D _ p' D' _ NE HV HV' Ed Ed' Hin Hin'). lia.
    - eapply limbs_not_cx; eauto.
    - eapply (err_not_block p D _ x Hin Hx); [|exact He]. intros q' Hq' E. subst q'. eapply (ids_ea_m _ _ _ p p IDS); eauto.
  Qed.

  Lemma own_fp_not_cx : forall hs x, own_fpc true hs ls OW AD EA x -> cx_fp ls OW AD x -> False.
  Proof.
    intros hs x HO HC.
    destruct HO as [HL|[(r' & a' & HA' & HV' & Hn' & [Hs|(p' & D' & Ed' & Hin' & Hx')])|[[Ec _]|He]]]; [| | |discriminate|].
    - destruct (cx_fp_block x HC) as (q & A & n & Hin & Hxb & _). eapply blk_not_libw; eauto.
    - eapply struct_not_cx; eauto.
    - eapply limbs_not_cx; eauto.
    - destruct (cx_fp_block x HC) as (q & A & n & Hin & Hxb & Hq).

      eapply (err_not_block q A n x Hin Hxb); [|exact He]. intros q' Hq' E. subst q'.
      destruct HC as [Hc|[(h & H & Eh & HinH & HxH)|(qi & I & Eqi & HinI & HxI)]].
      + destruct ADB as (_ & _ & _ & _ & _ & BC).
        assert (q = ad_pc AD).
        { destruct (decide (q = ad_pc AD)) as [E|NE]; [exact E|]. exfalso. eapply (blk_excl q A n (ad_pc AD) (ad_ctx AD) 72 x Hin BC NE Hxb Hc). }
        subst q. eapply (ids_ad_ea _ _ _ (ad_pc AD) (ad_pc AD) IDS); [unfold ad_ids; cbn; tauto| exact Hq'| reflexivity].
      + assert (q = h).
        { destruct (decide (q = h)) as [E|NE]; [exact E|]. exfalso. eapply (blk_excl q A n h H 400 x Hin HinH NE Hxb). lia. }
        subst q. eapply (ids_ea_m _ _ _ h h IDS); [exact Hq'| apply head_in_m; exact Eh| reflexivity].
      + assert (q = qi).
        { destruct (decide (q = qi)) as [E|NE]; [exact E|]. exfalso. eapply (blk_excl q A n qi I 128 x Hin HinI NE Hxb HxI). }
        subst q. eapply (ids_ea_m _ _ _ qi qi IDS); [exact Hq'| apply idx_in_m; exact Eqi| reflexivity].
  Qed.

  Theorem own_fp_outside : forall cxo hs W x, Forall (w_okc cxo hs) W -> own_fpc cxo hs ls OW AD EA x -> outside W x.
  Proof.
    intros cxo hs W x HW HO. induction HW as [|[lo hi] W Hiv HW IH]; [exact I|]. cbn [outside]. split; [|exact IH].
    intros Hx. cbn [fst snd] in *. destruct Hiv as [Hs|r a Hr HA H1 H2|r p D Hr HV Ed Hin H1 H2|q A n Hin Hq H1 H2|Ec Hcx]; cbn [fst snd] in *.
    - destruct (own_fp_block cxo hs x HO) as [HL|(q & A & n & Hin & Hxb & _)].
      + revert HL. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. clia.
      + pose proof (blk_below_ceiling q A n x Hin Hxb). lia.
    - eapply (own_fp_not_struct cxo hs x r a); eauto. lia.
    - eapply (own_fp_not_limbs cxo hs x r p D); eauto. lia.
    - destruct (own_fp_block cxo hs x HO) as [HL|(q' & A' & n' & Hin' & Hxb' & Hq')].
      + pose proof (LH_block_range _ _ _ _ HEAP Hin) as (_ & _ & _ & _ & BI). cbn [blk_addr blk_size fst snd] in BI.
        revert HL. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia.
      + assert (NE : q' <> q) by (intros ->; contradiction).
        pose proof (LH_disjoint _ _ _ (q', A', n') (q, A, n) HEAP ltac:(apply in_or_app; left; exact Hin') Hin NE) as DJ.
        cbn [blk_addr blk_size fst snd] in DJ. lia.
    - subst cxo. eapply own_fp_not_cx; [exact HO| apply Hcx; exact Hx].
  Qed.

End Disj.
End WithCeiling2.
Notation w_ok OW LB ls AD EA := (w_okc OW LB ls AD EA false).

Section WithCeiling3. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition all_ids (ls : lstate bptr) (AD : bn_addrs) (EA : err_addrs) : list bptr := ad_ids AD ++ ea_ids EA ++ map fst (blocks_of ls).

Lemma lib_state_h_parts : forall cxo hs ls m OW AD EA, lib_state_hc cxo hs ls m OW AD EA ->
  ids_ok ls AD EA /\ ad_blocks OW AD
  /\ (In (ea_pk EA, ea_MK EA, 72) OW /\ In (ea_ps EA, ea_SA EA, 32) OW /\ In (ea_pn EA, ea_ND EA, 128) OW /\ In (ea_pe EA, ea_ES EA, 904) OW)
  /\ st_okm ls.
Proof.
  intros cxo hs ls m OW AD EA (_ & (_ & (I1 & I2 & I3 & I4 & _)) & _ & (S1 & S3 & (_ & HB & _))). auto 8.
Qed.

Theorem lib_state_frame : forall s LB cxo hs ls m m' OW AD EA W,
  RHEAP s (OW ++ LB) m -> lib_state_hc cxo hs ls m OW AD EA -> munch W m m' -> wmono bgusegs m m' ->
  Forall (w_okc OW LB ls AD EA cxo hs) W -> lib_state_hc cxo hs ls m' OW AD EA.
Proof.
  intros s LB cxo hs ls m m' OW AD EA W HEAP HS MU WM HW.
  destruct (lib_state_h_parts _ _ _ _ _ _ _ HS) as (IDS & ADB & ERRB & _).
  eapply lib_state_hc_agree; [exact HS|]. eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|].
  intros a Ha. eapply own_fp_outside; eauto.
Qed.

Theorem lib_state_h_ow : forall cxo hs ls m OW OW' AD EA,
  lib_state_hc cxo hs ls m OW AD EA ->
  (forall q A n, In q (all_ids ls AD EA) -> In (q, A, n) OW -> In (q, A, n) OW') ->
  lib_state_hc cxo hs ls m OW' AD EA.
Proof.
  intros cxo hs ls m OW OW' AD EA HS HOW. pose proof HS as (HC & (HE1 & HE2) & HO & (S1 & S3 & HM)).
  unfold all_ids in HOW.
  split; [exact HC|]. split.
  { split; [exact HE1|]. eapply err_mem_agree; [apply agree_on_refl| intros a Ha; exact I| intros x Hx; exact I| | exact HE2].
    intros q A n Hq. apply HOW. apply in_or_app; right; apply in_or_app; left; exact Hq. }
  split; [exact HO|]. split; [exact S1|]. split; [exact S3|].
  pose proof HM as (_ & (B1 & B2 & B3 & B4 & B5 & BC) & _).
  assert (HAD : forall q A n, In q (ad_ids AD) -> In (q, A, n) OW -> In (q, A, n) OW') by (intros q A n Hq; apply HOW; apply in_or_app; left; exact Hq).
  assert (HMI : forall q A n, In q (map fst (blocks_of ls)) -> In (q, A, n) OW -> In (q, A, n) OW')
    by (intros q A n Hq; apply HOW; apply in_or_app; right; apply in_or_app; right; exact Hq).
  eapply (gen_transport (fun _ => True)); [exact HM| apply agree_on_refl| auto| auto| | | |].
  - intros p H Eh Hin. split; [|auto]. apply HMI; [apply head_in_m; exact Eh| exact Hin].
  - intros _ q I Eq Hin. split; [|auto]. apply HMI; [apply idx_in_m; exact Eq| exact Hin].
  - unfold ad_blocks, ad_ids in *. repeat split; apply HAD; cbn; tauto.
  - intros r a HA HV [Hh|HR]; [left; exact Hh|]. right.
    eapply (bn_rep_transport (fun _ => True)); [apply agree_on_refl| auto| | exact HR].
    intros p D Ed Hin. apply HMI; [eapply bn_in_m; eauto| exact Hin].
Qed.

Lemma lib_state_h_incl : forall cxo hs hs' ls m OW AD EA,
  lib_state_hc cxo hs ls m OW AD EA -> (forall r, In r hs -> In r hs') -> lib_state_hc cxo hs' ls m OW AD EA.
Proof.
  intros cxo hs hs' ls m OW AD EA (HC & HE & HO & (S1 & S3 & HM)) Hi.
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|]. split; [exact S1|]. split; [exact S3|].
  eapply gen_impl; [|exact HM]. intros r a _ _ [Hh|HR]; [left; apply Hi; exact Hh| right; exact HR].
Qed.

Lemma ref_at_fun : forall ls OW AD r a a', List.NoDup (map blk_id OW) -> ref_at ls OW AD r a -> ref_at ls OW AD r a' -> a = a'.
Proof.
  intros ls OW AD r a a' ND H1 H2. destruct r as [| | | | |i]; cbn [ref_at] in *; try congruence.
  destruct H1 as (p1 & A1 & E1 & I1 & _ & ->), H2 as (p2 & A2 & E2 & I2 & _ & ->). rewrite E1 in E2. injection E2 as <-.
  destruct (RH_addr_unique OW p1 A1 400 A2 400 ND I1 I2) as [-> _]. reflexivity.
Qed.

Lemma ref_at_valid : forall cxo hs ls m OW AD EA r a, lib_state_hc cxo hs ls m OW AD EA -> ref_at ls OW AD r a -> valid_refm r ls.
Proof.
  intros cxo hs ls m OW AD EA r a (_ & _ & _ & (_ & _ & (_ & _ & _ & _ & _ & _ & _ & HC))) HA.
  destruct r as [| | | | |i]; cbn [valid_refm]; try exact I.
  destruct HA as (p & H & Eh & _ & Hi & _). destruct HC as (H' & Cu & Ix & _ & HPool & _).
  rewrite Eh in HPool. destruct HPool as (_ & Hlen & _). lia.
Qed.

Theorem lib_state_open : forall cxo hs ls m OW AD EA r a,
  lib_state_hc cxo hs ls m OW AD EA -> List.NoDup (map blk_id OW) -> ref_at ls OW AD r a -> ~ In r hs ->
  bn_rep m OW a (getbn r ls) /\ bn_okm (getbn r ls) /\ lib_state_hc cxo (r :: hs) ls m OW AD EA.
Proof.
  intros cxo hs ls m OW AD EA r a HS ND HA Hn. pose proof (ref_at_valid _ _ _ _ _ _ _ _ _ HS HA) as HV.
  pose proof HS as (_ & _ & _ & (S1 & _ & HM)).
  split; [|split].
  - destruct (gen_get _ _ _ _ _ _ _ _ HM ND HA) as [Hh|HR]; [contradiction| exact HR].
  - apply st_okm_getbn; assumption.
  - eapply lib_state_h_incl; [exact HS|]. intros r' Hr'. right. exact Hr'.
Qed.

Theorem lib_state_close : forall cxo hs ls m OW AD EA r a b',
  lib_state_hc cxo (r :: hs) ls m OW AD EA -> List.NoDup (map blk_id OW) -> ref_at ls OW AD r a ->
  bn_rep m OW a b' -> bn_okm b' -> ids_ok (setbn r b' ls) AD EA ->
  lib_state_hc cxo hs (setbn r b' ls) m OW AD EA.
Proof.
  intros cxo hs ls m OW AD EA r a b' HS ND HA HR HOK HIDS. pose proof (ref_at_valid _ _ _ _ _ _ _ _ _ HS HA) as HV.
  destruct HS as (HC & HE & HO & (S1 & S3 & HM)).
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split; [apply st_okm_setbn; assumption|]. split; [exact HIDS|].
  assert (HM2 : bn_mem_gen (holeR (r :: hs) m OW) cxo (setbn r b' ls) m OW AD) by (eapply gen_set; [exact HM| exact ND| exact HA| right; exact HR]).
  eapply gen_impl; [|exact HM2]. intros r' a' HA' HV' [Hh|HR']; [|right; exact HR'].
  destruct Hh as [<-|Hh]; [|left; exact Hh]. right.
  apply ref_at_setbn in HA'. rewrite (ref_at_fun _ _ _ _ _ _ ND HA' HA). rewrite getbn_setbn_same_m by exact HV. exact HR.
Qed.

Lemma own_fp_lib : forall cxo hs ls m OW AD EA x, lib_state_hc cxo hs ls m OW AD EA -> own_fpc cxo hs ls OW AD EA x -> rin_ivs LIBW_bn x \/ in_block OW x.
Proof.
  intros cxo hs ls m OW AD EA x HS HO. destruct (lib_state_h_parts _ _ _ _ _ _ _ HS) as (IDS & ADB & ERRB & _).
  destruct (own_fp_block OW ls AD EA ADB ERRB cxo hs x HO) as [HL|(q & A & n & Hin & Hx & _)]; [left; exact HL| right].
  eapply in_block_intro; eauto.
Qed.

Lemma libw_client : forall L SP x, libw x -> rclient_addr L SP x.
Proof.
  intros L SP x H. right; left. revert H. unfold libw, LIBW_bn, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. cbn [rin_ivs fst snd]. lia.
Qed.

Theorem lib_state_h_heap_pres : forall cxo hs ls m m' OW AD EA L SP,
  lib_state_hc cxo hs ls m OW AD EA -> rheap_pres L SP m m' -> (forall b, In b OW -> In b L) -> lib_state_hc cxo hs ls m' OW AD EA.
Proof.
  intros cxo hs ls m m' OW AD EA L SP HS HP HI. eapply lib_state_hc_agree; [exact HS|].
  eapply agree_on_mono; [apply agree_of_heap_pres; exact HP|]. intros a Ha.
  destruct (own_fp_lib _ _ _ _ _ _ _ _ HS Ha) as [HL|(b & Hb & Hr)]; [apply libw_client; exact HL|].
  right; right. exists b. split; [apply HI; exact Hb| exact Hr].
Qed.

Theorem lib_state_h_free : forall s LB cxo hs ls m m' OW AD EA r p D SP,
  RHEAP s (OW ++ LB) m -> lib_state_hc cxo hs ls m OW AD EA -> In r hs -> valid_refm r ls -> bn_d (getbn r ls) = Some p ->
  In (p, D, 8 * Z.of_nat (bn_dmax (getbn r ls))) OW ->
  rheap_pres (lb_remove p (OW ++ LB)) SP m m' ->
  lib_state_hc cxo hs ls m' (lb_remove p OW) AD EA.
Proof.
  intros s LB cxo hs ls m m' OW AD EA r p D SP HEAP HS Hr HV Ed Hin HP.
  destruct (lib_state_h_parts _ _ _ _ _ _ _ HS) as (IDS & ADB & ERRB & SOK).
  pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
  assert (HS' : lib_state_hc cxo hs ls m' OW AD EA).
  { eapply lib_state_hc_agree; [exact HS|]. eapply agree_on_mono; [apply agree_of_heap_pres; exact HP|]. intros a Ha.
    destruct (own_fp_block OW ls AD EA ADB ERRB cxo hs a Ha) as [HL|(q & A & n & Hq & Hx & _)]; [apply libw_client; exact HL|].
    right; right. exists (q, A, n). split; [|exact Hx]. apply lb_remove_In. split; [apply in_or_app; left; exact Hq|].
    cbn [blk_id fst]. intros ->. destruct (RH_addr_unique OW p A n D _ ND Hq Hin) as [-> ->].
    eapply (own_fp_not_limbs s OW LB m HEAP ls AD EA IDS ADB ERRB cxo hs a r p D); eauto. }

  pose proof HS' as (HC & (HE1 & HE2) & HO & (S1 & S3 & HM)).
  pose proof (bn_in_m r ls p HV Ed) as Hpm. pose proof (ids_m_nodup _ _ _ IDS) as NDm.
  assert (KEEP : forall q A n, q <> p -> In (q, A, n) OW -> In (q, A, n) (lb_remove p OW)) by (intros q A n NE H; apply lb_remove_In; split; [exact H| exact NE]).
  split; [exact HC|]. split.
  { split; [exact HE1|]. eapply err_mem_agree; [apply agree_on_refl| intros a Ha; exact I| intros x Hx; exact I| | exact HE2].
    intros q A n Hq. apply KEEP. intros ->. eapply (ids_ea_m _ _ _ p p IDS); eauto. }
  split; [exact HO|]. split; [exact S1|]. split; [exact S3|].
  eapply (gen_transport (fun _ => True)); [exact HM| apply agree_on_refl| auto| auto| | | |].
  - intros h H Eh HinH. split; [|auto]. apply KEEP; [|exact HinH]. intros ->. eapply (ids_bn_head_neq r ls p p); eauto.
  - intros _ q I Eq HinI. split; [|auto]. apply KEEP; [|exact HinI]. intros ->. eapply (ids_bn_idx_neq r ls p p); eauto.
  - destruct ADB as (B1 & B2 & B3 & B4 & B5 & BC).
    assert (NA : forall q, In q (ad_ids AD) -> q <> p) by (intros q Hq ->; eapply (ids_ad_m _ _ _ p p IDS); eauto).
    unfold ad_blocks, ad_ids in *. repeat split; (apply KEEP; [apply NA; cbn; tauto| assumption]).
  - intros r' a' HA' HV' [Hh|HR]; [left; exact Hh|]. destruct (in_dec_bnref r' hs) as [Hi|Hni]; [left; exact Hi|]. right.
    eapply (bn_rep_transport (fun _ => True)); [apply agree_on_refl| auto| | exact HR].
    intros p' D' Ed' Hin'. apply KEEP; [|exact Hin']. intros ->. assert (NE : r <> r') by (intros ->; contradiction).
    eapply (ids_bn_neq r r' ls p p); eauto.
Qed.

End WithCeiling3.
Arguments lib_state_h_parts {cxo}.
Arguments lib_state_frame {CE__ RN__} s LB {cxo}.
Arguments lib_state_h_ow {cxo}.
Arguments lib_state_h_incl {cxo}.
Arguments ref_at_valid {cxo}.
Arguments lib_state_open {cxo}.
Arguments lib_state_close {cxo}.
Arguments lib_state_h_heap_pres {cxo}.
Arguments lib_state_h_free {CE__ RN__} s LB {cxo}.
Arguments own_fp_lib {cxo}.

Definition BN_NEW_BYTES : list byte := repeat (Z_to_bv 8 0) 20 ++ [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].

Definition init_facts (m : mem) (OW : list block) : Prop :=
  exists (AD : bn_addrs) (EA : err_addrs),
    List.NoDup (ad_ids AD ++ ea_ids EA)
    /\ ad_blocks OW AD
    /\ ro_cells bgusegs m BN_STATICS (ad_cells AD)
    /\ rw_cells bgusegs m (ad_b1 AD) [CB 24 BN_NEW_BYTES] /\ rw_cells bgusegs m (ad_b2 AD) [CB 24 BN_NEW_BYTES]
    /\ rw_cells bgusegs m (ad_b3 AD) [CB 24 BN_NEW_BYTES] /\ rw_cells bgusegs m (ad_b4 AD) [CB 24 BN_NEW_BYTES]
    /\ rw_cells bgusegs m (ad_b5 AD) [CB 24 BN_NEW_BYTES]
    /\ rw_cells bgusegs m (ad_ctx AD) [CB 72 (repeat (Z_to_bv 8 0) 72)]
    /\ crypto_statics m /\ err_inv m OW EA /\ ossl_exit_cells m.

Section WithCeiling4. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma same_id_same_block : forall (OW : list block) (b b' : block),
  List.NoDup (map blk_id OW) -> In b OW -> In b' OW -> blk_id b' = blk_id b -> b' = b.
Proof.
  induction OW as [|c OW IH]; intros b b' ND I1 I2 E; [contradiction|].
  cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [Hc ND].
  destruct I1 as [->|I1], I2 as [->|I2]; [reflexivity| | |auto].
  - exfalso. apply Hc. rewrite <- E. apply in_map. exact I2.
  - exfalso. apply Hc. rewrite E. apply in_map. exact I1.
Qed.

Lemma nodup_ids_of_addrs : forall (OW : list block) (bs : list block),
  List.NoDup (map blk_id OW) -> incl bs OW -> List.NoDup (map blk_addr bs) -> List.NoDup (map blk_id bs).
Proof.
  intros OW bs ND HI NA. induction bs as [|b bs IH]; [constructor|].
  cbn [map] in *. apply NoDup_cons_iff in NA. destruct NA as [Hb NA]. constructor.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as (b' & E & Hb').
    assert (b' = b) by (eapply same_id_same_block; [exact ND| apply HI; left; reflexivity| apply HI; right; exact Hb'| exact E]).
    subst b'. apply Hb. apply in_map. exact Hb'.
  - apply IH; [|exact NA]. intros x Hx. apply HI. right. exact Hx.
Qed.

End WithCeiling4.

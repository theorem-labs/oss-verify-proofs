(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require EvtBridge Nodes.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.EvtBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocCover.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock BzCDriver. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD BzCLemmas1 CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpArith2 CmpSess CmpSessB CmpLaws CmpLawsB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzInv CmpCarve. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCEmit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzRT1 BzRT S0_cmp_cb S0_b2c_bzc S0_b2c_segA S0_b2c_segB S0_b2c_segC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import U.S0B2BCStmt.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import ZBridge.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParamsLia.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParamsLia.BzParamsX.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil} {RUNW__ : RunW}.
Hypothesis HBS : CmpCut6.blockSort_spec2 BzCLemmasMs6.bsX S0C.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lb_remove_cons : forall p b l, lb_remove p (b :: l) = if bid_eqb (blk_id b) p then lb_remove p l else b :: lb_remove p l.
Proof. intros p b l. unfold lb_remove. cbn. destruct (bid_eqb (blk_id b) p); reflexivity. Qed.
Lemma lb_remove_notin : forall p l, ~ In p (map blk_id l) -> lb_remove p l = l.
Proof.
  induction l as [|b l IH]; intros H; [reflexivity|].
  rewrite lb_remove_cons. destruct (bid_eqb_spec (blk_id b) p) as [E|NE].
  - exfalso. apply H. left. exact E.
  - f_equal. apply IH. intros H'. apply H. right. exact H'.
Qed.
(* [comment removed for export] *)
Lemma nodup_mid : forall (l1 : list bid) (x : bid) (l2 : list bid), NoDup (l1 ++ x :: l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros l1 x l2 ND. apply (proj1 (stdpp.list_relations.list.NoDup_app l1 (x :: l2))) in ND. cps_destruct ND as (N1 & N12 & N2).
  apply (proj1 (stdpp.list_relations.list.NoDup_cons x l2)) in N2. destruct N2 as [N2 _]. split.
  - intros H. apply (N12 x); [apply list_elem_of_In; exact H | apply list_elem_of_In; left; reflexivity].
  - intros H. apply N2. apply list_elem_of_In. exact H.
Qed.
Lemma lb_remove_app : forall p l1 l2, lb_remove p (l1 ++ l2) = lb_remove p l1 ++ lb_remove p l2.
Proof. intros p l1 l2. unfold lb_remove. apply List.filter_app. Qed.
Lemma lb_remove_mid : forall p A n L1 L2, NoDup (map blk_id (L1 ++ (p, A, n) :: L2)) ->
  lb_remove p (L1 ++ (p, A, n) :: L2) = L1 ++ L2.
Proof.
  intros p A n L1 L2 ND. rewrite map_app in ND. cbn [map blk_id fst] in ND. destruct (nodup_mid _ _ _ ND) as [N1 N2].
  rewrite lb_remove_app, lb_remove_cons. cbn [blk_id fst]. rewrite bid_eqb_refl.
  rewrite !lb_remove_notin by assumption. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma size_CB1 : forall k bs, Z.of_nat (cells_size [CB k bs]) = Z.of_nat k.
Proof. intros. cbn. lia. Qed.
Lemma repeat_zero : forall n i (b : byte), nth_error (repeat (Z_to_bv 8 0) n) i = Some b -> b = Z_to_bv 8 0.
Proof. intros n i b H. apply nth_error_In in H. apply repeat_spec in H. exact H. Qed.

Lemma disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof. induction W as [|[l h] W IH]; intros a n a' n' H H1 H2; cbn in *; [exact I|]. destruct H as [H0 H3]. split; [lia| eapply IH; eauto]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pres (P : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall a : Z, 0 <= a < 2 ^ 64 -> P a ->
    m' (wa a) = m (wa a) /\ (wview s0segs m (wa a) <> None -> wview s0segs m' (wa a) <> None).
Lemma pres_refl : forall P m, pres P m m.
Proof. intros P m a _ _. auto. Qed.
Lemma pres_trans : forall P m1 m2 m3, pres P m1 m2 -> pres P m2 m3 -> pres P m1 m3.
Proof.
  intros P m1 m2 m3 H1 H2 a Ha HP. destruct (H1 a Ha HP) as [E1 W1]. destruct (H2 a Ha HP) as [E2 W2]. split; [congruence|auto].
Qed.
Lemma pres_mono : forall (P Q : Z -> Prop) m m', (forall a, 0 <= a < 2 ^ 64 -> Q a -> P a) -> pres P m m' -> pres Q m m'.
Proof. intros P Q m m' HPQ H a Ha HQ. apply H; auto. Qed.
Lemma pres_of_heap_pres : forall L LB SP m m', heap_pres s0segs L LB SP m m' -> pres (client_addr L LB SP) m m'.
Proof. intros L LB SP m m' H. exact H. Qed.
Lemma pres_of_munch : forall W m m', munch W m m' -> wmono s0segs m m' -> pres (outside W) m m'.
Proof. intros W m m' MU WM a Ha Ho. split; [apply MU; rewrite wa_unsigned by lia; exact Ho | apply WM]. Qed.
Lemma pres_bytes_at : forall P m m' A bs,
  pres P m m' -> bytes_at s0segs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> bytes_at s0segs m' A bs.
Proof.
  (intros P m m' A bs HP; cps_intros (H0 & H1 & HB); intros HR). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.
Lemma pres_wr_at : forall P m m' A n,
  pres P m m' -> wr_at s0segs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at s0segs m' A n.
Proof.
  (intros P m m' A n HP; cps_intros (H0 & H1 & HW); intros HR). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.
Lemma pres_rw_cells : forall P m m' A cs,
  pres P m m' -> rw_cells s0segs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) -> rw_cells s0segs m' A cs.
Proof.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply pres_wr_at; eauto.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma keep_blk : forall LBi SP m m' b A' cs,
  heap_pres s0segs S0_layout LBi SP m m' -> In b LBi -> blk_addr b <= A' -> A' + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b ->
  rw_cells s0segs m A' cs -> rw_cells s0segs m' A' cs.
Proof.
  intros LBi SP m m' b A' cs HP IN H1 H2 H. eapply pres_rw_cells; [exact (pres_of_heap_pres _ _ _ _ _ HP) | exact H |].
  intros a Ha. right; right. exists b. split; [exact IN | lia].
Qed.
Lemma keep_stk : forall LBi SP m m' A' cs,
  heap_pres s0segs S0_layout LBi SP m m' -> SP <= A' -> rw_cells s0segs m A' cs -> rw_cells s0segs m' A' cs.
Proof.
  intros LBi SP m m' A' cs HP H1 H. eapply pres_rw_cells; [exact (pres_of_heap_pres _ _ _ _ _ HP) | exact H |].
  intros a Ha. left. lia.
Qed.

(* [comment removed for export] *)
Lemma cmem_pres : forall (Q : Z -> Prop) m m' sv,
  (forall a, 0x32098 <= a < 0x335b0 -> Q a) -> pres Q m m' -> b2bC_mem S0CI m sv -> b2bC_mem S0CI m' sv.
Proof.
  (intros Q m m' sv HQ PR; cps_intros (G1 & G2 & G3 & G4)). unfold b2bC_mem, cimg_mem in *. cbn [bc_ci S0CI ci_got ci_crc ci_crcx ci_stderrp ci_segs S0C] in *.
  repeat match goal with |- _ /\ _ => split end;
    (eapply pres_rw_cells; [exact PR | eassumption | cbn; intros a Ha; apply HQ; lia]).
Qed.
(* [comment removed for export] *)
Lemma u8arr_split2 : forall m A (l1 l2 : list byte) n1 n2,
  u8arr s0segs m A (l1 ++ l2) -> length l1 = n1 -> length l2 = n2 ->
  rw_cells s0segs m A [CB n1 l1; CB n2 l2].
Proof.
  intros m A l1 l2 n1 n2 U L1 L2. eapply carve_cb; [exact (rw_cells_of_u8arr _ _ _ _ U) | | |].
  - cbn [cells_wf cell_wf]. rewrite L1, L2. repeat split; reflexivity.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
  - cbn [cells_size csize]. rewrite length_app. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_of_payload : forall l : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned l).
Proof.
  induction l as [|b l IH]; [constructor|]. cbn. constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

(* [comment removed for export] *)
Lemma mod8_of_q16 : forall q k, (16 * q - 8 * k) mod 8 = 0.
Proof. intros q k. replace (16 * q - 8 * k) with ((2 * q - k) * 8) by lia. apply Z_mod_mult. Qed.
Lemma mod16_of_q16 : forall q k, (16 * q - 16 * k) mod 16 = 0.
Proof. intros q k. replace (16 * q - 16 * k) with ((q - k) * 16) by lia. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
Lemma CB_head_len : forall m A n bs cs, rw_cells s0segs m A (CB n bs :: cs) -> length bs = n.
Proof. intros m A n bs cs [[Hwf _] _]. exact (proj1 Hwf). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section B2BK.
  Context (AI : AllocIface s0segs S0_layout) (AC : AllocCover s0segs S0_layout AI).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (dst dl src len wf0 nZ lo qsp : Z).
  Notation usp := (bv_unsigned sp).
  Hypothesis HW : wrap_sec sp dl src len wf0 nZ lo qsp.
  Variables (MD0 : Model) (s_ : ai_AS AI) (LB : list ablock) (pd : bid) (B : Z) (k : nat) (m0 : word -> option byte)
            (payload junk : list byte) (sv : word) (K : TSet).
  Hypothesis TP : tp = Z_to_bv 64 (al_tp S0_layout).
  Hypothesis AI0 : ai_inv AI s_ LB m0 MD0.
  Hypothesis SB : usp <= B.
  Hypothesis DST : dst = 0 \/ (In (pd, dst, nZ) LB /\ rw_cells s0segs m0 dst [CB (Z.to_nat nZ) junk]).
  Hypothesis DLB : dl + 4 <= B.
  Hypothesis SRC0 : bytes_at s0segs m0 src payload.
  Hypothesis PL : Z.of_nat (length payload) = len.
  Hypothesis CR : client_range S0_layout LB usp src len.
  Hypothesis SRC16 : src mod 16 = 0.
  Hypothesis SRCB : len = 0 \/ exists b, In b LB /\ blk_addr b <= src /\ src + len <= blk_addr b + blk_size b.
  Hypothesis AP1 : dst <> 0 -> src + len <= dst \/ dst + nZ <= src.
  Hypothesis AP2 : src + len <= dl \/ dl + 4 <= src.
  Hypothesis AP3 : dst <> 0 -> dst + nZ <= dl \/ dl + 4 <= dst.
  Hypothesis CM0 : b2bC_mem S0CI m0 sv.
  Hypothesis KONT : forall ms' MD',
      b2bC_post AI AC S0CI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB m0 MD0 dst nZ dl lo B payload junk sv k ms' MD' ->
      realizes s0segs (mkCfg ms' MD') K.

  Ltac prep :=
    pose proof HW as HW'; unfold wrap_sec in HW';
    cps_destruct HW' as (LEN & NZ & WF0 & WFE & ALQ & STK & LO & SPH & DL1 & DL2 & DL4 & SRC1 & SRC2);
    unfold CEIL, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, BZF_STRM, IMG_LO3, IMG_HI3 in *; bz_ceil; bz_params.

  (* [comment removed for export] *)
  Definition P0 (a : Z) : Prop := client_addr S0_layout LB usp a /\ ~ b2bC_out dst nZ dl a.

  (* [comment removed for export] *)
  Definition WLD (sx : ai_AS AI) (LBc : list ablock) (kk : nat) (m : word -> option byte) (MD : Model) : Prop :=
    ai_inv AI sx LBc m MD /\ ac_vm AC kk sx MD /\ vm_only MD0 MD /\
    ai_aux AI m B /\ (exists e, rw_cells s0segs m (errno_cell S0_layout) [C4 e]) /\ mem_inv s0segs m /\
    b2bC_mem S0CI m sv /\ pres P0 m0 m /\ (forall b, In b LB -> In b LBc).

  (* [comment removed for export] *)
  Lemma P0_img : forall a, 0x32098 <= a < 0x335b0 -> P0 a.
  Proof.
    intros a Ha. prep. split.
    - right. left. unfold errno_cell. cbn [al_rw_lo al_img_hi al_private al_tp S0_layout]. unfold S0_private. lia.
    - unfold b2bC_out. intros [[D X]|X]; [| lia].
      destruct DST as [D0|[IND _]]; [lia|]. cps_pose (ai_inv_blocks AI AI0 IND) as (_ & _ & _ & _ & B5). cbn [blk_addr blk_size fst snd al_img_lo al_img_hi S0_layout] in B5. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma client_ext : forall LBc SP a, (forall b, In b LB -> In b LBc) -> SP <= usp ->
    client_addr S0_layout LB usp a -> client_addr S0_layout LBc SP a.
  Proof.
    intros LBc SP a SUB HSP [C|[C|(b & Hb & R)]]; [left; lia | right; left; exact C | right; right; exists b; split; [apply SUB; exact Hb| exact R]].
  Qed.

  (* [comment removed for export] *)
  Lemma WLD_heap : forall sx LBc kk m MD sx' LBc' kk' m' MD' LBh SP e',
    WLD sx LBc kk m MD ->
    ai_inv AI sx' LBc' m' MD' -> vm_only MD MD' -> ac_vm AC kk' sx' MD' -> mem_inv s0segs m' ->
    rw_cells s0segs m' (errno_cell S0_layout) [C4 e'] -> ai_aux AI m' B -> heap_pres s0segs S0_layout LBh SP m m' ->
    (forall b, In b LB -> In b LBh) -> (forall b, In b LB -> In b LBc') -> SP <= usp ->
    WLD sx' LBc' kk' m' MD'.
  Proof.
    (intros sx LBc kk m MD sx' LBc' kk' m' MD' LBh SP e'; cps_intros (AIV & VM & VO & AUX & ERR & MI & CM & PR & SUB); intros AIV' VO' VM' MI' ERR' AUX' HP SUBh SUB' HSP).
    pose proof (pres_of_heap_pres _ _ _ _ _ HP) as PR'.
    assert (PR1 : pres P0 m m') by (eapply pres_mono; [| exact PR']; intros a Ha [CA _]; apply client_ext; assumption).
    split; [exact AIV'|]. split; [exact VM'|]. split; [eapply vm_only_trans; [exact VO| exact VO']|].
    split; [exact AUX'|]. split; [exists e'; exact ERR'|]. split; [exact MI'|].
    split; [eapply (cmem_pres P0); [apply P0_img | exact PR1 | exact CM]|].
    split; [eapply pres_trans; [exact PR | exact PR1] | exact SUB'].
  Qed.

  (* [comment removed for export] *)
  Definition wiv_ok (LBc : list ablock) (iv : Z * Z) : Prop :=
    (lo <= fst iv /\ snd iv <= usp) \/ (fst iv = dl /\ snd iv = dl + 4) \/ (dst <> 0 /\ dst <= fst iv /\ snd iv <= dst + nZ) \/
    (exists p A n, In (p, A, n) LBc /\ ~ In p (map blk_id LB) /\ A <= fst iv /\ snd iv <= A + n).

  Lemma blk_facts : forall sx LBc m MD p A n, ai_inv AI sx LBc m MD -> In (p, A, n) LBc ->
    0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ 0x66000 <= A).
  Proof. intros sx LBc m MD p A n AIV IN. exact (ai_inv_blocks AI AIV (b := (p, A, n)) IN). Qed.
  Lemma blk_apart : forall sx LBc m MD b1 b2, ai_inv AI sx LBc m MD -> In b1 LBc -> In b2 LBc -> b1 <> b2 ->
    blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
  Proof. intros. eapply (ai_inv_disjoint AI); eassumption. Qed.

  Lemma WLD_write : forall sx LBc kk m MD W m',
    WLD sx LBc kk m MD -> munch W m m' -> wmono s0segs m m' -> mem_inv s0segs m' -> Forall (wiv_ok LBc) W ->
    WLD sx LBc kk m' MD.
  Proof.
    intros sx LBc kk m MD W m' Wd MU WM MI' FW. cps_pose Wd as (AIV & VM & VO & AUX & [e ERR] & MI & CM & PR & SUB). prep.
    pose proof (ai_inv_nodup AI AIV) as ND.
    (* [comment removed for export] *)
    assert (ONE : forall iv, wiv_ok LBc iv ->
      client_write_ok S0_layout LBc iv /\ (snd iv <= B /\ (forall a, fst iv <= a < snd iv -> ~ al_static S0_layout a)) /\
      (alloc_ceiling <= fst iv \/ (snd iv <= 0x10000 \/ 0x66000 <= fst iv)) /\
      (forall a, 0 <= a < 2 ^ 64 -> P0 a -> ~ (fst iv <= a < snd iv))).
    { intros [l h] Hiv. unfold wiv_ok in Hiv. cbn [fst snd] in *. cbn [al_static S0_layout]. unfold S0_static, P0, b2bC_out.
      destruct Hiv as [[H1 H2] | [[-> ->] | [(D & H1 & H2) | (p & A & n & IN & NIP & H1 & H2)]]].
      - split; [left; cbn; lia|]. split; [split; [lia| intros; lia]|]. split; [lia|].
        intros a Ha [[C|[C|(b & Hb & Rb)]] _]; [lia | cbn [al_rw_lo al_img_hi S0_layout] in C; lia |].
        cps_pose (blk_facts _ _ _ _ (blk_id b) (blk_addr b) (blk_size b) AIV ltac:(destruct b as [[? ?] ?]; apply SUB; exact Hb)) as (_ & _ & _ & B4 & _). lia.
      - split; [left; cbn; lia|]. split; [split; [lia| intros; lia]|]. split; [lia|]. intros a Ha [_ NO]. lia.
      - destruct DST as [D0|[IND _]]; [lia|].
        cps_pose (blk_facts _ _ _ _ pd dst nZ AIV (SUB _ IND)) as (B1 & B2 & B3 & B4 & B5).
        split; [right; right; exists (pd, dst, nZ); split; [apply SUB; exact IND| cbn; lia]|].
        split; [split; [lia| intros; lia]|]. split; [lia|]. intros a Ha [_ NO]. lia.
      - cps_pose (blk_facts _ _ _ _ p A n AIV IN) as (B1 & B2 & B3 & B4 & B5).
        split; [right; right; exists (p, A, n); split; [exact IN| cbn; lia]|].
        split; [split; [lia| intros; lia]|]. split; [lia|].
        intros a Ha [[C|[C|(b & Hb & Rb)]] _]; [lia | cbn [al_rw_lo al_img_hi S0_layout] in C; lia |].
        assert (NEb : (p, A, n) <> b) by (intros <-; apply NIP; apply (in_map blk_id _ _ Hb)).
        pose proof (blk_apart _ _ _ _ _ _ AIV IN (SUB _ Hb) NEb) as Db. cbn [blk_addr blk_size fst snd] in Db. lia. }
    assert (OUT : forall a, 0 <= a < 2 ^ 64 -> (P0 a \/ 0x32000 <= a < 0x66000) -> outside W a).
    { intros a Ha Hp. clear - FW ONE Ha Hp. induction W as [|[l h] W IH]; [exact I|]. apply Forall_cons_1 in FW. destruct FW as [H1 H2].
      cbn. split; [| exact (IH H2)]. destruct Hp as [Hp|Hp]; [exact (proj2 (proj2 (proj2 (ONE _ H1))) a Ha Hp)|].
      pose proof (proj1 (proj2 (proj2 (ONE _ H1)))) as X. cbn in X. pose proof alloc_ceiling_range. lia. }
    pose proof (pres_of_munch W m m' MU WM) as PRW.
    split; [eapply (ai_inv_frame AI AIV); [exact MU | exact WM |]; apply Forall_forall; intros iv Hiv; exact (proj1 (ONE iv (proj1 (Forall_forall _ _) FW iv Hiv)))|].
    split; [exact VM|]. split; [exact VO|].
    split; [eapply (ai_aux_frame AI); [exact AUX | exact MU | exact WM |]; apply Forall_forall; intros iv Hiv; exact (proj1 (proj2 (ONE iv (proj1 (Forall_forall _ _) FW iv Hiv))))|].
    split. { exists e. eapply pres_rw_cells; [exact PRW | exact ERR |]. unfold errno_cell. cbn [al_tp S0_layout cells_size csize Nat.add]. intros a Ha. apply OUT; [lia| right; lia]. }
    split; [exact MI'|].
    split; [eapply (cmem_pres (outside W)); [| exact PRW | exact CM]; intros a Ha; apply OUT; [lia| right; lia]|].
    split; [| exact SUB].
    eapply pres_trans; [exact PR|]. intros a Ha Hp. apply PRW; [exact Ha|]. apply OUT; [exact Ha| left; exact Hp].
  Qed.

  Lemma fresh_id : forall sx LX p A n L2 m MD, ai_inv AI sx (LX ++ (p, A, n) :: L2 ++ LB) m MD -> ~ In p (map blk_id LB).
  Proof.
    intros sx LX p A n L2 m MD AIV Hin. pose proof (ai_inv_nodup AI AIV) as ND.
    rewrite map_app in ND. cbn [map] in ND. destruct (nodup_mid _ _ _ ND) as [_ N2]. apply N2. rewrite map_app. apply in_or_app. right. exact Hin.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma free_step : forall sx kk m MD (p : bid) (A n : Z) (L1 L2 : list ablock) (SPv : Z) (T : TSet)
      (xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    WLD sx (L1 ++ (p, A, n) :: L2) kk m MD -> c21_foreign n -> (forall b, In b LB -> In b (L1 ++ L2)) ->
    stk s0segs m lo SPv -> lo + 8192 <= SPv -> SPv <= usp -> 0 <= SPv ->
    (forall sx' m' MD' (yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
        WLD sx' (L1 ++ L2) kk m' MD' -> stk s0segs m' lo SPv -> heap_pres s0segs S0_layout (L1 ++ L2) SPv m m' ->
        realizes s0segs (mkCfg (MS (mkR xra (Z_to_bv 64 SPv) gp tp yt0 yt1 yt2 xs0 xs1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6)
                                 F (ret_pc xra) fc None m' (seg_rom s0segs)) MD') T) ->
    realizes s0segs (mkCfg (MS (mkR xra (Z_to_bv 64 SPv) gp tp xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 A) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                             F (Z_to_bv 64 FREE) fc None m (seg_rom s0segs)) MD) T.
  Proof.
    intros sx kk m MD p A n L1 L2 SPv T xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
      W FOR SUB' ST LOS SPU SP0 KK.
    cps_pose W as (AIV & VM & VO & AUX & [e ERR] & MI & CM & PR & SUB). prep.
    pose proof (ai_inv_nodup AI AIV) as ND.
    eapply (ac_free AC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m MD sx (L1 ++ (p, A, n) :: L2) kk p A n lo B e T AIV VM);
      [ apply in_or_app; right; left; reflexivity | left; exact FOR | exact AUX | rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; cbn [al_stack S0_layout]; lia
      | exact ERR | exact MI | exact TP | reflexivity | ].
    intros sx' m' MD' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 AIV' VO' VM' MI' ST' ERR' AUX' HP CF.
    rewrite unsigned_lit in ST', HP by lia.
    replace (lb_remove p (L1 ++ (p, A, n) :: L2)) with (L1 ++ L2) in AIV' by (symmetry; apply lb_remove_mid; exact ND).
    replace (lb_remove p (L1 ++ (p, A, n) :: L2)) with (L1 ++ L2) in HP by (symmetry; apply lb_remove_mid; exact ND).
    eapply (KK sx' m' MD'); [| exact ST' | exact HP].
    eapply (WLD_heap sx _ kk m MD sx' _ kk m' MD' (L1 ++ L2) SPv); [exact W | exact AIV' | exact VO' | exact VM' | exact MI' | exact ERR' | exact AUX' | exact HP | exact SUB' | exact SUB' | exact SPU].
  Qed.

  (* [comment removed for export] *)
  Lemma bigz_step : forall sx LBc kk m MD (n SPv : Z) (T : TSet)
      (xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    WLD sx LBc (S kk) m MD -> MMAP_THRESHOLD_C <= n <= MAX_REQ_C ->
    stk s0segs m lo SPv -> lo + 8192 <= SPv -> SPv <= usp -> 0 <= SPv ->
    (forall sx' m' MD' (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
        WLD sx' LBc kk m' MD' -> stk s0segs m' lo SPv -> heap_pres s0segs S0_layout LBc SPv m m' ->
        realizes s0segs (mkCfg (MS (mkR xra (Z_to_bv 64 SPv) gp tp yt0 yt1 yt2 xs0 xs1 (Z_to_bv 64 0) ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6)
                                 F (ret_pc xra) fc None m' (seg_rom s0segs)) MD') T) ->
    (forall sx' m' MD' (r : Z) (p : bid) (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
        WLD sx' ((p, r, n) :: LBc) kk m' MD' -> stk s0segs m' lo SPv -> heap_pres s0segs S0_layout LBc SPv m m' ->
        r <> 0 -> block_ok S0_layout r n -> ~ In p (map blk_id LBc) ->
        rw_cells s0segs m' r [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
        realizes s0segs (mkCfg (MS (mkR xra (Z_to_bv 64 SPv) gp tp yt0 yt1 yt2 xs0 xs1 (Z_to_bv 64 r) ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6)
                                 F (ret_pc xra) fc None m' (seg_rom s0segs)) MD') T) ->
    realizes s0segs (mkCfg (MS (mkR xra (Z_to_bv 64 SPv) gp tp xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 n) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                             F (Z_to_bv 64 MALLOC) fc None m (seg_rom s0segs)) MD) T.
  Proof.
    intros sx LBc kk m MD n SPv T xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
      W NR ST LOS SPU SP0 KFA KOK.
    cps_pose W as (AIV & VM & VO & AUX & [e ERR] & MI & CM & PR & SUB). prep.
    assert (CAN : ac_can AC n sx LBc MD).
    { apply (ac_can_intro AC n kk sx LBc m MD AIV); [| left; unfold c21_foreign; lia].
      replace (ac_cost n) with 1%nat by (unfold ac_cost; destruct (Z.ltb_spec n 1024); [unfold MMAP_THRESHOLD_C in NR; lia| reflexivity]). exact VM. }
    (* [comment removed for export] *)
    eapply (ac_malloc_bigz AC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m MD sx LBc kk n lo B e T AIV VM CAN NR AUX);
      [ rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; cbn [al_stack S0_layout]; lia
      | exact ERR | exact MI | exact TP | reflexivity | | ].
    - intros sx' m' MD' yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 e' AIV' VO' VM' MI' ST' ERR' AUX' HP CF.
      rewrite unsigned_lit in ST', HP by lia.
      eapply (KFA sx' m' MD'); [| exact ST' | exact HP].
      eapply (WLD_heap sx LBc (S kk) m MD sx' LBc kk m' MD' LBc SPv); [exact W | exact AIV' | exact VO' | exact VM' | exact MI' | exact ERR' | exact AUX' | exact HP | exact SUB | exact SUB | exact SPU].
    - intros sx' m' MD' r p yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 e' AIV' VO' VM' MI' ST' ERR' AUX' HP Hr BOK NIN BLK CF.
      rewrite unsigned_lit in ST', HP by lia.
      eapply (KOK sx' m' MD' r p); [| exact ST' | exact HP | exact Hr | exact BOK | exact NIN | exact BLK].
      eapply (WLD_heap sx LBc (S kk) m MD sx' _ kk m' MD' LBc SPv); [exact W | exact AIV' | exact VO' | exact VM' | exact MI' | exact ERR' | exact AUX' | exact HP | exact SUB | intros b Hb; right; exact (SUB b Hb) | exact SPU].
  Qed.

  (* [comment removed for export] *)
  Lemma cover_step : forall sx LBc kk m MD (n SPv : Z) (T : TSet)
      (xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    WLD sx LBc (S kk) m MD -> 1024 <= n < MMAP_THRESHOLD_C -> c21_foreign n ->
    stk s0segs m lo SPv -> lo + 8192 <= SPv -> SPv <= usp -> 0 <= SPv ->
    (forall sx' m' MD' (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
        WLD sx' LBc kk m' MD' -> stk s0segs m' lo SPv -> heap_pres s0segs S0_layout LBc SPv m m' ->
        realizes s0segs (mkCfg (MS (mkR xra (Z_to_bv 64 SPv) gp tp yt0 yt1 yt2 xs0 xs1 (Z_to_bv 64 0) ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6)
                                 F (ret_pc xra) fc None m' (seg_rom s0segs)) MD') T) ->
    (forall sx' m' MD' (r : Z) (p : bid) (junk' : list byte) (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
        WLD sx' ((p, r, n) :: LBc) kk m' MD' -> stk s0segs m' lo SPv -> heap_pres s0segs S0_layout LBc SPv m m' ->
        r <> 0 -> block_ok S0_layout r n -> ~ In p (map blk_id LBc) ->
        rw_cells s0segs m' r [CB (Z.to_nat n) junk'] ->
        realizes s0segs (mkCfg (MS (mkR xra (Z_to_bv 64 SPv) gp tp yt0 yt1 yt2 xs0 xs1 (Z_to_bv 64 r) ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6)
                                 F (ret_pc xra) fc None m' (seg_rom s0segs)) MD') T) ->
    realizes s0segs (mkCfg (MS (mkR xra (Z_to_bv 64 SPv) gp tp xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 n) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                             F (Z_to_bv 64 MALLOC) fc None m (seg_rom s0segs)) MD) T.
  Proof.
    intros sx LBc kk m MD n SPv T xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
      W NR FOR ST LOS SPU SP0 KFA KOK.
    cps_pose W as (AIV & VM & VO & AUX & [e ERR] & MI & CM & PR & SUB). prep.
    assert (CO : ac_cost n = 1%nat) by (unfold ac_cost; destruct (Z.ltb_spec n 1024); [lia| reflexivity]).
    assert (VM1 : ac_vm AC (ac_cost n + kk) sx MD) by (rewrite CO; exact VM).
    pose proof (ac_can_intro AC n kk sx LBc m MD AIV VM1 (or_introl FOR)) as CAN.
    eapply (ac_malloc_cover AC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m MD sx LBc kk n lo B e T T AIV VM1 CAN AUX);
      [ rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; cbn [al_stack S0_layout]; lia
      | exact ERR | exact MI | exact TP | reflexivity | lia | | | intros tr Htr; exact Htr ].
    - intros sx' m' MD' yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 e' AIV' VO' VM' MI' ST' ERR' AUX' HP CF.
      rewrite unsigned_lit in ST', HP by lia.
      eapply (KFA sx' m' MD'); [| exact ST' | exact HP].
      eapply (WLD_heap sx LBc (S kk) m MD sx' LBc kk m' MD' LBc SPv); [exact W | exact AIV' | exact VO' | exact VM' | exact MI' | exact ERR' | exact AUX' | exact HP | exact SUB | exact SUB | exact SPU].
    - intros sx' m' MD' r p yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 e' junk' AIV' VO' VM' MI' ST' ERR' AUX' HP Hr BOK NIN BLK CF.
      rewrite unsigned_lit in ST', HP by lia.
      eapply (KOK sx' m' MD' r p junk'); [| exact ST' | exact HP | exact Hr | exact BOK | exact NIN | exact BLK].
      eapply (WLD_heap sx LBc (S kk) m MD sx' _ kk m' MD' LBc SPv); [exact W | exact AIV' | exact VO' | exact VM' | exact MI' | exact ERR' | exact AUX' | exact HP | exact SUB | intros b Hb; right; exact (SUB b Hb) | exact SPU].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation RETpost := (S0_b2c_segA.RETpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo).

  Lemma result_pres : forall Q m m' rc dlv,
    pres Q m m' -> (forall a, dst <> 0 -> dst <= a < dst + nZ -> Q a) ->
    b2bC_result s0segs rc dst nZ payload junk m dlv -> b2bC_result s0segs rc dst nZ payload junk m' dlv.
  Proof.
    intros Q m m' rc dlv PR HQ R. prep.
    destruct R as [R | [(R1 & R2 & R3 & R4) | (a1 & a2 & ft & inU & uns & mtf & sel & selM & len' & code & rfreq & lenp & bsB & bsL & nIn & oP & nM & junk' & E1 & E2 & E3 & R)]].
    - left. exact R.
    - right; left. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
      eapply pres_rw_cells; [exact PR | exact R4 | rewrite size_CB1, Z2Nat.id by lia; intros a Ha; apply HQ; [exact R2| exact Ha]].
    - right; right. exists a1, a2, ft, inU, uns, mtf, sel, selM, len', code, rfreq, lenp, bsB, bsL, nIn, oP, nM, junk'.
      split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. cbv zeta in R |- *. destruct R as [D R]. split; [exact D|].
      destruct R as [(R1 & R2 & R3 & R4) | (R1 & R2 & R3 & R4)].
      + left. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
        eapply pres_rw_cells; [exact PR | exact R4 | cbn [cells_size csize]; rewrite ?Nat.add_0_r, Nat2Z.inj_add, Z2Nat.id by lia; intros a Ha; apply HQ; [exact D| lia]].
      + right. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
        eapply pres_rw_cells; [exact PR | exact R4 | rewrite size_CB1, Z2Nat.id by lia; intros a Ha; apply HQ; [exact D| exact Ha]].
  Qed.

  Lemma FIN : forall sx kk m MD rc dlv W ms,
    WLD sx LB kk m MD -> (k <= kk)%nat ->
    Forall (fun iv => lo <= fst iv /\ snd iv <= usp) W ->
    rw_cells s0segs m dl [C4 (Z_to_bv 64 dlv)] -> 0 <= dlv <= nZ ->
    b2bC_result s0segs rc dst nZ payload junk m dlv ->
    RETpost rc W m ms -> realizes s0segs (mkCfg ms MD) K.
  Proof.
    intros sx kk m MD rc dlv W ms Wd KK FW DLC DLV RES PO. prep.
    unfold S0_b2c_segA.RETpost in PO.
    cps_destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & -> & MU & WM & MI' & ST').
    assert (W' : WLD sx LB kk m' MD).
    { eapply WLD_write; [exact Wd | exact MU | exact WM | exact MI' |]. eapply Forall_impl; [| exact FW]. intros iv Hiv. left. exact Hiv. }
    cps_pose W' as (AIV' & VM' & VO' & AUX' & [e' ERR'] & _ & CM' & PR' & _).
    assert (OUT : forall a, (a < lo \/ usp <= a) -> outside W a).
    { intros a Ha. clear - FW Ha. induction W as [|[l h] W IH]; [exact I|]. apply Forall_cons_1 in FW. destruct FW as [H1 H2]. cbn in H1 |- *. split; [lia| exact (IH H2)]. }
    pose proof (pres_of_munch W m m' MU WM) as PRW.
    apply KONT. unfold b2bC_post.
    exists u0, u1, u2, (Z_to_bv 64 rc), b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, e', m', sx, rc, dlv.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact AIV'|]. split; [eapply (ac_vm_le _ _ _ AC); [exact VM'| exact KK]|].
    split; [exact VO'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [intros a Ha CA NO; exact (PR' a Ha (conj CA NO))|].
    split; [eapply pres_rw_cells; [exact PRW | exact DLC | cbn; intros a Ha; apply OUT; right; lia]|].
    split; [exact DLV|]. split; [exact CM'|].
    eapply result_pres; [exact PRW | | exact RES]. intros a D Ha. apply OUT. left.
    destruct DST as [D0|[IND _]]; [lia|]. cps_pose (blk_facts _ _ _ _ pd dst nZ AI0 IND) as (_ & _ & _ & B4 & _). lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let wW1a := S0_b2c_segA.W1a ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst dl src len wf0 nZ lo qsp HW.
  Let wW1b := S0_b2c_segA.W1b ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst dl src len wf0 nZ lo qsp HW.
  Let wW2f := S0_b2c_segA.W2f ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst dl src len wf0 nZ lo qsp HW.
  Let wW2 := S0_b2c_segA.W2 ra sp gp tp s0 s1 s2 s3 s4 s6 s7 s8 s9 s10 s11 F fc dst dl src len wf0 nZ lo qsp HW.
  Let wW3 := S0_b2c_segA.W3 ra sp gp tp s0 s1 s2 s3 s4 s7 s8 s9 s10 s11 F fc dl src len wf0 nZ lo qsp HW.
  Let wW4 := S0_b2c_segA.W4 ra sp gp tp s0 s1 s2 s3 s4 s7 s8 s9 s10 s11 F fc dl src len wf0 nZ lo qsp HW.
  Let wG3a := S0_b2c_segB.G3a sp gp tp s7 s8 s9 s10 s11 F fc dl src len wf0 nZ lo qsp HW.
  Let wG3b := S0_b2c_segB.G3b ra sp gp tp s0 s1 s2 s3 s4 s7 s8 s9 s10 s11 F fc dl src len wf0 nZ lo qsp HW.
  Let wG4a := S0_b2c_segB.G4a sp gp tp s7 s8 s9 s10 s11 F fc dl src len wf0 nZ lo qsp HW.
  Let wG4b := S0_b2c_segB.G4b ra sp gp tp s0 s1 s2 s3 s4 s7 s8 s9 s10 s11 F fc dl src len wf0 nZ lo qsp HW.
  Let wG5a := S0_b2c_segB.G5a sp gp tp s7 s8 s9 s10 s11 F fc dl src len wf0 nZ lo qsp HW.
  Let wG5b := S0_b2c_segB.G5b ra sp gp tp s0 s1 s2 s3 s4 s7 s8 s9 s10 s11 F fc dl src len wf0 nZ lo qsp HW.
  Let wG6 := S0_b2c_segB.G6 ra sp gp tp s0 s1 s2 s3 s4 s7 s8 s9 s10 s11 F fc dl src len wf0 nZ lo qsp HW.
  Let wG7 := S0_b2c_segB.G7 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst dl src len wf0 nZ lo qsp HW.
  Let wT := S0_b2c_segB.T ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst dl src len wf0 nZ lo qsp HW.
  Let wRC3 := S0_b2c_segC.RC3 sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc dst dl src len wf0 nZ lo qsp HW.
  Let wRC4 := S0_b2c_segC.RC4 sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc dst dl src len wf0 nZ lo qsp HW.
  Let wE1 := S0_b2c_segC.E1 sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc dst dl src len wf0 nZ lo qsp HW.
  Let wE2 := S0_b2c_segC.E2 sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc dst dl src len wf0 nZ lo qsp HW.
  Let wE3 := S0_b2c_segC.E3 sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc dst dl src len wf0 nZ lo qsp HW.
  Let wE4 := S0_b2c_segC.E4 sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc dst dl src len wf0 nZ lo qsp HW.
  Let wE5 := S0_b2c_segC.E5 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst dl src len wf0 nZ lo qsp HW.
  Local Notation FRI := (S0_b2c_segA.FRI s5 s6 dst dl src len).
  Local Notation FRWj jb := (S0_b2c_segA.FRW ra s0 s1 s2 s3 s4 jb DBZA DBZF).

  (* [comment removed for export] *)
  Definition STC (jb : list byte) (m : word -> option byte) : Prop :=
    rw_cells s0segs m (usp - 192) FRI /\ rw_cells s0segs m (usp - 128) (FRWj jb) /\
    rw_cells s0segs m dl [C4 (Z_to_bv 64 nZ)] /\ rw_cells s0segs m dst [CB (Z.to_nat nZ) junk].
  Lemma STC_heap : forall jb m m' LBh SP, STC jb m -> heap_pres s0segs S0_layout LBh SP m m' -> SP <= usp - 192 -> In (pd, dst, nZ) LBh -> STC jb m'.
  Proof.
    (intros jb m m' LBh SP; cps_intros (A1 & A2 & A3 & A4); intros HP HSP IND). prep.
    split; [eapply keep_stk; [exact HP | | exact A1]; lia|]. split; [eapply keep_stk; [exact HP | | exact A2]; lia|].
    split; [eapply keep_stk; [exact HP | | exact A3]; lia|].
    eapply (keep_blk _ _ m m' (pd, dst, nZ)); [exact HP | exact IND | cbn; lia | cbn [blk_addr blk_size fst snd]; rewrite size_CB1, Z2Nat.id by lia; lia | exact A4].
  Qed.
  Lemma STC_munch : forall jb m m' W, STC jb m -> munch W m m' -> wmono s0segs m m' ->
    disjoint_from W (usp - 192) 192 -> disjoint_from W dl 4 -> disjoint_from W dst nZ -> STC jb m'.
  Proof.
    (intros jb m m' W; cps_intros (A1 & A2 & A3 & A4); intros MU WM D1 D2 D3). prep.
    split; [eapply rw_cells_transport; [exact A1 | exact MU | exact WM | eapply disjoint_from_sub; [exact D1| cbn; lia| cbn; lia]]|].
    split; [eapply rw_cells_transport; [exact A2 | exact MU | exact WM | eapply disjoint_from_sub; [exact D1| cbn; lia| unfold S0_b2c_segA.FRW; cbn; lia]]|].
    split; [eapply rw_cells_transport; [exact A3 | exact MU | exact WM | cbn; exact D2]|].
    eapply rw_cells_transport; [exact A4 | exact MU | exact WM | rewrite size_CB1, Z2Nat.id by lia; exact D3].
  Qed.


  Definition opt (r : Z) (b : ablock) : list ablock := if r =? 0 then [] else [b].
  Lemma opt_0 : forall b, opt 0 b = []. Proof. reflexivity. Qed.
  Lemma opt_nz : forall r b, r <> 0 -> opt r b = [b]. Proof. intros r b H. unfold opt. rewrite (proj2 (Z.eqb_neq r 0) H). reflexivity. Qed.

  Lemma IND : dst <> 0 -> In (pd, dst, nZ) LB.
  Proof. intros D. destruct DST as [D0|[H _]]; [lia| exact H]. Qed.

  Local Notation EJ1w := S0_b2c_segA.EJ1w.
  Local Notation GREGS xra xt0 xt1 xt2 E xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 :=
    (mkR xra (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
         xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) (Z_to_bv 64 (-3)) xs6
         s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma CL_E : forall sx kk m MD (jb : list byte) (pE : bid) (E : Z)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 : word),
    WLD sx ([(pE, E, 55768)] ++ LB) kk m MD -> (k <= kk)%nat -> dst <> 0 ->
    STC jb m -> stk s0segs m lo (usp - 192) ->
    realizes s0segs (mkCfg (MS (GREGS xra xt0 xt1 xt2 E xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6)
                             F (Z_to_bv 64 0x13de4) fc None m (seg_rom s0segs)) MD) K.
  Proof.
    intros sx kk m MD jb pE E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 W KK D0 SC ST.
    cps_pose W as (AIV & VM & VO & AUX & [e ERR] & MI & CM & PR & SUB). prep.
    cps_pose (blk_facts _ _ _ _ pE E 55768 AIV ltac:(left; reflexivity)) as (RE1 & _ & _ & RE2 & _).
    pose proof (ai_inv_model AI AIV) as [Hh Hl]. cps_pose SC as (FR2 & FR & DLC & DSB).
    (* [comment removed for export] *)
    eapply (evt_realizes s0segs _ _ MD K Hh Hl (wG6 m jb E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 _ xs6
              RE1 ltac:(unfold CEIL; bz_ceil; bz_params; lia) FR MI)).
    intros ms ->.
    (* [comment removed for export] *)
    eapply (free_step sx kk m MD pE E 55768 [] LB (usp - 192) K);
      [exact W | unfold c21_foreign; lia | intros b Hb; exact Hb | exact ST | lia | lia | lia |].
    intros sx2 m2 MD2 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 W2 ST2 HP2. cbn [app] in W2, HP2.
    cps_pose (STC_heap jb m m2 LB (usp - 192) SC HP2 ltac:(lia) (IND D0)) as (FR2b & FRb & DLCb & DSBb).
    cps_pose W2 as (AIV2 & _ & _ & _ & _ & MI2 & _). pose proof (ai_inv_model AI AIV2) as [Hh2 Hl2].
    rewrite (ret_pc_even 0x13df4) by (first [lia | reflexivity]).
    (* [comment removed for export] *)
    eapply (evt_realizes s0segs _ _ MD2 K Hh2 Hl2 (wG7 m2 jb _ yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs6 yt3 yt4 yt5 yt6 E FR2b FRb MI2 ST2)).
    intros ms PO.
    eapply (FIN sx2 kk m2 MD2 (-3) nZ [(usp - 192, usp)]); [exact W2 | exact KK | apply Forall_cons; [cbn; lia| apply Forall_nil] | exact DLCb | lia | | exact PO].
    right; left. split; [reflexivity|]. split; [exact D0|]. split; [reflexivity| exact DSBb].
  Qed.

  (* [comment removed for export] *)
  Lemma CL_3 : forall sx kk m MD (J jb : list byte) (pFT pE : bid) (E r1 r2 r3 : Z)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 : word),
    WLD sx (opt r3 (pFT, r3, 262148) ++ [(pE, E, 55768)] ++ LB) kk m MD -> (k <= kk)%nat -> dst <> 0 -> 0 <= r3 ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 r3)) ->
    STC jb m -> stk s0segs m lo (usp - 192) ->
    realizes s0segs (mkCfg (MS (GREGS xra xt0 xt1 xt2 E xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6)
                             F (Z_to_bv 64 0x13dd0) fc None m (seg_rom s0segs)) MD) K.
  Proof.
    intros sx kk m MD J jb pFT pE E r1 r2 r3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 W KK D0 R3 EH SC ST.
    prep. cps_pose SC as (FR2 & FR & DLC & DSB).
    destruct (Z.eq_dec r3 0) as [R0 | RNZ].
    - rewrite R0, opt_0 in W. cbn [app] in W. rewrite R0 in EH.
      cps_pose W as (AIV & VM & VO & AUX & [e ERR] & MI & CM & PR & SUB). pose proof (ai_inv_model AI AIV) as [Hh Hl].
      cps_pose (blk_facts _ _ _ _ pE E 55768 AIV ltac:(left; reflexivity)) as (RE1 & _ & _ & RE2 & _).
      eapply (evt_realizes s0segs _ _ MD K Hh Hl (wG5a m J E r1 r2 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 _ xs6
                RE1 ltac:(unfold CEIL; bz_ceil; bz_params; lia) EH MI)).
      intros ms ->.
      eapply (CL_E sx kk m MD jb pE E); [exact W | exact KK | exact D0 | exact SC | exact ST].
    - rewrite (opt_nz r3 _ RNZ) in W. cbn [app] in W.
      cps_pose W as (AIV & VM & VO & AUX & [e ERR] & MI & CM & PR & SUB). pose proof (ai_inv_model AI AIV) as [Hh Hl].
      cps_pose (blk_facts _ _ _ _ pE E 55768 AIV ltac:(right; left; reflexivity)) as (RE1 & _ & _ & RE2 & _).
      cps_pose (blk_facts _ _ _ _ pFT r3 262148 AIV ltac:(left; reflexivity)) as (RF1 & _ & _ & RF2 & _).
      eapply (evt_realizes s0segs _ _ MD K Hh Hl (wG5b m J jb E r1 r2 r3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 _ xs6
                RE1 ltac:(unfold CEIL; bz_ceil; bz_params; lia) ltac:(lia) EH FR MI)).
      intros ms ->.
      eapply (free_step sx kk m MD pFT r3 262148 [] ([(pE, E, 55768)] ++ LB) (usp - 192) K);
        [exact W | unfold c21_foreign, MMAP_THRESHOLD_C, MAX_REQ_C; lia | intros b Hb; right; exact Hb | exact ST | lia | lia | lia |].
      intros sx2 m2 MD2 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 W2 ST2 HP2. cbn [app] in W2, HP2.
      pose proof (STC_heap jb m m2 _ (usp - 192) SC HP2 ltac:(lia) (or_intror (IND D0))) as SC2.
      rewrite (ret_pc_even 0x13de4) by (first [lia | reflexivity]).
      eapply (CL_E sx2 kk m2 MD2 jb pE E); [exact W2 | exact KK | exact D0 | exact SC2 | exact ST2].
  Qed.

  (* [comment removed for export] *)
  Lemma CL_2 : forall sx kk m MD (J jb : list byte) (pFT pA2 pE : bid) (E r1 r2 r3 : Z)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 : word),
    WLD sx (opt r3 (pFT, r3, 262148) ++ opt r2 (pA2, r2, ARR2_SIZE) ++ [(pE, E, 55768)] ++ LB) kk m MD -> (k <= kk)%nat -> dst <> 0 ->
    0 <= r2 -> 0 <= r3 ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 r3)) ->
    STC jb m -> stk s0segs m lo (usp - 192) ->
    realizes s0segs (mkCfg (MS (GREGS xra xt0 xt1 xt2 E xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6)
                             F (Z_to_bv 64 0x13dbc) fc None m (seg_rom s0segs)) MD) K.
  Proof.
    intros sx kk m MD J jb pFT pA2 pE E r1 r2 r3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 W KK D0 R2 R3 EH SC ST.
    prep. cps_pose SC as (FR2 & FR & DLC & DSB).
    cps_pose W as (AIV & VM & VO & AUX & [e ERR] & MI & CM & PR & SUB). pose proof (ai_inv_model AI AIV) as [Hh Hl].
    assert (INE : In (pE, E, 55768) (opt r3 (pFT, r3, 262148) ++ opt r2 (pA2, r2, ARR2_SIZE) ++ [(pE, E, 55768)] ++ LB)).
    { apply in_or_app; right. apply in_or_app; right. left; reflexivity. }
    cps_pose (blk_facts _ _ _ _ pE E 55768 AIV INE) as (RE1 & _ & _ & RE2 & _).
    destruct (Z.eq_dec r2 0) as [R0 | RNZ].
    - rewrite R0 in EH. rewrite R0, opt_0 in W. cbn [app] in W.
      eapply (evt_realizes s0segs _ _ MD K Hh Hl (wG4a m J E r1 r3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 _ xs6
                RE1 ltac:(unfold CEIL; bz_ceil; bz_params; lia) EH MI)).
      intros ms ->.
      eapply (CL_3 sx kk m MD J jb pFT pE E r1 0 r3); [exact W | exact KK | exact D0 | exact R3 | exact EH | exact SC | exact ST].
    - rewrite (opt_nz r2 _ RNZ) in W, AIV, INE.
      assert (INA : In (pA2, r2, ARR2_SIZE) (opt r3 (pFT, r3, 262148) ++ [(pA2, r2, ARR2_SIZE)] ++ [(pE, E, 55768)] ++ LB)).
      { apply in_or_app; right. left; reflexivity. }
      cps_pose (blk_facts _ _ _ _ pA2 r2 ARR2_SIZE AIV INA) as (RA1 & _ & _ & RA2 & _).
      eapply (evt_realizes s0segs _ _ MD K Hh Hl (wG4b m J jb E r1 r2 r3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 _ xs6
                RE1 ltac:(unfold CEIL; bz_ceil; bz_params; lia) ltac:(lia) EH FR MI)).
      intros ms ->.
      change (opt r3 (pFT, r3, 262148) ++ [(pA2, r2, ARR2_SIZE)] ++ [(pE, E, 55768)] ++ LB)
        with (opt r3 (pFT, r3, 262148) ++ (pA2, r2, ARR2_SIZE) :: ([(pE, E, 55768)] ++ LB)) in W.
      eapply (free_step sx kk m MD pA2 r2 ARR2_SIZE (opt r3 (pFT, r3, 262148)) ([(pE, E, 55768)] ++ LB) (usp - 192) K);
        [exact W | unfold c21_foreign, MMAP_THRESHOLD_C, MAX_REQ_C; lia | intros b Hb; apply in_or_app; right; right; exact Hb | exact ST | lia | lia | lia |].
      intros sx2 m2 MD2 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 W2 ST2 HP2.
      assert (INE2 : In (pE, E, 55768) (opt r3 (pFT, r3, 262148) ++ [(pE, E, 55768)] ++ LB)) by (apply in_or_app; right; left; reflexivity).
      pose proof (keep_blk _ _ m m2 (pE, E, 55768) E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 r3)) HP2 INE2 ltac:(cbn; lia)
                    ltac:(cbn [blk_addr blk_size fst snd]; cbv [cells_size csize S0_b2c_segA.EJ1w Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia) EH) as EH2.
      pose proof (STC_heap jb m m2 _ (usp - 192) SC HP2 ltac:(lia) ltac:(apply in_or_app; right; right; exact (IND D0))) as SC2.
      rewrite (ret_pc_even 0x13dd0) by (first [lia | reflexivity]).
      eapply (CL_3 sx2 kk m2 MD2 J jb pFT pE E r1 r2 r3); [exact W2 | exact KK | exact D0 | exact R3 | exact EH2 | exact SC2 | exact ST2].
  Qed.


  (* [comment removed for export] *)
  Lemma E_dst_apart : forall sx LX L2 m MD pE E n, ai_inv AI sx (LX ++ (pE, E, n) :: L2 ++ LB) m MD -> dst <> 0 ->
    E + n <= dst \/ dst + nZ <= E.
  Proof.
    intros sx LX L2 m MD pE E n AIV D0.
    assert (INE : In (pE, E, n) (LX ++ (pE, E, n) :: L2 ++ LB)) by (apply in_or_app; right; left; reflexivity).
    assert (IND' : In (pd, dst, nZ) (LX ++ (pE, E, n) :: L2 ++ LB)) by (apply in_or_app; right; right; apply in_or_app; right; exact (IND D0)).
    assert (NE : (pE, E, n) <> (pd, dst, nZ)).
    { intros X. apply (fresh_id _ _ _ _ _ _ _ _ AIV). injection X as -> _ _. apply (in_map blk_id _ _ (IND D0)). }
    pose proof (blk_apart _ _ _ _ _ _ AIV INE IND' NE) as D. cbn [blk_addr blk_size fst snd] in D. exact D.
  Qed.

  (* [comment removed for export] *)
  Lemma CLEAN : forall sx kk m MD (J jb : list byte) (pFT pA2 pA1 pE : bid) (E r1 r2 r3 : Z) (c40 : word)
      (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 : word),
    WLD sx (opt r3 (pFT, r3, 262148) ++ opt r2 (pA2, r2, ARR2_SIZE) ++ opt r1 (pA1, r1, ARR1_SIZE) ++ [(pE, E, 55768)] ++ LB) kk m MD ->
    (k <= kk)%nat -> dst <> 0 -> 0 <= r1 -> 0 <= r2 -> 0 <= r3 -> (r1 = 0 \/ r2 = 0 \/ r3 = 0) ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) c40) ->
    STC jb m -> stk s0segs m lo (usp - 192) ->
    realizes s0segs (mkCfg (MS (GREGS (Z_to_bv 64 0x13d20) xt0 xt1 xt2 E (Z_to_bv 64 r3) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6)
                             F (ret_pc (Z_to_bv 64 0x13d20)) fc None m (seg_rom s0segs)) MD) K.
  Proof.
    intros sx kk m MD J jb pFT pA2 pA1 pE E r1 r2 r3 c40 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 W KK D0 R1 R2 R3 SOME EH SC ST.
    prep. cps_pose SC as (FR2 & FR & DLC & DSB).
    cps_pose W as (AIV & VM & VO & AUX & [e ERR] & MI & CM & PR & SUB). pose proof (ai_inv_model AI AIV) as [Hh Hl].
    set (LX := opt r3 (pFT, r3, 262148) ++ opt r2 (pA2, r2, ARR2_SIZE) ++ opt r1 (pA1, r1, ARR1_SIZE)) in *.
    assert (LBE : LX ++ (pE, E, 55768) :: [] ++ LB = opt r3 (pFT, r3, 262148) ++ opt r2 (pA2, r2, ARR2_SIZE) ++ opt r1 (pA1, r1, ARR1_SIZE) ++ [(pE, E, 55768)] ++ LB).
    { subst LX. rewrite <- !app_assoc. reflexivity. }
    assert (INE : In (pE, E, 55768) (LX ++ (pE, E, 55768) :: [] ++ LB)) by (apply in_or_app; right; left; reflexivity).
    rewrite <- LBE in W, AIV.
    pose proof (fresh_id _ _ _ _ _ _ _ _ AIV) as NPE.
    cps_pose (blk_facts _ _ _ _ pE E 55768 AIV INE) as (RE1 & _ & _ & RE2 & RE5).
    pose proof (E_dst_apart _ _ _ _ _ _ _ _ AIV D0) as DED.
    assert (WIV : Forall (wiv_ok (LX ++ (pE, E, 55768) :: [] ++ LB)) [(E + 40, E + 48)]).
    { apply Forall_cons; [| apply Forall_nil]. right; right; right. exists pE, E, 55768. split; [exact INE|]. split; [exact NPE|]. cbn. lia. }
    assert (R3B : r3 < 2 ^ 64).
    { destruct (Z.eq_dec r3 0) as [->|NZ3]; [lia|].
      cps_pose (blk_facts _ _ _ _ pFT r3 262148 AIV ltac:(subst LX; rewrite (opt_nz r3 _ NZ3); apply in_or_app; left; left; reflexivity)) as (_ & _ & _ & X & _). lia. }
    assert (R2B : r2 < 2 ^ 64).
    { destruct (Z.eq_dec r2 0) as [->|NZ2]; [lia|].
      cps_pose (blk_facts _ _ _ _ pA2 r2 ARR2_SIZE AIV ltac:(subst LX; rewrite (opt_nz r2 _ NZ2); apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; left; reflexivity)) as (_ & _ & _ & X & _).
      lia. }
    destruct (Z.eq_dec r1 0) as [R10 | R1NZ].
    - (* [comment removed for export] *)
      rewrite R10 in EH.
      eapply (evt_realizes s0segs _ _ MD K Hh Hl (wG3a m J E r2 r3 c40 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 _ xs6
                RE1 ltac:(unfold CEIL; bz_ceil; bz_params; lia) ltac:(lia) EH MI)).
      (intros ms; cps_intros (m1 & -> & MU01 & WM01 & MI1 & EH1)).
      pose proof (WLD_write _ _ _ _ _ _ _ W MU01 WM01 MI1 WIV) as W1.
      pose proof (STC_munch jb m m1 _ SC MU01 WM01 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as SC1.
      assert (ST1 : stk s0segs m1 lo (usp - 192)) by (eapply stk_transport_disjoint; [exact ST | exact MU01 | exact WM01 | cbn; lia]).
      eapply (CL_2 sx kk m1 MD J jb pFT pA2 pE E 0 r2 r3);
        [rewrite LBE, R10, opt_0 in W1; exact W1 | exact KK | exact D0 | exact R2 | exact R3 | exact EH1 | exact SC1 | exact ST1].
    - (* [comment removed for export] *)
      assert (RZ : r2 = 0 \/ r3 = 0) by lia.
      assert (INA : In (pA1, r1, ARR1_SIZE) (LX ++ (pE, E, 55768) :: [] ++ LB)).
      { subst LX. rewrite (opt_nz r1 _ R1NZ). apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. left; reflexivity. }
      cps_pose (blk_facts _ _ _ _ pA1 r1 ARR1_SIZE AIV INA) as (RA1 & _ & _ & RA2 & _).
      eapply (evt_realizes s0segs _ _ MD K Hh Hl (wG3b m J jb E r1 r2 r3 c40 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 _ xs6
                RE1 ltac:(unfold CEIL; bz_ceil; bz_params; lia) ltac:(lia) ltac:(lia) ltac:(lia) RZ EH FR MI)).
      (intros ms; cps_intros (xa2' & m1 & -> & MU01 & WM01 & MI1 & EH1 & FR1)).
      pose proof (WLD_write _ _ _ _ _ _ _ W MU01 WM01 MI1 WIV) as W1.
      pose proof (STC_munch jb m m1 _ SC MU01 WM01 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as SC1.
      assert (ST1 : stk s0segs m1 lo (usp - 192)) by (eapply stk_transport_disjoint; [exact ST | exact MU01 | exact WM01 | cbn; lia]).
      assert (LBE2 : LX ++ (pE, E, 55768) :: [] ++ LB = (opt r3 (pFT, r3, 262148) ++ opt r2 (pA2, r2, ARR2_SIZE)) ++ (pA1, r1, ARR1_SIZE) :: ([(pE, E, 55768)] ++ LB)).
      { subst LX. rewrite (opt_nz r1 _ R1NZ). rewrite <- !app_assoc. reflexivity. }
      rewrite LBE2 in W1.
      eapply (free_step sx kk m1 MD pA1 r1 ARR1_SIZE (opt r3 (pFT, r3, 262148) ++ opt r2 (pA2, r2, ARR2_SIZE)) ([(pE, E, 55768)] ++ LB) (usp - 192) K);
        [exact W1 | unfold c21_foreign, MMAP_THRESHOLD_C, MAX_REQ_C; lia | intros b Hb; apply in_or_app; right; right; exact Hb | exact ST1 | lia | lia | lia |].
      intros sx2 m2 MD2 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 W2 ST2 HP2.
      assert (INE2 : In (pE, E, 55768) ((opt r3 (pFT, r3, 262148) ++ opt r2 (pA2, r2, ARR2_SIZE)) ++ [(pE, E, 55768)] ++ LB)) by (apply in_or_app; right; left; reflexivity).
      pose proof (keep_blk _ _ m1 m2 (pE, E, 55768) E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 r3)) HP2 INE2 ltac:(cbn; lia)
                    ltac:(cbn [blk_addr blk_size fst snd]; cbv [cells_size csize S0_b2c_segA.EJ1w Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia) EH1) as EH2.
      pose proof (STC_heap jb m1 m2 _ (usp - 192) SC1 HP2 ltac:(lia) ltac:(apply in_or_app; right; right; exact (IND D0))) as SC2.
      rewrite (ret_pc_even 0x13dbc) by (first [lia | reflexivity]).
      eapply (CL_2 sx2 kk m2 MD2 J jb pFT pA2 pE E r1 r2 r3);
        [rewrite <- app_assoc in W2; exact W2 | exact KK | exact D0 | exact R2 | exact R3 | exact EH2 | exact SC2 | exact ST2].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation FRWR := (S0_b2c_segB.FRWR ra s0 s1 s2 s3 s4).
  Local Notation STRMX := S0_b2c_segC.STRMX.

  (* [comment removed for export] *)
  Definition EK (w0 w1 w2 w3 w4 w5 : word) (avo : Z) (w7 w8 w9 : word) (E : Z) (j8 : list byte) (rc dlv : Z) (m : word -> option byte) : Prop :=
    rw_cells s0segs m (usp - 128) (STRMX w0 w1 w2 w3 w4 w5 avo w7 w8 w9 E) /\ rw_cells s0segs m (usp - 48) FRWR /\
    rw_cells s0segs m (usp - 160) (S0_b2c_segC.FRE dl j8 rc) /\ rw_cells s0segs m dl [C4 (Z_to_bv 64 dlv)] /\
    b2bC_result s0segs rc dst nZ payload junk m dlv.
  Lemma EK_heap : forall w0 w1 w2 w3 w4 w5 avo w7 w8 w9 E j8 rc dlv m m' LBh SP,
    EK w0 w1 w2 w3 w4 w5 avo w7 w8 w9 E j8 rc dlv m -> heap_pres s0segs S0_layout LBh SP m m' -> SP <= usp - 160 -> In (pd, dst, nZ) LBh ->
    EK w0 w1 w2 w3 w4 w5 avo w7 w8 w9 E j8 rc dlv m'.
  Proof.
    (intros w0 w1 w2 w3 w4 w5 avo w7 w8 w9 E j8 rc dlv m m' LBh SP; cps_intros (A1 & A2 & A3 & A4 & A5); intros HP HSP INd). prep.
    split; [eapply keep_stk; [exact HP | | exact A1]; lia|]. split; [eapply keep_stk; [exact HP | | exact A2]; lia|].
    split; [eapply keep_stk; [exact HP | | exact A3]; lia|]. split; [eapply keep_stk; [exact HP | | exact A4]; lia|].
    eapply result_pres; [exact (pres_of_heap_pres _ _ _ _ _ HP) | | exact A5]. intros a D Ha. right; right. exists (pd, dst, nZ). split; [exact INd| cbn; lia].
  Qed.

  Lemma ENDC : forall sx m MD (cx : cctx) (g : eg) (e : est) (pFT pA2 pA1 pE : bid) (rc avo dlv : Z)
      (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 w0 w1 w2 w3 w4 w5 w7 w8 w9 : word),
    WLD sx ([(pFT, c_FT cx, 262148); (pA2, c_A2 cx, ARR2_SIZE); (pA1, c_A1 cx, ARR1_SIZE); (pE, c_E cx, 55768)] ++ LB) k m MD ->
    dst <> 0 -> c_bz cx + 5016 = usp - 128 ->
    rw_cells s0segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells s0segs m (usp - 128) (STRMX w0 w1 w2 w3 w4 w5 avo w7 w8 w9 (c_E cx)) ->
    rw_cells s0segs m (usp - 48) FRWR -> rw_cells s0segs m dl [C4 (Z_to_bv 64 dlv)] -> 0 <= dlv <= nZ -> - 2 ^ 63 <= rc < 2 ^ 63 ->
    b2bC_result s0segs rc dst nZ payload junk m dlv ->
    stk s0segs m lo (usp - 128) ->
    realizes s0segs (mkCfg (MS (mkR (Z_to_bv 64 0x15f04) (Z_to_bv 64 (usp - 128)) gp tp xt0 xt1 xt2 (Z_to_bv 64 dl) (Z_to_bv 64 rc)
                                  (Z_to_bv 64 (usp - 128)) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                  (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                             F (Z_to_bv 64 0x14528) fc None m (seg_rom s0segs)) MD) K.
  Proof.
    intros sx m MD cx g e pFT pA2 pA1 pE rc avo dlv xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 w0 w1 w2 w3 w4 w5 w7 w8 w9
      W D0 SA EH SM FR DLC DLV RC RES ST.
    prep. cps_pose W as (AIV & VM & VO & AUX & [er ERR] & MI & CM & PR & SUB). pose proof (ai_inv_model AI AIV) as [Hh Hl].
    set (LBc := [(pFT, c_FT cx, 262148); (pA2, c_A2 cx, ARR2_SIZE); (pA1, c_A1 cx, ARR1_SIZE); (pE, c_E cx, 55768)] ++ LB) in *.
    assert (IF : In (pFT, c_FT cx, 262148) LBc) by (left; reflexivity).
    assert (I2 : In (pA2, c_A2 cx, ARR2_SIZE) LBc) by (right; left; reflexivity).
    assert (I1 : In (pA1, c_A1 cx, ARR1_SIZE) LBc) by (do 2 right; left; reflexivity).
    assert (IE : In (pE, c_E cx, 55768) LBc) by (do 3 right; left; reflexivity).
    cps_pose (blk_facts _ _ _ _ _ _ _ AIV IF) as (RF1 & _ & _ & RF2 & _).
    cps_pose (blk_facts _ _ _ _ _ _ _ AIV I2) as (RA21 & _ & _ & RA22 & _).
    cps_pose (blk_facts _ _ _ _ _ _ _ AIV I1) as (RA11 & _ & _ & RA12 & _).
    cps_pose (blk_facts _ _ _ _ _ _ _ AIV IE) as (RE1 & RE4 & _ & RE2 & _).
    (* [comment removed for export] *)
    eapply (evt_realizes s0segs _ _ MD K Hh Hl (wE1 m cx g e rc avo xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 w0 w1 w2 w3 w4 w5 w7 w8 w9
              SA RE1 RE4 ltac:(unfold CEIL; bz_ceil; bz_params; lia) ltac:(lia) EH SM MI ST)).
    (intros ms; cps_intros (xa2' & m1 & j8 & -> & MU01 & WM01 & MI1 & ST1 & FR31 & EH1 & SM1)).
    assert (W1 : WLD sx LBc k m1 MD).
    { eapply WLD_write; [exact W | exact MU01 | exact WM01 | exact MI1 |]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (K1 : EK w0 w1 w2 w3 w4 w5 avo w7 w8 w9 (c_E cx) j8 rc dlv m1).
    { split; [exact SM1|]. split; [eapply rw_cells_transport; [exact FR | exact MU01 | exact WM01 | cbn; lia]|]. split; [exact FR31|].
      split; [eapply rw_cells_transport; [exact DLC | exact MU01 | exact WM01 | cbn; lia]|].
      eapply result_pres; [exact (pres_of_munch _ _ _ MU01 WM01) | | exact RES]. intros a D Ha. cbn.
      cps_pose (blk_facts _ _ _ _ pd dst nZ AIV (SUB _ (IND D0))) as (_ & _ & _ & X & _). lia. }
    clear EH SM FR DLC RES ST.
    (* [comment removed for export] *)
    change LBc with ([(pFT, c_FT cx, 262148); (pA2, c_A2 cx, ARR2_SIZE)] ++ (pA1, c_A1 cx, ARR1_SIZE) :: ([(pE, c_E cx, 55768)] ++ LB)) in W1.
    eapply (free_step sx k m1 MD pA1 (c_A1 cx) ARR1_SIZE _ _ (usp - 160) K);
      [exact W1 | unfold c21_foreign, MMAP_THRESHOLD_C, MAX_REQ_C; lia | intros b Hb; apply in_or_app; right; right; exact Hb | exact ST1 | lia | lia | lia |].
    intros sx2 m2 MD2 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 W2 ST2 HP2.
    pose proof (keep_blk _ _ m1 m2 (pE, c_E cx, 55768) (c_E cx) (EHEAD1 cx g e) HP2 ltac:(apply in_or_app; right; left; reflexivity) ltac:(cbn; lia)
                  ltac:(cbn [blk_addr blk_size fst snd]; cbv [cells_size csize EHEAD1 Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia) EH1) as EH2.
    pose proof (EK_heap _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 m2 _ _ K1 HP2 ltac:(lia) ltac:(apply in_or_app; right; right; exact (IND D0))) as K2.
    cps_pose W2 as (AIV2 & _ & _ & _ & _ & MI2 & _). pose proof (ai_inv_model AI AIV2) as [Hh2 Hl2]. pose proof K2 as (SM2 & _).
    rewrite (ret_pc_even 0x14578) by (first [lia | reflexivity]).
    (* [comment removed for export] *)
    eapply (evt_realizes s0segs _ _ MD2 K Hh2 Hl2 (wE2 m2 cx g e avo _ yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 w0 w1 w2 w3 w4 w5 w7 w8 w9
              RE1 ltac:(unfold CEIL; bz_ceil; bz_params; lia) ltac:(lia) EH2 SM2 MI2)).
    intros ms ->.
    change ([(pFT, c_FT cx, 262148); (pA2, c_A2 cx, ARR2_SIZE)] ++ [(pE, c_E cx, 55768)] ++ LB)
      with ([(pFT, c_FT cx, 262148)] ++ (pA2, c_A2 cx, ARR2_SIZE) :: ([(pE, c_E cx, 55768)] ++ LB)) in W2.
    eapply (free_step sx2 k m2 MD2 pA2 (c_A2 cx) ARR2_SIZE _ _ (usp - 160) K);
      [exact W2 | unfold c21_foreign, MMAP_THRESHOLD_C, MAX_REQ_C; lia | intros b Hb; apply in_or_app; right; right; exact Hb | exact ST2 | lia | lia | lia |].
    intros sx3 m3 MD3 zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 W3 ST3 HP3.
    pose proof (keep_blk _ _ m2 m3 (pE, c_E cx, 55768) (c_E cx) (EHEAD1 cx g e) HP3 ltac:(apply in_or_app; right; left; reflexivity) ltac:(cbn; lia)
                  ltac:(cbn [blk_addr blk_size fst snd]; cbv [cells_size csize EHEAD1 Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia) EH2) as EH3.
    pose proof (EK_heap _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 m3 _ _ K2 HP3 ltac:(lia) ltac:(apply in_or_app; right; right; exact (IND D0))) as K3.
    cps_pose W3 as (AIV3 & _ & _ & _ & _ & MI3 & _). pose proof (ai_inv_model AI AIV3) as [Hh3 Hl3]. pose proof K3 as (SM3 & _).
    rewrite (ret_pc_even 0x1458c) by (first [lia | reflexivity]).
    (* [comment removed for export] *)
    eapply (evt_realizes s0segs _ _ MD3 K Hh3 Hl3 (wE3 m3 cx g e avo _ zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 w0 w1 w2 w3 w4 w5 w7 w8 w9
              RE1 ltac:(unfold CEIL; bz_ceil; bz_params; lia) ltac:(lia) EH3 SM3 MI3)).
    intros ms ->.
    change ([(pFT, c_FT cx, 262148)] ++ [(pE, c_E cx, 55768)] ++ LB) with ([] ++ (pFT, c_FT cx, 262148) :: ([(pE, c_E cx, 55768)] ++ LB)) in W3.
    eapply (free_step sx3 k m3 MD3 pFT (c_FT cx) 262148 _ _ (usp - 160) K);
      [exact W3 | unfold c21_foreign, MMAP_THRESHOLD_C, MAX_REQ_C; lia | intros b Hb; apply in_or_app; right; right; exact Hb | exact ST3 | lia | lia | lia |].
    intros sx4 m4 MD4 vt0 vt1 vt2 va0 va1 va2 va3 va4 va5 va6 va7 vt3 vt4 vt5 vt6 W4 ST4 HP4. cbn [app] in W4, HP4.
    pose proof (EK_heap _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 m4 _ _ K3 HP4 ltac:(lia) ltac:(right; exact (IND D0))) as K4.
    cps_pose W4 as (AIV4 & _ & _ & _ & _ & MI4 & _). pose proof (ai_inv_model AI AIV4) as [Hh4 Hl4]. pose proof K4 as (SM4 & _).
    rewrite (ret_pc_even 0x145a0) by (first [lia | reflexivity]).
    (* [comment removed for export] *)
    eapply (evt_realizes s0segs _ _ MD4 K Hh4 Hl4 (wE4 m4 (c_E cx) avo _ vt0 vt1 vt2 va0 va1 va2 va3 va4 va5 va6 va7 vt3 vt4 vt5 vt6 w0 w1 w2 w3 w4 w5 w7 w8 w9
              ltac:(lia) SM4 MI4)).
    intros ms ->.
    change ((pE, c_E cx, 55768) :: LB) with ([] ++ (pE, c_E cx, 55768) :: LB) in W4.
    eapply (free_step sx4 k m4 MD4 pE (c_E cx) 55768 [] LB (usp - 160) K);
      [exact W4 | unfold c21_foreign; lia | intros b Hb; exact Hb | exact ST4 | lia | lia | lia |].
    intros sx5 m5 MD5 ut0 ut1 ut2 ua0 ua1 ua2 ua3 ua4 ua5 ua6 ua7 ut3 ut4 ut5 ut6 W5 ST5 HP5. cbn [app] in W5, HP5.
    cps_pose (EK_heap _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 m5 _ _ K4 HP5 ltac:(lia) (IND D0)) as (SM5 & FR5 & FR35 & DLC5 & RES5).
    cps_pose W5 as (AIV5 & _ & _ & _ & _ & MI5 & _). pose proof (ai_inv_model AI AIV5) as [Hh5 Hl5].
    rewrite (ret_pc_even 0x145b0) by (first [lia | reflexivity]).
    (* [comment removed for export] *)
    eapply (evt_realizes s0segs _ _ MD5 K Hh5 Hl5 (wE5 m5 (c_E cx) avo rc j8 _ ut0 ut1 ut2 ua0 ua1 ua2 ua3 ua4 ua5 ua6 ua7 ut3 ut4 ut5 ut6 w0 w1 w2 w3 w4 w5 w7 w8 w9
              SM5 FR35 FR5 MI5 ST5 RC)).
    intros ms PO.
    eapply (FIN sx5 k m5 MD5 rc dlv [(usp - 160, usp)]); [exact W5 | lia | apply Forall_cons; [cbn; lia| apply Forall_nil] | exact DLC5 | exact DLV | exact RES5 | exact PO].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EBR (J : list byte) (E : Z) (m : word -> option byte) : Prop :=
    rw_cells s0segs m (E + 128) [CB 256 (jseg J 128 256)] /\ rw_cells s0segs m (E + 384) [CB 256 (jseg J 384 256)] /\
    rw_cells s0segs m (E + 640) (EJ2 J) /\ rw_cells s0segs m (E + 672) [CB (Z.to_nat 55096) (jseg J 672 55096)].
  Lemma EBR_heap : forall J E m m' LBh SP pE, EBR J E m -> heap_pres s0segs S0_layout LBh SP m m' -> In (pE, E, 55768) LBh -> EBR J E m'.
  Proof.
    (intros J E m m' LBh SP pE; cps_intros (B1 & B2 & B3 & B4); intros HP IN).
    assert (KP : forall A cs, E <= A -> A + Z.of_nat (cells_size cs) <= E + 55768 -> rw_cells s0segs m A cs -> rw_cells s0segs m' A cs).
    { intros A cs H1 H2 H. eapply (keep_blk _ _ m m' (pE, E, 55768)); [exact HP | exact IN | cbn; lia | cbn [blk_addr blk_size fst snd]; lia | exact H]. }
    split; [apply KP; [lia | cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia | exact B1]|].
    split; [apply KP; [lia | cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia | exact B2]|].
    split; [apply KP; [lia | cbv [cells_size csize EJ2 jcells jcell ESHAPE2 Nat.eqb Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia | exact B3]|].
    apply KP; [lia | rewrite size_CB1, Z2Nat.id by lia; lia | exact B4].
  Qed.
  Lemma EBR_munch : forall J E m m' W, EBR J E m -> munch W m m' -> wmono s0segs m m' -> disjoint_from W (E + 128) 55640 -> EBR J E m'.
  Proof.
    (intros J E m m' W; cps_intros (B1 & B2 & B3 & B4); intros MU WM D).
    assert (KP : forall A cs, E + 128 <= A -> A + Z.of_nat (cells_size cs) <= E + 55768 -> rw_cells s0segs m A cs -> rw_cells s0segs m' A cs).
    { intros A cs H1 H2 H. eapply rw_cells_transport; [exact H | exact MU | exact WM | eapply disjoint_from_sub; [exact D | lia | lia]]. }
    split; [apply KP; [lia | cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia | exact B1]|].
    split; [apply KP; [lia | cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia | exact B2]|].
    split; [apply KP; [lia | cbv [cells_size csize EJ2 jcells jcell ESHAPE2 Nat.eqb Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia | exact B3]|].
    apply KP; [lia | rewrite size_CB1, Z2Nat.id by lia; lia | exact B4].
  Qed.
  Lemma keep_zero : forall LBi SP m m' (p : bid) (A n : Z), heap_pres s0segs S0_layout LBi SP m m' -> In (p, A, n) LBi -> 0 <= n ->
    rw_cells s0segs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
    rw_cells s0segs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
  Proof.
    intros LBi SP m m' p A n HP IN Hn H. eapply (keep_blk _ _ m m' (p, A, n) A _ HP IN); [cbn; lia | cbn [blk_addr blk_size fst snd]; rewrite size_CB1, Z2Nat.id by lia; lia | exact H].
  Qed.

  (* [comment removed for export] *)
  Lemma fresh_apart : forall sx LX L2 m MD p A n b, ai_inv AI sx (LX ++ (p, A, n) :: L2 ++ LB) m MD -> In b LB ->
    A + n <= blk_addr b \/ blk_addr b + blk_size b <= A.
  Proof.
    intros sx LX L2 m MD p A n b AIV Hb.
    assert (INA : In (p, A, n) (LX ++ (p, A, n) :: L2 ++ LB)) by (apply in_or_app; right; left; reflexivity).
    assert (INb : In b (LX ++ (p, A, n) :: L2 ++ LB)) by (apply in_or_app; right; right; apply in_or_app; right; exact Hb).
    assert (NE : (p, A, n) <> b).
    { intros X. apply (fresh_id _ _ _ _ _ _ _ _ AIV). replace p with (blk_id b) by (rewrite <- X; reflexivity). apply in_map. exact Hb. }
    pose proof (blk_apart _ _ _ _ _ _ AIV INA INb NE) as D. cbn [blk_addr blk_size fst snd] in D. exact D.
  Qed.

  (* [comment removed for export] *)
  Lemma src_now : forall m, pres P0 m0 m -> u8ro s0segs m src payload.
  Proof.
    intros m PR. unfold u8ro. eapply pres_bytes_at; [exact PR | exact SRC0 |]. rewrite PL. intros a Ha. split.
    - eapply client_range_addr; [exact CR | exact Ha].
    - unfold b2bC_out. intros [[D X]|X]; [pose proof (AP1 D); lia | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition POSTB (cx : cctx) (jb : list byte) (m1 : word -> option byte) : machine_state -> Prop :=
    bzCompress_postB s0segs S0C cx dst nZ DBZA DBZF (eg_init (Z_to_bv 64 0)) est0 (z_b2b (map bv_unsigned payload) nZ) src payload junk
      (jw4 jb 20) (jw4 jb 44) sv (Z_to_bv 64 0x15ecc) (Z_to_bv 64 (usp - 128)) gp tp (Z_to_bv 64 dl) (Z_to_bv 64 0)
      (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 F fc lo (bzCompress_WB cx dst nZ (usp - 128)) m1.

  Lemma BZCALL : forall m1 MD (cx : cctx) (jb : list byte) (u0 u1 u2 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
    m_halted MD = None -> m_vm_lazy MD = [] ->
    c_bz cx + 5016 = usp - 128 ->
    emem cx s0segs (eg_init (Z_to_bv 64 0)) est0 m1 -> amem cx s0segs est0 m1 -> b2bC_mem S0CI m1 sv ->
    rw_cells s0segs m1 (usp - 128) (STRMB cx dst nZ DBZA DBZF (z_b2b (map bv_unsigned payload) nZ) src (jw4 jb 20) (jw4 jb 44)) ->
    u8arr s0segs m1 dst junk -> Z.of_nat (length junk) = nZ -> out_okB S0C cx dst nZ -> u8ro s0segs m1 src payload ->
    pay_condB cx dst nZ src payload -> mem_inv s0segs m1 -> stk s0segs m1 lo (usp - 128) ->
    cctx_ok cx -> cctx_sep cx -> cctx_img S0C cx ->
    (forall ms', POSTB cx jb m1 ms' -> realizes s0segs (mkCfg ms' MD) K) ->
    realizes s0segs (mkCfg (MS (mkR (Z_to_bv 64 0x15ecc) (Z_to_bv 64 (usp - 128)) gp tp u0 u1 u2 (Z_to_bv 64 dl) (Z_to_bv 64 0)
                                  (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 2) b2 b3 b4 b5 b6 b7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src)
                                  s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                             F (Z_to_bv 64 0x13ea0) fc None m1 (seg_rom s0segs)) MD) K.
  Proof.
    intros m1 MD cx jb u0 u1 u2 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Hh Hl CBZ EM AM CM SMB OBM LOB OOK PLM PAY MI ST CX SEP IMG KK.
    prep.
    pose proof (bytes_of_payload payload) as BY.
    assert (FT0 : forall i, 0 <= zget znew i < 4294967296) by (intros i; rewrite zget_znew; lia).
    assert (NZ0 : 0 <= nZ) by (clear - NZ LEN; lia).
    assert (PLB : Z.of_nat (length (map bv_unsigned payload)) < 67108864) by (rewrite length_map; clear - PL LEN; lia).
    pose proof (HCXB_init cx nZ (Z_to_bv 64 0) (map bv_unsigned payload) znew znew znew znew znew znew znew znew znew znew znew znew 0 0 0 0 0
                  zbok_znew zbok_znew FT0 NZ0 PLB BY) as HX.
    cbv zeta in HX. change (est_init znew znew znew znew znew znew znew znew znew znew znew znew 0 0 0 0 0) with est0 in HX.
    pose proof (hc_lawsB_intro cbm_ok cb_facts (fun g e _ F => F)) as LAWS.
    pose proof (S0_bzCompressB HCXB cb_facts (S0_compressBlock HBS)) as BZC. unfold bzCompress_specB in BZC.
    specialize (BZC (Z_to_bv 64 0x15ecc) (Z_to_bv 64 (usp - 128)) gp tp u0 u1 u2 (Z_to_bv 64 dl) (Z_to_bv 64 0)
                    (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 2) b2 b3 b4 b5 b6 b7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
                    F fc m1 cx dst nZ DBZA DBZF (eg_init (Z_to_bv 64 0)) est0 (z_b2b (map bv_unsigned payload) nZ) src payload junk (jw4 jb 20) (jw4 jb 44) sv lo).
    cbv zeta in BZC. change (ci_segs S0C) with s0segs in BZC. change (ci_bzCompress S0C) with 81568 in BZC.
    assert (U128 : bv_unsigned (Z_to_bv 64 (usp - 128)) = usp - 128) by (apply unsigned_lit; clear - STK SPH LO; lia).
    rewrite U128 in BZC.
    assert (SOK : strm_okB cx (usp - 128)).
    { unfold strm_okB, BZF_STRM. rewrite CBZ. split; [clear; lia|]. split; [clear - SPH; lia|].
      replace (usp - 128) with (16 * qsp - 8 * 16) by (clear - ALQ; lia). apply mod8_of_q16. }
    assert (M16 : (usp - 128) mod 16 = 0) by (replace (usp - 128) with (16 * qsp - 16 * 8) by (clear - ALQ; lia); apply mod16_of_q16).
    assert (LOS : lo + BZC_STACKB <= usp - 128) by (unfold BZC_STACKB; clear - STK; lia).
    assert (CL' : CEIL <= lo) by (unfold CEIL; exact LO).
    assert (A0E : Z_to_bv 64 (usp - 128) = Z_to_bv 64 (c_bz cx + BZF_STRM)) by (unfold BZF_STRM; rewrite CBZ; reflexivity).
    assert (SMB' : rw_cells s0segs m1 (c_bz cx + BZF_STRM) (STRMB cx dst nZ DBZA DBZF (z_b2b (map bv_unsigned payload) nZ) src (jw4 jb 20) (jw4 jb 44)))
      by (unfold BZF_STRM; rewrite CBZ; exact SMB).
    assert (AVI : z_avail_in (z_b2b (map bv_unsigned payload) nZ) = Z.of_nat (length payload)) by (cbn [z_avail_in z_b2b]; rewrite length_map; reflexivity).
    unfold b2bC_mem in CM. cbn [bc_ci S0CI] in CM.
    specialize (BZC A0E eq_refl eq_refl eq_refl AVI eq_refl eq_refl EM AM CM SMB' SOK OBM LOB OOK PLM eq_refl PAY MI ST LOS CL' M16 CX SEP IMG LAWS HX).
    eapply (evt_realizes s0segs _ _ MD K Hh Hl BZC).
    intros ms' PO. apply KK. exact PO.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma POSTC : forall sx m1 MD (J jb : list byte) (pFT pA2 pA1 pE : bid) (E r1 r2 r3 : Z) ms',
    let cx := CC E r1 r2 r3 (usp - 128 - 5016) 0 J [] in
    WLD sx ([(pFT, r3, 262148); (pA2, r2, ARR2_SIZE); (pA1, r1, ARR1_SIZE); (pE, E, 55768)] ++ LB) k m1 MD ->
    dst <> 0 -> length junk = Z.to_nat nZ ->
    rw_cells s0segs m1 (usp - 48) FRWR -> rw_cells s0segs m1 dl [C4 (Z_to_bv 64 nZ)] ->
    POSTB cx jb m1 ms' ->
    realizes s0segs (mkCfg ms' MD) K.
  Proof.
    intros sx m1 MD J jb pFT pA2 pA1 pE E r1 r2 r3 ms' cx W D0 LJK FRR DLC1 PO.
    prep. cps_pose W as (AIV1 & VM1 & VO1 & AUX1 & [er1 ERR1] & MI1 & CM1 & PR1 & SUB1).
    set (LBc := [(pFT, r3, 262148); (pA2, r2, ARR2_SIZE); (pA1, r1, ARR1_SIZE); (pE, E, 55768)] ++ LB) in *.
    assert (IF : In (pFT, r3, 262148) LBc) by (left; reflexivity).
    assert (I2 : In (pA2, r2, ARR2_SIZE) LBc) by (right; left; reflexivity).
    assert (I1 : In (pA1, r1, ARR1_SIZE) LBc) by (do 2 right; left; reflexivity).
    assert (IE : In (pE, E, 55768) LBc) by (do 3 right; left; reflexivity).
    assert (ID : In (pd, dst, nZ) LBc) by (do 4 right; exact (IND D0)).
    cps_pose (blk_facts _ _ _ _ _ _ _ AIV1 IE) as (RE1 & _ & _ & RE2 & _).
    cps_pose (blk_facts _ _ _ _ _ _ _ AIV1 ID) as (RD1 & _ & RD3 & RD2 & _).
    pose proof (fresh_id sx [(pFT, r3, 262148); (pA2, r2, ARR2_SIZE); (pA1, r1, ARR1_SIZE)] pE E 55768 [] m1 MD AIV1) as NPE.
    pose proof (fresh_id sx [(pFT, r3, 262148); (pA2, r2, ARR2_SIZE)] pA1 r1 ARR1_SIZE [(pE, E, 55768)] m1 MD AIV1) as NP1.
    pose proof (fresh_id sx [(pFT, r3, 262148)] pA2 r2 ARR2_SIZE [(pA1, r1, ARR1_SIZE); (pE, E, 55768)] m1 MD AIV1) as NP2.
    pose proof (fresh_id sx [] pFT r3 262148 [(pA2, r2, ARR2_SIZE); (pA1, r1, ARR1_SIZE); (pE, E, 55768)] m1 MD AIV1) as NPF.
    (* [comment removed for export] *)
    unfold POSTB, bzCompress_postB in PO.
    cps_destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & g2 & PO).
    pose proof (b2b_round_trip0 false (map bv_unsigned payload) nZ (Z.of_nat (length (map bv_unsigned payload))) (bytes_of_payload payload)
                  ltac:(clear - NZ LEN; lia) ltac:(clear; lia)) as RT.
    cbv zeta in RT. destruct RT as [RT _].
    set (R := bzCompress znew est0 (z_b2b (map bv_unsigned payload) nZ) BZ_FINISH) in PO, RT. clearbody R. destruct R as [[ret e2] z2].
    cbv beta iota in PO. cbv beta iota in RT.
    cps_destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & EM2 & AM2 & CM2 & SM2 & OB2 & PLM2 & [AVO2 OLEN2] & EOK2).
    rewrite unsigned_lit in ST2 by (clear - STK SPH LO; lia).
    set (str := enc_stream est0 (map bv_unsigned payload)) in RT.
    (* [comment removed for export] *)
    assert (W2 : WLD sx LBc k m2 MD).
    { eapply WLD_write; [exact W | exact MU2 | exact WM2 | exact MI2 |].
      unfold bzCompress_WB. cbn [c_E c_A1 c_A2 c_FT c_bz cx]. unfold ESTATE_SIZE, FTAB_WORDS, BZF_STRM, BZC_STACKB.
      apply Forall_cons; [right; right; right; exists pE, E, 55768; split; [exact IE|]; split; [exact NPE| cbn; clear; lia]|].
      apply Forall_cons; [right; right; right; exists pA1, r1, ARR1_SIZE; split; [exact I1|]; split; [exact NP1| cbn; clear; lia]|].
      apply Forall_cons; [right; right; right; exists pA2, r2, ARR2_SIZE; split; [exact I2|]; split; [exact NP2| cbn; clear; lia]|].
      apply Forall_cons; [right; right; right; exists pFT, r3, 262148; split; [exact IF|]; split; [exact NPF| cbn; clear; lia]|].
      apply Forall_cons; [right; right; left; cbn; clear - D0; split; [exact D0| lia]|].
      apply Forall_cons; [left; cbn; clear - LO STK; lia|].
      apply Forall_cons; [left; cbn; clear - LO STK; lia| apply Forall_nil]. }
    assert (DJ2 : forall A n, CEIL <= A -> (A + n <= usp - 128 - 16528 \/ usp - 48 <= A) -> disjoint_from (bzCompress_WB cx dst nZ (usp - 128)) A n).
    { intros A n H1 H2. unfold bzCompress_WB. cbn [c_E c_A1 c_A2 c_FT c_bz cx disjoint_from]. unfold ESTATE_SIZE, FTAB_WORDS, BZF_STRM, BZC_STACKB, CEIL in *.
      cps_pose (blk_facts _ _ _ _ _ _ _ AIV1 IF) as (_ & _ & _ & RF2 & _).
      cps_pose (blk_facts _ _ _ _ _ _ _ AIV1 I2) as (_ & _ & _ & RA22 & _).
      cps_pose (blk_facts _ _ _ _ _ _ _ AIV1 I1) as (_ & _ & _ & RA12 & _).
      clear - H1 H2 RF2 RA22 RA12 RE2 RD2. repeat split; lia. }
    assert (FRR2 : rw_cells s0segs m2 (usp - 48) FRWR) by (eapply rw_cells_transport; [exact FRR | exact MU2 | exact WM2 | apply DJ2; cbn; unfold CEIL; clear - LO STK; lia]).
    assert (DLC2 : rw_cells s0segs m2 dl [C4 (Z_to_bv 64 nZ)]) by (eapply rw_cells_transport; [exact DLC1 | exact MU2 | exact WM2 | apply DJ2; cbn; unfold CEIL; clear - LO STK DL1; lia]).
    cps_pose W2 as (AIV2 & _ & _ & _ & _ & _ & _ & _ & _). pose proof (ai_inv_model AI AIV2) as [Hh2 Hl2].
    pose proof EM2 as (EH12 & _).
    unfold STRMB in SM2. cbn [c_bz c_E cx] in SM2. unfold BZF_STRM in SM2. replace (usp - 128 - 5016 + 5016) with (usp - 128) in SM2 by (clear; lia).
    assert (LOUT : (length (z_outr z2) <= length junk)%nat) by (clear - LJK AVO2 OLEN2; lia).
    destruct (Z.le_gt_cases (Z.of_nat (length str)) nZ) as [FIT | OVF].
    - (* [comment removed for export] *)
      destruct RT as [RT1 _]. cps_destruct (RT1 FIT) as (-> & OUTR & AVO & _ & _). clear RT1.
      rewrite AVO in SM2. unfold BzCDriver.BZ_STREAM_END.
      eapply (evt_realizes s0segs _ _ MD K Hh2 Hl2 (wRC4 m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 _ _ _ _ _ _ _ _ _ (nZ - Z.of_nat (length str)) E
                MI2 ltac:(clear - FIT; lia) SM2 DLC2)).
      (intros ms; cps_intros (xa1' & m3 & -> & MU3 & WM3 & MI3 & SM3 & DLC3)).
      assert (W3 : WLD sx LBc k m3 MD).
      { eapply WLD_write; [exact W2 | exact MU3 | exact WM3 | exact MI3 | apply Forall_cons; [right; left; cbn; split; reflexivity | apply Forall_nil]]. }
      assert (EH13 : rw_cells s0segs m3 E (EHEAD1 cx g2 e2)).
      { eapply rw_cells_transport; [exact EH12 | exact MU3 | exact WM3 |].
        cbv [cells_size csize EHEAD1 Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. cbn [disjoint_from]. split; [clear - RE2 DL1 LO STK; lia| exact I]. }
      assert (FRR3 : rw_cells s0segs m3 (usp - 48) FRWR) by (eapply rw_cells_transport; [exact FRR2 | exact MU3 | exact WM3 | cbn; clear - DL1; lia]).
      assert (ST3 : stk s0segs m3 lo (usp - 128)) by (eapply stk_transport_disjoint; [exact ST2 | exact MU3 | exact WM3 | cbn; clear - DL1; lia]).
      assert (OB3 : u8arr s0segs m3 dst (map (Z_to_bv 8) str ++ skipn (length str) junk)).
      { rewrite OUTR, outb_eq, rev_involutive, length_rev in OB2.
        eapply u8arr_transport; [exact OB2 | exact MU3 | exact WM3 |]. rewrite length_app, length_map, length_skipn. cbn [disjoint_from].
        pose proof (AP3 D0) as X. clear - X FIT LJK NZ LEN. split; [lia| exact I]. }
      eapply (ENDC sx m3 MD cx g2 e2 pFT pA2 pA1 pE 0 (nZ - Z.of_nat (length str)) (nZ - (nZ - Z.of_nat (length str))));
        [exact W3 | exact D0 | cbn [c_bz cx]; clear; lia | exact EH13 | exact SM3 | exact FRR3 | exact DLC3
        | clear - FIT; lia | clear; lia | | exact ST3].
      right; right. exists znew, znew, znew, znew, znew, znew, znew, znew, znew, znew, znew, znew, 0, 0, 0, 0, 0, (skipn (length str) junk).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. cbv zeta.
      change (enc_stream (est_init znew znew znew znew znew znew znew znew znew znew znew znew 0 0 0 0 0) (map bv_unsigned payload)) with str.
      split; [exact D0|]. left. split; [reflexivity|]. split; [exact FIT|]. split; [clear; lia|].
      apply (u8arr_split2 m3 dst _ _ _ _ OB3); [rewrite length_map; reflexivity | rewrite length_skipn; clear - FIT LJK NZ LEN; lia].
    - (* [comment removed for export] *)
      destruct RT as [_ RT2]. cps_destruct (RT2 OVF) as (-> & OUTR & AVO). clear RT2.
      rewrite AVO in SM2. unfold BzCDriver.BZ_FINISH_OK.
      eapply (evt_realizes s0segs _ _ MD K Hh2 Hl2 (wRC3 m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 MI2)).
      intros ms ->.
      eapply (ENDC sx m2 MD cx g2 e2 pFT pA2 pA1 pE (-8) 0 nZ);
        [exact W2 | exact D0 | cbn [c_bz cx]; clear; lia | exact EH12 | exact SM2 | exact FRR2 | exact DLC2
        | clear - NZ LEN; lia | clear; lia | | exact ST2].
      right; right. exists znew, znew, znew, znew, znew, znew, znew, znew, znew, znew, znew, znew, 0, 0, 0, 0, 0, (outb (z_outr z2) junk).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. cbv zeta.
      change (enc_stream (est_init znew znew znew znew znew znew znew znew znew znew znew znew 0 0 0 0 0) (map bv_unsigned payload)) with str.
      split; [exact D0|]. right. split; [reflexivity|]. split; [exact OVF|]. split; [reflexivity|].
      replace (Z.to_nat nZ) with (length (outb (z_outr z2) junk)) by (rewrite outb_length_nat by exact LOUT; exact LJK).
      exact (rw_cells_of_u8arr _ _ _ _ OB2).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma SUCC : forall sx m MD (J jb : list byte) (pFT pA2 pA1 pE : bid) (E r1 r2 r3 : Z) (c40 : word)
      (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 : word),
    WLD sx ([(pFT, r3, 262148); (pA2, r2, ARR2_SIZE); (pA1, r1, ARR1_SIZE); (pE, E, 55768)] ++ LB) k m MD ->
    dst <> 0 -> Z.of_nat (length J) = 55768 -> Z.of_nat (length jb) = 56 ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) c40) ->
    EBR J E m -> STC jb m -> stk s0segs m lo (usp - 192) ->
    rw_cells s0segs m r1 [CB (Z.to_nat ARR1_SIZE) (repeat (Z_to_bv 8 0) (Z.to_nat ARR1_SIZE))] ->
    rw_cells s0segs m r2 [CB (Z.to_nat ARR2_SIZE) (repeat (Z_to_bv 8 0) (Z.to_nat ARR2_SIZE))] ->
    rw_cells s0segs m r3 [CB (Z.to_nat 262148) (repeat (Z_to_bv 8 0) (Z.to_nat 262148))] ->
    realizes s0segs (mkCfg (MS (mkR (Z_to_bv 64 0x13d20) (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                                  (Z_to_bv 64 r3) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                  (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 (Z_to_bv 64 ARR1_SIZE) s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                             F (ret_pc (Z_to_bv 64 0x13d20)) fc None m (seg_rom s0segs)) MD) K.
  Proof.
    (intros sx m MD J jb pFT pA2 pA1 pE E r1 r2 r3 c40 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 W D0 LJ LJB EH; cps_intros (MIDa & MIDb & EH2 & REST); intros SC ST AR1 AR2 AR3).
    prep. cps_pose SC as (FR2 & FR & DLC & DSB).
    cps_pose W as (AIV & VM & VO & AUX & [er ERR] & MI & CM & PR & SUB). pose proof (ai_inv_model AI AIV) as [Hh Hl].
    set (LBc := [(pFT, r3, 262148); (pA2, r2, ARR2_SIZE); (pA1, r1, ARR1_SIZE); (pE, E, 55768)] ++ LB) in *.
    assert (IF : In (pFT, r3, 262148) LBc) by (left; reflexivity).
    assert (I2 : In (pA2, r2, ARR2_SIZE) LBc) by (right; left; reflexivity).
    assert (I1 : In (pA1, r1, ARR1_SIZE) LBc) by (do 2 right; left; reflexivity).
    assert (IE : In (pE, E, 55768) LBc) by (do 3 right; left; reflexivity).
    assert (ID : In (pd, dst, nZ) LBc) by (do 4 right; exact (IND D0)).
    cps_pose (blk_facts _ _ _ _ _ _ _ AIV IF) as (RF1 & RF4 & _ & RF2 & RF5).
    cps_pose (blk_facts _ _ _ _ _ _ _ AIV I2) as (RA21 & RA24 & _ & RA22 & RA25).
    cps_pose (blk_facts _ _ _ _ _ _ _ AIV I1) as (RA11 & RA14 & _ & RA12 & RA15).
    cps_pose (blk_facts _ _ _ _ _ _ _ AIV IE) as (RE1 & RE4 & _ & RE2 & RE5).
    cps_pose (blk_facts _ _ _ _ _ _ _ AIV ID) as (RD1 & RD4 & RD3 & RD2 & RD5).
    cbn [al_img_lo al_img_hi S0_layout] in RF5, RA25, RA15, RE5, RD5.
    (* [comment removed for export] *)
    Ltac ap H AIV Ix Iy := pose proof (blk_apart _ _ _ _ _ _ AIV Ix Iy ltac:(intros X; injection X; lia)) as H; cbn [blk_addr blk_size fst snd] in H.
    ap D_E_A1 AIV IE I1. ap D_E_A2 AIV IE I2. ap D_E_F AIV IE IF. ap D_A1_A2 AIV I1 I2. ap D_A1_F AIV I1 IF. ap D_A2_F AIV I2 IF.
    pose proof (fresh_apart sx [] [(pA2, r2, ARR2_SIZE); (pA1, r1, ARR1_SIZE); (pE, E, 55768)] m MD pFT r3 262148 _ AIV (IND D0)) as D_F_D.
    pose proof (fresh_apart sx [(pFT, r3, 262148)] [(pA1, r1, ARR1_SIZE); (pE, E, 55768)] m MD pA2 r2 ARR2_SIZE _ AIV (IND D0)) as D_A2_D.
    pose proof (fresh_apart sx [(pFT, r3, 262148); (pA2, r2, ARR2_SIZE)] [(pE, E, 55768)] m MD pA1 r1 ARR1_SIZE _ AIV (IND D0)) as D_A1_D.
    pose proof (fresh_apart sx [(pFT, r3, 262148); (pA2, r2, ARR2_SIZE); (pA1, r1, ARR1_SIZE)] [] m MD pE E 55768 _ AIV (IND D0)) as D_E_D.
    cbn [blk_addr blk_size fst snd] in D_F_D, D_A2_D, D_A1_D, D_E_D.
    pose proof (fresh_id sx [(pFT, r3, 262148); (pA2, r2, ARR2_SIZE); (pA1, r1, ARR1_SIZE)] pE E 55768 [] m MD AIV) as NPE.
    (* [comment removed for export] *)
    set (cx := CC E r1 r2 r3 (usp - 128 - 5016) 0 J []).
    assert (CX : cctx_ok cx).
    { unfold cctx_ok; cbv zeta. cbn [c_E c_A1 c_A2 c_FT c_J cx]. unfold ESTATE_SIZE, FTAB_WORDS, CEIL.
      repeat match goal with |- _ /\ _ => split end;
      first [exact I | assumption | clear - RF2; lia]. }
    assert (SEP : cctx_sep cx).
    { unfold cctx_sep, apart; cbv zeta. cbn [c_E c_A1 c_A2 c_FT cx]. unfold ESTATE_SIZE, FTAB_WORDS.
      repeat match goal with |- _ /\ _ => split end;
      first [exact I | clear - D_E_A1; lia | clear - D_E_A2; lia | clear - D_E_F; lia | clear - D_A1_A2; lia | clear - D_A1_F; lia | clear - D_A2_F; lia]. }
    assert (IMG : cctx_img S0C cx).
    { unfold cctx_img, img_apart. cbn [c_E c_A1 c_A2 c_FT cx ci_hi S0C]. unfold ESTATE_SIZE, FTAB_WORDS, IMG_LO3.
      repeat match goal with |- _ /\ _ => split end;
      first [exact I | clear - RE5; lia | clear - RA15; lia | clear - RA25; lia | clear - RF5; lia]. }
    assert (OOK : out_okB S0C cx dst nZ).
    { unfold out_okB, apart, img_apart. cbn [c_E c_A1 c_A2 c_FT cx ci_hi S0C]. unfold ESTATE_SIZE, FTAB_WORDS, IMG_LO3, CEIL.
      repeat match goal with |- _ /\ _ => split end;
      first [clear - RD1; lia | clear - NZ LEN; lia | clear - RD2; lia | clear - D_E_D; lia | clear - D_A1_D; lia | clear - D_A2_D; lia
            | clear - D_F_D; lia | clear - RD5; lia]. }
    assert (PAY : pay_condB cx dst nZ src payload).
    { intros NE. unfold pay_okB, apart. cbn [c_E c_A1 c_A2 c_FT cx]. unfold ESTATE_SIZE, FTAB_WORDS, CEIL. rewrite PL.
      destruct SRCB as [L0 | (b & Hb & Hb1 & Hb2)];
        [exfalso; apply NE; rewrite L0 in PL; clear - PL; destruct payload; [reflexivity| cbn [length] in PL; lia] |].
      pose proof (fresh_apart sx [] [(pA2, r2, ARR2_SIZE); (pA1, r1, ARR1_SIZE); (pE, E, 55768)] m MD pFT r3 262148 b AIV Hb) as X3.
      pose proof (fresh_apart sx [(pFT, r3, 262148)] [(pA1, r1, ARR1_SIZE); (pE, E, 55768)] m MD pA2 r2 ARR2_SIZE b AIV Hb) as X2.
      pose proof (fresh_apart sx [(pFT, r3, 262148); (pA2, r2, ARR2_SIZE)] [(pE, E, 55768)] m MD pA1 r1 ARR1_SIZE b AIV Hb) as X1.
      pose proof (fresh_apart sx [(pFT, r3, 262148); (pA2, r2, ARR2_SIZE); (pA1, r1, ARR1_SIZE)] [] m MD pE E 55768 b AIV Hb) as XE.
      cbn [blk_addr blk_size fst snd] in X3, X2, X1, XE.
      pose proof (AP1 D0) as XD.
      repeat match goal with |- _ /\ _ => split end;
      first [clear - SRC1; lia | clear - LEN; lia | clear - SRC2; lia | clear - XE Hb1 Hb2; lia | clear - X1 Hb1 Hb2; lia
            | clear - X2 Hb1 Hb2; lia | clear - X3 Hb1 Hb2; lia | clear - XD; lia]. }
    clear RF5 RA25 RA15 RE5 RD5 D_A1_A2 D_A1_F D_A2_F D_F_D D_A2_D D_A1_D.
    assert (LJK : length junk = Z.to_nat nZ) by (exact (CB_head_len _ _ _ _ _ DSB)).
    pose proof (ovb_init s0segs m (E + 128) 256 (jseg J 128 256) MIDa ltac:(clear; lia)) as INU.
    (* [comment removed for export] *)
    eapply (evt_realizes s0segs _ _ MD K Hh Hl (wT m J jb E r1 r2 r3 c40 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5
              RE1 RE4 ltac:(unfold CEIL; bz_ceil; bz_params; lia) ltac:(lia) ltac:(lia) ltac:(lia) LJB EH INU EH2 FR2 FR DLC MI ST)).
    intros ms PO. unfold S0_b2c_segB.Tpost in PO.
    cps_destruct PO as (u0 & u1 & u2 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU & WM & MI1 & ST1 & EHF & INUF & EH2F & SMW & FRR).
    assert (W1 : WLD sx LBc k m1 MD).
    { eapply WLD_write; [exact W | exact MU | exact WM | exact MI1 |].
      apply Forall_cons; [left; cbn; clear - LO STK; lia|].
      apply Forall_cons; [right; right; right; exists pE, E, 55768; split; [exact IE|]; split; [exact NPE| cbn; clear; lia]|].
      apply Forall_cons; [right; right; right; exists pE, E, 55768; split; [exact IE|]; split; [exact NPE| cbn; clear; lia]| apply Forall_nil]. }
    assert (DJ : forall A n, (A + n <= usp - 192 \/ usp <= A) -> (A + n <= E \/ E + 384 <= A) -> (A + n <= E + 640 \/ E + 672 <= A) ->
                 disjoint_from [(usp - 192, usp); (E, E + 384); (E + 640, E + 672)] A n).
    { intros A n H1 H2 H3. clear - H1 H2 H3. cbn. repeat split; lia. }
    assert (DSB1 : rw_cells s0segs m1 dst [CB (Z.to_nat nZ) junk]).
    { eapply rw_cells_transport; [exact DSB | exact MU | exact WM |]. rewrite size_CB1, Z2Nat.id by (clear - NZ LEN; lia).
      apply DJ; [clear - RD2 LO STK; lia | clear - D_E_D; lia | clear - D_E_D; lia]. }
    clear D_E_D.
    assert (AR1' : rw_cells s0segs m1 r1 [CB (Z.to_nat ARR1_SIZE) (repeat (Z_to_bv 8 0) (Z.to_nat ARR1_SIZE))]).
    { eapply rw_cells_transport; [exact AR1 | exact MU | exact WM |]. rewrite size_CB1, Z2Nat.id by (clear; lia).
      apply DJ; [clear - RA12 LO STK; lia | clear - D_E_A1; lia | clear - D_E_A1; lia]. }
    clear D_E_A1.
    assert (AR2' : rw_cells s0segs m1 r2 [CB (Z.to_nat ARR2_SIZE) (repeat (Z_to_bv 8 0) (Z.to_nat ARR2_SIZE))]).
    { eapply rw_cells_transport; [exact AR2 | exact MU | exact WM |]. rewrite size_CB1, Z2Nat.id by (clear; lia).
      apply DJ; [clear - RA22 LO STK; lia | clear - D_E_A2; lia | clear - D_E_A2; lia]. }
    clear D_E_A2.
    assert (AR3' : rw_cells s0segs m1 r3 [CB (Z.to_nat 262148) (repeat (Z_to_bv 8 0) (Z.to_nat 262148))]).
    { eapply rw_cells_transport; [exact AR3 | exact MU | exact WM |]. rewrite size_CB1, Z2Nat.id by (clear; lia).
      apply DJ; [clear - RF2 LO STK; lia | clear - D_E_F; lia | clear - D_E_F; lia]. }
    clear D_E_F.
    assert (MIDb' : rw_cells s0segs m1 (E + 384) [CB 256 (jseg J 384 256)])
      by (eapply rw_cells_transport; [exact MIDb | exact MU | exact WM | apply DJ; cbn; clear - RE2 LO STK; lia]).
    assert (REST' : rw_cells s0segs m1 (E + 672) [CB (Z.to_nat 55096) (jseg J 672 55096)])
      by (eapply rw_cells_transport; [exact REST | exact MU | exact WM | rewrite size_CB1, Z2Nat.id by (clear; lia); apply DJ; clear - RE2 LO STK; lia]).
    assert (DLC1 : rw_cells s0segs m1 dl [C4 (Z_to_bv 64 nZ)])
      by (eapply rw_cells_transport; [exact DLC | exact MU | exact WM | apply DJ; cbn; clear - RE2 LO STK DL1; lia]).
    clear EH MIDa MIDb EH2 REST FR2 FR DLC DSB AR1 AR2 AR3 INU ST MI DJ.
    pose proof (ovb_init s0segs m1 (E + 384) 256 (jseg J 384 256) MIDb' ltac:(clear; lia)) as UNS.
    cps_destruct (erest_carve s0segs m1 E J REST' LJ) as (MTF & SEL & SLM & LEN_ & COD & RFQ & LNP).
    pose proof (zb8_init s0segs m1 r1 ARR1_SIZE _ AR1' ltac:(clear; lia) (repeat_zero _)) as ZA1.
    pose proof (zb8_init s0segs m1 r2 ARR2_SIZE _ AR2' ltac:(clear; lia) (repeat_zero _)) as ZA2.
    change (Z.to_nat 262148) with (Z.to_nat (4 * 65537)) in AR3' at 1.
    pose proof (zw32_init s0segs m1 r3 65537 _ AR3' ltac:(clear; lia) (repeat_zero _)) as ZFT.
    cps_pose W1 as (AIV1 & _ & _ & _ & _ & _ & CM1 & PR1 & _). pose proof (ai_inv_model AI AIV1) as [Hh1 Hl1].
    (* [comment removed for export] *)
    assert (EM : emem cx s0segs (eg_init (Z_to_bv 64 0)) est0 m1).
    { eapply emem_intro; cbn [c_E c_A1 c_A2 c_FT c_bz c_Fb c_J cx].
      - unfold EHEAD1. cbn [c_E c_A1 c_A2 c_FT c_bz c_J cx g_aie g_sort g_mtf g_zbits eg_init]. unfold est0, est_init.
        cbn [e_mode e_state e_nblock e_state_in_ch e_state_in_len e_state_out_pos e_bw bw_numZ].
        unfold BZF_STRM, BZ_M_RUNNING, BZ_S_INPUT. replace (usp - 128 - 5016 + 5016) with (usp - 128) by (clear; lia).
        unfold S0_b2c_segB.EFIN in EHF. exact EHF.
      - unfold est0, est_init. cbn [e_inUse]. rewrite ovb_inUse_clear. exact INUF.
      - unfold est0, est_init. cbn [e_unseqToSeq]. exact UNS.
      - unfold EHEAD2. cbn [c_J cx g_bs g_mtf eg_init]. unfold est0, est_init. cbn [e_blockCRC e_combinedCRC e_blockNo e_bw bw_buff bw_live].
        unfold crc_init. unfold S0_b2c_segB.EFIN2 in EH2F. exact EH2F.
      - exact MTF. - exact SEL. - exact SLM. - exact LEN_. - exact COD. - exact RFQ. - exact LNP. }
    assert (AM : amem cx s0segs est0 m1).
    { eapply amem_intro; cbn [c_A1 c_A2 c_FT cx]; unfold est0, est_init; cbn [e_arr1 e_arr2 e_ftab]; [exact ZA1 | exact ZA2 | exact ZFT]. }
    assert (SMB : rw_cells s0segs m1 (usp - 128) (STRMB cx dst nZ DBZA DBZF (z_b2b (map bv_unsigned payload) nZ) src (jw4 jb 20) (jw4 jb 44))).
    { unfold STRMB. cbn [c_bz c_E cx z_avail_in z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi z_b2b].
      rewrite length_map, PL. replace (dst + (nZ - nZ)) with dst by (clear; lia).
      unfold S0_b2c_segB.STRMW in SMW. exact SMW. }
    assert (OBM : u8arr s0segs m1 dst junk) by (exact (u8arr_of_rw_cells s0segs m1 dst _ junk DSB1)).
    assert (LOB : Z.of_nat (length junk) = nZ) by (clear - LJK NZ LEN; lia).
    pose proof (src_now m1 PR1) as PLM.
    clear MTF SEL SLM LEN_ COD RFQ LNP ZA1 ZA2 ZFT UNS INUF EHF EH2F SMW AR1' AR2' AR3' MIDb' REST' DSB1.
    (* [comment removed for export] *)
    eapply (BZCALL m1 MD cx jb u0 u1 u2 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Hh1 Hl1);
      [cbn [c_bz cx]; clear; lia | exact EM | exact AM | exact CM1 | exact SMB | exact OBM | exact LOB | exact OOK | exact PLM | exact PAY
      | exact MI1 | exact ST1 | exact CX | exact SEP | exact IMG |].
    intros ms' PO.
    eapply (POSTC sx m1 MD J jb pFT pA2 pA1 pE E r1 r2 r3 ms'); [exact W1 | exact D0 | exact LJK | exact FRR | exact DLC1 | exact PO].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ST5 : forall sx m MD (J jb : list byte) (pA2 pA1 pE : bid) (E r1 r2 : Z) (c40 : word)
      (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    WLD sx (opt r2 (pA2, r2, ARR2_SIZE) ++ opt r1 (pA1, r1, ARR1_SIZE) ++ [(pE, E, 55768)] ++ LB) (S k) m MD ->
    dst <> 0 -> 0 <= r1 -> 0 <= r2 -> Z.of_nat (length J) = 55768 -> Z.of_nat (length jb) = 56 ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) c40) ->
    EBR J E m -> STC jb m -> stk s0segs m lo (usp - 192) ->
    (r1 <> 0 -> rw_cells s0segs m r1 [CB (Z.to_nat ARR1_SIZE) (repeat (Z_to_bv 8 0) (Z.to_nat ARR1_SIZE))]) ->
    (r2 <> 0 -> rw_cells s0segs m r2 [CB (Z.to_nat ARR2_SIZE) (repeat (Z_to_bv 8 0) (Z.to_nat ARR2_SIZE))]) ->
    realizes s0segs (mkCfg (MS (mkR (Z_to_bv 64 0x13d20) (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                                  (Z_to_bv 64 262148) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                  (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) (Z_to_bv 64 (-3)) (Z_to_bv 64 ARR1_SIZE) s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                             F (Z_to_bv 64 MALLOC) fc None m (seg_rom s0segs)) MD) K.
  Proof.
    intros sx m MD J jb pA2 pA1 pE E r1 r2 c40 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
      W D0 R1 R2 LJ LJB EH EB SC ST AZ1 AZ2.
    prep. cps_pose W as (AIV & VM & VO & AUX & [er ERR] & MI & CM & PR & SUB).
    set (LX := opt r2 (pA2, r2, ARR2_SIZE) ++ opt r1 (pA1, r1, ARR1_SIZE)) in *.
    assert (LBE : LX ++ (pE, E, 55768) :: [] ++ LB = opt r2 (pA2, r2, ARR2_SIZE) ++ opt r1 (pA1, r1, ARR1_SIZE) ++ [(pE, E, 55768)] ++ LB).
    { subst LX. rewrite <- !app_assoc. reflexivity. }
    rewrite <- LBE in W, AIV.
    assert (INE : In (pE, E, 55768) (LX ++ (pE, E, 55768) :: [] ++ LB)) by (apply in_or_app; right; left; reflexivity).
    assert (IN1 : r1 <> 0 -> In (pA1, r1, ARR1_SIZE) (LX ++ (pE, E, 55768) :: [] ++ LB)).
    { intros N1. subst LX. rewrite (opt_nz r1 _ N1). apply in_or_app; left. apply in_or_app; right. left; reflexivity. }
    assert (IN2 : r2 <> 0 -> In (pA2, r2, ARR2_SIZE) (LX ++ (pE, E, 55768) :: [] ++ LB)).
    { intros N2. subst LX. rewrite (opt_nz r2 _ N2). apply in_or_app; left. left; reflexivity. }
    cps_pose (blk_facts _ _ _ _ pE E 55768 AIV INE) as (RE1 & _ & _ & RE2 & _).
    eapply (bigz_step sx _ k m MD 262148 (usp - 192) K); [exact W | unfold MMAP_THRESHOLD_C, MAX_REQ_C; lia | exact ST | lia | lia | lia | |].
    - (* [comment removed for export] *)
      intros sx' m' MD' yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 W' ST' HP'.
      pose proof (keep_blk _ _ m m' (pE, E, 55768) E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) c40) HP' INE ltac:(cbn; lia)
                    ltac:(cbn [blk_addr blk_size fst snd]; cbv [cells_size csize S0_b2c_segA.EJ1w Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia) EH) as EH'.
      pose proof (STC_heap jb m m' _ (usp - 192) SC HP' ltac:(lia) ltac:(apply in_or_app; right; right; exact (IND D0))) as SC'.
      eapply (CLEAN sx' k m' MD' J jb pE pA2 pA1 pE E r1 r2 0 c40);
        [rewrite LBE in W'; exact W' | lia | exact D0 | exact R1 | exact R2 | lia | lia | exact EH' | exact SC' | exact ST'].
    - (* [comment removed for export] *)
      intros sx' m' MD' r3 p yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 W' ST' HP' Hr BOK NIN AR3.
      pose proof (keep_blk _ _ m m' (pE, E, 55768) E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) c40) HP' INE ltac:(cbn; lia)
                    ltac:(cbn [blk_addr blk_size fst snd]; cbv [cells_size csize S0_b2c_segA.EJ1w Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia) EH) as EH'.
      pose proof (EBR_heap _ _ m m' _ _ pE EB HP' INE) as EB'.
      pose proof (STC_heap jb m m' _ (usp - 192) SC HP' ltac:(lia) ltac:(apply in_or_app; right; right; exact (IND D0))) as SC'.
      cps_pose BOK as (R31 & _ & _ & R32 & _).
      destruct (Z.eq_dec r1 0) as [R10 | N1].
      + eapply (CLEAN sx' k m' MD' J jb p pA2 pA1 pE E r1 r2 r3 c40);
          [rewrite (opt_nz r3 _ Hr); rewrite LBE in W'; exact W' | lia | exact D0 | exact R1 | exact R2 | lia | lia | exact EH' | exact SC' | exact ST'].
      + destruct (Z.eq_dec r2 0) as [R20 | N2].
        * eapply (CLEAN sx' k m' MD' J jb p pA2 pA1 pE E r1 r2 r3 c40);
            [rewrite (opt_nz r3 _ Hr); rewrite LBE in W'; exact W' | lia | exact D0 | exact R1 | exact R2 | lia | lia | exact EH' | exact SC' | exact ST'].
        * (* [comment removed for export] *)
          pose proof (keep_zero _ _ m m' pA1 r1 ARR1_SIZE HP' (IN1 N1) ltac:(lia) (AZ1 N1)) as AZ1'.
          pose proof (keep_zero _ _ m m' pA2 r2 ARR2_SIZE HP' (IN2 N2) ltac:(lia) (AZ2 N2)) as AZ2'.
          eapply (SUCC sx' m' MD' J jb p pA2 pA1 pE E r1 r2 r3 c40);
            [subst LX; rewrite (opt_nz r1 _ N1), (opt_nz r2 _ N2) in W'; exact W' | exact D0 | exact LJ | exact LJB | exact EH' | exact EB' | exact SC' | exact ST'
            | exact AZ1' | exact AZ2' | exact AR3].
  Qed.

  (* [comment removed for export] *)
  Lemma WIV_E : forall sx LX L2 m MD pE E lo' hi', ai_inv AI sx (LX ++ (pE, E, 55768) :: L2 ++ LB) m MD -> E <= lo' -> hi' <= E + 55768 ->
    Forall (wiv_ok (LX ++ (pE, E, 55768) :: L2 ++ LB)) [(lo', hi')].
  Proof.
    intros sx LX L2 m MD pE E lo' hi' AIV H1 H2. apply Forall_cons; [| apply Forall_nil]. right; right; right. exists pE, E, 55768.
    split; [apply in_or_app; right; left; reflexivity|]. split; [exact (fresh_id _ _ _ _ _ _ _ _ AIV)| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ST4 : forall sx m MD (J jb : list byte) (pA1 pE : bid) (E r1 : Z)
      (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    WLD sx (opt r1 (pA1, r1, ARR1_SIZE) ++ [(pE, E, 55768)] ++ LB) (S (S k)) m MD ->
    dst <> 0 -> 0 <= r1 -> Z.of_nat (length J) = 55768 -> Z.of_nat (length jb) = 56 ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
    EBR J E m -> STC jb m -> stk s0segs m lo (usp - 192) ->
    (r1 <> 0 -> rw_cells s0segs m r1 [CB (Z.to_nat ARR1_SIZE) (repeat (Z_to_bv 8 0) (Z.to_nat ARR1_SIZE))]) ->
    realizes s0segs (mkCfg (MS (mkR (Z_to_bv 64 0x13d00) (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                                  (Z_to_bv 64 ARR2_SIZE) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                  (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) (Z_to_bv 64 (-3)) (Z_to_bv 64 ARR1_SIZE) s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                             F (Z_to_bv 64 MALLOC) fc None m (seg_rom s0segs)) MD) K.
  Proof.
    intros sx m MD J jb pA1 pE E r1 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
      W D0 R1 LJ LJB EH EB SC ST AZ1.
    prep. cps_pose W as (AIV & VM & VO & AUX & [er ERR] & MI & CM & PR & SUB).
    set (LX := opt r1 (pA1, r1, ARR1_SIZE)) in *.
    assert (INE : In (pE, E, 55768) (LX ++ [(pE, E, 55768)] ++ LB)) by (apply in_or_app; right; left; reflexivity).
    assert (IN1 : r1 <> 0 -> In (pA1, r1, ARR1_SIZE) (LX ++ [(pE, E, 55768)] ++ LB)).
    { intros N1. subst LX. rewrite (opt_nz r1 _ N1). left; reflexivity. }
    cps_pose (blk_facts _ _ _ _ pE E 55768 AIV INE) as (RE1 & _ & _ & RE2 & _).
    pose proof (E_dst_apart sx LX [] m MD pE E 55768 AIV D0) as DED.
    eapply (bigz_step sx _ (S k) m MD ARR2_SIZE (usp - 192) K); [exact W | unfold MMAP_THRESHOLD_C, MAX_REQ_C; lia | exact ST | lia | lia | lia | |].
    - (* [comment removed for export] *)
      intros sx' m' MD' yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 W' ST' HP'.
      pose proof (keep_blk _ _ m m' (pE, E, 55768) E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 0) (Z_to_bv 64 0)) HP' INE ltac:(cbn; lia)
                    ltac:(cbn [blk_addr blk_size fst snd]; cbv [cells_size csize S0_b2c_segA.EJ1w Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia) EH) as EH'.
      pose proof (EBR_heap _ _ m m' _ _ pE EB HP' INE) as EB'.
      pose proof (STC_heap jb m m' _ (usp - 192) SC HP' ltac:(lia) ltac:(apply in_or_app; right; right; exact (IND D0))) as SC'.
      assert (AZ1' : r1 <> 0 -> rw_cells s0segs m' r1 [CB (Z.to_nat ARR1_SIZE) (repeat (Z_to_bv 8 0) (Z.to_nat ARR1_SIZE))]).
      { intros N1. exact (keep_zero _ _ m m' pA1 r1 ARR1_SIZE HP' (IN1 N1) ltac:(lia) (AZ1 N1)). }
      cps_pose W' as (AIV' & _ & _ & _ & _ & MI' & _). pose proof (ai_inv_model AI AIV') as [Hh' Hl']. cps_pose SC' as (FR2' & FR' & DLC' & DSB').
      eapply (evt_realizes s0segs _ _ MD' K Hh' Hl' (wW4 m' J jb E r1 0 _ yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6
                RE1 ltac:(unfold CEIL; bz_ceil; bz_params; lia) ltac:(lia) EH' FR' MI')).
      intros ms PO. unfold S0_b2c_segA.W4post in PO.
      cps_destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU & WM & MI2 & EH2 & FRb).
      pose proof (WLD_write _ _ _ _ _ _ _ W' MU WM MI2 (WIV_E sx' LX [] m' MD' pE E (E + 32) (E + 40) AIV' ltac:(lia) ltac:(lia))) as W2.
      pose proof (EBR_munch _ _ m' m2 _ EB' MU WM ltac:(cbn; lia)) as EB2.
      pose proof (STC_munch jb m' m2 _ SC' MU WM ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as SC2.
      assert (STq : stk s0segs m2 lo (usp - 192)) by (eapply stk_transport_disjoint; [exact ST' | exact MU | exact WM | cbn; lia]).
      eapply (ST5 sx' m2 MD' J jb pE pA1 pE E r1 0 (Z_to_bv 64 0));
        [exact W2 | exact D0 | exact R1 | lia | exact LJ | exact LJB | exact EH2 | exact EB2 | exact SC2 | exact STq
        | intros N1; eapply rw_cells_transport; [exact (AZ1' N1) | exact MU | exact WM |] | intros N; exfalso; exact (N eq_refl)].
      pose proof (blk_apart _ _ _ _ _ _ AIV INE (IN1 N1) ltac:(intros X; injection X; lia)) as DA. cbn [blk_addr blk_size fst snd] in DA.
      rewrite size_CB1, Z2Nat.id by lia. cbn. lia.
    - (* [comment removed for export] *)
      intros sx' m' MD' r2 p yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 W' ST' HP' Hr BOK NIN AR2.
      pose proof (keep_blk _ _ m m' (pE, E, 55768) E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 0) (Z_to_bv 64 0)) HP' INE ltac:(cbn; lia)
                    ltac:(cbn [blk_addr blk_size fst snd]; cbv [cells_size csize S0_b2c_segA.EJ1w Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia) EH) as EH'.
      pose proof (EBR_heap _ _ m m' _ _ pE EB HP' INE) as EB'.
      pose proof (STC_heap jb m m' _ (usp - 192) SC HP' ltac:(lia) ltac:(apply in_or_app; right; right; exact (IND D0))) as SC'.
      assert (AZ1' : r1 <> 0 -> rw_cells s0segs m' r1 [CB (Z.to_nat ARR1_SIZE) (repeat (Z_to_bv 8 0) (Z.to_nat ARR1_SIZE))]).
      { intros N1. exact (keep_zero _ _ m m' pA1 r1 ARR1_SIZE HP' (IN1 N1) ltac:(lia) (AZ1 N1)). }
      cps_pose BOK as (R21 & _ & _ & R22 & _).
      cps_pose W' as (AIV' & _ & _ & _ & _ & MI' & _). pose proof (ai_inv_model AI AIV') as [Hh' Hl']. cps_pose SC' as (FR2' & FR' & DLC' & DSB').
      eapply (evt_realizes s0segs _ _ MD' K Hh' Hl' (wW4 m' J jb E r1 r2 _ yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6
                RE1 ltac:(unfold CEIL; bz_ceil; bz_params; lia) ltac:(lia) EH' FR' MI')).
      intros ms PO. unfold S0_b2c_segA.W4post in PO.
      cps_destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU & WM & MI2 & EH2 & FRb).
      pose proof (WLD_write _ _ _ _ _ _ _ W' MU WM MI2 (WIV_E sx' ((p, r2, ARR2_SIZE) :: LX) [] m' MD' pE E (E + 32) (E + 40) AIV' ltac:(lia) ltac:(lia))) as W2.
      pose proof (EBR_munch _ _ m' m2 _ EB' MU WM ltac:(cbn; lia)) as EB2.
      pose proof (STC_munch jb m' m2 _ SC' MU WM ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as SC2.
      assert (STq : stk s0segs m2 lo (usp - 192)) by (eapply stk_transport_disjoint; [exact ST' | exact MU | exact WM | cbn; lia]).
      pose proof (blk_apart _ _ _ _ _ _ AIV' (or_introl eq_refl) (or_intror INE) ltac:(intros X; injection X; lia)) as DA2. cbn [blk_addr blk_size fst snd] in DA2.
      eapply (ST5 sx' m2 MD' J jb p pA1 pE E r1 r2 (Z_to_bv 64 0));
        [rewrite (opt_nz r2 _ Hr); exact W2 | exact D0 | exact R1 | lia | exact LJ | exact LJB | exact EH2 | exact EB2 | exact SC2 | exact STq
        | intros N1; eapply rw_cells_transport; [exact (AZ1' N1) | exact MU | exact WM |]
        | intros _; eapply rw_cells_transport; [exact AR2 | exact MU | exact WM | rewrite size_CB1, Z2Nat.id by lia; cbn; lia]].
      pose proof (blk_apart _ _ _ _ _ _ AIV INE (IN1 N1) ltac:(intros X; injection X; lia)) as DA. cbn [blk_addr blk_size fst snd] in DA.
      rewrite size_CB1, Z2Nat.id by lia. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ST3 : forall sx m MD (J jb : list byte) (pE : bid) (E : Z)
      (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    WLD sx ([(pE, E, 55768)] ++ LB) (S (S (S k))) m MD ->
    dst <> 0 -> Z.of_nat (length J) = 55768 -> Z.of_nat (length jb) = 56 ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
    EBR J E m -> STC jb m -> stk s0segs m lo (usp - 192) ->
    realizes s0segs (mkCfg (MS (mkR (Z_to_bv 64 0x13ce4) (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                                  (Z_to_bv 64 ARR1_SIZE) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                  (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) (Z_to_bv 64 (-3)) (Z_to_bv 64 ARR1_SIZE) s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                             F (Z_to_bv 64 MALLOC) fc None m (seg_rom s0segs)) MD) K.
  Proof.
    intros sx m MD J jb pE E xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 W D0 LJ LJB EH EB SC ST.
    prep. cps_pose W as (AIV & VM & VO & AUX & [er ERR] & MI & CM & PR & SUB).
    assert (INE : In (pE, E, 55768) ([(pE, E, 55768)] ++ LB)) by (left; reflexivity).
    cps_pose (blk_facts _ _ _ _ pE E 55768 AIV INE) as (RE1 & _ & _ & RE2 & _).
    pose proof (E_dst_apart sx [] [] m MD pE E 55768 AIV D0) as DED.
    eapply (bigz_step sx _ (S (S k)) m MD ARR1_SIZE (usp - 192) K); [exact W | unfold MMAP_THRESHOLD_C, MAX_REQ_C; lia | exact ST | lia | lia | lia | |].
    - (* [comment removed for export] *)
      intros sx' m' MD' yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 W' ST' HP'.
      pose proof (keep_blk _ _ m m' (pE, E, 55768) E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) HP' INE ltac:(cbn; lia)
                    ltac:(cbn [blk_addr blk_size fst snd]; cbv [cells_size csize S0_b2c_segA.EJ1w Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia) EH) as EH'.
      pose proof (EBR_heap _ _ m m' _ _ pE EB HP' INE) as EB'.
      pose proof (STC_heap jb m m' _ (usp - 192) SC HP' ltac:(lia) ltac:(right; exact (IND D0))) as SC'.
      cps_pose W' as (AIV' & _ & _ & _ & _ & MI' & _). pose proof (ai_inv_model AI AIV') as [Hh' Hl']. cps_pose SC' as (FR2' & FR' & DLC' & DSB').
      eapply (evt_realizes s0segs _ _ MD' K Hh' Hl' (wW3 m' J jb E 0 _ yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6
                RE1 ltac:(unfold CEIL; bz_ceil; bz_params; lia) ltac:(lia) EH' FR' MI')).
      intros ms PO. unfold S0_b2c_segA.W3post in PO.
      cps_destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU & WM & MI2 & EH2 & FRb).
      pose proof (WLD_write _ _ _ _ _ _ _ W' MU WM MI2 (WIV_E sx' [] [] m' MD' pE E (E + 24) (E + 32) AIV' ltac:(lia) ltac:(lia))) as W2.
      pose proof (EBR_munch _ _ m' m2 _ EB' MU WM ltac:(cbn; lia)) as EB2.
      pose proof (STC_munch jb m' m2 _ SC' MU WM ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as SC2.
      assert (STq : stk s0segs m2 lo (usp - 192)) by (eapply stk_transport_disjoint; [exact ST' | exact MU | exact WM | cbn; lia]).
      eapply (ST4 sx' m2 MD' J jb pE pE E 0);
        [exact W2 | exact D0 | lia | exact LJ | exact LJB | exact EH2 | exact EB2 | exact SC2 | exact STq | intros N; exfalso; exact (N eq_refl)].
    - (* [comment removed for export] *)
      intros sx' m' MD' r1 p yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 W' ST' HP' Hr BOK NIN AR1.
      pose proof (keep_blk _ _ m m' (pE, E, 55768) E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) HP' INE ltac:(cbn; lia)
                    ltac:(cbn [blk_addr blk_size fst snd]; cbv [cells_size csize S0_b2c_segA.EJ1w Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia) EH) as EH'.
      pose proof (EBR_heap _ _ m m' _ _ pE EB HP' INE) as EB'.
      pose proof (STC_heap jb m m' _ (usp - 192) SC HP' ltac:(lia) ltac:(right; exact (IND D0))) as SC'.
      cps_pose BOK as (R11 & _ & _ & R12 & _).
      cps_pose W' as (AIV' & _ & _ & _ & _ & MI' & _). pose proof (ai_inv_model AI AIV') as [Hh' Hl']. cps_pose SC' as (FR2' & FR' & DLC' & DSB').
      eapply (evt_realizes s0segs _ _ MD' K Hh' Hl' (wW3 m' J jb E r1 _ yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6
                RE1 ltac:(unfold CEIL; bz_ceil; bz_params; lia) ltac:(lia) EH' FR' MI')).
      intros ms PO. unfold S0_b2c_segA.W3post in PO.
      cps_destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU & WM & MI2 & EH2 & FRb).
      pose proof (WLD_write _ _ _ _ _ _ _ W' MU WM MI2 (WIV_E sx' [(p, r1, ARR1_SIZE)] [] m' MD' pE E (E + 24) (E + 32) AIV' ltac:(lia) ltac:(lia))) as W2.
      pose proof (EBR_munch _ _ m' m2 _ EB' MU WM ltac:(cbn; lia)) as EB2.
      pose proof (STC_munch jb m' m2 _ SC' MU WM ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as SC2.
      assert (STq : stk s0segs m2 lo (usp - 192)) by (eapply stk_transport_disjoint; [exact ST' | exact MU | exact WM | cbn; lia]).
      pose proof (blk_apart _ _ _ _ _ _ AIV' (or_introl eq_refl) (or_intror INE) ltac:(intros X; injection X; lia)) as DA1. cbn [blk_addr blk_size fst snd] in DA1.
      eapply (ST4 sx' m2 MD' J jb p pE E r1);
        [rewrite (opt_nz r1 _ Hr); exact W2 | exact D0 | lia | exact LJ | exact LJB | exact EH2 | exact EB2 | exact SC2 | exact STq
        | intros _; eapply rw_cells_transport; [exact AR1 | exact MU | exact WM | rewrite size_CB1, Z2Nat.id by lia; cbn; lia]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ST2 : forall sx m MD (jb : list byte) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    WLD sx LB (S (S (S (S k)))) m MD -> dst <> 0 -> Z.of_nat (length jb) = 56 ->
    STC jb m -> stk s0segs m lo (usp - 192) ->
    realizes s0segs (mkCfg (MS (mkR (Z_to_bv 64 0x13ca0) (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                                  (Z_to_bv 64 55768) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                  (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 dst) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                             F (Z_to_bv 64 MALLOC) fc None m (seg_rom s0segs)) MD) K.
  Proof.
    intros sx m MD jb xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 W D0 LJB SC ST.
    prep. cps_pose W as (AIV & VM & VO & AUX & [er ERR] & MI & CM & PR & SUB).
    cps_pose (blk_facts _ _ _ _ pd dst nZ AIV (IND D0)) as (RD1 & _ & _ & RD2 & _).
    eapply (cover_step sx LB (S (S (S k))) m MD 55768 (usp - 192) K);
      [exact W | unfold MMAP_THRESHOLD_C; lia | unfold c21_foreign; lia | exact ST | lia | lia | lia | |].
    - (* [comment removed for export] *)
      intros sx' m' MD' yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 W' ST' HP'.
      cps_pose (STC_heap jb m m' LB (usp - 192) SC HP' ltac:(lia) (IND D0)) as (FR2' & FR' & DLC' & DSB').
      cps_pose W' as (AIV' & _ & _ & _ & _ & MI' & _). pose proof (ai_inv_model AI AIV') as [Hh' Hl'].
      eapply (evt_realizes s0segs _ _ MD' K Hh' Hl' (wW2f m' jb _ yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 FR2' FR' MI' ST')).
      intros ms PO.
      eapply (FIN sx' (S (S (S k))) m' MD' (-3) nZ [(usp - 192, usp)]); [exact W' | lia | apply Forall_cons; [cbn; lia| apply Forall_nil] | exact DLC' | lia | | exact PO].
      right; left. split; [reflexivity|]. split; [exact D0|]. split; [reflexivity| exact DSB'].
    - (* [comment removed for export] *)
      intros sx' m' MD' E pE J yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 W' ST' HP' Hr BOK NIN BLK.
      pose proof (STC_heap jb m m' LB (usp - 192) SC HP' ltac:(lia) (IND D0)) as SC'. cps_pose SC' as (FR2' & FR' & DLC' & DSB').
      cps_pose W' as (AIV' & _ & _ & _ & _ & MI' & _). pose proof (ai_inv_model AI AIV') as [Hh' Hl'].
      cps_pose BOK as (RE1 & RE4 & _ & RE2 & _).
      assert (LJ : Z.of_nat (length J) = 55768) by (rewrite (CB_head_len _ _ _ _ _ BLK); lia).
      cps_destruct (estate_carve3 s0segs m' E J BLK LJ) as (EHJ & MIDa & MIDb & EH2c & REST).
      pose proof (E_dst_apart sx' [] [] m' MD' pE E 55768 AIV' D0) as DED.
      eapply (evt_realizes s0segs _ _ MD' K Hh' Hl' (wW2 m' J jb E _ yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6
                RE1 RE4 ltac:(unfold CEIL; bz_ceil; bz_params; lia) EHJ FR' MI')).
      intros ms PO. unfold S0_b2c_segA.W2post in PO.
      cps_destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU & WM & MI2 & EH2 & FRb).
      pose proof (WLD_write _ _ _ _ _ _ _ W' MU WM MI2 (WIV_E sx' [] [] m' MD' pE E E (E + 48) AIV' ltac:(lia) ltac:(lia))) as W2.
      assert (EB2 : EBR J E m2).
      { eapply EBR_munch; [split; [exact MIDa| split; [exact MIDb| split; [exact EH2c| exact REST]]] | exact MU | exact WM | cbn; lia]. }
      pose proof (STC_munch jb m' m2 _ SC' MU WM ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as SC2.
      assert (STq : stk s0segs m2 lo (usp - 192)) by (eapply stk_transport_disjoint; [exact ST' | exact MU | exact WM | cbn; lia]).
      eapply (ST3 sx' m2 MD' J jb pE E); [exact W2 | exact D0 | exact LJ | exact LJB | exact EH2 | exact EB2 | exact SC2 | exact STq].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma TOP : forall (t0 t1 t2 a7 t3 t4 t5 t6 errv : word),
    ac_vm AC (4 + k)%nat s_ MD0 -> ai_aux AI m0 B ->
    rw_cells s0segs m0 dl [C4 (Z_to_bv 64 nZ)] ->
    stk s0segs m0 lo usp -> rw_cells s0segs m0 (errno_cell S0_layout) [C4 errv] -> mem_inv s0segs m0 ->
    realizes s0segs
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 dl) (Z_to_bv 64 src) (Z_to_bv 64 len)
                      (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 0) (Z_to_bv 64 wf0) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x15e1c) fc None m0 (seg_rom s0segs)) MD0) K.
  Proof.
    intros t0 t1 t2 a7 t3 t4 t5 t6 errv VM AUX DLC ST ERR MI. prep.
    pose proof (ai_inv_model AI AI0) as [Hh Hl].
    assert (W0 : WLD s_ LB (4 + k)%nat m0 MD0).
    { split; [exact AI0|]. split; [exact VM|]. split; [apply vm_only_refl|]. split; [exact AUX|]. split; [exists errv; exact ERR|].
      split; [exact MI|]. split; [exact CM0|]. split; [apply pres_refl| intros b Hb; exact Hb]. }
    destruct (Z.eq_dec dst 0) as [D0 | D0].
    - (* [comment removed for export] *)
      eapply (evt_realizes s0segs _ _ MD0 K Hh Hl (wW1a m0 t0 t1 t2 a7 t3 t4 t5 t6 D0 MI ST)).
      intros ms PO.
      eapply (FIN s_ (4 + k)%nat m0 MD0 (-2) nZ [(usp - 128, usp)]);
        [exact W0 | lia | apply Forall_cons; [cbn; lia| apply Forall_nil] | exact DLC | lia | | unfold S0_b2c_segA.W1apost in PO; unfold S0_b2c_segA.RETpost; exact PO].
      left. split; [reflexivity|]. split; [exact D0| reflexivity].
    - (* [comment removed for export] *)
      cps_pose (blk_facts _ _ _ _ pd dst nZ AI0 (IND D0)) as (RD1 & _ & _ & RD2 & _).
      pose proof DST as [X | [_ DSB]]; [lia|].
      eapply (evt_realizes s0segs _ _ MD0 K Hh Hl (wW1b m0 t0 t1 t2 a7 t3 t4 t5 t6 D0 ltac:(lia) MI ST)).
      intros ms PO. unfold S0_b2c_segA.W1bpost in PO.
      cps_destruct PO as (u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & jb & -> & MU & WM & MI1 & ST1 & FR2 & FR).
      assert (LJB : Z.of_nat (length jb) = 56) by (unfold S0_b2c_segA.FRW in FR; rewrite (CB_head_len _ _ _ _ _ FR); reflexivity).
      assert (W1 : WLD s_ LB (4 + k)%nat m1 MD0).
      { eapply WLD_write; [exact W0 | exact MU | exact WM | exact MI1 | apply Forall_cons; [left; cbn; lia| apply Forall_nil]]. }
      assert (DLC1 : rw_cells s0segs m1 dl [C4 (Z_to_bv 64 nZ)]) by (eapply rw_cells_transport; [exact DLC | exact MU | exact WM | cbn; lia]).
      assert (DSB1 : rw_cells s0segs m1 dst [CB (Z.to_nat nZ) junk]) by (eapply rw_cells_transport; [exact DSB | exact MU | exact WM | rewrite size_CB1, Z2Nat.id by lia; cbn; lia]).
      eapply (ST2 s_ m1 MD0 jb); [exact W1 | exact D0 | exact LJB | | exact ST1].
      split; [exact FR2|]. split; [exact FR|]. split; [exact DLC1| exact DSB1].
  Qed.

End B2BK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem b2bC_s0 (AI : AllocIface s0segs S0_layout) (AC : AllocCover s0segs S0_layout AI) : b2bC_spec AI AC S0CI.
Proof.
  unfold b2bC_spec. intros until K.
  intros A0 A1 A2 A3 A4 A5 A6 WF0 WFE TP LEN NZ AIV VM AUX SB DST DLC DL1 DL2 DL4 DLB SRC0 PL CR SRC1 SRC2 SRC16 SRCB AP1 AP2 AP3 ST CL LO AL SPH ERR MI CM KONT.
  subst a0 a1 a2 a3 a4 a5 a6. cbn [bc_entry S0CI].
  destruct (mod16_lin _ AL) as [qsp ALQ].
  assert (HW : wrap_sec sp dl src len wf0 nZ lo qsp).
  { unfold wrap_sec, CEIL, B2BC_STACK in *. repeat match goal with |- _ /\ _ => split end; lia. }
  eapply (TOP AI AC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst dl src len wf0 nZ lo qsp HW MD s LB p B k m payload junk sv K
            TP AIV SB DST DLB SRC0 PL CR SRC16 SRCB AP1 AP2 AP3 CM KONT);
    [exact VM | exact AUX | exact DLC | exact ST | exact ERR | exact MI].
Qed.

End ACeilS1.

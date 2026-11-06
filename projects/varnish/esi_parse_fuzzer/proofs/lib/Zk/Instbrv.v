(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KInv MI_Inv MI_Kit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Arith MI_Geom MI_Ext MI_Pres2 MI_Cnt MI_WFree Mallkgx Mall1es Mall79j KNodes RzImpl KLink KLinkC MSafe KFrame.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall79j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzImpl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KFrame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import W_rejt8 InstDefs InstFree Instjhg Instqy7 Instbka.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls6g Mallx0l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import LB_Inv LB_Sum LB_Rrk0 LB_Own InstQ.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma Forall2_map_map {A B A' B'} (R : A -> B -> Prop) (R' : A' -> B' -> Prop) (f : A -> A') (h : B -> B') l1 l2 :
  Forall2 R l1 l2 -> (forall x y, R x y -> R' (f x) (h y)) -> Forall2 R' (map f l1) (map h l2).
Proof. intros F HR. induction F; cbn; constructor; auto. Qed.

Lemma strip_of_ctrl_eq st st' : ctrl_eq st st' -> strip st' = strip st.
Proof. intros [C1 C2 C3 C4 C5 C6 C7 C8 C9]. unfold strip. rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9. reflexivity. Qed.

Lemma set_size_mem_outside m P E n b3 (x : word) :
  3 <= P -> 0 <= n -> P + n <= E -> E + 1 <= 2^64 -> ~ (P - 3 <= bv_unsigned x < E) -> set_size_mem m P E n b3 x = m x.
Proof.
  intros P3 N0 PE E64 Hx. unfold set_size_mem. cbv zeta.
  assert (W1 : forall mm a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> ~ (a <= bv_unsigned x < a + Z.of_nat (length bs)) -> write_to_mem mm (wa a) bs x = mm x).
  { intros mm a bs Ha Hl N. rewrite write_to_mem_spec by lia.
    destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity. exfalso. lia. }
  assert (L4 : forall v, length (le4 v) = 4%nat) by (intros; apply length_le4).
  destruct (Z.eqb_spec (E - P - n) 0) as [R0|R0]; destruct (Z.leb_spec 5 (E - P - n)) as [R5|R5]; try (exfalso; lia).
  - rewrite W1 by (cbn; lia). reflexivity.
  - rewrite W1 by (cbn; lia). rewrite W1 by (rewrite ?L4; cbn; lia). rewrite W1 by (cbn; lia). rewrite W1 by (cbn; lia). reflexivity.
  - rewrite W1 by (cbn; lia). rewrite W1 by (cbn; lia). reflexivity.
Qed.

Section CEIL.
Context {Clg : Ceiling} {Rr : MRep.RunRandom}.  (* [comment removed for export] *)

Theorem inplace_model : forall s LB m md b st off g bm i r ar q res n',
  p0_ainv (mkIAS s LB Rr) m md -> In b LB -> heap_wit s LB m st ->
  blk_addr b = r_base r + snd (blk_slot b) + UNIT * off ->
  rbf st m (blk_slot b) off (blk_size b) g bm i r ar q res ->
  let mr := get_meta_rec st g in
  let P := blk_addr b in
  let E := r_base r + snd (blk_slot b) + get_stride mr - IB in
  0 <= n' -> P + n' <= E -> n' < MMAP_THRESHOLD -> m_sizeclass mr <= size_to_class n' + 1 ->
  p0_ainv (mkIAS s (lb_resize b n' LB) Rr) (set_size_mem m P E n' (i + 32 * Z.min res 5)) md.
Proof.
  intros until n'. intros AI Hb HW HA RB. cbv zeta. intros N0 FIT NT CLS.
  destruct AI as (HP & OW & RP & QVs). cbn [ia_s ia_LB ia_rr] in *.
  destruct HW as (LB0 & PERM & Hst & MRP & [BL AR]).
  pose proof AR as (L & LS & BLs & INV & LIVE & RESV & SEC & CR).
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
  destruct (Forall2_In_l _ _ _ _ CR IN0) as (k & Hk & (KS & KZ & KA)).
  destruct k as [[c off2] n]. cbn [bslot boff bsize fst snd] in KS, KZ, KA.
  set (stride := get_stride (get_meta_rec st g)) in *.
  set (b3 := i + 32 * Z.min res 5).
  pose proof (rb_reg _ _ _ _ _ _ _ _ _ _ _ _ RB) as Hr. pose proof (rb_fst _ _ _ _ _ _ _ _ _ _ _ _ RB) as Fc.
  pose proof (rb_c _ _ _ _ _ _ _ _ _ _ _ _ RB) as Ec2. fold stride in Ec2.
  pose proof (rb_stride _ _ _ _ _ _ _ _ _ _ _ _ RB) as [S16 SM]. fold stride in S16, SM.
  pose proof (rb_i _ _ _ _ _ _ _ _ _ _ _ _ RB) as Hi. pose proof (rb_li _ _ _ _ _ _ _ _ _ _ _ _ RB) as LI.
  pose proof (rb_off _ _ _ _ _ _ _ _ _ _ _ _ RB) as HOFF. pose proof (rb_res _ _ _ _ _ _ _ _ _ _ _ _ RB) as [ERES RES0]. fold stride in ERES.
  pose proof (rb_q _ _ _ _ _ _ _ _ _ _ _ _ RB) as [Q16 QR]. fold stride in Q16.
  pose proof (rb_sc _ _ _ _ _ _ _ _ _ _ _ _ RB) as SC. fold stride in SC.
  pose proof (rb_b0 _ _ _ _ _ _ _ _ _ _ _ _ RB) as B0. pose proof (rb_si0 _ _ _ _ _ _ _ _ _ _ _ _ RB) as SI0. fold stride in SI0.
  pose proof (rb_span _ _ _ _ _ _ _ _ _ _ _ _ RB) as SPAN. fold stride in SPAN.
  pose proof (rb_rbase _ _ _ _ _ _ _ _ _ _ _ _ RB) as (R0 & RAL & RC & RIMG).
  subst c. set (c := blk_slot b) in *.
  (* [comment removed for export] *)
  assert (Cc : conc st c = r_base r + snd c) by (apply conc_region'; exact Hr).
  assert (EOFF : off2 = off) by (rewrite Cc in KA; rewrite KA in HA; try (generalize alloc_ceiling_val); clear - HA; try pose proof alloc_ceiling_val; unfold UNIT in HA; lia).
  subst off2. rewrite KZ in RB.
  (* [comment removed for export] *)
  pose proof (size_to_class_ok n' ltac:(lia)) as [SCn _].
  assert (SC48 : m_sizeclass (get_meta_rec st g) < 48) by (destruct SC as [[? _]|[E63 _]]; lia).
  pose proof (rb_stride20 _ _ _ _ _ _ _ _ _ _ _ _ RB SC48) as ST20. fold stride in ST20.
  assert (STL : stride < 2^20) by (try (generalize alloc_ceiling_val); clear - ST20 S16 Hi; try pose proof alloc_ceiling_val; nia).
  assert (Ec : c = (fst bm, sstart (MI_Inv.MR st g) i)).
  { apply injective_projections; cbn [fst snd]; [exact Fc|]. unfold sstart, gbase. unfold MI_Inv.MR.
    rewrite (rb_mem _ _ _ _ _ _ _ _ _ _ _ _ RB). cbn [snd]. exact Ec2. }
  assert (EQ : (snd (aadd c (UNIT * off)) - (snd bm + UNIT)) / UNIT = q).
  { cbn [aadd snd]. rewrite Ec2. replace (snd bm + UNIT + stride * i + UNIT * off - (snd bm + UNIT)) with (q * UNIT) by (try (generalize alloc_ceiling_val); clear - Q16; try pose proof alloc_ceiling_val; unfold UNIT in *; lia).
    unfold UNIT. apply Z.div_mul. lia. }
  assert (B3L : Z.land b3 31 = i) by (subst b3; apply land31_idx; [try (generalize alloc_ceiling_val); clear - Hi LI; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - RES0; try pose proof alloc_ceiling_val; lia]).
  assert (B3R : 0 <= b3 < 256) by (subst b3; try (generalize alloc_ceiling_val); clear - Hi LI RES0; try pose proof alloc_ceiling_val; lia).
  assert (FIT' : UNIT * off + n' <= stride - IB) by (try (generalize alloc_ceiling_val); clear - FIT HA; try pose proof alloc_ceiling_val; unfold UNIT, IB in *; lia).
  assert (RES' : stride - IB - UNIT * off - n' < 2^32) by (try (generalize alloc_ceiling_val); clear - STL N0 HOFF; try pose proof alloc_ceiling_val; unfold UNIT, IB; lia).
  pose proof (ip_INVL (Clg:=Clg) st L BLs LS c off n g bm i n' b3 INV Hk (rb_slot _ _ _ _ _ _ _ _ _ _ _ _ RB) (rb_hosts _ _ _ _ _ _ _ _ _ _ _ _ RB)
                Hi Ec HOFF N0 FIT' RES' B3L B3R (rb_k4 _ _ _ _ _ _ _ _ _ _ _ _ RB)
                ltac:(rewrite EQ; exact (rb_k2 _ _ _ _ _ _ _ _ _ _ _ _ RB)) ltac:(rewrite EQ; exact (rb_k1 _ _ _ _ _ _ _ _ _ _ _ _ RB)) ltac:(rewrite EQ; exact QR)) as INV'.
  assert (TK : ticks_ok st) by exact (ci_ticks _ _ (Mallx0l.areach_cinv_proof _ _ AR)).
  pose proof (ip_mrep (Clg:=Clg) st L BLs LS c off n g bm i n' b3 INV Hk (rb_hosts _ _ _ _ _ _ _ _ _ _ _ _ RB) Hi Ec HOFF N0 FIT' RES' B3L B3R
                ltac:(rewrite EQ; exact QR) m r MRP TK ltac:(rewrite <- Fc; exact Hr) (rb_kind _ _ _ _ _ _ _ _ _ _ _ _ RB) B0 SPAN) as [MR' TK'].
  cbn [aadd snd] in MR'.
  replace (r_base r + (snd c + UNIT * off)) with (blk_addr b) in MR' by (try (generalize alloc_ceiling_val); clear - HA; try pose proof alloc_ceiling_val; lia).
  replace (r_base r + (snd c + (stride - IB))) with (r_base r + snd c + stride - IB) in MR' by (clear; lia).
  set (st' := stf st c off g n' b3) in *.
  destruct (stf_ctrl_st st c off g n' b3) as [CE TKE]. fold st' in CE, TKE.
  pose proof (strip_of_ctrl_eq _ _ CE) as STRIP.
  cbn [ia_s ia_LB ia_rr]. split; [| split; [| split]].
  - (* [comment removed for export] *)
    exists st', (lb_resize b n' LB0). split; [| split; [| split; [exact MR'| split]]].
    + unfold lb_resize. apply Permutation_map. exact PERM.
    + rewrite STRIP. exact Hst.
    + unfold brk_link in *. unfold ctx in *. rewrite (ce_ctx _ _ CE).
      destruct (c_brk (s_ctx st)); try exact I. rewrite BL. unfold conc, get_region. rewrite (ce_regions _ _ CE). reflexivity.
    + exists L, LS, (bl_resize c n' BLs). split; [exact INV'|]. split; [rewrite bl_resize_slots; exact LIVE|]. split; [exact RESV|].
      split; [rewrite (ce_secret _ _ CE); exact SEC|].
      unfold CORR, lb_resize, bl_resize. eapply Forall2_map_map; [exact CR|].
      intros x y (C1 & C2 & C3). unfold corr1.
      assert (CX : conc st' (bslot y) = conc st (bslot y)) by (unfold conc, get_region; rewrite (ce_regions _ _ CE); reflexivity).
      rewrite C1. subst c. destruct (aptr_eqb (bslot y) (blk_slot b)); cbn [blk_slot blk_size blk_addr blk_id bslot bsize boff fst snd]; rewrite ?CX; auto.
  - (* [comment removed for export] *) rewrite lb_resize_ids. exact OW.
  - (* [comment removed for export] *)
    apply (repl0_agree m _ RP). intros a Ha. apply set_size_mem_outside.
    + try (generalize alloc_ceiling_val); clear - HA R0 B0 Ec2 SI0 HOFF; try pose proof alloc_ceiling_val. unfold UNIT in *. lia.
    + exact N0.
    + exact FIT.
    + pose proof (round_up_pg_ge (r_len r)). clear - RC SPAN Ec2 Hi H S16 SI0; try pose proof alloc_ceiling_val. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold UNIT, IB in *.
      assert (stride * (i + 1) <= stride * (m_last_idx (get_meta_rec st g) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
    + rewrite unsigned_lit by (unfold MALLOC_REPLACED in Ha; lia). unfold MALLOC_REPLACED in Ha.
      pose proof (round_up_pg_ge (r_len r)). clear - Ha RIMG HA R0 B0 SI0 HOFF Ec2 SPAN Hi S16 H; try pose proof alloc_ceiling_val. unfold UNIT, IB in *.
      assert (stride * (i + 1) <= stride * (m_last_idx (get_meta_rec st g) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
      lia.
  - (* [comment removed for export] *)
    assert (E0 : blk0 (lb_resize b n' LB) = bl_resz c n' (blk0 LB)).
    { unfold lb_resize. apply blk0_map_resize. intros x. fold c. destruct (aptr_eqb (blk_slot x) c); cbn [blk_slot blk_size blk_id fst snd]; auto. }
    rewrite E0. apply (QV_resize (ps_m s) (blk0 LB) c n' g i QVs).
    + rewrite <- Hst. change (s_slots (strip st)) with (s_slots st). exact (rb_slot _ _ _ _ _ _ _ _ _ _ _ _ RB).
    + rewrite <- Hst. exact SC48.
    + exact NT.
Qed.

End CEIL.

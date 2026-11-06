(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module HW := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0 R_memcpy.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KInv MI_Inv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Mall1es Mall79j KNodes RzImpl KLink KLinkC MSafe KFrame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RzAux.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall79j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzImpl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KFrame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.RzBridge.RzEvt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require W_ge3a6 W_redqm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require W_rejt8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require W_rejt8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require W_rejt8 W_retp0 RF_m8yt Instfes Inst8ld InstDefs InstFree Instjhg Instffk Instrcx Instjk7 Instqy7 Inst41h Instbrv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_redqm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_rejt8.W_re997 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_rejt8.W_reagh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_rejt8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_retp0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Instfes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Inst8ld OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.InstDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.InstFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Instjhg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Instffk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Instrcx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Instjk7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Instqy7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Inst41h OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Instbrv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls6g Mallx0l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import LB_Inv LB_Sum InstQ.   (* [comment removed for export] *)
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma realloc_sym_ptr_evt : forall R F fc m,
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 realloc_entry) fc None m (seg_rom rsegs))
      (MS R F (Z_to_bv 64 realloc_sym) fc None m (seg_rom rsegs)).
Proof. intros. unfold realloc_sym, realloc_entry. step. apply evt_done. reflexivity. Qed.

Lemma bytes_at_ov1 m a x : bytes_at rsegs m a [x] -> ov_read_bytes rsegs m (wa a) 1 = Some [x].
Proof.
  intros H. pose proof (bytes_at_read rsegs m a [x] 0 1 H ltac:(lia) ltac:(cbn; lia)) as R.
  cbn [firstn skipn Z.to_nat] in R. rewrite Z.add_0_r in R. exact R.
Qed.
Lemma bytes_at_ov4 m a w : bytes_at rsegs m a (le4 w) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 w).
Proof.
  intros H. pose proof (bytes_at_read rsegs m a (le4 w) 0 4 H ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as R.
  cbn [skipn Z.to_nat] in R. rewrite firstn_all2 in R by (rewrite length_le4; lia). rewrite Z.add_0_r in R. exact R.
Qed.

Lemma write_other mm a bs (x : word) : (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  ~ (a <= bv_unsigned x < a + Z.of_nat (length bs))%Z -> write_to_mem mm (wa a) bs x = mm x.
Proof.
  intros Ha Hb OUT. rewrite write_to_mem_spec by lia.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity. exfalso; lia.
Qed.
Lemma write_mono mm a bs (x : word) : (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  mm x <> None -> write_to_mem mm (wa a) bs x <> None.
Proof.
  intros Ha Hb H. rewrite write_to_mem_spec by lia.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try exact H.
  intros E0. apply nth_error_None in E0. lia.
Qed.

Lemma set_size_mem_outside m P E n b3 x :
  0 <= P - 3 -> E + 1 <= 2^64 -> 0 <= n -> P + n <= E ->
  bv_unsigned x <> P - 3 -> ~ (P + n <= bv_unsigned x <= E) ->
  set_size_mem m P E n b3 x = m x.
Proof.
  intros P3 EH N0 PN NX1 NX2. unfold set_size_mem. set (r := E - P - n).
  pose proof (length_le4 (MRep.wz r)) as L4.
  destruct (5 <=? r) eqn:R5; [apply Z.leb_le in R5| apply Z.leb_gt in R5]; cbv beta iota zeta;
    (destruct (r =? 0) eqn:R0; [apply Z.eqb_eq in R0| apply Z.eqb_neq in R0]);
    rewrite !write_other by (cbn [length]; rewrite ?L4; lia); reflexivity.
Qed.

Lemma set_size_mem_mono m P E n b3 x :
  0 <= P - 3 -> E + 1 <= 2^64 -> 0 <= n -> P + n <= E -> m x <> None -> set_size_mem m P E n b3 x <> None.
Proof.
  intros P3 EH N0 PN Hm. unfold set_size_mem. set (r := E - P - n).
  pose proof (length_le4 (MRep.wz r)) as L4.
  destruct (5 <=? r) eqn:R5; [apply Z.leb_le in R5| apply Z.leb_gt in R5]; cbv beta iota zeta;
    (destruct (r =? 0) eqn:R0; [apply Z.eqb_eq in R0| apply Z.eqb_neq in R0]);
    repeat (apply write_mono; [cbn [length]; rewrite ?L4; lia| cbn [length]; rewrite ?L4; lia|]); exact Hm.
Qed.

Lemma md_frame_refl md : m_vm_lazy md = [] -> m_halted md = None -> md_frame md md.
Proof. intros L H. unfold md_frame. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto. Qed.

(* [comment removed for export] *)
Lemma frame_ok_pre_agree (O O' : Z -> Prop) sp win (V NB : Z -> Prop) m m1 m' :
  (forall a, 0 <= a < 2^64 -> ~ (sp - win <= a < sp) -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2^64 -> m (Z_to_bv 64 a) <> None -> m1 (Z_to_bv 64 a) <> None) ->
  frame_ok LayoutP0 O O' sp win V NB m1 m' -> frame_ok LayoutP0 O O' sp win V NB m m'.
Proof.
  (intros AG MONO; (first [ intro dR_9; dand7 dR_9 as F1 F2 F3 F4 F5 F6 F7 | intros (F1 & F2 & F3 & F4 & F5 & F6 & F7) ])).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - intros a Ha NO NO' NW NE NV NN. rewrite <- (AG a Ha NW). apply F1; auto.
  - intros a Ha NI Hm. apply F2; auto.
  - exact F3.
  - intros a Ha Hn. destruct (F4 a Ha Hn) as [X|[X|[X HZ]]]; [left; exact X| right; left; exact X| right; right].
    split; [| exact HZ]. destruct (m (Z_to_bv 64 a)) eqn:E; [| reflexivity]. exfalso. apply (MONO a Ha); [congruence| exact X].
  - intros a Ha Ho. destruct (F5 a Ha Ho) as [X|[X|[X HZ]]]; [left; exact X| right; left; exact X| right; right].
    split; [| exact HZ]. destruct (m (Z_to_bv 64 a)) eqn:E; [| reflexivity]. exfalso. apply (MONO a Ha); [congruence| exact X].
  - exact F6.
  - exact F7.
Qed.

End CEIL.

Section REALLOC.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

(* [comment removed for export] *)
Hypothesis slot_private : forall {Rr : MRep.RunRandom} s LB m st b off g bm i r ar q res y,   (* [comment removed for export] *)
  heap_wit s LB m st -> In b LB ->
  blk_addr b = r_base r + snd (blk_slot b) + UNIT * off ->
  rbf st m (blk_slot b) off (blk_size b) g bm i r ar q res ->
  In y LB -> y <> b ->
  blk_addr y + blk_size y <= r_base r + snd (blk_slot b) - IB
  \/ r_base r + snd (blk_slot b) + get_stride (get_meta_rec st g) - IB < blk_addr y.

(* [comment removed for export] *)
Hypothesis stride_small : forall {Rr : MRep.RunRandom} s LB m st b off g bm i r ar q res,
  heap_wit s LB m st -> In b LB ->
  blk_addr b = r_base r + snd (blk_slot b) + UNIT * off ->
  rbf st m (blk_slot b) off (blk_size b) g bm i r ar q res ->
  m_sizeclass (get_meta_rec st g) < 48 -> get_stride (get_meta_rec st g) < 2^31.

(* [comment removed for export] *)
Definition realloc_K (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (md : Model) (A : ias) (p n old : Z) (T : TSet) : Prop :=
  forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : ias) (m' : mem) (md' : Model),
        p0_ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
        (* [comment removed for export] *)
        (r <> 0 /\ p0_live A' r = Some n /\ (r = p \/ (p0_live A r = None /\ p0_live A' p = None)) /\
             (forall q, q <> r -> q <> p -> p0_live A' q = p0_live A q) /\
             (forall i, 0 <= i < Z.min n old -> m' (wz (r + i)) = m (wz (p + i))) /\
             p0_livebytes A' = p0_livebytes A + n - old /\ p0_nlive A' = p0_nlive A /\
             frame_ok LayoutP0 (p0_owned A) (p0_owned A') (bv_unsigned sp) AllocSpec.REALLOC_STACK (blk p old) (blk r n) m m') ->
        realizes rsegs (mkCfg (HW.mkst (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') ra m' (seg_rom rsegs)) md') T.

(* [comment removed for export] *)
Hypothesis mremap_path_rz :
  forall {Rr : MRep.RunRandom} (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m m1 : mem) (md : Model) (s : PState) (LB : list block) (b : block) (p n old : Z) (T : TSet)
         (st : mstate) (off : Z) (g bm : aptr) (i : Z) (r : region) (ar : area) (q res : Z)
         (t2y t3y t4y : word),
    let mr := get_meta_rec st g in
    let stride := get_stride mr in
    let c := blk_slot b in
    let E := r_base r + snd c + stride - 4 in
    (* [comment removed for export] *)
    p0_ainv (mkIAS s LB Rr) m md -> mem_inv rsegs m ->
    a0 = wz p -> a1 = wz n -> 0 <= n < 2^32 -> p <> 0 -> p0_live (mkIAS s LB Rr) p = Some old ->
    lb_bytes LB + n <= LIVE_MAX -> zlen LB + 1 <= NLIVE_MAX ->   (* [comment removed for export] *)
    tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
    alloc_ceiling <= bv_unsigned sp - AllocSpec.REALLOC_STACK ->
    mapped m (bv_unsigned sp - AllocSpec.REALLOC_STACK) AllocSpec.REALLOC_STACK ->
    realloc_K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md (mkIAS s LB Rr) p n old T ->
    (* [comment removed for export] *)
    p0_ainv (mkIAS s LB Rr) m1 md -> mem_inv rsegs m1 ->
    (forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 64 <= a < bv_unsigned sp) -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
    (forall a, 0 <= a < 2^64 -> m (Z_to_bv 64 a) <> None -> m1 (Z_to_bv 64 a) <> None) ->
    rw_cells rsegs m1 (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    mapped m1 (bv_unsigned sp - 64 - 8192) 8192 ->
    (* [comment removed for export] *)
    In b LB -> blk_addr b = p -> blk_size b = old ->
    heap_wit s LB m1 st -> ps_m s = strip st -> mrep st m1 -> ticks_ok st ->
    p = r_base r + snd c + UNIT * off -> rbf st m1 c off old g bm i r ar q res ->
    (* [comment removed for export] *)
    MMAP_THRESHOLD <= n -> m_sizeclass mr = 63 ->
    realizes rsegs (mkCfg (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp
                                  (wz E) (wz (conc st bm + 16 + stride * i)) t2y s0 (Z_to_bv 64 (conc st g)) a0 a1
                                  (wz (conc st bm)) (wz (m_sizeclass mr)) (Z_to_bv 64 (meta_word mr)) t3y (wz (E + 4)) (wz (E - p)) (wz (p + old))
                                  s3 s4 s5 s6 s7 s8 s9 s10 s11 t4y t4 t5 t6)
                             bvmap_empty (wz 0x24ad4) (Z_to_bv 32 0) None m1 (seg_rom rsegs)) md) T.

Theorem p0_realloc_cps :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : mem) (md : Model) (A : ias) (p n old : Z) (T : TSet),
    p0_ainv A m md -> mem_inv rsegs m ->
    a0 = wz p -> a1 = wz n -> 0 <= n < 2^32 -> p <> 0 -> p0_live A p = Some old ->
    n <= NREQ_CAP -> p0_livebytes A + n <= LIVE_MAX -> p0_nlive A + 1 <= NLIVE_MAX ->   (* [comment removed for export] *)
    tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
    alloc_ceiling <= bv_unsigned sp - AllocSpec.REALLOC_STACK ->
    mapped m (bv_unsigned sp - AllocSpec.REALLOC_STACK) AllocSpec.REALLOC_STACK ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : ias) (m' : mem) (md' : Model),
        p0_ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
        (* [comment removed for export] *)
        (r <> 0 /\ p0_live A' r = Some n /\ (r = p \/ (p0_live A r = None /\ p0_live A' p = None)) /\
             (forall q, q <> r -> q <> p -> p0_live A' q = p0_live A q) /\
             (forall i, 0 <= i < Z.min n old -> m' (wz (r + i)) = m (wz (p + i))) /\
             p0_livebytes A' = p0_livebytes A + n - old /\ p0_nlive A' = p0_nlive A /\
             frame_ok LayoutP0 (p0_owned A) (p0_owned A') (bv_unsigned sp) AllocSpec.REALLOC_STACK (blk p old) (blk r n) m m') ->
        realizes rsegs (mkCfg (HW.mkst (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') ra m' (seg_rom rsegs)) md') T) ->
    realizes rsegs (mkCfg (HW.mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_realloc_pc LayoutP0) m (seg_rom rsegs)) md) T.
Proof.
  intros until T. intros AI MI A0 A1 NR PNZ LV _ BYTES NLV TP SPA RAA CEIL MAP K.
  pose proof (ainv_KI _ _ _ AI) as [Hh Hl].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ ra) as RAR. change (bv_modulus 64) with (2^64) in RAR.
  pose proof alloc_ceiling_val as ACV.
  unfold AllocSpec.REALLOC_STACK in *. cbn [al_realloc_pc LayoutP0]. rewrite mkst_MS'.
  assert (SP64 : 0 <= bv_unsigned sp - 64 < 2^64) by (try (generalize alloc_ceiling_val); clear - SPR CEIL ACV; try pose proof alloc_ceiling_val; lia).
  (first [ pose proof ((p0_live_ok A m md p old AI LV)) as dR_1; dand7 dR_1 as OLD0 P16 P4096 PC PIMG PM PNO | pose proof (p0_live_ok A m md p old AI LV) as (OLD0 & P16 & P4096 & PC & PIMG & PM & PNO) ]). cbn [al_image_lo al_image_hi LayoutP0] in PIMG.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  set (lo := bv_unsigned sp - 8256) in *.
  pose proof (mapped_stk_p0 (Clg:=Clg) m lo (bv_unsigned sp) ltac:(replace (bv_unsigned sp - lo) with 8256 by lia; exact MAP) CEIL ltac:(lia)) as ST.
  destruct (stk_carve rsegs m lo (bv_unsigned sp) 64 ST ltac:(lia)) as [ST1 [junk FR]].
  change (Z.of_nat 64) with 64 in ST1, FR.
  (first [ pose proof ((rw_cells_C8x8 m _ junk FR)) as dR_2; dex8 dR_2 as j0 j1 j2 j3 j4 j5 j6 j7; rename dR_2 into FR8 | pose proof ((rw_cells_C8x8 m _ junk FR)) as dR_2; dand9 dR_2 as j0 j1 j2 j3 j4 j5 j6 j7 FR8 | destruct (rw_cells_C8x8 m _ junk FR) as (j0 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & FR8) ]).
  (* [comment removed for export] *)
  eapply rz_evt; [apply realloc_sym_ptr_evt| exact Hh| exact Hl|]. intros ms0 ->.
  (* [comment removed for export] *)
  eapply rz_evt; [| exact Hh| exact Hl|].
  { eapply (realloc_entry_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ _ m j0 j1 j2 j3 j4 j5 j6 j7 p n);
      [rewrite A0; apply unsigned_lit; lia| exact PNZ| rewrite A1; apply unsigned_lit; lia| unfold SIZE_OVF; lia| lia| exact FR8| exact MI]. }
  (intros ms1; (first [ intro dR_10; dex1 dR_10 as m1; dand5 dR_10 as -> MU1 WM1 MI1 FR1 | intro dR_10; dand6 dR_10 as m1 -> MU1 WM1 MI1 FR1 | intros (m1 & -> & MU1 & WM1 & MI1 & FR1) ])).
  assert (AG1 : forall a, 0 <= a < bv_unsigned sp - 64 -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros a Ha. apply MU1. cbn. rewrite unsigned_lit by lia. lia. }
  pose proof (p0_ainv_agree (Clg:=Clg) A m m1 md (bv_unsigned sp - 64) AI ltac:((let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia) AG1) as AI1.
  assert (MONO1 : forall a, 0 <= a < 2^64 -> m (Z_to_bv 64 a) <> None -> m1 (Z_to_bv 64 a) <> None).
  { intros a Ha Hm. destruct (Classical_Prop.classic (bv_unsigned sp - 64 <= a < bv_unsigned sp)) as [IN|OUT].
    - destruct FR1 as [_ (_ & _ & W)]. cbn [cells_size csize Nat.add] in W.
      specialize (W (a - (bv_unsigned sp - 64)) ltac:(lia)). replace (bv_unsigned sp - 64 + (a - (bv_unsigned sp - 64))) with a in W by lia.
      rewrite p0_wview_overlay in W by (unfold wa; rewrite unsigned_lit; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia). exact W.
    - rewrite (MU1 (Z_to_bv 64 a)); [exact Hm|]. cbn. rewrite unsigned_lit by lia. lia. }
  assert (AGo : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 64 <= a < bv_unsigned sp) -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros a Ha OUT. apply MU1. cbn. rewrite unsigned_lit by lia. lia. }
  assert (MAP1 : mapped m1 (bv_unsigned sp - 64 - 8192) 8192).
  { intros ii Hii. unfold MRep.wz. rewrite AG1 by lia. replace (bv_unsigned sp - 64 - 8192 + ii) with (lo + ii) by lia. apply MAP. lia. }
  (* [comment removed for export] *)
  destruct A as [s LB Rr]. pose proof AI1 as (HP1 & OW1 & RP1 & _). cbn [ia_s ia_LB ia_rr] in HP1, OW1.
  unfold p0_livebytes, p0_nlive in BYTES, NLV. cbn [ia_LB] in BYTES, NLV.
  (first [ pose proof ((p0_live_some _ _ _ LV)) as dR_4; dex1 dR_4 as b; dand3 dR_4 as Hb Eaddr Esize | pose proof ((p0_live_some _ _ _ LV)) as dR_4; dand4 dR_4 as b Hb Eaddr Esize | destruct (p0_live_some _ _ _ LV) as (b & Hb & Eaddr & Esize) ]). cbn [ia_LB] in Hb.
  (first [ pose proof ((live_block_rbf s LB m1 b HP1 Hb)) as dR_5; dex9 dR_5 as st off g bm i r ar q res; dand6 dR_5 as HWT Hst MR TK HA RB | pose proof ((live_block_rbf s LB m1 b HP1 Hb)) as dR_5; dand15 dR_5 as st off g bm i r ar q res HWT Hst MR TK HA RB | destruct (live_block_rbf s LB m1 b HP1 Hb) as (st & off & g & bm & i & r & ar & q & res & HWT & Hst & MR & TK & HA & RB) ]).
  rewrite Eaddr, Esize in *.
  set (c := blk_slot b) in *. set (mr := get_meta_rec st g) in *. set (stride := get_stride mr) in *.
  destruct (rb_hosts _ _ _ _ _ _ _ _ _ _ _ _ RB) as [ai HO].
  (first [ pose proof ((rb_rbase _ _ _ _ _ _ _ _ _ _ _ _ RB)) as dR_6; dand4 dR_6 as R0 RAL RC RI | pose proof (rb_rbase _ _ _ _ _ _ _ _ _ _ _ _ RB) as (R0 & RAL & RC & RI) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  pose proof (rb_q _ _ _ _ _ _ _ _ _ _ _ _ RB) as [Q16 QR]. fold mr stride in Q16.
  pose proof (rb_res _ _ _ _ _ _ _ _ _ _ _ _ RB) as [ERES RES0]. fold mr stride in ERES.
  pose proof (rb_i _ _ _ _ _ _ _ _ _ _ _ _ RB) as HI. fold mr in HI.
  pose proof (rb_li _ _ _ _ _ _ _ _ _ _ _ _ RB) as HLI. fold mr in HLI.
  pose proof (rb_off _ _ _ _ _ _ _ _ _ _ _ _ RB) as HOFF.
  pose proof (rb_fit _ _ _ _ _ _ _ _ _ _ _ _ RB) as FIT. fold mr stride in FIT.
  pose proof (rb_stride _ _ _ _ _ _ _ _ _ _ _ _ RB) as [S16 SM]. fold mr stride in S16, SM.
  pose proof (rb_si0 _ _ _ _ _ _ _ _ _ _ _ _ RB) as SI0. fold mr stride in SI0.
  pose proof (rb_span _ _ _ _ _ _ _ _ _ _ _ _ RB) as SPAN. fold mr stride in SPAN.
  pose proof (rb_c _ _ _ _ _ _ _ _ _ _ _ _ RB) as EC. fold mr stride in EC.
  pose proof (rb_b0 _ _ _ _ _ _ _ _ _ _ _ _ RB) as B0.
  pose proof (rb_fst _ _ _ _ _ _ _ _ _ _ _ _ RB) as FST.
  pose proof (rb_sc _ _ _ _ _ _ _ _ _ _ _ _ RB) as BSC. fold mr stride in BSC.
  pose proof (rb_maplen _ _ _ _ _ _ _ _ _ _ _ _ RB) as ML0. fold mr in ML0.
  set (b3 := i + 32 * Z.min res 5) in *.
  assert (B3R : 0 <= b3 < 192) by (subst b3; try (generalize alloc_ceiling_val); clear - HI HLI RES0; try pose proof alloc_ceiling_val; lia).
  assert (IDX : Z.land b3 31 = i) by (subst b3; apply land31_idx; try (generalize alloc_ceiling_val); clear - HI HLI RES0; try pose proof alloc_ceiling_val; lia).
  pose proof (u16_bytes q QR) as U16.
  set (p0 := aadd c (UNIT * off)).
  assert (Fp : fst p0 = fst c) by reflexivity.
  assert (Sp : snd p0 = snd c + UNIT * off) by reflexivity.
  assert (Ebase : aadd p0 (- (UNIT * (byte_of q 0 + 256 * byte_of q 1)) - UNIT) = bm).
  { rewrite U16. unfold p0, aadd. cbn [fst snd]. apply injective_projections; cbn [fst snd]; [exact FST|]. unfold UNIT in *. nia. }
  assert (OFS : 16 * off + 16 <= stride) by (try (generalize alloc_ceiling_val); clear - FIT OLD0 SM S16 HOFF; try pose proof alloc_ceiling_val; unfold UNIT, IB in *; Z.div_mod_to_equations; nia).
  assert (CB : conc st bm = r_base r + snd bm) by (apply conc_region'; rewrite <- FST; exact (rb_reg _ _ _ _ _ _ _ _ _ _ _ _ RB)).
  assert (SIL : stride * (i + 1) <= stride * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; try (generalize alloc_ceiling_val); clear - S16 HI; try pose proof alloc_ceiling_val; unfold UNIT in *; lia).
  assert (PHI : snd p0 + 16 <= round_up_pg (r_len r)).
  { rewrite Sp, EC. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. try (generalize alloc_ceiling_val); clear - SPAN OFS SIL SI0 B0 HOFF; try pose proof alloc_ceiling_val. unfold UNIT in *. lia. }
  assert (EE : conc st bm + 16 + stride * i = r_base r + snd c) by (rewrite CB, EC; clear; unfold UNIT; lia).
  assert (HPa0 : bv_unsigned a0 = r_base r + snd p0).
  { rewrite A0, Sp, HA. unfold MRep.wz. rewrite unsigned_lit; [clear; unfold UNIT; lia|]. try (generalize alloc_ceiling_val); clear - P4096 PC ACV HA OLD0; try pose proof alloc_ceiling_val. unfold UNIT in *. lia. }
  assert (SC64 : 0 <= m_sizeclass mr < 64) by (try (generalize alloc_ceiling_val); clear - BSC; try pose proof alloc_ceiling_val; lia).
  (* [comment removed for export] *)
  eapply rz_evt; [| exact Hh| exact Hl|].
  { eapply (realloc_getmeta_spec ra (wz (bv_unsigned sp - 64)) gp tp t0 t1 t2 s0 s1 a0 a1 (wz SIZE_OVF) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              bvmap_empty (Z_to_bv 32 0) m1 st p0 r g (mkGhdr (Some g) ai) ar b3 (byte_of q 0) (byte_of q 1)).
    all: rewrite ?IDX, ?Ebase, ?U16.
    - exact MR.
    - exact MI1.
    - rewrite Fp. exact (rb_reg _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - exact (rb_kind _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - exact HPa0.
    - rewrite Sp. clear - P16 RAL HA; try pose proof alloc_ceiling_val. unfold UNIT in *. Z.div_mod_to_equations. lia.
    - rewrite Sp, EC. try (generalize alloc_ceiling_val); clear - B0 SI0 HOFF; try pose proof alloc_ceiling_val. unfold UNIT. lia.
    - rewrite Sp, EC. try (generalize alloc_ceiling_val); clear - Q16 B0; try pose proof alloc_ceiling_val. unfold UNIT in *. lia.
    - exact PHI.
    - exact (rb_k4 _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - exact (rb_k3 _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - exact (rb_k2 _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - exact (rb_k1 _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - exact HO.
    - reflexivity.
    - exact (rb_mslot _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - exact (rb_g0 _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - exact (rb_mem _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - exact (proj1 (rb_area _ _ _ _ _ _ _ _ _ _ _ _ RB)).
    - exact (proj2 (rb_area _ _ _ _ _ _ _ _ _ _ _ _ RB)).
    - exact (rb_avail _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - exact (rb_freed _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - exact (rb_sec _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - cbv delta [mr] in HLI. try (generalize alloc_ceiling_val); clear - HLI; try pose proof alloc_ceiling_val. lia.
    - rewrite (rb_freeable _ _ _ _ _ _ _ _ _ _ _ _ RB). clear. lia.
    - exact SC64.
    - cbv delta [mr] in ML0. try (generalize alloc_ceiling_val); clear - ML0; try pose proof alloc_ceiling_val. lia.
    - cbv delta [mr] in HI. try (generalize alloc_ceiling_val); clear - HI; try pose proof alloc_ceiling_val. lia.
    - exact (rb_notA _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - exact (rb_notF _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - exact (rb_g16 _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - cbv delta [mr stride] in BSC. try (generalize alloc_ceiling_val); clear - BSC; try pose proof alloc_ceiling_val. lia.
    - exact (rb_g17 _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - cbv delta [mr stride] in BSC. try (generalize alloc_ceiling_val); clear - BSC; try pose proof alloc_ceiling_val. lia. }
  (intros ms2; (first [ intro dR_11; dand4 dR_11 as t2x t3x t4x -> | intros (t2x & t3x & t4x & ->) ])). rewrite IDX, Ebase. fold mr. fold stride.
  (* [comment removed for export] *)
  set (E := r_base r + snd c + stride - 4).
  assert (EE2 : conc st bm + 16 + stride * i + stride - 4 = E) by (subst E; rewrite <- EE; clear; lia).
  assert (ERES2 : res = E - p - old) by (subst E; rewrite ERES, HA; clear; unfold UNIT, IB; lia).
  assert (RSV : (if 160 <=? b3 then res else Z.shiftr b3 5) = res).
  { subst b3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
    destruct (Z.leb_spec 160 (i + 32 * Z.min res 5)); [reflexivity|]. cbv delta [mr] in HI, HLI. clear - HI HLI RES0 H; try pose proof alloc_ceiling_val. Z.div_mod_to_equations. lia. }
  assert (ELO : p <= E) by (rewrite ERES2 in RES0; try (generalize alloc_ceiling_val); clear - RES0 OLD0; try pose proof alloc_ceiling_val; lia).
  assert (ETOP : E + 4 <= r_base r + round_up_pg (r_len r)).
  { subst E. pose proof SPAN as SP2. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. try (generalize alloc_ceiling_val); clear - SP2 SIL EC B0 SI0 S16; try pose proof alloc_ceiling_val. unfold UNIT in *. lia. }
  assert (EHI : E + 5 <= 2^64) by (try (generalize alloc_ceiling_val); clear - ETOP RC ACV; try pose proof alloc_ceiling_val; lia).
  eapply rz_evt; [| exact Hh| exact Hl|].
  { eapply (realloc_geom_walk ra (wz (bv_unsigned sp - 64)) gp tp (wz (m_last_idx mr)) t2x s0 (wz (conc st g)) a0 a1
              (wz (m_sizeclass mr)) (wz (meta_word mr)) (wz SIZE_CLASSES) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5 t6
              bvmap_empty (Z_to_bv 32 0) m1 p (conc st bm) stride i b3 res); rewrite ?EE2, ?RSV.
    - rewrite HPa0, Sp, HA. clear. lia.
    - rewrite CB. try (generalize alloc_ceiling_val); clear - R0 B0; try pose proof alloc_ceiling_val. lia.
    - try (generalize alloc_ceiling_val); clear - HI; try pose proof alloc_ceiling_val. lia.
    - try (generalize alloc_ceiling_val); clear - S16; try pose proof alloc_ceiling_val. unfold UNIT in S16. lia.
    - exact EHI.
    - try (generalize alloc_ceiling_val); clear - B3R; try pose proof alloc_ceiling_val. lia.
    - exact ELO.
    - try (generalize alloc_ceiling_val); clear - ERES2 OLD0; try pose proof alloc_ceiling_val. lia.
    - intros H160. assert (R5 : 5 <= res).
      { subst b3. cbv delta [mr] in HI, HLI. clear - H160 HI HLI RES0; try pose proof alloc_ceiling_val. Z.div_mod_to_equations. lia. }
      (first [ pose proof ((rb_rd5 _ _ _ _ _ _ _ _ _ _ _ _ RB R5)) as dR_7; dand3 dR_7 as RD4 RD5 R32 | destruct (rb_rd5 _ _ _ _ _ _ _ _ _ _ _ _ RB R5) as (RD4 & RD5 & R32) ]). fold mr stride in RD4, RD5.
      split. { subst b3. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. cbv delta [mr] in HI, HLI. clear - R5 HI HLI; try pose proof alloc_ceiling_val. Z.div_mod_to_equations. lia. }
      split. { try (generalize alloc_ceiling_val); clear - R5 R32; try pose proof alloc_ceiling_val. lia. }
      split.
      + replace (E - 4) with (r_base r + snd c + stride - IB - 4) by (subst E; clear; unfold IB; lia). apply bytes_at_ov4. exact RD4.
      + replace (E - 5) with (r_base r + snd c + stride - IB - 5) by (subst E; clear; unfold IB; lia). apply bytes_at_ov1. exact RD5.
    - replace (E - res) with (r_base r + snd c + stride - IB - res) by (subst E; clear; unfold IB; lia). apply bytes_at_ov1.
      exact (rb_rdc _ _ _ _ _ _ _ _ _ _ _ _ RB).
    - replace E with (r_base r + snd c + stride - IB) by (subst E; clear; unfold IB; lia). apply bytes_at_ov1.
      exact (rb_rde _ _ _ _ _ _ _ _ _ _ _ _ RB). }
  (intros ms3; (first [ intro dR_12; dand4 dR_12 as t2y t3y t4y -> | intros (t2y & t3y & t4y & ->) ])). rewrite EE2, RSV.
  replace (E - res) with (p + old) by (try (generalize alloc_ceiling_val); clear - ERES2; try pose proof alloc_ceiling_val; lia).
  assert (AVR : 0 <= E - p < 2^64) by (try (generalize alloc_ceiling_val); clear - ELO EHI P4096; try pose proof alloc_ceiling_val; lia).
  assert (HN : bv_unsigned a1 = n) by (rewrite A1; apply unsigned_lit; try (generalize alloc_ceiling_val); clear - NR; try pose proof alloc_ceiling_val; lia).
  assert (ESP : wz (bv_unsigned sp - 64 + 64) = sp) by (unfold MRep.wz; replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) by lia; apply Z_to_bv_bv_unsigned).
  assert (RET : ret_pc ra = ra).
  { rewrite <- (definitions.Z_to_bv_bv_unsigned 64 ra) at 1. rewrite ret_pc_even; [apply definitions.Z_to_bv_bv_unsigned| lia| ].
    clear - RAA RAR; try pose proof alloc_ceiling_val. Z.div_mod_to_equations. lia. }
  assert (AGw : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 8256 <= a < bv_unsigned sp) -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros a Ha NW. apply AGo; [exact Ha|]. try (generalize alloc_ceiling_val); clear - NW; try pose proof alloc_ceiling_val. lia. }
  (* [comment removed for export] *)
  destruct (Classical_Prop.classic (inplace_ok n (E - p) (m_sizeclass mr))) as [IP|NIP].
  { (* [comment removed for export] *)
    (first [ dand3 IP as IP1 IP2 IP3 | destruct IP as (IP1 & IP2 & IP3) ]).
    eapply rz_evt; [| exact Hh| exact Hl|].
    { eapply realloc_decide_inplace; [exact HN| exact AVR| exact SC64| split; [exact IP1| split; [exact IP2| exact IP3]]| exact MI1]. }
    (intros ms4; (first [ intro dR_13; dand7 dR_13 as t1z t2z t3z a4z a5z a7z -> | intros (t1z & t2z & t3z & a4z & a5z & a7z & ->) ])).
    assert (RS31 : E - p - n < 2^31).
    { pose proof (RF_m8yt.size_to_class_props n ltac:(try (generalize alloc_ceiling_val); clear - NR IP2; try pose proof alloc_ceiling_val; lia)) as (SCR & _).
      pose proof (stride_small s LB m1 st b off g bm i r ar q res HWT Hb ltac:(rewrite Eaddr; exact HA) ltac:(rewrite Esize; exact RB) ltac:(cbv delta [mr stride] in IP3, BSC; try (generalize alloc_ceiling_val); clear - IP3 SCR BSC; try pose proof alloc_ceiling_val; lia)) as SS.
      fold mr stride in SS. subst E. rewrite HA. try (generalize alloc_ceiling_val); clear - SS NR HOFF IP1; try pose proof alloc_ceiling_val. unfold UNIT in *. lia. }
    assert (WR3 : wr_at rsegs m1 (p - 3) (E - p + 3)).
    { eapply wr_at_sub; [exact (rb_wr _ _ _ _ _ _ _ _ _ _ _ _ RB)| |]; subst E; rewrite HA.
      - try (generalize alloc_ceiling_val); clear - EC B0 SI0 HOFF; try pose proof alloc_ceiling_val. unfold UNIT in *. lia.
      - pose proof SPAN as SP2. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. try (generalize alloc_ceiling_val); clear - SP2 SIL EC B0 SI0 HOFF S16; try pose proof alloc_ceiling_val. unfold UNIT in *. lia. }
    assert (RD3 : bytes_at rsegs m1 (p - 3) [b8 b3]).
    { replace (p - 3) with (r_base r + snd c + UNIT * off - 3) by (rewrite HA; clear; lia). exact (rb_rd3 _ _ _ _ _ _ _ _ _ _ _ _ RB). }
    (* [comment removed for export] *)
    eapply rz_evt; [| exact Hh| exact Hl|].
    { eapply (realloc_inplace_walk ra _ gp tp t1z t2z s0 _ a0 a1 _ _ a4z a5z a7z _ s3 s4 s5 s6 s7 s8 s9 s10 s11 t3z t4y t5 t6 _ _ m1 ra s0 s1 s2 s3 s4 s5 s6 p E n b3);
        [rewrite A0; apply unsigned_lit; try (generalize alloc_ceiling_val); clear - P4096 PC ACV OLD0; try pose proof alloc_ceiling_val; lia| exact HN| try (generalize alloc_ceiling_val); clear - NR; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - P4096; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - IP1; try pose proof alloc_ceiling_val; lia
        | exact RS31| exact EHI| rewrite unsigned_lit by exact SP64; try (generalize alloc_ceiling_val); clear - ETOP RC CEIL ACV SPR; try pose proof alloc_ceiling_val; lia
        | rewrite unsigned_lit by exact SP64; try (generalize alloc_ceiling_val); clear - SPR; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - B3R; try pose proof alloc_ceiling_val; lia| exact MI1| exact WR3| exact RD3| rewrite unsigned_lit by exact SP64; exact FR1]. }
    (intros ms5; (first [ intro dR_14; dex6 dR_14 as w0 w1 w2 x1 x2 m'; dand4 dR_14 as -> Em' MI' FR' | intro dR_14; dand10 dR_14 as w0 w1 w2 x1 x2 m' -> Em' MI' FR' | intros (w0 & w1 & w2 & x1 & x2 & m' & -> & Em' & MI' & FR') ])).
    rewrite unsigned_lit in FR' by exact SP64. rewrite unsigned_lit by exact SP64. unfold MRep.wz. rewrite ESP, RET, <- mkst_MS'. rewrite A0.
    pose proof (inplace_model (Clg:=Clg) s LB m1 md b st off g bm i r ar q res n AI1 Hb HWT ltac:(rewrite Eaddr; exact HA) ltac:(rewrite Esize; exact RB)) as AIP.
    cbv zeta in AIP. rewrite ?Eaddr, ?Esize in AIP.
    specialize (AIP ltac:(try (generalize alloc_ceiling_val); clear - NR; try pose proof alloc_ceiling_val; lia) ltac:(subst E; cbv delta [c stride mr] in IP1 |- *; try (generalize alloc_ceiling_val); clear - IP1; try pose proof alloc_ceiling_val; unfold IB; lia) IP2 IP3).
    assert (Em2 : m' = set_size_mem m1 p (r_base r + snd (blk_slot b) + get_stride (get_meta_rec st g) - IB) n (i + 32 * Z.min res 5)).
    { rewrite Em'. subst E b3. cbv delta [c stride mr]. unfold IB. reflexivity. }
    rewrite <- Em2 in AIP.
    apply (K w0 w1 w2 x1 x2 (Z_to_bv 64 (m_sizeclass mr)) a4z a5z (Z_to_bv 64 (E + 4)) a7z t3z t4y t5 t6 p (mkIAS s (lb_resize b n LB) Rr) m' md AIP MI' (md_frame_refl md Hl Hh)).
    split; [exact PNZ|]. split; [rewrite <- Eaddr; apply (p0_live_resize_self s s LB m1 b n HP1 Hb)|]. split; [left; reflexivity|]. split.
    { intros qq Hq _. rewrite <- Eaddr in Hq. exact (p0_live_resize_other s s LB m1 b n qq HP1 Hb Hq). }
    assert (P3 : 0 <= p - 3) by (try (generalize alloc_ceiling_val); clear - P4096; try pose proof alloc_ceiling_val; lia).
    assert (E1 : E + 1 <= 2^64) by (try (generalize alloc_ceiling_val); clear - EHI; try pose proof alloc_ceiling_val; lia).
    assert (N0 : 0 <= n) by (try (generalize alloc_ceiling_val); clear - NR; try pose proof alloc_ceiling_val; lia).
    assert (OUTm' : forall a, 0 <= a < 2^64 -> a <> p - 3 -> ~ (p + n <= a <= E) -> m' (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)).
    { intros a Ha N1 N2. rewrite Em'. apply set_size_mem_outside; rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - Ha; try pose proof alloc_ceiling_val; lia); auto. try (generalize alloc_ceiling_val); clear - IP1; try pose proof alloc_ceiling_val; lia. }
    assert (MONOm' : forall a, 0 <= a < 2^64 -> m1 (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None).
    { intros a Ha Hm. rewrite Em'. apply set_size_mem_mono; auto. try (generalize alloc_ceiling_val); clear - IP1; try pose proof alloc_ceiling_val; lia. }
    split.
    { intros i0 Hi0. unfold MRep.wz. rewrite OUTm' by (try (generalize alloc_ceiling_val); clear - Hi0 P4096 PC ACV IP1 ELO EHI; try pose proof alloc_ceiling_val; lia). apply AG1. try (generalize alloc_ceiling_val); clear - Hi0 PC P4096 ACV CEIL OLD0; try pose proof alloc_ceiling_val. lia. }
    (* [comment removed for export] *)
    assert (DLT : lb_bytes (lb_resize b n LB) = lb_bytes LB + n - old /\ zlen (lb_resize b n LB) = zlen LB).
    { unfold lb_resize.
      destruct (lb_bytes_map_one (fun x : block => if aptr_eqb (blk_slot x) (blk_slot b) then (blk_id x, blk_addr x, n) else x) b LB
                  (heap_ids_nodup s LB m1 HP1) Hb) as [D1 D2].
      - intros x Hx NEx. destruct (MI_Kit.aptr_eqb_spec (blk_slot x) (blk_slot b)) as [ES|NS]; [| reflexivity].
        exfalso. apply NEx. exact (heap_slot_inj s LB m1 x b HP1 Hx Hb ES).
      - rewrite D1, D2. rewrite aptr_eqb_refl. cbn [blk_size snd]. rewrite Esize. split; [lia| reflexivity]. }
    split; [unfold p0_livebytes; cbn [ia_LB]; exact (proj1 DLT)|]. split; [unfold p0_nlive; cbn [ia_LB]; exact (proj2 DLT)|].
    (* [comment removed for export] *)
    assert (SLOTZ : forall a, p - 4 <= a <= E -> heap_zone LayoutP0 a).
    { intros a Ha. apply heap_zone_p0. subst E. rewrite HA in Ha. pose proof SPAN as SP2. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL.
      try (generalize alloc_ceiling_val); clear - Ha SP2 SIL RC RI R0 EC B0 SI0 HOFF S16 ACV; try pose proof alloc_ceiling_val. unfold UNIT in *. lia. }
    assert (PRIV : forall y, In y LB -> y <> b -> blk_addr y + blk_size y <= p - 4 \/ E < blk_addr y).
    { intros y Hy NE. destruct (slot_private s LB m1 st b off g bm i r ar q res y HWT Hb ltac:(rewrite Eaddr; exact HA) ltac:(rewrite Esize; exact RB) Hy NE) as [X|X];
        fold c mr stride in X; [left| right; subst E; try (generalize alloc_ceiling_val); clear - X; try pose proof alloc_ceiling_val; unfold IB in X; lia].
      rewrite HA. try (generalize alloc_ceiling_val); clear - X HOFF; try pose proof alloc_ceiling_val. unfold UNIT, IB in *. lia. }
    assert (INB' : forall a, in_block (lb_resize b n LB) a <-> (p <= a < p + n) \/ (exists y, In y LB /\ y <> b /\ blk_addr y <= a < blk_addr y + blk_size y)).
    { intros a. rewrite <- Eaddr. apply (in_block_resize s LB m1 b n a HP1 Hb). }
    assert (INB : forall a, in_block LB a <-> (p <= a < p + old) \/ (exists y, In y LB /\ y <> b /\ blk_addr y <= a < blk_addr y + blk_size y)).
    { intros a. split.
      - ((first [ intro dR_15; dex1 dR_15 as y; destruct dR_15 as [Hy Ha] | intro dR_15; dand3 dR_15 as y Hy Ha | intros (y & Hy & Ha) ])). destruct (Classical_Prop.classic (y = b)) as [->|NE]; [left; rewrite <- Eaddr, <- Esize; exact Ha| right; exists y; auto].
      - intros [Ha|(y & Hy & NE & Ha)]; [exists b; rewrite Eaddr, Esize; auto| exists y; auto]. }
    cbn [ia_LB]. unfold p0_owned. cbn [ia_LB].
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - intros a Ha NO NO' NW NE NV NN. unfold MRep.wz. rewrite OUTm'; [apply AGw; [exact Ha| exact NW]| exact Ha| |].
      + intros Ea. apply NO'. right. split; [apply SLOTZ; try (generalize alloc_ceiling_val); clear - Ea ELO; try pose proof alloc_ceiling_val; lia|]. rewrite INB'. intros [X|(y & Hy & NEy & X)]; [try (generalize alloc_ceiling_val); clear - X Ea N0; try pose proof alloc_ceiling_val; lia|].
        destruct (PRIV y Hy NEy); try (generalize alloc_ceiling_val); clear - X Ea H ELO; try pose proof alloc_ceiling_val; lia.
      + intros Ra. apply NO'. right. split; [apply SLOTZ; try (generalize alloc_ceiling_val); clear - Ra N0 P4096; try pose proof alloc_ceiling_val; lia|]. rewrite INB'. intros [X|(y & Hy & NEy & X)]; [try (generalize alloc_ceiling_val); clear - X Ra; try pose proof alloc_ceiling_val; lia|].
        destruct (PRIV y Hy NEy); try (generalize alloc_ceiling_val); clear - X Ra H N0 P4096; try pose proof alloc_ceiling_val; lia.
    - intros a Ha NI Hm. right. right. unfold MRep.wz. apply MONOm'; [exact Ha|]. apply MONO1; [exact Ha| exact Hm].
    - intros i0 Hi0. unfold MRep.wz. apply MONOm'; [try (generalize alloc_ceiling_val); clear - Hi0 SPR CEIL ACV; try pose proof alloc_ceiling_val; lia|].
      destruct (Z_lt_le_dec (bv_unsigned sp - 8256 + i0) (bv_unsigned sp - 64)).
      + rewrite AG1 by (try (generalize alloc_ceiling_val); clear - Hi0 l SPR CEIL ACV; try pose proof alloc_ceiling_val; lia). replace (bv_unsigned sp - 8256 + i0) with (lo + i0) by (clear; subst lo; lia). apply MAP. try (generalize alloc_ceiling_val); clear - Hi0; try pose proof alloc_ceiling_val; lia.
      + destruct FR1 as [_ (_ & _ & W)]. cbn [cells_size csize Nat.add] in W. rewrite ?unsigned_lit in W by lia.
        specialize (W (bv_unsigned sp - 8256 + i0 - (bv_unsigned sp - 64)) ltac:(try (generalize alloc_ceiling_val); clear - Hi0 l; try pose proof alloc_ceiling_val; lia)).
        replace (bv_unsigned sp - 64 + (bv_unsigned sp - 8256 + i0 - (bv_unsigned sp - 64))) with (bv_unsigned sp - 8256 + i0) in W by (clear; lia).
        rewrite p0_wview_overlay in W by (unfold wa; rewrite unsigned_lit; try (generalize alloc_ceiling_val); clear - Hi0 l SPR CEIL ACV; try pose proof alloc_ceiling_val; lia). exact W.
    - intros a Ha [_ Hn]. destruct (Z_lt_le_dec a (p + old)) as [LT|GE]; [right; left; split; [exact PNZ| try (generalize alloc_ceiling_val); clear - Hn LT; try pose proof alloc_ceiling_val; lia]|].
      left. right. split; [apply SLOTZ; try (generalize alloc_ceiling_val); clear - Hn GE IP1 OLD0; try pose proof alloc_ceiling_val; lia|]. rewrite INB. intros [X|(y & Hy & NEy & X)]; [try (generalize alloc_ceiling_val); clear - X GE; try pose proof alloc_ceiling_val; lia|].
      destruct (PRIV y Hy NEy); try (generalize alloc_ceiling_val); clear - X Hn GE H IP1 OLD0; try pose proof alloc_ceiling_val; lia.
    - intros a Ha [St|[HZ NI']]; [left; left; exact St|].
      destruct (Classical_Prop.classic (in_block LB a)) as [IN|NIN]; [| left; right; split; [exact HZ| exact NIN]].
      rewrite INB in IN. destruct IN as [X|(y & Hy & NEy & X)].
      + right. left. split; [exact PNZ| exact X].
      + exfalso. apply NI'. rewrite INB'. right. exists y. auto.
    - intros a Ha [St|[HZ NI]] NO'.
      + exfalso. apply NO'. left. exact St.
      + left. destruct (Classical_Prop.classic (in_block (lb_resize b n LB) a)) as [IN|NIN]; [| exfalso; apply NO'; right; split; [exact HZ| exact NIN]].
        rewrite INB' in IN. destruct IN as [X|(y & Hy & NEy & X)]; [split; [exact PNZ| exact X]|].
        exfalso. apply NI. rewrite INB. right. exists y. auto.
    - intros a Ha [_ Hv]. destruct (Z_lt_le_dec a (p + n)) as [LT|GE]; [right; left; split; [exact PNZ| try (generalize alloc_ceiling_val); clear - Hv LT; try pose proof alloc_ceiling_val; lia]|].
      left. right. split; [apply SLOTZ; try (generalize alloc_ceiling_val); clear - Hv GE ELO OLD0 P4096 N0 ERES2 RES0; try pose proof alloc_ceiling_val; lia|]. rewrite INB'. intros [X|(y & Hy & NEy & X)]; [try (generalize alloc_ceiling_val); clear - X GE; try pose proof alloc_ceiling_val; lia|].
      destruct (PRIV y Hy NEy); try (generalize alloc_ceiling_val); clear - X Hv GE H ELO ERES2 RES0; try pose proof alloc_ceiling_val; lia. }
  destruct (Classical_Prop.classic (MMAP_THRESHOLD <= n /\ 48 <= m_sizeclass mr)) as [MMc|NMM].
  { (* [comment removed for export] *)
    destruct MMc as [NT SC48x]. assert (SC63 : m_sizeclass mr = 63) by (cbv delta [mr stride] in BSC, SC48x |- *; try (generalize alloc_ceiling_val); clear - BSC SC48x; try pose proof alloc_ceiling_val; lia).
    eapply rz_evt; [| exact Hh| exact Hl|].
    { eapply realloc_decide_mremap; [exact HN| exact NT| exact SC63]. }
    (intros ms4; (first [ intro dR_16; dand4 dR_16 as t2z t3z a5z -> | intros (t2z & t3z & a5z & ->) ])).
    eapply (mremap_path_rz ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4y t5 t6
              m m1 md s LB b p n old T st off g bm i r ar q res t2z a5z t3z);
      try eassumption; try reflexivity. }
  (* [comment removed for export] *)
  eapply rz_evt; [| exact Hh| exact Hl|].
  { eapply realloc_decide_fallback; [exact HN| exact AVR| exact SC64| exact NIP| exact NMM| exact MI1]. }
  (intros ms4; (first [ intro dR_17; dand8 dR_17 as t1z t2z t3z a2z a4z a5z a7z -> | intros (t1z & t2z & t3z & a2z & a4z & a5z & a7z & ->) ])).
  rewrite A0.
  apply (realloc_fallback_cps ra _ gp tp (wz E) t1z t2z s0 (Z_to_bv 64 (conc st g)) a1 a2z (Z_to_bv 64 (m_sizeclass mr)) a4z a5z (wz (E + 4)) a7z
           s3 s4 s5 s6 s7 s8 s9 s10 s11 t3z t4y t5 t6 ra s0 s1 s2 s3 s4 s5 s6 m1 md (mkIAS s LB Rr) p n old T AI1 MI1 LV PNZ HN NR BYTES NLV TP);
    [rewrite unsigned_lit by exact SP64; try (generalize alloc_ceiling_val); clear - SPA SPR; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia| exact RAA| rewrite unsigned_lit by exact SP64; try (generalize alloc_ceiling_val); clear - CEIL; try pose proof alloc_ceiling_val; lia
    | rewrite unsigned_lit by exact SP64; try (generalize alloc_ceiling_val); clear - SPR; try pose proof alloc_ceiling_val; lia| rewrite unsigned_lit by exact SP64; exact MAP1| rewrite unsigned_lit by exact SP64; exact FR1|].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' rr A' m' md' AI' MI' FRd' RES'.
  rewrite unsigned_lit in RES' by exact SP64. rewrite unsigned_lit by exact SP64. rewrite ESP.
  apply (K t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' rr A' m' md' AI' MI' FRd').
  replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) in RES' by lia.
  destruct RES' as (Rnz & LVr & LD & LQ & PRE & DB & DN & FRM').
  split; [exact Rnz|]. split; [exact LVr|]. split; [right; exact LD|]. split; [exact LQ|]. split.
  + intros ii Hii. rewrite (PRE ii Hii). unfold MRep.wz. apply AG1. try (generalize alloc_ceiling_val); clear - Hii PC P4096 ACV CEIL; try pose proof alloc_ceiling_val. lia.
  + split; [exact DB|]. split; [exact DN|]. exact (frame_ok_pre_agree _ _ _ _ _ _ m m1 m' AGw MONO1 FRM').
Qed.
End REALLOC.

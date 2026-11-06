(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep
     ECH_LibState ECH_LibFrame ECH_Rostr ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C1_realloc ECH_C3_stmt ECH_C4_stmt ECH_C4_frame ECH_C4_frame2 ECH_C4_raise ECH_C4
     ECH_C6_stmt ECH_C7_stmt ECH_C7_rd ECH_C7_rd2 ECH_C13_stmt ECH_C14_stmt ECH_KitSeg ECH_LibMid ECH_C14_bio2buf ECH_C14_ladder ECH_C14_ladloop ECH_C14_tail.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition LD_RF2 : Z := 0x26c634.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section K.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma xpres_drop_memflag : forall LB SP X m m',
    xpres LB SP (memflag_foot ++ X) m m' -> MEMFLAG m 1 -> MEMFLAG m' 1 -> xpres LB SP X m m'.
  Proof.
    intros LB SP X m m' XP F0 F1 a Ha [HC HX].
    destruct (Z.eq_dec a A_mem_inited) as [->|NE]; [apply memflag_same; assumption|].
    apply XP; [exact Ha|]. split; [exact HC|]. intros K. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (HX K)].
    unfold memflag_foot in K. cbn [rin_ivs fst snd] in K. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_raise_sp : forall LB SP SP' c X m m',
    xpres LB SP ((c, c + 8) :: X) m m' -> SP <= SP' -> c + 8 <= SP' -> IMG_HI <= c ->
    (forall b, In b LB -> blk_addr b + blk_size b <= c) -> xpres LB SP' X m m'.
  Proof.
    intros LB SP SP' c X m m' XP LE CB CI BEL a Ha [HC HX]. apply XP; [exact Ha|]. split.
    - destruct HC as [HC|[HC|(b & Hb & Hr)]]; [left; lia| right; left; exact HC| right; right; exists b; split; assumption].
    - cbn [rin_ivs fst snd]. intros [K|K]; [| exact (HX K)].
      destruct HC as [HC|[[[HC1 HC2] _]|(b & Hb & Hr)]]; [lia| unfold IMG_HI in CI; lia|]. pose proof (BEL b Hb). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma MEMBIO_frameI : forall L L' SP X m m' a R,
    MEMBIO L m a R -> (forall b, In b (blocks_MEMBIO a R) -> In b L') -> xpres L' SP X m m' ->
    Forall (fun iv : Z * Z => IMG_LO <= fst iv /\ snd iv <= IMG_HI) X -> MEMBIO L' m' a R.
  Proof.
    intros L L' SP X m m' a R MB KEEP XP FX. unfold MEMBIO in *.
    destruct MB as (C1 & C2 & C3 & C4 & I1 & I2 & I3 & I4 & RB1 & RB2 & RB3 & RB4 & REST).
    assert (K1 : In (mb_id R, a, BIO_SIZE) L') by (apply KEEP; left; reflexivity).
    assert (K2 : In (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE) L') by (apply KEEP; right; left; reflexivity).
    assert (K3 : In (mb_bmid R, mb_bm R, BUFMEM_SIZE) L') by (apply KEEP; right; right; left; reflexivity).
    assert (K4 : In (mb_rpid R, mb_rp R, BUFMEM_SIZE) L') by (apply KEEP; right; right; right; left; reflexivity).
    pose proof RB1 as (_ & _ & _ & _ & O1). pose proof RB2 as (_ & _ & _ & _ & O2). pose proof RB3 as (_ & _ & _ & _ & O3). pose proof RB4 as (_ & _ & _ & _ & O4).
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
    repeat match goal with |- _ /\ _ => split end; try assumption; try apply REST.
    - eapply xpres_rw_cells'; [exact XP| exact C1| | apply avoid_of_img; [exact FX| unfold bio_cells; cbn [cells_size csize Nat.add length]; unfold IMG_LO, IMG_HI; lia]].
      right; right. exists (mb_id R, a, 128). split; [exact K1|]. unfold bio_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. lia.
    - eapply xpres_rw_cells'; [exact XP| exact C2| | apply avoid_of_img; [exact FX| cbn [cells_size csize Nat.add length]; unfold IMG_LO, IMG_HI; lia]].
      right; right. exists (mb_bbid R, mb_bb R, 16). split; [exact K2|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. lia.
    - eapply xpres_rw_cells'; [exact XP| exact C3| | apply avoid_of_img; [exact FX| unfold buf_cells; cbn [cells_size csize Nat.add length]; unfold IMG_LO, IMG_HI; lia]].
      right; right. exists (mb_bmid R, mb_bm R, 32). split; [exact K3|]. unfold buf_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. lia.
    - eapply xpres_rw_cells'; [exact XP| exact C4| | apply avoid_of_img; [exact FX| unfold buf_cells; cbn [cells_size csize Nat.add length]; unfold IMG_LO, IMG_HI; lia]].
      right; right. exists (mb_rpid R, mb_rp R, 32). split; [exact K4|]. unfold buf_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma MEMBIO_frameA : forall L L' SP X m m' a R,
    MEMBIO L m a R -> (forall b, In b (blocks_MEMBIO a R) -> In b L') -> xpres L' SP X m m' ->
    Forall (fun iv : Z * Z => Forall (fun b => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) (blocks_MEMBIO a R)) X ->
    MEMBIO L' m' a R.
  Proof.
    intros L L' SP X m m' a R MB KEEP XP FX. unfold MEMBIO in *.
    destruct MB as (C1 & C2 & C3 & C4 & I1 & I2 & I3 & I4 & RB1 & RB2 & RB3 & RB4 & REST).
    assert (K1 : In (mb_id R, a, BIO_SIZE) L') by (apply KEEP; left; reflexivity).
    assert (K2 : In (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE) L') by (apply KEEP; right; left; reflexivity).
    assert (K3 : In (mb_bmid R, mb_bm R, BUFMEM_SIZE) L') by (apply KEEP; right; right; left; reflexivity).
    assert (K4 : In (mb_rpid R, mb_rp R, BUFMEM_SIZE) L') by (apply KEEP; right; right; right; left; reflexivity).
    assert (FXi : forall i (b : block), nth_error (blocks_MEMBIO a R) i = Some b ->
              Forall (fun iv : Z * Z => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) X).
    { intros i b Hi. eapply Forall_impl; [| exact FX]. cbn beta. intros iv Fb. exact (proj1 (Forall_forall _ _) Fb b (nth_error_In _ _ Hi)). }
    pose proof (FXi 0%nat _ eq_refl) as F1. pose proof (FXi 1%nat _ eq_refl) as F2. pose proof (FXi 2%nat _ eq_refl) as F3. pose proof (FXi 3%nat _ eq_refl) as F4.
    cbn [blk_addr blk_size fst snd] in F1, F2, F3, F4. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
    repeat match goal with |- _ /\ _ => split end; try assumption; try apply REST.
    - eapply xpres_rw_cells'; [exact XP| exact C1| | unfold bio_cells; cbn [cells_size csize Nat.add length]; exact F1].
      right; right. exists (mb_id R, a, 128). split; [exact K1|]. unfold bio_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. lia.
    - eapply xpres_rw_cells'; [exact XP| exact C2| | cbn [cells_size csize Nat.add length]; exact F2].
      right; right. exists (mb_bbid R, mb_bb R, 16). split; [exact K2|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. lia.
    - eapply xpres_rw_cells'; [exact XP| exact C3| | unfold buf_cells; cbn [cells_size csize Nat.add length]; exact F3].
      right; right. exists (mb_bmid R, mb_bm R, 32). split; [exact K3|]. unfold buf_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. lia.
    - eapply xpres_rw_cells'; [exact XP| exact C4| | unfold buf_cells; cbn [cells_size csize Nat.add length]; exact F4].
      right; right. exists (mb_rpid R, mb_rp R, 32). split; [exact K4|]. unfold buf_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. lia.
  Qed.

  Lemma ctxph_nonneg3 : forall ph, 0 <= ctxph_bytes ph /\ 0 <= ctxph_cnt ph /\ 0 <= ctxph_big ph.
  Proof. intros [|?]; cbn [ctxph_bytes ctxph_cnt ctxph_big]; unfold CTXINIT_BYTES, CTXINIT_CNT, CTXINIT_BIG; lia. Qed.

  Lemma mid_eta : forall M, M = mkMID (mid_flag M) (mid_ctx M) (mid_err M) (mid_E M) (mid_vdso M).
  Proof. intros [f c e E v]; reflexivity. Qed.

  Lemma store_empty_eq : forall S, es_entries S = 0 -> es_entries_o S = None -> S = store_empty (es_id S).
  Proof. intros [e eo id] E1 E2. cbn in *. subst. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma rp_segF :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv rsegs m ->
      evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 RP_595_R1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom rsegs))
        (MS (mkR (Z_to_bv 64 LD_RF) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 LD_RF)) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros MI.
    replace (ret_pc (Z_to_bv 64 LD_RF)) with (Z_to_bv 64 LD_RF) by (symmetry; apply ret_pc_even; [unfold LD_RF; lia| reflexivity]).
    unfold LD_RF, RP_595_R1, P_ERR_new. step. step. apply evt_done. reflexivity.
  Qed.
End K.

(* [comment removed for export] *)
Section RC.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Hypothesis CERTO3 : egs_fresh_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let HRE : realloc_sr_stmt H := proj1 (proj2 HX).

  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LIB LB : list block)
            (M : libmid) (x : ctxinfo) (st mb lo B : Z) (S : storerep) (R : membio) (ds : list byte) (errv : word).
  Hypotheses (A0 : a0 = Z_to_bv 64 st) (A1 : a1 = Z_to_bv 64 mb)
             (SO : STOREobj LB m st S) (SE : es_entries S = 0) (SEO : es_entries_o S = None) (STL : st + STORE_SIZE <= lo)
             (MBO : MEMBIO LB m mb R) (MP0 : mb_pos R = 0) (MN0 : mb_nread R = 0) (MBB : MEMBIO_below mb R lo) (MBS : MEMBIO_sep mb R)
             (DS : bytes_at rsegs m (mb_buf R) ds) (DSL : zlength ds = mb_len R)
             (PAYL : 1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB /\ forall b, In b LIB -> blk_id b <> pD)
             (NDsm : List.NoDup (map blk_id ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R)))
             (LM : LIBMID LIB m M) (SUBL : forall b, In b LIB -> In b LB) (CTX : mid_ctx M = CtxReady x) (MF1 : mid_flag M = 1)
             (DJ6 : forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id b <> blk_id b')
             (HP : hs_RHEAP H s (mid_errblocks M ++ LB) m) (KREL : hs_KREL H s mo)
             (BUD : lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + DECODE_BYTES + ERRSTR_BYTES <= hs_LIVE_MAX H)
             (BUDC : Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + DECODE_CNT + ERRSTR_CNT <= hs_LIVE_CNT_MAX H)
             (BUDG : lb_big (mid_errblocks M ++ LB) + mid_big M + DECODE_BIG <= hs_LIVE_BIG_MAX H)
             (AUX : hs_rauxv_ok H m B) (SPB : bv_unsigned sp <= B) (BHI : B < 2^64) (SPA : bv_unsigned sp mod 16 = 0)
             (ST : stk rsegs m lo (bv_unsigned sp)) (CEIL : hceil <= lo) (LO : lo <= bv_unsigned sp - READCFG_STACK M)
             (ERR : rw_cells rsegs m (errno_addr tp) [C4 errv]) (MI : mem_inv rsegs m) (TP : tp = Z_to_bv 64 RATP) (RAE : bv_unsigned ra mod 2 = 0).

  (* [comment removed for export] *)
  Definition E0 : list block := mid_errblocks M.
  Definition L0 : list block := mid_errblocks M ++ LB.
  Definition SP' : Z := bv_unsigned sp + -2352.
  Definition RBP : Z := bv_unsigned sp + -2240.
  Definition POST : config -> Prop := readcfg_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LIB LB M st S mb R ds lo B m mo.
  (* [comment removed for export] *)
  Definition XF : list (Z * Z) := [(st, st + STORE_SIZE)] ++ MEMBIO_foot mb R ++ ERR_X ++ VDSO_X ++ errph_foot (mid_err M).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SAVES : list cell := rp_saves s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

  Local Ltac img_static := unfold RERRNO, A_malloc_impl, A_got_CRYPTO_malloc, A_mem_buf_method, O_METH_BREAD, A_mem_inited; cbn; lia.

  (* [comment removed for export] *)
  Lemma rc_facts :
       S = store_empty (es_id S) /\ In (es_id S, st, STORE_SIZE) L0 /\ rblock_range st STORE_SIZE
    /\ (forall b, In b L0 -> blk_addr b + blk_size b <= hceil) /\ (forall b, In b LB -> In b L0)
    /\ List.NoDup (map blk_id L0) /\ 11136 <= READCFG_STACK M /\ 0 <= lo /\ MEMFLAG m 1
    /\ (forall b', In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> In b' L0)
    /\ (forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) ->
          blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b).
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX.
    assert (SUB0 : forall b, In b LB -> In b L0) by (intros b Hb; unfold L0; apply in_or_app; right; exact Hb).
    pose proof SO as (SC & SIN & _).
    assert (OBJ : forall b', In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> In b' L0).
    { intros b' Hb'. apply SUB0. destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _). unfold blocks_MEMBIO in Hb'.
      destruct Hb' as [<-|[<-|[<-|[<-|[<-|[]]]]]]; assumption. }
    repeat match goal with |- _ /\ _ => split end.
    - exact (store_empty_eq S SE SEO).
    - apply SUB0. exact SIN.
    - exact (HH_RHEAP_block_range H HH _ _ _ _ HP (SUB0 _ SIN)).
    - intros b Hb. exact (HH_blocks_below H HH _ _ _ HP b Hb).
    - exact SUB0.
    - exact (HH_RHEAP_blocks_nodup H HH _ _ _ HP).
    - apply readcfg_stack_lo.
    - destruct ST as [? _]; assumption.
    - destruct LM as (_ & MF & _). rewrite MF1 in MF. exact MF.
    - exact OBJ.
    - intros b b' Hb Hb'. exact (HH_RHEAP_blocks_disjoint H HH _ _ _ b b' HP (SUB0 _ (SUBL _ Hb)) (OBJ _ Hb') (DJ6 _ _ Hb Hb')).
  Qed.

  (* [comment removed for export] *)
  Lemma errph_foot_apart : forall b', In b' L0 -> (forall b, In b LIB -> blk_id b <> blk_id b') ->
    Forall (fun iv : Z * Z => blk_addr b' + blk_size b' <= fst iv \/ snd iv <= blk_addr b') (errph_foot (mid_err M)).
  Proof using LM SUBL CTX HP HH HX.
    intros b' Hb' NE. destruct LM as (_ & _ & _ & EPm & _). rewrite CTX in EPm. cbn [ERRPH_mid] in EPm.
    destruct (mid_err M) as [|c]; cbn [errph_foot]; [apply Forall_nil|]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
    cbn [ERRPH] in EPm. destruct EPm as [_ CH]. pose proof CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ (ec_es c) b' HP ltac:(unfold L0; apply in_or_app; right; exact (SUBL _ I5)) Hb' (NE _ I5)) as D.
    rewrite Z5 in D. unfold ERRST_SIZE in *. clear - D. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rc_stack_gen : forall cph eph,
       RAISE_STACK eph + 2352 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 512 + Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) RREALLOC_STACK
    /\ LAD_STACK + 2352 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 512 + Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) RREALLOC_STACK
    /\ CZALLOC_STACK + 2352 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 512 + Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) RREALLOC_STACK.
  Proof. clear. intros [|?] [|?]; repeat split; vm_compute; discriminate. Qed.
  Lemma rc_stack : RAISE_STACK (mid_err M) + 2352 <= READCFG_STACK M /\ LAD_STACK + 2352 <= READCFG_STACK M /\ CZALLOC_STACK + 2352 <= READCFG_STACK M.
  Proof. clear. unfold READCFG_STACK, mid_stack. apply rc_stack_gen. Qed.


  (* [comment removed for export] *)
  Lemma rp_post_S0 : forall m' mo' (s' : PState) (rv : Z) (M' : libmid) (R' : membio) (LE : list block)
      (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 errv' : word),
    (rv = 0 \/ rv = 1) -> hs_KREL H s' mo' -> hs_MPRES H mo mo' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
    rw_cells rsegs m' RERRNO [C4 errv'] -> hs_rauxv_ok H m' B ->
    hs_RHEAP H s' (mid_errblocks M' ++ LE ++ LB) m' -> LIBMID (LE ++ LIB) m' M' -> mid_step M M' -> mid_newlib_ok M M' LE -> mid_ctx M' = mid_ctx M ->
    Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M') <= ERRSTR_BYTES -> lb_big (mid_errblocks M') = 0 ->
    MEMBIO LB m' mb R' -> mb_static R R' -> bytes_at rsegs m' (mb_buf R) ds -> rw_cells rsegs m' st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    xpres LB (bv_unsigned sp) XF m m' ->
    hs_SR H POST (mkCfg (MS (mkR ra sp gp (Z_to_bv 64 RATP) u0 u1 u2 s0 s1 (Z_to_bv 64 rv) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                             F (ret_pc ra) fc None m' (seg_rom rsegs)) mo').
  Proof using SO SE SEO TP HH.
    intros m' mo' s' rv M' R' LE u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 errv' RV KREL' MP' MI' ST' ERR' AUX' HP' LM' STEP' NEW' CTX' EC' EB' EG' MBO' MST' DS' SC' XP'.
    pose proof SO as (_ & SINB & _).
    apply (sr_done H HH). unfold POST, readcfg_post. cbn [cfg_ms cfg_model]. rewrite TP, errno_RATP.
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', errv', s', rv, M', S, R', LE, [].
    cbv zeta. cbn [app].
    split; [reflexivity|]. split; [exact RV|]. split; [exact KREL'|]. split; [exact MP'|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|]. split; [exact HP'|].
    split; [exact LM'|]. split; [exact STEP'|]. split; [exact NEW'|]. split; [exact CTX'|].
    split; [unfold STOREobj, ENTRIES; rewrite SE, SEO; split; [exact SC'| split; [apply in_or_app; right; exact SINB| reflexivity]]|].
    split; [reflexivity|]. split; [unfold blocks_STORE; rewrite SEO; apply Permutation_refl|].
    split; [cbn; unfold DECODE_CNT; clear; lia|]. split; [cbn; unfold DECODE_BYTES; clear; lia|]. split; [cbn; unfold DECODE_BIG; clear; lia|].
    split; [exact EC'|]. split; [exact EB'|]. split; [exact EG'|].
    split; [unfold blocks_STORE; rewrite SEO; cbn; constructor; [intros []| constructor]|].
    split; [eapply MEMBIO_mono; [exact MBO'| intros b Hb; apply in_or_app; right; exact Hb]|].
    split; [exact (mb_static_blocks mb R R' MST')|]. split; [exact DS'| exact XP'].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_fail595 :
    forall m1 mo1 (s1' : PState) (p : bptr) (A n0 rv : Z) (R' : membio) (clo : list cell) (j2 : list byte)
           (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s1v s3v s4v s5v s6v s8v s9v s10v s11v u3 u4 u5 u6 : word),
      hs_RHEAP H s1' ((p, A, n0) :: L0) m1 -> hs_KREL H s1' mo1 -> hs_MPRES H mo mo1 ->
      MEMBIO LB m1 mb R' -> mb_static R R' -> bytes_at rsegs m1 (mb_buf R) ds ->
      cells_size clo = 120%nat -> rw_cells rsegs m1 SP' clo -> rw_cells rsegs m1 (bv_unsigned sp + -2232) (CB 2128 j2 :: SAVES) ->
      (exists errv1, rw_cells rsegs m1 RERRNO [C4 errv1]) -> MEMFLAG m1 1 -> IMPL_mem m1 -> GOT_mem m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo SP' -> hs_rauxv_ok H m1 B ->
      xpres LB (bv_unsigned sp) (MEMBIO_foot mb R) m m1 ->
      hs_SR H POST (mkCfg (MS (mkR (Z_to_bv 64 LD_RC) (Z_to_bv 64 SP') gp (Z_to_bv 64 RATP) u0 u1 u2 sp s1v (Z_to_bv 64 rv) b1 b2 b3 b4 b5 b6 b7
                                    (Z_to_bv 64 mb) s3v s4v s5v s6v (Z_to_bv 64 A) s8v s9v s10v s11v u3 u4 u5 u6)
                               F (ret_pc (Z_to_bv 64 LD_RC)) fc None m1 (seg_rom rsegs)) mo1).
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HRE HX CERTO3.
    intros m1 mo1 s1' p A n0 rv R' clo j2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s1v s3v s4v s5v s6v s8v s9v s10v s11v u3 u4 u5 u6.
    intros HP1 KREL1 MP1 MBO1 MST1 DS1 CLOZ FRlo FRhi [errv1 ERR1] MF IM1 GM1 MI1 ST1 AUX1 XP1.
    destruct rc_facts as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    pose proof rc_stack as (STKR & _ & _).
    hcb. pose proof (word_range sp) as SPR.
    destruct (lad_head_facts H HX L0 _ _ _ _ _ HP1) as (BR & BH & NIP & DISJ & BEL).
    pose proof MST1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
    assert (SUB0' : forall b, In b (blocks_MEMBIO mb R) -> In b LB).
    { intros b Hb. destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _). unfold blocks_MEMBIO in Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption. }
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 LD_RC)) with (Z_to_bv 64 LD_RC) by (symmetry; apply ret_pc_even; [unfold LD_RC; lia| reflexivity]).
    eapply (sr_evt_krel H HH); [exact KREL1| eapply ld_segc2; exact MI1|]. intros ms2 (a0' & -> & _).
    pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := (p, A, n0) :: L0) (s := s1') (p := p) (A := A) (n := n0) (errv := errv1); try reflexivity.
      all: try first [exact HP1| exact KREL1| exact AUX1| exact MI1| exact IM1| exact GM1| exact CEIL].
      all: lazymatch goal with
           | |- In _ _ => left; reflexivity
           | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
           | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST1
           | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); unfold CFREE_STACK, RFREE_STACK; clear - LO STK0; lia
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR1
           end. }
    clear CF. intros [ms3 mo2] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & s2' & -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & HP2 & IM2 & GM2).
    rewrite (proj1 (HH_lb_remove H HH)) in XP2, HP2 by exact NIP.
    unfold SP' in ST2, XP2. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST2, XP2 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR2.
    fold SP' in ST2, XP2.
    (* [comment removed for export] *)
    assert (XPL2 : xpres LB SP' [] m1 m2) by (eapply xpres_weaken; [exact XP2| clear; lia| exact SUB0| intros q Hq; exact Hq]).
    assert (MF2 : MEMFLAG m2 1).
    { destruct MF as (fb & FB & V). exists fb. split; [| exact V]. eapply xpres_rw_cells'; [exact XP2| exact FB| | apply Forall_nil].
      right; left. unfold A_mem_inited, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. clear. lia. }
    assert (XA2 : xpres LB (bv_unsigned sp) (MEMBIO_foot mb R) m m2).
    { eapply xpres_trans; [exact XP1|]. eapply xpres_weaken; [exact XPL2| unfold SP'; clear; lia| intros b Hb; exact Hb| intros q Hq; destruct Hq]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply rp_segF; exact MI2|]. intros ms4 ->.
    assert (LM2 : LIBMID LIB m2 M).
    { pose proof (LIBMID_mf_X LIB LB (bv_unsigned sp) (MEMBIO_foot mb R) m m2 M LM
                    ltac:(eapply xpres_weaken; [exact XA2| clear; lia| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app; right; exact Hq]) SUBL MF2) as K.
      destruct M as [f cph eph E v]. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in K, MF1 |- *. subst f. apply K.
      - intros q Hq. destruct MBO as (_ & _ & _ & _ & _ & _ & _ & _ & XB1 & _ & XB3 & _).
        pose proof XB1 as (_ & _ & _ & _ & O1). pose proof XB3 as (_ & _ & _ & _ & O3).
        unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE, IMG_LO, IMG_HI in *. cbn [rin_ivs fst snd] in Hq. clear - Hq O1 O3. lia.
      - intros q b Hq Hb. unfold MEMBIO_foot in Hq. cbn [rin_ivs fst snd] in Hq.
        pose proof (DJA b (mb_id R, mb, BIO_SIZE) Hb ltac:(right; left; reflexivity)) as D1.
        pose proof (DJA b (mb_bmid R, mb_bm R, BUFMEM_SIZE) Hb ltac:(right; right; right; left; reflexivity)) as D3.
        cbn [blk_addr blk_size fst snd] in D1, D3. clear - Hq D1 D3. lia. }
    pose proof (errph_nonneg (mid_err M)) as (EN1 & EN2 & EN3). pose proof (ctxph_nonneg3 (mid_ctx M)) as (CN1 & CN2 & CN3).
    eapply (rp_raise H HX CERTO3) with (LIBc := LIB) (Lc := LB) (M := M) (x := x) (lo := lo) (B := B) (line := 595) (reason := R_INTERNAL_ERROR)
                                        (ra2 := RP_595_R2) (ra3 := RP_EPI0).
    all: try first [exact HP2| exact KREL2| exact LM2| exact SUBL| exact CTX| exact MF1| exact AUX2| exact ERR2| exact MI2| exact CEIL| exact rp_g595a| exact rp_g595b].
    all: lazymatch goal with
         | |- lb_bytes _ + _ + _ <= _ => unfold mid_bytes, DECODE_BYTES, ERRSTR_BYTES in BUD; unfold ERRDEBUG_BYTES; clear - BUD EN1 CN1; lia
         | |- Z.of_nat _ + _ + _ <= _ => unfold mid_cnt, DECODE_CNT, ERRSTR_CNT in BUDC; clear - BUDC EN2 CN2; lia
         | |- lb_big _ + _ <= _ => unfold mid_big, DECODE_BIG in BUDG; clear - BUDG EN3 CN3; lia
         | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
         | |- bv_unsigned _ mod 16 = 0 => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPA; lia
         | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST2
         | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - LO STKR; lia
         | |- 0 <= 595 < _ => clear; lia
         | |- 0 < R_INTERNAL_ERROR < _ => unfold R_INTERNAL_ERROR; clear; lia
         | |- 0 <= _ < 2 ^ 64 => unfold RP_595_R1, RP_595_R2, RP_EPI0; clear; lia
         | |- _ mod 2 = 0 => reflexivity
         | |- _ => idtac
         end.
    (* [comment removed for export] *)
    intros u7 u8 u9 b0 b8 b9 b10 b11 b12 b13 b14 u10 u11 u12 u13 m3 mo3 s3' errv3 LE M' c KREL3 MP3 MI3 ST3 AUX3 HP3 LM3 STEP3 NEW3 F3 CTX3 ERR3' VD3 DL3 EC3 EB3 EG3 ERR3 XP3.
    unfold SP' in ST3, XP3. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST3, XP3 by (clear - SPR LO STK0 LO0; lia). fold SP' in ST3, XP3.
    (* [comment removed for export] *)
    assert (FXS : forall A n, SP' <= A -> Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) (ERR_X ++ memflag_foot ++ errph_foot (mid_err M))).
    { intros A' n' HA. apply Forall_app; split; [| apply Forall_app; split].
      - apply avoid_of_img; [apply img_ERR_X| right; unfold SP', IMG_HI in *; clear - HA LO STK0 CEIL HCEILB; lia].
      - apply avoid_of_img; [apply img_memflag| right; unfold SP', IMG_HI in *; clear - HA LO STK0 CEIL HCEILB; lia].
      - destruct LM as (_ & _ & _ & EPm & _). rewrite CTX in EPm. cbn [ERRPH_mid] in EPm.
        destruct (mid_err M) as [|cc]; cbn [errph_foot]; [apply Forall_nil|]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        cbn [ERRPH] in EPm. destruct EPm as [_ CH]. pose proof CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
        pose proof (BEL0 _ (SUB0 _ (SUBL _ I5))) as K. rewrite Z5 in K. right. unfold SP' in *. clear - HA K LO STK0 CEIL; lia. }
    assert (T13 : forall A cs, rw_cells rsegs m1 A cs -> SP' <= A -> rw_cells rsegs m3 A cs).
    { intros A' cs C1 HA. eapply xpres_rw_cells'; [exact XP3| | left; exact HA| apply FXS; exact HA].
      eapply xpres_rw_cells'; [exact XP2| exact C1| left; exact HA| apply Forall_nil]. }
    pose proof (T13 _ _ FRlo ltac:(clear; lia)) as FRlo3.
    pose proof (T13 _ _ FRhi ltac:(unfold SP'; clear; lia)) as FRhi3.
    pose proof (proj1 (rw_cells_app rsegs m3 _ [CB 2128 j2] SAVES) FRhi3) as [_ SV3]. cbn [cells_size csize Nat.add] in SV3.
    replace (bv_unsigned sp + -2232 + Z.of_nat (2128 + 0)) with (bv_unsigned sp + -104) in SV3 by (clear; lia).
    replace (ret_pc (Z_to_bv 64 RP_EPI0)) with (Z_to_bv 64 RP_EPI0) by (symmetry; apply ret_pc_even; [unfold RP_EPI0; lia| reflexivity]).
    pose proof rp_epi0 as EPI. unfold rp_epi_stmt in EPI. unfold SP'.
    eapply (sr_evt_krel H HH); [exact KREL3| eapply EPI; [clear - LO STK0 LO0; lia| unfold SAVES in SV3; exact SV3| exact MI3]|]. clear EPI. fold SP'.
    intros ms5 ->.
    (* [comment removed for export] *)
    assert (FRALL : rw_cells rsegs m3 SP' (clo ++ (CB 2128 j2 :: SAVES))).
    { apply (proj2 (rw_cells_app rsegs m3 _ _ _)). split; [exact FRlo3|].
      rewrite CLOZ. unfold SP' in *. replace (bv_unsigned sp + -2352 + Z.of_nat 120) with (bv_unsigned sp + -2232) by (clear; lia). exact FRhi3. }
    pose proof (stk_release rsegs m3 lo _ _ ST3 FRALL ltac:(unfold SP'; clear - LO STK0; lia)) as STf.
    rewrite cells_size_app, CLOZ in STf. unfold SAVES, rp_saves in STf. cbn [cells_size csize Nat.add app length] in STf. unfold SP' in STf.
    replace (bv_unsigned sp + -2352 + Z.of_nat (120 + 2232)) with (bv_unsigned sp) in STf by (clear; lia).
    (* [comment removed for export] *)
    assert (OFFI : forall b', In b' L0 -> blk_addr b' + blk_size b' <= IMG_LO \/ IMG_HI <= blk_addr b').
    { intros b' Hb'. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP Hb') as (_ & _ & _ & _ & O). unfold IMG_LO, IMG_HI. exact O. }
    assert (FXH : forall b' A n, In b' LB -> (forall b, In b LIB -> blk_id b <> blk_id b') -> blk_addr b' <= A -> A + n <= blk_addr b' + blk_size b' ->
              Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) (ERR_X ++ memflag_foot ++ errph_foot (mid_err M))).
    { intros b' A' n' Hb' NE HA HN. pose proof (OFFI _ (SUB0 _ Hb')) as O.
      apply Forall_app; split; [| apply Forall_app; split].
      - apply avoid_of_img; [apply img_ERR_X| clear - O HA HN; lia].
      - apply avoid_of_img; [apply img_memflag| clear - O HA HN; lia].
      - eapply Forall_impl; [| exact (errph_foot_apart b' (SUB0 _ Hb') NE)]. cbn beta. intros iv K. clear - K HA HN. lia. }
    assert (T13h : forall b' A cs, rw_cells rsegs m1 A cs -> In b' LB -> (forall b, In b LIB -> blk_id b <> blk_id b') ->
              blk_addr b' <= A -> A + Z.of_nat (cells_size cs) <= blk_addr b' + blk_size b' -> rw_cells rsegs m3 A cs).
    { intros b' A' cs C1 Hb' NE HA HN.
      eapply xpres_rw_cells'; [exact XP3| | right; right; exists b'; split; [exact Hb'| split; [exact HA| exact HN]]| exact (FXH _ _ _ Hb' NE HA HN)].
      eapply xpres_rw_cells'; [exact XP2| exact C1| right; right; exists b'; split; [exact (SUB0 _ Hb')| split; [exact HA| exact HN]]| apply Forall_nil]. }
    assert (MF3 : MEMFLAG m3 1) by (destruct LM3 as (_ & MF3 & _); rewrite F3 in MF3; exact MF3).
    pose proof SO as (SC & SINB & _). rewrite SE in SC.
    assert (SC3 : rw_cells rsegs m3 st [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
    { eapply (T13h (es_id S, st, STORE_SIZE)); [| exact SINB| intros b Hb; exact (DJ6 _ _ Hb (or_introl eq_refl))| cbn; clear; lia| cbn; unfold STORE_SIZE; clear; lia].
      eapply xpres_rw_cells'; [exact XP1| exact SC| right; right; exists (es_id S, st, STORE_SIZE); split; [exact SINB| cbn; unfold STORE_SIZE; clear; lia]|].
      unfold MEMBIO_foot.
      pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ (es_id S, st, STORE_SIZE) (mb_id R, mb, BIO_SIZE) HP (OBJ0 _ (or_introl eq_refl)) (OBJ0 _ ltac:(right; left; reflexivity))
                    (nodup_ids_cons_ne _ _ _ NDsm ltac:(left; reflexivity))) as D1.
      pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ (es_id S, st, STORE_SIZE) (mb_bmid R, mb_bm R, BUFMEM_SIZE) HP (OBJ0 _ (or_introl eq_refl)) (OBJ0 _ ltac:(right; right; right; left; reflexivity))
                    (nodup_ids_cons_ne _ _ _ NDsm ltac:(right; right; left; reflexivity))) as D3.
      cbn [blk_addr blk_size fst snd cells_size csize Nat.add length] in D1, D3 |- *. unfold STORE_SIZE, BIO_SIZE, BUFMEM_SIZE in D1, D3 |- *.
      apply Forall_cons; [cbn; clear - D1; lia|]. apply Forall_cons; [cbn; clear - D3; lia| apply Forall_nil]. }
    assert (MBO3 : MEMBIO LB m3 mb R').
    { eapply (MEMBIO_frameA LB LB SP'); [eapply (MEMBIO_frame0 LB LB SP'); [exact MBO1| intros b Hb; rewrite (mb_static_blocks mb R R' MST1) in Hb; exact (SUB0' b Hb)| exact XPL2]
                                        | intros b Hb; rewrite (mb_static_blocks mb R R' MST1) in Hb; exact (SUB0' b Hb)| exact XP3|].
      rewrite (mb_static_blocks mb R R' MST1).
      assert (EACH : forall b, In b (blocks_MEMBIO mb R) -> Forall (fun iv : Z * Z => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) (ERR_X ++ memflag_foot ++ errph_foot (mid_err M))).
      { intros bk Hbk. exact (FXH bk (blk_addr bk) (blk_size bk) (SUB0' bk Hbk) ltac:(intros bq Hbq; exact (DJ6 _ _ Hbq (or_intror Hbk))) ltac:(clear; lia) ltac:(clear; lia)). }
      apply Forall_forall. intros iv Hiv. apply Forall_forall. intros bk Hbk. exact (proj1 (Forall_forall _ _) (EACH bk Hbk) iv Hiv). }
    assert (DS3 : bytes_at rsegs m3 (mb_buf R) ds).
    { destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      - assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; lia]). rewrite DN. apply bytes_at_nil.
        destruct MBO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BUFP & BUFH & _). clear - BUFP BUFH HCEILB L0Z. lia.
      - destruct (PAYL ltac:(destruct MBO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LENR & _); clear - LNZ LENR; lia)) as [pD [PIN PNL]].
        eapply xpres_bytes_at'; [exact XP3| | right; right; exists (pD, mb_buf R, mb_len R); split; [exact PIN| cbn; unfold zlength in DSL; rewrite DSL; clear; lia]|].
        + eapply xpres_bytes_at'; [exact XP2| exact DS1| right; right; exists (pD, mb_buf R, mb_len R); split; [exact (SUB0 _ PIN)| cbn; unfold zlength in DSL; rewrite DSL; clear; lia]| apply Forall_nil].
        + unfold zlength in DSL. rewrite DSL. exact (FXH (pD, mb_buf R, mb_len R) (mb_buf R) (mb_len R) PIN ltac:(intros bq Hbq; cbn; exact (PNL _ Hbq)) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)). }
    (* [comment removed for export] *)
    assert (XP3d : xpres LB SP' (ERR_X ++ errph_foot (mid_err M)) m2 m3).
    { eapply xpres_drop_memflag; [| exact MF2| exact MF3]. eapply xpres_weaken; [exact XP3| clear; lia| intros b Hb; exact Hb|].
      intros q Hq. pose proof (proj1 (rin_ivs_app _ _ _) Hq) as [K|K]; [| pose proof (proj1 (rin_ivs_app _ _ _) K) as [K'|K']].
      - apply (proj2 (rin_ivs_app _ _ _)). right. apply (proj2 (rin_ivs_app _ _ _)). left. exact K.
      - apply (proj2 (rin_ivs_app _ _ _)). left. exact K'.
      - apply (proj2 (rin_ivs_app _ _ _)). right. apply (proj2 (rin_ivs_app _ _ _)). right. exact K'. }
    assert (INC : forall q, rin_ivs (ERR_X ++ errph_foot (mid_err M)) q -> rin_ivs XF q).
    { intros q Hq. unfold XF. apply (proj2 (rin_ivs_app _ _ _)). right. pose proof (proj1 (rin_ivs_app _ _ _) Hq) as [K|K].
      - apply (proj2 (rin_ivs_app _ _ _)). right. apply (proj2 (rin_ivs_app _ _ _)). left. exact K.
      - apply (proj2 (rin_ivs_app _ _ _)). right. apply (proj2 (rin_ivs_app _ _ _)). right. apply (proj2 (rin_ivs_app _ _ _)). right. exact K. }
    assert (XPF : xpres LB (bv_unsigned sp) XF m m3).
    { eapply xpres_trans; [eapply xpres_weaken; [exact XP1| clear; lia| intros b Hb; exact Hb| intros q Hq; unfold XF; apply (proj2 (rin_ivs_app _ _ _)); right; apply (proj2 (rin_ivs_app _ _ _)); left; exact Hq]|].
      eapply xpres_trans; [eapply xpres_weaken; [exact XPL2| unfold SP'; clear; lia| intros b Hb; exact Hb| intros q Hq; destruct Hq]|].
      eapply xpres_weaken; [exact XP3d| unfold SP'; clear; lia| intros b Hb; exact Hb| exact INC]. }
    eapply rp_post_S0; [left; reflexivity| exact KREL3| | exact MI3| exact STf| exact ERR3| exact AUX3| exact HP3| exact LM3| exact STEP3| exact NEW3| rewrite CTX3, CTX; reflexivity
                       | exact EC3| exact EB3| exact EG3| exact MBO3| exact MST1| exact DS3| exact SC3| exact XPF].
    eapply (mpres_trans H HH); [exact MP1| eapply (mpres_trans H HH); [exact MP2| exact MP3]].
  Qed.

  Let PERM : RHEAP_perm_law H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).

  (* [comment removed for export] *)
  Lemma rp_fail_lbuf :
    forall (line reason raA raB : Z),
      0 <= line < 2^31 -> 0 < reason < 2^23 -> 0 <= raA < 2^64 -> raA mod 2 = 0 -> 0 <= raB < 2^64 -> raB mod 2 = 0 ->
      rp_glue raA raB P_ERR_set_debug A_ECHS_FILE_RP line A_ECHS_FUNC_RP -> rp_glue raB RP_ERRL0 P_ERR_set_error ERR_LIB_SSL reason 0 ->
    forall m1 mo1 (s1' : PState) (p : bptr) (A nA : Z) (R' : membio) (clo : list cell) (j2 : list byte)
           (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v u3 u4 u5 u6 : word),
      0 <= nA <= 512 * 33 ->
      hs_RHEAP H s1' ((p, A, nA) :: L0) m1 -> hs_KREL H s1' mo1 -> hs_MPRES H mo mo1 ->
      MEMBIO LB m1 mb R' -> mb_static R R' -> bytes_at rsegs m1 (mb_buf R) ds ->
      cells_size clo = 120%nat -> rw_cells rsegs m1 SP' clo -> rw_cells rsegs m1 (bv_unsigned sp + -2232) (CB 2128 j2 :: SAVES) ->
      (exists errv1, rw_cells rsegs m1 RERRNO [C4 errv1]) -> MEMFLAG m1 1 -> IMPL_mem m1 -> GOT_mem m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo SP' -> hs_rauxv_ok H m1 B ->
      xpres LB (bv_unsigned sp) (MEMBIO_foot mb R) m m1 ->
      hs_SR H POST (mkCfg (MS (mkR (Z_to_bv 64 raA) (Z_to_bv 64 SP') gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7
                                    s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v u3 u4 u5 u6)
                               F (Z_to_bv 64 P_ERR_new) fc None m1 (seg_rom rsegs)) mo1).
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HRE HX CERTO3 PERM.
    intros line reason raA raB LNR REAS RA1 RA1E RA2 RA2E GA GB.
    intros m1 mo1 s1' p A nA R' clo j2 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v u3 u4 u5 u6.
    intros NAR HP1 KREL1 MP1 MBO1 MST1 DS1 CLOZ FRlo FRhi [errv1 ERR1] MF IM1 GM1 MI1 ST1 AUX1 XP1.
    destruct rc_facts as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    pose proof rc_stack as (STKR & _ & _).
    hcb. pose proof (word_range sp) as SPR.
    destruct (lad_head_facts H HX L0 _ _ _ _ _ HP1) as (BR & BH & NIP & DISJ & BEL).
    assert (SUB0' : forall b, In b (blocks_MEMBIO mb R) -> In b LB).
    { intros b Hb. destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _). unfold blocks_MEMBIO in Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption. }
    pose proof SO as (SC & SINB & _). rewrite SE in SC.
    set (Lc := (p, A, nA) :: LB).
    assert (HPp : hs_RHEAP H s1' (mid_errblocks M ++ Lc) m1) by (eapply PERM; [exact HP1| unfold Lc, L0; apply Permutation_middle]).
    assert (SUBc : forall b, In b LIB -> In b Lc) by (intros b Hb; unfold Lc; right; exact (SUBL _ Hb)).
    assert (LM1 : LIBMID LIB m1 M).
    { pose proof (LIBMID_mf_X LIB LB (bv_unsigned sp) (MEMBIO_foot mb R) m m1 M LM
                    ltac:(eapply xpres_weaken; [exact XP1| clear; lia| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app; right; exact Hq]) SUBL MF) as K.
      destruct M as [f cph eph E v]. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in K, MF1 |- *. subst f. apply K.
      - intros q Hq. destruct MBO as (_ & _ & _ & _ & _ & _ & _ & _ & XB1 & _ & XB3 & _).
        pose proof XB1 as (_ & _ & _ & _ & O1). pose proof XB3 as (_ & _ & _ & _ & O3).
        unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE, IMG_LO, IMG_HI in *. cbn [rin_ivs fst snd] in Hq. clear - Hq O1 O3. lia.
      - intros q b Hq Hb. unfold MEMBIO_foot in Hq. cbn [rin_ivs fst snd] in Hq.
        pose proof (DJA b (mb_id R, mb, BIO_SIZE) Hb ltac:(right; left; reflexivity)) as D1.
        pose proof (DJA b (mb_bmid R, mb_bm R, BUFMEM_SIZE) Hb ltac:(right; right; right; left; reflexivity)) as D3.
        cbn [blk_addr blk_size fst snd] in D1, D3. clear - Hq D1 D3. lia. }
    pose proof (errph_nonneg (mid_err M)) as (EN1 & EN2 & EN3). pose proof (ctxph_nonneg3 (mid_ctx M)) as (CN1 & CN2 & CN3).
    (* [comment removed for export] *)
    eapply (rp_raise H HX CERTO3) with (LIBc := LIB) (Lc := Lc) (M := M) (x := x) (lo := lo) (B := B) (line := line) (reason := reason)
                                        (ra2 := raB) (ra3 := RP_ERRL0).
    all: try first [exact HPp| exact KREL1| exact LM1| exact SUBc| exact CTX| exact MF1| exact AUX1| exact ERR1| exact MI1| exact CEIL| exact GA| exact GB| exact LNR| exact REAS| exact RA1| exact RA1E| exact RA2| exact RA2E].
    all: lazymatch goal with
         | |- lb_bytes _ + _ + _ <= _ => unfold Lc; rewrite lb_bytes_app, lb_bytes_cons; unfold L0 in BUD; rewrite lb_bytes_app in BUD; cbn [blk_size snd];
                                         unfold mid_bytes, DECODE_BYTES, ERRSTR_BYTES in BUD; unfold ERRDEBUG_BYTES; clear - BUD EN1 CN1 NAR; lia
         | |- Z.of_nat _ + _ + _ <= _ => unfold Lc; rewrite length_app; cbn [length]; unfold L0 in BUDC; rewrite length_app in BUDC;
                                         unfold mid_cnt, DECODE_CNT, ERRSTR_CNT in BUDC; clear - BUDC EN2 CN2; lia
         | |- lb_big _ + _ <= _ => unfold Lc; rewrite lb_big_app, lb_big_cons; unfold L0 in BUDG; rewrite lb_big_app in BUDG; cbn [blk_size snd];
                                   pose proof (big1_range nA) as G1; unfold mid_big, DECODE_BIG in BUDG; clear - BUDG EN3 CN3 G1; lia
         | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
         | |- bv_unsigned _ mod 16 = 0 => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPA; lia
         | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST1
         | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - LO STKR; lia
         | |- 0 <= _ < 2 ^ 64 => unfold RP_ERRL0; clear; lia
         | |- _ mod 2 = 0 => reflexivity
         | |- _ => idtac
         end.
    (* [comment removed for export] *)
    intros u7 u8 u9 c0 b8 b9 b10 b11 b12 b13 b14 u10 u11 u12 u13 m2 mo2 s2' errv2 LE M' c KREL2 MP2 MI2 ST2 AUX2 HP2 LM2 STEP2 NEW2 F2 CTX2 ERR2' VD2 DL2 EC2 EB2 EG2 ERR2 XP2.
    unfold SP' in ST2, XP2. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST2, XP2 by (clear - SPR LO STK0 LO0; lia). fold SP' in ST2, XP2.
    destruct LM2 as (IM2 & MF2 & LMrest2). rewrite F2 in MF2. pose proof (conj IM2 (conj MF2 LMrest2)) as LM2. rewrite <- F2 in LM2. change (LIBMID (LE ++ LIB) m2 M') in LM2.
    pose proof LMrest2 as (_ & _ & _ & _ & _ & _ & GM2 & _). clear LMrest2.
    eapply (sr_evt_krel H HH); [exact KREL2| eapply rp_errl0; exact MI2|]. intros ms3 ->.
    eapply (sr_evt_krel H HH); [exact KREL2| eapply bio_free_all_null; exact MI2|]. intros ms4 ->.
    eapply (sr_evt_krel H HH); [exact KREL2| eapply rp_errl2; exact MI2|]. intros ms5 ->.
    (* [comment removed for export] *)
    pose proof (cfree_null_spec H HH) as CF0. unfold cfree_null_stmt in CF0.
    eapply (sr_seq H HH).
    { eapply CF0 with (lo := lo); clear CF0.
      all: try first [eapply (krel_halted H HH); exact KREL2| eapply (krel_lazy H HH); exact KREL2| exact CEIL| exact MI2| exact IM2| exact GM2].
      all: lazymatch goal with
           | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST2
           | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - LO STK0; lia
           end. }
    clear CF0. intros [ms6 mo6] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & -> & MU3 & WM3 & MI3 & ST3 & IM3 & GM3).
    unfold SP' in MU3, ST3. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in MU3, ST3 by (clear - SPR LO STK0 LO0; lia). fold SP' in MU3, ST3.
    eapply (sr_evt_krel H HH); [exact KREL2| eapply rp_errl3; exact MI3|]. intros ms7 ->.
    (* [comment removed for export] *)
    assert (HP3 : hs_RHEAP H s2' ((p, A, nA) :: mid_errblocks M' ++ LE ++ LB) m3).
    { eapply (HH_RHEAP_frame H HH); [| exact MU3| exact WM3| apply Forall_cons; [left; cbn; clear - CEIL; lia| apply Forall_nil]].
      eapply PERM; [exact HP2|]. unfold Lc. apply Permutation_sym.
      replace (mid_errblocks M' ++ LE ++ (p, A, nA) :: LB) with ((mid_errblocks M' ++ LE) ++ (p, A, nA) :: LB) by (rewrite <- app_assoc; reflexivity).
      replace (mid_errblocks M' ++ LE ++ LB) with ((mid_errblocks M' ++ LE) ++ LB) by (rewrite <- app_assoc; reflexivity). apply Permutation_middle. }
    assert (AUX3 : hs_rauxv_ok H m3 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL, SP'. clear - SPB CEIL HCEILB LO STK0; apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    apply (rw_cells_transport rsegs _ m2 m3 _ _ ERR2) in MU3 as ERR3; [| exact WM3| clear - CEIL HCEILB; img_static].
    destruct (lad_head_facts H HX (mid_errblocks M' ++ LE ++ LB) _ _ _ _ _ HP3) as (_ & _ & NIP3 & _ & BEL3).
    pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := (p, A, nA) :: mid_errblocks M' ++ LE ++ LB) (s := s2') (p := p) (A := A) (n := nA) (errv := errv2); try reflexivity.
      all: try first [exact HP3| exact KREL2| exact AUX3| exact MI3| exact IM3| exact GM3| exact CEIL].
      all: lazymatch goal with
           | |- In _ _ => left; reflexivity
           | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
           | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST3
           | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); unfold CFREE_STACK, RFREE_STACK; clear - LO STK0; lia
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR3
           end. }
    clear CF. intros [ms8 mo8] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & m4 & s4' & -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & XP4 & HP4 & IM4 & GM4).
    rewrite (proj1 (HH_lb_remove H HH)) in XP4, HP4 by exact NIP3.
    unfold SP' in ST4, XP4. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST4, XP4 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR4. fold SP' in ST4, XP4.
    (* [comment removed for export] *)
    assert (OFFI : forall b', In b' L0 -> blk_addr b' + blk_size b' <= IMG_LO \/ IMG_HI <= blk_addr b').
    { intros b' Hb'. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP Hb') as (_ & _ & _ & _ & O). unfold IMG_LO, IMG_HI. exact O. }
    assert (FXS : forall A' n, SP' <= A' -> Forall (fun iv : Z * Z => A' + n <= fst iv \/ snd iv <= A') (ERR_X ++ memflag_foot ++ errph_foot (mid_err M))).
    { intros A' n' HA. apply Forall_app; split; [| apply Forall_app; split].
      - apply avoid_of_img; [apply img_ERR_X| right; unfold SP', IMG_HI in *; clear - HA LO STK0 CEIL HCEILB; lia].
      - apply avoid_of_img; [apply img_memflag| right; unfold SP', IMG_HI in *; clear - HA LO STK0 CEIL HCEILB; lia].
      - destruct LM as (_ & _ & _ & EPm & _). rewrite CTX in EPm. cbn [ERRPH_mid] in EPm.
        destruct (mid_err M) as [|cc]; cbn [errph_foot]; [apply Forall_nil|]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        cbn [ERRPH] in EPm. destruct EPm as [_ CH]. pose proof CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
        pose proof (BEL0 _ (SUB0 _ (SUBL _ I5))) as K. rewrite Z5 in K. right. unfold SP' in *. clear - HA K LO STK0 CEIL; lia. }
    assert (FXH : forall b' A' n, In b' LB -> (forall b, In b LIB -> blk_id b <> blk_id b') -> blk_addr b' <= A' -> A' + n <= blk_addr b' + blk_size b' ->
              Forall (fun iv : Z * Z => A' + n <= fst iv \/ snd iv <= A') (ERR_X ++ memflag_foot ++ errph_foot (mid_err M))).
    { intros b' A' n' Hb' NE HA HN. pose proof (OFFI _ (SUB0 _ Hb')) as O.
      apply Forall_app; split; [| apply Forall_app; split].
      - apply avoid_of_img; [apply img_ERR_X| clear - O HA HN; lia].
      - apply avoid_of_img; [apply img_memflag| clear - O HA HN; lia].
      - eapply Forall_impl; [| exact (errph_foot_apart b' (SUB0 _ Hb') NE)]. cbn beta. intros iv K. clear - K HA HN. lia. }
    assert (T14s : forall A' cs, rw_cells rsegs m1 A' cs -> SP' <= A' -> rw_cells rsegs m4 A' cs).
    { intros A' cs C1 HA.
      eapply xpres_rw_cells'; [exact XP4| | left; exact HA| apply Forall_nil].
      eapply rw_cells_transport; [| exact MU3| exact WM3| cbn; unfold SP' in *; clear - HA LO STK0 CEIL; lia].
      eapply xpres_rw_cells'; [exact XP2| exact C1| left; exact HA| apply FXS; exact HA]. }
    assert (T14h : forall b' A' cs, rw_cells rsegs m1 A' cs -> In b' LB -> (forall b, In b LIB -> blk_id b <> blk_id b') ->
              blk_addr b' <= A' -> A' + Z.of_nat (cells_size cs) <= blk_addr b' + blk_size b' -> rw_cells rsegs m4 A' cs).
    { intros b' A' cs C1 Hb' NE HA HN. pose proof (BEL0 _ (SUB0 _ Hb')) as Bb.
      eapply xpres_rw_cells'; [exact XP4| | right; right; exists b'; split; [apply in_or_app; right; apply in_or_app; right; exact Hb'| split; [exact HA| exact HN]]| apply Forall_nil].
      eapply rw_cells_transport; [| exact MU3| exact WM3| cbn; clear - HA HN Bb CEIL; lia].
      eapply xpres_rw_cells'; [exact XP2| exact C1| right; right; exists b'; split; [unfold Lc; right; exact Hb'| split; [exact HA| exact HN]]| exact (FXH _ _ _ Hb' NE HA HN)]. }
    pose proof (T14s _ _ FRlo ltac:(clear; lia)) as FRlo4.
    pose proof (T14s _ _ FRhi ltac:(unfold SP'; clear; lia)) as FRhi4.
    pose proof (proj1 (rw_cells_app rsegs m4 _ [CB 2128 j2] SAVES) FRhi4) as [_ SV4]. cbn [cells_size csize Nat.add] in SV4.
    replace (bv_unsigned sp + -2232 + Z.of_nat (2128 + 0)) with (bv_unsigned sp + -104) in SV4 by (clear; lia).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL4| unfold SP'; eapply rp_errl4; [clear - LO STK0 LO0; lia| unfold SAVES in SV4; exact SV4| exact MI4]|].
    intros ms9 ->.
    assert (FRALL : rw_cells rsegs m4 SP' (clo ++ (CB 2128 j2 :: SAVES))).
    { apply (proj2 (rw_cells_app rsegs m4 _ _ _)). split; [exact FRlo4|].
      rewrite CLOZ. unfold SP' in *. replace (bv_unsigned sp + -2352 + Z.of_nat 120) with (bv_unsigned sp + -2232) by (clear; lia). exact FRhi4. }
    pose proof (stk_release rsegs m4 lo _ _ ST4 FRALL ltac:(unfold SP'; clear - LO STK0; lia)) as STf.
    rewrite cells_size_app, CLOZ in STf. unfold SAVES, rp_saves in STf. cbn [cells_size csize Nat.add app length] in STf. unfold SP' in STf.
    replace (bv_unsigned sp + -2352 + Z.of_nat (120 + 2232)) with (bv_unsigned sp) in STf by (clear; lia).
    assert (SC4 : rw_cells rsegs m4 st [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
    { eapply (T14h (es_id S, st, STORE_SIZE)); [| exact SINB| intros b Hb; exact (DJ6 _ _ Hb (or_introl eq_refl))| cbn; clear; lia| cbn; unfold STORE_SIZE; clear; lia].
      eapply xpres_rw_cells'; [exact XP1| exact SC| right; right; exists (es_id S, st, STORE_SIZE); split; [exact SINB| cbn; unfold STORE_SIZE; clear; lia]|].
      unfold MEMBIO_foot.
      pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ (es_id S, st, STORE_SIZE) (mb_id R, mb, BIO_SIZE) HP (OBJ0 _ (or_introl eq_refl)) (OBJ0 _ ltac:(right; left; reflexivity))
                    (nodup_ids_cons_ne _ _ _ NDsm ltac:(left; reflexivity))) as D1.
      pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ (es_id S, st, STORE_SIZE) (mb_bmid R, mb_bm R, BUFMEM_SIZE) HP (OBJ0 _ (or_introl eq_refl)) (OBJ0 _ ltac:(right; right; right; left; reflexivity))
                    (nodup_ids_cons_ne _ _ _ NDsm ltac:(right; right; left; reflexivity))) as D3.
      cbn [blk_addr blk_size fst snd cells_size csize Nat.add length] in D1, D3 |- *. unfold STORE_SIZE, BIO_SIZE, BUFMEM_SIZE in D1, D3 |- *.
      apply Forall_cons; [cbn; clear - D1; lia|]. apply Forall_cons; [cbn; clear - D3; lia| apply Forall_nil]. }
    assert (EACH : forall b, In b (blocks_MEMBIO mb R) -> Forall (fun iv : Z * Z => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) (ERR_X ++ memflag_foot ++ errph_foot (mid_err M))).
    { intros bk Hbk. exact (FXH bk (blk_addr bk) (blk_size bk) (SUB0' bk Hbk) ltac:(intros bq Hbq; exact (DJ6 _ _ Hbq (or_intror Hbk))) ltac:(clear; lia) ltac:(clear; lia)). }
    assert (KEEPB : forall b, In b (blocks_MEMBIO mb R') -> In b LB) by (intros b Hb; rewrite (mb_static_blocks mb R R' MST1) in Hb; exact (SUB0' b Hb)).
    assert (MBO2 : MEMBIO LB m2 mb R').
    { eapply (MEMBIO_frameA LB LB SP'); [exact MBO1| exact KEEPB| eapply xpres_weaken; [exact XP2| clear; lia| intros b Hb; unfold Lc; right; exact Hb| intros q Hq; exact Hq]|].
      rewrite (mb_static_blocks mb R R' MST1). apply Forall_forall. intros iv Hiv. apply Forall_forall. intros bk Hbk. exact (proj1 (Forall_forall _ _) (EACH bk Hbk) iv Hiv). }
    assert (MBO3 : MEMBIO LB m3 mb R').
    { eapply (MEMBIO_frame0 LB LB SP'); [exact MBO2| exact KEEPB|].
      eapply xpres_of_munch; [exact MU3| exact WM3| apply Forall_cons; [left; cbn; unfold SP'; clear - CEIL LO STK0; lia| apply Forall_nil]| intros b Hb; exact (BEL0 _ (SUB0 _ Hb))]. }
    assert (MBO4 : MEMBIO LB m4 mb R').
    { eapply (MEMBIO_frame0 LB LB SP'); [exact MBO3| exact KEEPB|].
      eapply xpres_weaken; [exact XP4| clear; lia| intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb| intros q Hq; exact Hq]. }
    assert (DS4 : bytes_at rsegs m4 (mb_buf R) ds).
    { destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      - assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; lia]). rewrite DN. apply bytes_at_nil.
        destruct MBO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BUFP & BUFH & _). clear - BUFP BUFH HCEILB L0Z. lia.
      - destruct (PAYL ltac:(destruct MBO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LENR & _); clear - LNZ LENR; lia)) as [pD [PIN PNL]].
        unfold zlength in DSL. pose proof (BEL0 _ (SUB0 _ PIN)) as Bb. cbn [blk_addr blk_size fst snd] in Bb.
        eapply xpres_bytes_at'; [exact XP4| | right; right; exists (pD, mb_buf R, mb_len R); split; [apply in_or_app; right; apply in_or_app; right; exact PIN| cbn; rewrite DSL; clear; lia]| apply Forall_nil].
        eapply bytes_at_transport; [| exact MU3| rewrite DSL; cbn; clear - Bb CEIL; lia].
        eapply xpres_bytes_at'; [exact XP2| exact DS1| right; right; exists (pD, mb_buf R, mb_len R); split; [unfold Lc; right; exact PIN| cbn; rewrite DSL; clear; lia]|].
        rewrite DSL. exact (FXH (pD, mb_buf R, mb_len R) (mb_buf R) (mb_len R) PIN ltac:(intros bq Hbq; cbn; exact (PNL _ Hbq)) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)). }
    assert (MF4 : MEMFLAG m4 1).
    { destruct MF2 as (fb & FB & V). exists fb. split; [| exact V].
      eapply xpres_rw_cells'; [exact XP4| | right; left; unfold A_mem_inited, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; cbn; clear; lia| apply Forall_nil].
      eapply rw_cells_transport; [exact FB| exact MU3| exact WM3| clear - CEIL HCEILB; img_static]. }
    assert (XP2d : xpres LB SP' (ERR_X ++ errph_foot (mid_err M)) m1 m2).
    { eapply xpres_drop_memflag; [| exact MF| exact MF2]. eapply xpres_weaken; [exact XP2| clear; lia| intros b Hb; unfold Lc; right; exact Hb|].
      intros q Hq. pose proof (proj1 (rin_ivs_app _ _ _) Hq) as [K|K]; [| pose proof (proj1 (rin_ivs_app _ _ _) K) as [K'|K']].
      - apply (proj2 (rin_ivs_app _ _ _)). right. apply (proj2 (rin_ivs_app _ _ _)). left. exact K.
      - apply (proj2 (rin_ivs_app _ _ _)). left. exact K'.
      - apply (proj2 (rin_ivs_app _ _ _)). right. apply (proj2 (rin_ivs_app _ _ _)). right. exact K'. }
    assert (INC : forall q, rin_ivs (ERR_X ++ errph_foot (mid_err M)) q -> rin_ivs XF q).
    { intros q Hq. unfold XF. apply (proj2 (rin_ivs_app _ _ _)). right. pose proof (proj1 (rin_ivs_app _ _ _) Hq) as [K|K].
      - apply (proj2 (rin_ivs_app _ _ _)). right. apply (proj2 (rin_ivs_app _ _ _)). left. exact K.
      - apply (proj2 (rin_ivs_app _ _ _)). right. apply (proj2 (rin_ivs_app _ _ _)). right. apply (proj2 (rin_ivs_app _ _ _)). right. exact K. }
    assert (XPF : xpres LB (bv_unsigned sp) XF m m4).
    { eapply xpres_trans; [eapply xpres_weaken; [exact XP1| clear; lia| intros b Hb; exact Hb| intros q Hq; unfold XF; apply (proj2 (rin_ivs_app _ _ _)); right; apply (proj2 (rin_ivs_app _ _ _)); left; exact Hq]|].
      eapply xpres_trans; [eapply xpres_weaken; [exact XP2d| unfold SP'; clear; lia| intros b Hb; exact Hb| exact INC]|].
      eapply xpres_trans; [eapply xpres_of_munch; [exact MU3| exact WM3| apply Forall_cons; [left; cbn; unfold SP'; clear - CEIL LO STK0; lia| apply Forall_nil]| intros b Hb; exact (BEL0 _ (SUB0 _ Hb))]|].
      eapply xpres_weaken; [exact XP4| unfold SP'; clear; lia| intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb| intros q Hq; destruct Hq]. }
    eapply rp_post_S0; [left; reflexivity| exact KREL4| | exact MI4| exact STf| exact ERR4| exact AUX4| exact HP4| | exact STEP2| exact NEW2| rewrite CTX2, CTX; reflexivity
                       | exact EC2| exact EB2| exact EG2| exact MBO4| exact MST1| exact DS4| exact SC4| exact XPF].
    - eapply (mpres_trans H HH); [exact MP1| eapply (mpres_trans H HH); [exact MP2| exact MP4]].
    - (* [comment removed for export] *)
      eapply (LIBMID_xpres0 _ (mid_errblocks M' ++ LE ++ LB) SP'); [| exact XP4| intros b Hb; apply in_or_app; right; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; exact (SUBL _ Hb)]].
      eapply (LIBMID_xpres0 _ (LE ++ LB) SP'); [exact LM2| | intros b Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; exact (SUBL _ Hb)]].
      eapply xpres_of_munch; [exact MU3| exact WM3| apply Forall_cons; [left; cbn; unfold SP'; clear - CEIL LO STK0; lia| apply Forall_nil]|].
      intros b Hb. apply BEL3. apply in_or_app. right. exact Hb.
  Qed.

  Lemma rp_fail599 :
    forall m1 mo1 (s1' : PState) (p : bptr) (A nA : Z) (R' : membio) (clo : list cell) (j2 : list byte)
           (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v u3 u4 u5 u6 : word),
      0 <= nA <= 512 * 33 ->
      hs_RHEAP H s1' ((p, A, nA) :: L0) m1 -> hs_KREL H s1' mo1 -> hs_MPRES H mo mo1 ->
      MEMBIO LB m1 mb R' -> mb_static R R' -> bytes_at rsegs m1 (mb_buf R) ds ->
      cells_size clo = 120%nat -> rw_cells rsegs m1 SP' clo -> rw_cells rsegs m1 (bv_unsigned sp + -2232) (CB 2128 j2 :: SAVES) ->
      (exists errv1, rw_cells rsegs m1 RERRNO [C4 errv1]) -> MEMFLAG m1 1 -> IMPL_mem m1 -> GOT_mem m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo SP' -> hs_rauxv_ok H m1 B ->
      xpres LB (bv_unsigned sp) (MEMBIO_foot mb R) m m1 ->
      hs_SR H POST (mkCfg (MS (mkR (Z_to_bv 64 RP_599_R1) (Z_to_bv 64 SP') gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7
                                    s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v u3 u4 u5 u6)
                               F (Z_to_bv 64 P_ERR_new) fc None m1 (seg_rom rsegs)) mo1).
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HRE HX CERTO3 PERM.
    apply (rp_fail_lbuf 599 R_INTERNAL_ERROR RP_599_R1 RP_599_R2); [clear; lia| unfold R_INTERNAL_ERROR; clear; lia| unfold RP_599_R1; clear; lia| reflexivity
      | unfold RP_599_R2; clear; lia| reflexivity| exact rp_g599a| exact rp_g599b].
  Qed.

  (* [comment removed for export] *)
  Definition rp_okK : Prop :=
    forall (k n : Z) (m' : mem) (mo' : Model) (s' : PState) (p : bptr) (A : Z) (R' : membio) (junk j0 j2 : list byte)
           (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
      0 <= k <= 31 -> n = mb_len R - 512 * k -> 1 <= n <= 512 -> mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN ->
      hs_RHEAP H s' ((p, A, 512 * (k + 1)) :: L0) m' -> hs_KREL H s' mo' -> hs_MPRES H mo mo' ->
      MEMBIO LB m' mb R' -> mb_static R R' -> mb_pos R' = mb_len R ->
      bytes_at rsegs m' (mb_buf R) ds -> bytes_at rsegs m' A ds -> rw_cells rsegs m' (A + mb_len R) [CB (Z.to_nat (512 * (k + 1) - mb_len R)) junk] ->
      rw_cells rsegs m' SP' [CB 88 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 0)] ->
      rw_cells rsegs m' RBP [C8 (wz n)] -> rw_cells rsegs m' (bv_unsigned sp + -2232) (CB 2128 j2 :: SAVES) ->
      (exists errv', rw_cells rsegs m' RERRNO [C4 errv']) -> MEMFLAG m' 1 -> LIBMID LIB m' M ->
      mem_inv rsegs m' -> stk rsegs m' lo SP' -> hs_rauxv_ok H m' B ->
      xpres LB (bv_unsigned sp) (MEMBIO_foot mb R) m m' ->
      hs_SR H POST (mkCfg (MS (mkR (Z_to_bv 64 LD_RD) (Z_to_bv 64 SP') gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) (Z_to_bv 64 OSSL_ECH_MAX_ECHCONFIG_LEN) b1 b2 b3 b4 b5 b6 b7
                                    (Z_to_bv 64 mb) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (32 - k)) (Z_to_bv 64 (mb_len R))
                                    (Z_to_bv 64 (A + 512 * k)) (Z_to_bv 64 (- (512 * k))) (Z_to_bv 64 (512 * k)) (Z_to_bv 64 (- (512 * k))) u3 u4 u5 u6)
                               F (Z_to_bv 64 LD_OK) fc None m' (seg_rom rsegs)) mo').

  (* [comment removed for export] *)
  Lemma rp_b2b : rp_okK ->
    hs_SR H POST (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 P_OSSL_ECHSTORE_read_echconfiglist) fc None m (seg_rom rsegs)) mo).
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HRE HX CERTO3 PERM.
    intros KOK.
    destruct rc_facts as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    pose proof rc_stack as (STKR & STKL & STKZ).
    hcb. pose proof (word_range sp) as SPR.
    assert (SUB0' : forall b, In b (blocks_MEMBIO mb R) -> In b LB).
    { intros b Hb. destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _). unfold blocks_MEMBIO in Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption. }
    pose proof SO as (SC & SINB & _). rewrite SE in SC.
    pose proof MBO as MB0. destruct MB0 as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & XB1 & XB2 & XB3 & XB4 & POSR & LENR & BUFP & BUFH & _).
    pose proof SBR as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof XB1 as (W1 & _ & _ & W4 & O1). pose proof XB3 as (_ & _ & _ & _ & O3). unfold BIO_SIZE in W4, O1. unfold BUFMEM_SIZE in O3.
    pose proof LM as (IM & MF & _ & _ & _ & _ & _ & _ & GM & _ & _ & MM & _). rewrite MF1 in MF.
    rewrite A0, A1, TP. pose proof ERR as ERR0. rewrite TP, errno_RATP in ERR0.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply rp_seg1 with (lo := lo); [unfold STORE_SIZE in Q4; clear - Q1 Q4 HCEILB; lia| clear - W1 W4 HCEILB; lia| exact ST| exact CEIL| clear - LO STK0; lia| exact MI]|].
    intros ms1 (m1 & j1 & j2 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (XPa : xpres L0 (bv_unsigned sp) [] m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| apply Forall_cons; [left; cbn; clear - CEIL LO STK0; lia| apply Forall_nil]| exact BEL0]. }
    assert (HP1 : hs_RHEAP H s L0 m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; clear - CEIL LO STK0; lia| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. clear - SPB CEIL HCEILB LO STK0; apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    apply (rw_cells_transport rsegs _ m m1 _ _ ERR0) in MU1 as ERR1; [| exact WM1| clear - CEIL HCEILB LO STK0; img_static].
    assert (MFa : MEMFLAG m1 1).
    { destruct MF as (fb & FB & V). exists fb. split; [| exact V]. eapply rw_cells_transport; [exact FB| exact MU1| exact WM1| clear - CEIL HCEILB LO STK0; img_static]. }
    apply (rw_cells_transport rsegs _ m m1 _ _ IM) in MU1 as IM1; [| exact WM1| clear - CEIL HCEILB LO STK0; img_static].
    apply (rw_cells_transport rsegs _ m m1 _ _ GM) in MU1 as GM1; [| exact WM1| clear - CEIL HCEILB LO STK0; img_static].
    (* [comment removed for export] *)
    pose proof (czalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (sr_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := L0) (s := s) (num := 512) (size := 1) (v := 1) (errv := errv); clear CZ; try reflexivity.
      all: try first [exact HP1| exact KREL| exact AUX1| exact MI1| exact IM1| exact GM1| exact MFa| exact CEIL].
      all: lazymatch goal with
           | |- 1 <= _ < _ => clear; lia
           | |- lb_bytes _ + _ <= _ => unfold L0; unfold mid_bytes, DECODE_BYTES, ERRSTR_BYTES in BUD; pose proof (errph_nonneg (mid_err M)) as (EN1 & _); pose proof (ctxph_nonneg3 (mid_ctx M)) as (CN1 & _); clear - BUD EN1 CN1; lia
           | |- Z.of_nat _ + _ <= _ => unfold L0; unfold mid_cnt, DECODE_CNT, ERRSTR_CNT in BUDC; pose proof (errph_nonneg (mid_err M)) as (_ & EN2 & _); pose proof (ctxph_nonneg3 (mid_ctx M)) as (_ & CN2 & _); clear - BUDC EN2 CN2; lia
           | |- lb_big _ + _ <= _ => unfold L0; unfold mid_big, DECODE_BIG in BUDG; rewrite big1_small by (unfold BIGB; clear; lia); pose proof (errph_nonneg (mid_err M)) as (_ & _ & EN3); pose proof (ctxph_nonneg3 (mid_ctx M)) as (_ & _ & CN3); clear - BUDG EN3 CN3; lia
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST1
           | |- lo <= _ => rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - LO STKZ; lia
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR1
           | |- _ => idtac
           end. }
    clear CZ. intros [ms2 mo2] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & errv2 & A & p & s2' & -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & BRA & HP2 & ZK & MF2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST2, XP2 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR2.
    change (bv_unsigned sp + -2352) with SP' in ST2, XP2.
    pose proof BRA as (C1 & C2 & C3 & C4 & C5).
    change (bv_unsigned sp + -2352) with SP'. change (bv_unsigned sp + -2240) with RBP.
    destruct (lad_head_facts H HX L0 _ _ _ _ _ HP2) as (_ & BHA & NIPA & DISJA & _).
    (* [comment removed for export] *)
    assert (XP12 : xpres L0 SP' [] m1 m2) by (eapply xpres_drop_memflag; [rewrite app_nil_r; exact XP2| exact MFa| exact MF2]).
    assert (FR2 : rw_cells rsegs m2 SP' (CB 112 j1 :: C8 (Z_to_bv 64 0) :: CB 2128 j2 :: SAVES)).
    { eapply xpres_rw_cells'; [exact XP12| unfold SAVES; exact FR1| left; clear; lia| apply Forall_nil]. }
    assert (MBO2 : MEMBIO LB m2 mb R).
    { eapply (MEMBIO_frame0 LB LB SP'); [| exact SUB0'| eapply xpres_weaken; [exact XP12| clear; lia| exact SUB0| intros q Hq; exact Hq]].
      eapply (MEMBIO_frame0 LB LB (bv_unsigned sp)); [exact MBO| exact SUB0'| eapply xpres_weaken; [exact XPa| clear; lia| exact SUB0| intros q Hq; exact Hq]]. }
    assert (DS1 : bytes_at rsegs m1 (mb_buf R) ds).
    { eapply bytes_at_transport; [exact DS| exact MU1| unfold zlength in DSL; rewrite DSL; cbn; clear - BUFH CEIL LO STK0; lia]. }
    assert (DS2 : bytes_at rsegs m2 (mb_buf R) ds).
    { destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      - assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; lia]). rewrite DN in *. apply bytes_at_nil. clear - BUFP BUFH HCEILB L0Z. lia.
      - destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN _]].
        eapply xpres_bytes_at'; [exact XP12| exact DS1| right; right; exists (pD, mb_buf R, mb_len R); split; [exact (SUB0 _ PIN)| cbn; unfold zlength in DSL; rewrite DSL; clear; lia]| apply Forall_nil]. }
    assert (LM2 : LIBMID LIB m2 M).
    { rewrite (mid_eta M), MF1. eapply (LIBMID_mf LIB L0 SP'); [| exact XP2| intros b Hb; exact (SUB0 _ (SUBL _ Hb))| exact MF2].
      eapply (LIBMID_xpres0 LIB L0 (bv_unsigned sp)); [exact LM| exact XPa| intros b Hb; exact (SUB0 _ (SUBL _ Hb))]. }
    pose proof LM2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MM2 & _).
    assert (XA2 : xpres LB (bv_unsigned sp) (MEMBIO_foot mb R) m m2).
    { eapply xpres_trans; [eapply xpres_weaken; [exact XPa| clear; lia| exact SUB0| intros q Hq; destruct Hq]|].
      eapply xpres_weaken; [exact XP12| unfold SP'; clear; lia| exact SUB0| intros q Hq; destruct Hq]. }
    clear XP2 MU1 WM1 FR1 HP1 AUX1 ERR1 MFa IM1 GM1 MI1 ST1 XPa DS1.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 RP_R1)) with (Z_to_bv 64 RP_R1) by (symmetry; apply ret_pc_even; [unfold RP_R1; lia| reflexivity]).
    eapply (sr_evt_krel H HH); [exact KREL2| eapply rp_seg2; [clear - C1 C4 HCEILB; lia| exact MI2]|]. intros ms3 ->.
    pose proof bioeof_mem_spec as EF. unfold bioeof_mem_stmt in EF.
    eapply (sr_evt_krel H HH); [exact KREL2| |].
    { eapply EF with (lo := lo) (LB := LB) (a := mb) (R := R); clear EF; try reflexivity.
      all: try first [exact MBO2| exact MBB| exact MBS| exact MM2| exact MI2| exact CEIL].
      all: lazymatch goal with
           | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST2
           | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); revert STKL LO; unfold LAD_STACK; clear; intros; lia
           | |- _ mod 2 = 0 => unfold RP_R2; rewrite unsigned_lit by (clear; lia); reflexivity
           end. }
    clear EF. intros ms4 PO. unfold memctrl_post in PO.
    destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & MBO3).
    unfold SP' in MU3, ST3. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in MU3, ST3 by (clear - SPR LO STK0 LO0; lia). fold SP' in MU3, ST3.
    (* [comment removed for export] *)
    assert (HP3 : hs_RHEAP H s2' ((p, A, 512 * 1) :: L0) m3).
    { eapply (HH_RHEAP_frame H HH); [exact HP2| exact MU3| exact WM3|]. apply Forall_cons; [left; cbn; unfold SP'; clear - CEIL; lia| apply Forall_nil]. }
    assert (AUX3 : hs_rauxv_ok H m3 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL, SP'. clear - SPB CEIL HCEILB LO STK0; apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    apply (rw_cells_transport rsegs _ m2 m3 _ _ ERR2) in MU3 as ERR3; [| exact WM3| clear - CEIL HCEILB; img_static].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ FR2) in MU3 as FR3; [| exact WM3| unfold SP'; cbn; clear; lia].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ ZK) in MU3 as ZK3; [| exact WM3| cbn; clear - BHA CEIL; lia].
    apply (bytes_at_transport rsegs _ m2 m3 _ _ DS2) in MU3 as DS3; [| unfold zlength in DSL; rewrite DSL; cbn; clear - BUFH CEIL; lia].
    assert (MF3 : MEMFLAG m3 1).
    { destruct MF2 as (fb & FB & V). exists fb. split; [| exact V]. eapply rw_cells_transport; [exact FB| exact MU3| exact WM3| clear - CEIL HCEILB; img_static]. }
    apply (rw_cells_transport rsegs _ m2 m3 _ _ IM2) in MU3 as IM3; [| exact WM3| clear - CEIL HCEILB; img_static].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ GM2) in MU3 as GM3; [| exact WM3| clear - CEIL HCEILB; img_static].
    assert (XP23 : xpres L0 SP' [] m2 m3).
    { eapply xpres_of_munch; [exact MU3| exact WM3| apply Forall_cons; [left; cbn; unfold SP'; clear - CEIL; lia| apply Forall_nil]| exact BEL0]. }
    pose proof (LIBMID_xpres0 LIB L0 SP' m2 m3 M LM2 XP23 ltac:(intros b Hb; exact (SUB0 _ (SUBL _ Hb)))) as LM3.
    assert (XA3 : xpres LB (bv_unsigned sp) (MEMBIO_foot mb R) m m3).
    { eapply xpres_trans; [exact XA2|]. eapply xpres_weaken; [exact XP23| unfold SP'; clear; lia| exact SUB0| intros q Hq; destruct Hq]. }
    (* [comment removed for export] *)
    pose proof (proj1 (rw_cells_app rsegs m3 _ [CB 112 j1; C8 (Z_to_bv 64 0)] (CB 2128 j2 :: SAVES)) FR3) as [FRlo3 FRhi3]. cbn [cells_size csize Nat.add] in FRhi3.
    replace (SP' + Z.of_nat (120 + 0)) with (bv_unsigned sp + -2232) in FRhi3 by (unfold SP'; clear; lia).
    assert (RV : mem_ctrl_rv R BIO_CTRL_EOF = if mb_len R =? 0 then 1 else 0) by (unfold mem_ctrl_rv, mb_avail; rewrite MP0, Z.sub_0_r; reflexivity).
    rewrite RV. clear RV.
    replace (ret_pc (Z_to_bv 64 RP_R2)) with (Z_to_bv 64 RP_R2) by (symmetry; apply ret_pc_even; [unfold RP_R2; lia| reflexivity]).
    destruct (Z.eqb_spec (mb_len R) 0) as [L0Z|LNZ].
    - (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL2| eapply ld_segc1 with (e := 1); [reflexivity| clear; lia| exact MI3]|]. intros ms5 ->.
      pose proof bioeof_mem_spec as EF. unfold bioeof_mem_stmt in EF.
      eapply (sr_evt_krel H HH); [exact KREL2| |].
      { eapply EF with (lo := lo) (LB := LB) (a := mb) (R := R); clear EF; try reflexivity.
        all: try first [exact MBO3| exact MBB| exact MBS| exact MI3| exact CEIL].
        all: lazymatch goal with
             | |- METH_mem _ => destruct LM3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MM3 & _); exact MM3
             | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST3
             | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); revert STKL LO; unfold LAD_STACK; clear; intros; lia
             | |- _ mod 2 = 0 => unfold LD_RC; rewrite unsigned_lit by (clear; lia); reflexivity
             end. }
      clear EF. intros ms6 PO. unfold memctrl_post in PO.
      destruct PO as (x0 & x1 & x2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & MBO4).
      unfold SP' in MU4, ST4. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in MU4, ST4 by (clear - SPR LO STK0 LO0; lia). fold SP' in MU4, ST4.
      assert (XP34 : xpres L0 SP' [] m3 m4).
      { eapply xpres_of_munch; [exact MU4| exact WM4| apply Forall_cons; [left; cbn; unfold SP'; clear - CEIL; lia| apply Forall_nil]| exact BEL0]. }
      eapply (rp_fail595 m4 mo2 s2' p A (512 * 1) _ R [CB 112 j1; C8 (Z_to_bv 64 0)] j2).
      all: try first [exact KREL2| exact MP2| exact MBO4| apply mb_static_refl| reflexivity| exact MI4| exact ST4].
      + eapply (HH_RHEAP_frame H HH); [exact HP3| exact MU4| exact WM4|]. apply Forall_cons; [left; cbn; unfold SP'; clear - CEIL; lia| apply Forall_nil].
      + eapply bytes_at_transport; [exact DS3| exact MU4| unfold zlength in DSL; rewrite DSL; cbn; clear - BUFH CEIL; lia].
      + eapply rw_cells_transport; [exact FRlo3| exact MU4| exact WM4| unfold SP'; cbn; clear; lia].
      + eapply rw_cells_transport; [exact FRhi3| exact MU4| exact WM4| unfold SP'; cbn; clear; lia].
      + exists errv2. eapply rw_cells_transport; [exact ERR3| exact MU4| exact WM4| clear - CEIL HCEILB; img_static].
      + destruct MF3 as (fb & FB & V). exists fb. split; [| exact V]. eapply rw_cells_transport; [exact FB| exact MU4| exact WM4| clear - CEIL HCEILB; img_static].
      + eapply rw_cells_transport; [exact IM3| exact MU4| exact WM4| clear - CEIL HCEILB; img_static].
      + eapply rw_cells_transport; [exact GM3| exact MU4| exact WM4| clear - CEIL HCEILB; img_static].
      + eapply (HH_rauxv_frame H HH); [exact AUX3| exact MU4| exact WM4|]. unfold RAUXV_CELL, SP'. clear - SPB CEIL HCEILB LO STK0; apply Forall_cons; [cbn; lia| apply Forall_nil].
      + eapply xpres_trans; [exact XA3|]. eapply xpres_weaken; [exact XP34| unfold SP'; clear; lia| exact SUB0| intros q Hq; destruct Hq].
    - (* [comment removed for export] *)
      unfold SP', RBP.
      eapply (sr_evt_krel H HH); [exact KREL2| eapply rp_seg3 with (lo := lo) (saves := SAVES); [exact sp| clear - Q1 Q4 HCEILB; unfold STORE_SIZE in Q4; lia| reflexivity| exact FR3| exact ST3| exact CEIL| clear - LO STK0; lia| exact MI3]|].
      intros ms5 (m4 & j0 & -> & MU4 & WM4 & MI4 & ST4 & FR4).
      fold SP' RBP. change (bv_unsigned sp + -2352) with SP' in FR4, ST4. change (bv_unsigned sp + -2352) with SP'. change (bv_unsigned sp + -2240) with RBP.
      assert (XP34 : xpres L0 (bv_unsigned sp) [] m3 m4).
      { eapply xpres_of_munch; [exact MU4| exact WM4| apply Forall_cons; [left; cbn; clear - CEIL LO STK0; lia| apply Forall_nil]| exact BEL0]. }
      assert (HP4 : hs_RHEAP H s2' ((p, A, 512 * (0 + 1)) :: L0) m4).
      { eapply (HH_RHEAP_frame H HH); [exact HP3| exact MU4| exact WM4|]. apply Forall_cons; [left; cbn; clear - CEIL LO STK0; lia| apply Forall_nil]. }
      assert (AUX4 : hs_rauxv_ok H m4 B).
      { eapply (HH_rauxv_frame H HH); [exact AUX3| exact MU4| exact WM4|]. unfold RAUXV_CELL. clear - SPB CEIL HCEILB LO STK0; apply Forall_cons; [cbn; lia| apply Forall_nil]. }
      apply (rw_cells_transport rsegs _ m3 m4 _ _ ERR3) in MU4 as ERR4; [| exact WM4| clear - CEIL HCEILB LO STK0; img_static].
      apply (rw_cells_transport rsegs _ m3 m4 _ _ ZK3) in MU4 as ZK4; [| exact WM4| cbn; clear - BHA CEIL LO STK0; lia].
      apply (bytes_at_transport rsegs _ m3 m4 _ _ DS3) in MU4 as DS4; [| unfold zlength in DSL; rewrite DSL; cbn; clear - BUFH CEIL LO STK0; lia].
      assert (MF4 : MEMFLAG m4 1).
      { destruct MF3 as (fb & FB & V). exists fb. split; [| exact V]. eapply rw_cells_transport; [exact FB| exact MU4| exact WM4| clear - CEIL HCEILB LO STK0; img_static]. }
      apply (rw_cells_transport rsegs _ m3 m4 _ _ IM3) in MU4 as IM4; [| exact WM4| clear - CEIL HCEILB LO STK0; img_static].
      apply (rw_cells_transport rsegs _ m3 m4 _ _ GM3) in MU4 as GM4; [| exact WM4| clear - CEIL HCEILB LO STK0; img_static].
      assert (MBO4 : MEMBIO LB m4 mb R).
      { eapply (MEMBIO_frame0 LB LB (bv_unsigned sp)); [exact MBO3| exact SUB0'| eapply xpres_weaken; [exact XP34| clear; lia| exact SUB0| intros q Hq; exact Hq]]. }
      pose proof (LIBMID_xpres0 LIB L0 (bv_unsigned sp) m3 m4 M LM3 XP34 ltac:(intros b Hb; exact (SUB0 _ (SUBL _ Hb)))) as LM4.
      pose proof LM4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MM4 & _).
      assert (XA4 : xpres LB (bv_unsigned sp) (MEMBIO_foot mb R) m m4).
      { eapply xpres_trans; [exact XA3|]. eapply xpres_weaken; [exact XP34| clear; lia| exact SUB0| intros q Hq; destruct Hq]. }
      (* [comment removed for export] *)
      pose proof (proj1 (rw_cells_app rsegs m4 _ [CB 88 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 0)] (C8 (Z_to_bv 64 0) :: CB 2128 j2 :: SAVES)) FR4) as [FRlo4 FR4b].
      cbn [cells_size csize Nat.add] in FR4b.
      pose proof (proj1 (rw_cells_app rsegs m4 _ [C8 (Z_to_bv 64 0)] (CB 2128 j2 :: SAVES)) FR4b) as [RB4 FRhi4]. cbn [cells_size csize Nat.add] in FRhi4.
      replace (SP' + Z.of_nat (112 + 0)) with RBP in RB4 by (unfold SP', RBP; clear; lia).
      replace (SP' + Z.of_nat (112 + 0) + Z.of_nat (8 + 0)) with (bv_unsigned sp + -2232) in FRhi4 by (unfold SP'; clear; lia). clear FR4b FR4.
      (* [comment removed for export] *)
      assert (CARRY : forall m5 (rbx : Z), xpres L0 SP' ((bv_unsigned sp + -2240, bv_unsigned sp + -2232) :: MEMBIO_foot mb R) m4 m5 ->
                rw_cells rsegs m5 RBP [C8 (wz rbx)] -> hs_rauxv_ok H m5 B ->
                   rw_cells rsegs m5 SP' [CB 88 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 0); C8 (wz rbx)]
                /\ rw_cells rsegs m5 (bv_unsigned sp + -2232) (CB 2128 j2 :: SAVES)
                /\ MEMFLAG m5 1 /\ LIBMID LIB m5 M /\ xpres LB (bv_unsigned sp) (MEMBIO_foot mb R) m m5).
      { intros m5 rbx XP5 RB5 AUX5.
        assert (FXW : forall A' n', SP' <= A' -> (A' + n' <= RBP \/ RBP + 8 <= A') ->
                  Forall (fun iv : Z * Z => A' + n' <= fst iv \/ snd iv <= A') ((bv_unsigned sp + -2240, bv_unsigned sp + -2232) :: MEMBIO_foot mb R)).
        { intros A' n' HA HR. apply Forall_cons; [cbn; unfold RBP in HR; clear - HR; lia|]. unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE.
          pose proof (BEL0 _ (SUB0 _ I1)) as E1. pose proof (BEL0 _ (SUB0 _ I3)) as E3. cbn [blk_addr blk_size fst snd] in E1, E3. unfold BIO_SIZE, BUFMEM_SIZE in E1, E3.
          apply Forall_cons; [cbn; unfold SP' in HA; clear - HA E1 CEIL LO STK0; lia|]. apply Forall_cons; [cbn; unfold SP' in HA; clear - HA E3 CEIL LO STK0; lia| apply Forall_nil]. }
        assert (FRlo5 : rw_cells rsegs m5 SP' [CB 88 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 0)]).
        { eapply xpres_rw_cells'; [exact XP5| exact FRlo4| left; clear; lia| apply FXW; [clear; lia| left; cbn; unfold SP', RBP; clear; lia]]. }
        split. { apply (proj2 (rw_cells_app rsegs m5 _ [CB 88 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 0)] [C8 (wz rbx)])). split; [exact FRlo5|].
                 cbn [cells_size csize Nat.add]. replace (SP' + Z.of_nat (112 + 0)) with RBP by (unfold SP', RBP; clear; lia). exact RB5. }
        split. { eapply xpres_rw_cells'; [exact XP5| exact FRhi4| left; unfold SP'; clear; lia| apply FXW; [unfold SP'; clear; lia| right; unfold RBP; clear; lia]]. }
        assert (MF5 : MEMFLAG m5 1).
        { destruct MF4 as (fb & FB & V). exists fb. split; [| exact V].
          eapply xpres_rw_cells'; [exact XP5| exact FB| right; left; unfold A_mem_inited, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; cbn; clear; lia|].
          apply Forall_cons; [cbn; unfold A_mem_inited, RBP; clear - CEIL HCEILB LO STK0; lia|].
          unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE, A_mem_inited. apply Forall_cons; [cbn; clear - O1; lia|]. apply Forall_cons; [cbn; clear - O3; lia| apply Forall_nil]. }
        split; [exact MF5|]. split.
        { pose proof (LIBMID_mf_X LIB L0 SP' ((bv_unsigned sp + -2240, bv_unsigned sp + -2232) :: MEMBIO_foot mb R) m4 m5 M LM4
                        ltac:(eapply xpres_weaken; [exact XP5| clear; lia| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app; right; exact Hq])
                        ltac:(intros b Hb; exact (SUB0 _ (SUBL _ Hb))) MF5) as K.
          rewrite (mid_eta M), MF1. rewrite (mid_eta M) in K. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in K. apply K.
          - intros q Hq. unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE, IMG_LO, IMG_HI in *. cbn [rin_ivs fst snd] in Hq. clear - Hq O1 O3 CEIL HCEILB LO STK0. lia.
          - intros q b Hq Hb. cbn [rin_ivs fst snd] in Hq. unfold MEMBIO_foot in Hq. cbn [rin_ivs fst snd] in Hq.
            pose proof (BEL0 _ (SUB0 _ (SUBL _ Hb))) as Bb.
            pose proof (DJA b (mb_id R, mb, BIO_SIZE) Hb ltac:(right; left; reflexivity)) as D1.
            pose proof (DJA b (mb_bmid R, mb_bm R, BUFMEM_SIZE) Hb ltac:(right; right; right; left; reflexivity)) as D3.
            cbn [blk_addr blk_size fst snd] in D1, D3. unfold BIO_SIZE, BUFMEM_SIZE in *. clear - Hq Bb D1 D3 CEIL LO STK0. lia. }
        eapply xpres_trans; [exact XA4|].
        eapply (xpres_raise_sp LB SP' (bv_unsigned sp) (bv_unsigned sp + -2240)).
        - replace (bv_unsigned sp + -2240 + 8) with (bv_unsigned sp + -2232) by (clear; lia).
          eapply xpres_weaken; [exact XP5| clear; lia| exact SUB0| intros q Hq; exact Hq].
        - unfold SP'; clear; lia.
        - clear; lia.
        - unfold IMG_HI. clear - CEIL HCEILB LO STK0. lia.
        - intros b Hb. pose proof (BEL0 _ (SUB0 _ Hb)). clear - H0 CEIL LO STK0. lia. }
      (* [comment removed for export] *)
      lazymatch goal with |- hs_SR _ _ {| cfg_ms := ?c ; cfg_model := _ |} =>
        replace c with (lad_entry sp gp F fc mb 0 m4 A s7 w0 w1 w2 d4 d5 d6 d7 w3 w4 w5 w6)
          by (unfold lad_entry, OSSL_ECH_BUFCHUNK; rewrite Z.mul_0_r, Z.add_0_r, Z.sub_0_r, Z.opp_0; reflexivity) end.
      assert (PAYL' : 1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB) by (intros K; destruct (PAYL K) as [pD [PIN _]]; exists pD; exact PIN).
      pose proof (errph_nonneg (mid_err M)) as (EN1 & EN2 & EN3). pose proof (ctxph_nonneg3 (mid_ctx M)) as (CN1 & CN2 & CN3).
      eapply (lad_loop H HX sp gp F fc mb lo B R ds LB L0 m4 mo MBB MBS DSL SUB0 PAYL') with (fuel := 32%nat) (s := s2') (p := p) (R' := R).
      + unfold L0. unfold mid_bytes, DECODE_BYTES, ERRSTR_BYTES in BUD. clear - BUD EN1 CN1. lia.
      + unfold L0. unfold mid_cnt, DECODE_CNT, ERRSTR_CNT in BUDC. clear - BUDC EN2 CN2. lia.
      + unfold L0. unfold mid_big, DECODE_BIG in BUDG. clear - BUDG EN3 CN3. lia.
      + exact SPB.
      + exact CEIL.
      + clear - LO STKL. lia.
      + reflexivity.
      + clear; lia.
      + (* [comment removed for export] *) unfold LAD. rewrite Z.mul_0_r, Z.add_0_r.
        split; [exact HP4|]. split; [exact MBO4|]. split; [apply mb_static_refl|]. split; [exact MP0|]. split; [clear - LNZ LENR; lia|].
        split; [exact DS4|]. split; [cbn [Z.to_nat firstn]; apply bytes_at_nil; clear - C1 C4 HCEILB; lia|].
        split; [exists (zeros (Z.to_nat 512)); exact ZK4|]. split; [exists 0; exact RB4|]. split; [exists errv2; exact ERR4|].
        split; [exact MM4|]. split; [exact IM4|]. split; [exact GM4|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact AUX4| apply xpres_refl].
      + exact KREL2.
      + exact MP2.
      + (* [comment removed for export] *)
        unfold lad_doneK. clear MBO4 DS4 ZK4 ERR4 IM4 GM4 MI4 ST4 AUX4 HP4.
        intros k n m5 mo5 s5' p5 A5 R5 junk s7v x0 x1 x2 e1 e2 e3 e4 e5 e6 e7 x3 x4 x5 x6 KR NEQ NR HP5 KREL5 MP5 MBO5 MST5 POS5 DS5 ALL5 JK5 RBc5 [errv5 ERR5] ME5 IM5 GM5 MI5 ST5 AUX5 XP5.
        destruct (CARRY m5 n XP5 RBc5 AUX5) as (CLO5 & FRhi5 & MF5 & LM5 & XA5).
        destruct (Z_lt_ge_dec (mb_len R) OSSL_ECH_MAX_ECHCONFIG_LEN) as [GOK|GBIG].
        * eapply (sr_evt_krel H HH); [exact KREL5| eapply ld_segE_ok with (K := 512 * k) (n := n); [clear; lia| clear - NR; lia| clear - KR; lia| rewrite NEQ; unfold OSSL_ECH_MAX_ECHCONFIG_LEN in *; clear - GOK KR; lia| exact RBc5| exact MI5]|].
          intros ms6 ->. replace (n + 512 * k) with (mb_len R) by (clear - NEQ; lia).
          pose proof (proj1 (rw_cells_app rsegs m5 _ [CB 88 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 0)] [C8 (wz n)]) CLO5) as [FRlo5 _].
          unfold rp_okK in KOK. eapply (KOK k n m5 mo5 s5' p5 A5 R5 junk j0 j2); try eassumption.
          exists errv5; exact ERR5.
        * eapply (sr_evt_krel H HH); [exact KREL5| eapply ld_segE_big with (K := 512 * k) (n := n); [clear; lia| clear - NR; lia| clear - KR; lia| rewrite NEQ; unfold OSSL_ECH_MAX_ECHCONFIG_LEN in *; clear - GBIG KR; lia| exact RBc5| exact MI5]|].
          intros ms6 ->. change LD_RN with RP_599_R1.
          eapply (rp_fail599 m5 mo5 s5' p5 A5 (512 * (k + 1)) R5 _ j2); try eassumption.
          -- clear - KR; lia.
          -- reflexivity.
          -- exists errv5; exact ERR5.
      + (* [comment removed for export] *)
        unfold lad_capK. clear MBO4 DS4 ZK4 ERR4 IM4 GM4 MI4 ST4 AUX4 HP4.
        intros m5 mo5 s5' p5 A5 rv R5 x0 x1 x2 e1 e2 e3 e4 e5 e6 e7 s8v s9v s10v s11v x3 x4 x5 x6 HP5 KREL5 MP5 MBO5 MST5 POS5 KL5 DS5 [rb5 RBc5] [errv5 ERR5] ME5 IM5 GM5 MI5 ST5 AUX5 XP5.
        destruct (CARRY m5 rb5 XP5 RBc5 AUX5) as (CLO5 & FRhi5 & MF5 & LM5 & XA5).
        eapply (rp_fail595 m5 mo5 s5' p5 A5 (512 * 33) rv R5 _ j2); try eassumption.
        * reflexivity.
        * exists errv5; exact ERR5.
  Qed.
End RC.

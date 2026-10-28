(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib
  ECH_ALibMF ECH_Iface ECH_AStmt_C1 ECH_AC1_zalloc ECH_AC1_free ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C7 ECH_AStmt_C13 ECH_AKit ECH_AKitSeg ECH_AsKit
  ECH_AC7_kit ECH_AC7_rd ECH_AC7_rd2 ECH_AC7_bioread ECH_AKitSeg ECH_ARostr ECH_ALibMid ECH_AC11_fail ECH_AC14_bio2buf_seg ECH_AC14_ladder_seg ECH_AC14_ladloop ECH_AC14_fmt_seg ECH_AC14_flat_seg ECH_AStmt_C14.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition S_ARP_FILE : list byte := Eval vm_compute in img_cstr ARP_FILE 64.
Definition K_ARP_FILE : list byte := Eval vm_compute in img_slack ARP_FILE (length S_ARP_FILE).
Definition S_ARP_FUNC : list byte := Eval vm_compute in img_cstr ARP_FUNC 64.
Definition K_ARP_FUNC : list byte := Eval vm_compute in img_slack ARP_FUNC (length S_ARP_FUNC).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section K.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Lemma R_ARP_FILE : AROSTR ARP_FILE S_ARP_FILE K_ARP_FILE.
  Proof. eapply AROSTR_intro_hull; [apply ROSTR_of_image; vm_compute; reflexivity| unfold aglobals; cbn; do 52 right; left; reflexivity| ..];
    vm_compute; intros X; discriminate X. Qed.
  Lemma R_ARP_FUNC : AROSTR ARP_FUNC S_ARP_FUNC K_ARP_FUNC.
  Proof. eapply AROSTR_intro; [apply ROSTR_of_image; vm_compute; reflexivity| unfold aglobals; cbn; tauto| vm_compute; intros X; discriminate X| vm_compute; intros X; discriminate X]. Qed.
  Lemma S_ARP_FILE_len : Z.of_nat (length S_ARP_FILE) = 19. Proof. reflexivity. Qed.
  Lemma S_ARP_FUNC_len : Z.of_nat (length S_ARP_FUNC) = 27. Proof. reflexivity. Qed.

  Lemma mid_eta : forall M, M = mkMID (mid_flag M) (mid_ctx M) (mid_err M) (mid_E M) (mid_vdso M).
  Proof. intros [f c e E v]; reflexivity. Qed.

  Lemma store_empty_eq : forall S, es_entries S = 0 -> es_entries_o S = None -> S = store_empty (es_id S).
  Proof. intros [e eo id] E1 E2. cbn in *. subst. reflexivity. Qed.

  Lemma abyte_eq_of_unsigned : forall (b : byte) z, bv_unsigned b = z -> b = Z_to_bv 8 z.
  Proof. intros b z E. subst z. symmetry. apply (bitvector.definitions.Z_to_bv_bv_unsigned 8). Qed.

  (* [comment removed for export] *)
  Lemma amemflag_same : forall m m', MEMFLAG m 1 -> MEMFLAG m' 1 ->
    m' (wa A_mem_inited) = m (wa A_mem_inited) /\ (wview asegs m (wa A_mem_inited) <> None -> wview asegs m' (wa A_mem_inited) <> None).
  Proof.
    intros m m' (fb & [[_ (_ & _ & B1)] _] & V1 & _) (fb' & [[_ (_ & _ & B2)] (_ & _ & W2)] & V2 & _).
    cbn [cells_bytes cbytes app length cells_size csize Nat.add] in *.
    specialize (B1 0%nat ltac:(lia)). specialize (B2 0%nat ltac:(lia)). cbn [nth_error Z.of_nat] in B1, B2.
    replace (A_mem_inited + 0) with A_mem_inited in B1, B2 by lia.
    assert (ROM : seg_rom asegs (wa A_mem_inited) = Some (b8 0)) by (vm_compute; reflexivity).
    assert (E : fb = fb') by (rewrite (abyte_eq_of_unsigned fb 1 V1), (abyte_eq_of_unsigned fb' 1 V2); reflexivity). subst fb'.
    unfold mrd in B1, B2. split.
    - destruct (m (wa A_mem_inited)) as [x1|] eqn:E1, (m' (wa A_mem_inited)) as [x2|] eqn:E2; try congruence;
        exfalso; rewrite ROM in *; assert (EF : fb = b8 0) by congruence; rewrite EF in V1; vm_compute in V1; discriminate.
    - intros _. specialize (W2 0 ltac:(lia)). replace (A_mem_inited + 0) with A_mem_inited in W2 by lia. exact W2.
  Qed.

  (* [comment removed for export] *)
  Lemma axpres_drop_memflag : forall LB SP X m m',
    xpres H LB SP (memflag_foot ++ X) m m' -> MEMFLAG m 1 -> MEMFLAG m' 1 -> xpres H LB SP X m m'.
  Proof.
    intros LB SP X m m' XP F0 F1 a Ha [HC HX].
    destruct (Z.eq_dec a A_mem_inited) as [->|NE]; [apply amemflag_same; assumption|].
    apply XP; [exact Ha|]. split; [exact HC|]. intros K. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (HX K)].
    unfold memflag_foot in K. cbn [rin_ivs fst snd] in K. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma AMEMBIO_xpres : forall LB LBx SP X m m' a Rm,
    MEMBIO H LB m a Rm -> (forall b, In b (blocks_MEMBIO a Rm) -> In b LBx) -> xpres H LBx SP X m m' ->
    Forall (fun iv : Z * Z => Forall (fun b => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) (blocks_MEMBIO a Rm)) X ->
    MEMBIO H LB m' a Rm.
  Proof.
    intros LB LBx SP X m m' a Rm MB KEEP XP FX. destruct MB as (X1 & X2 & X3 & X4 & REST).
    assert (K1 : In (mb_id Rm, a, BIO_SIZE) LBx) by (apply KEEP; left; reflexivity).
    assert (K2 : In (mb_bbid Rm, mb_bb Rm, BIOBUFMEM_SIZE) LBx) by (apply KEEP; right; left; reflexivity).
    assert (K3 : In (mb_bmid Rm, mb_bm Rm, BUFMEM_SIZE) LBx) by (apply KEEP; right; right; left; reflexivity).
    assert (K4 : In (mb_rpid Rm, mb_rp Rm, BUFMEM_SIZE) LBx) by (apply KEEP; right; right; right; left; reflexivity).
    assert (FXi : forall i (b : block), nth_error (blocks_MEMBIO a Rm) i = Some b ->
              Forall (fun iv : Z * Z => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) X).
    { intros i b Hi. eapply Forall_impl; [| exact FX]. cbn beta. intros iv Fb. exact (proj1 (Forall_forall _ _) Fb b (nth_error_In _ _ Hi)). }
    pose proof (FXi 0%nat _ eq_refl) as F1. pose proof (FXi 1%nat _ eq_refl) as F2. pose proof (FXi 2%nat _ eq_refl) as F3. pose proof (FXi 3%nat _ eq_refl) as F4.
    cbn [blk_addr blk_size fst snd] in F1, F2, F3, F4. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
    split; [| split; [| split; [| split; [| exact REST]]]].
    all: eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP); [eassumption| |]; cbn [cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ].
    - right; right; left. exists (mb_id Rm, a, 128). split; [exact K1| cbn [blk_addr blk_size fst snd]; lia].
    - exact F1.
    - right; right; left. exists (mb_bbid Rm, mb_bb Rm, 16). split; [exact K2| cbn [blk_addr blk_size fst snd]; lia].
    - exact F2.
    - right; right; left. exists (mb_bmid Rm, mb_bm Rm, 32). split; [exact K3| cbn [blk_addr blk_size fst snd]; lia].
    - exact F3.
    - right; right; left. exists (mb_rpid Rm, mb_rp Rm, 32). split; [exact K4| cbn [blk_addr blk_size fst snd]; lia].
    - exact F4.
  Qed.
  (* [comment removed for export] *)
  Lemma AMEMBIO_munch : forall LB W m m' a Rm,
    MEMBIO H LB m a Rm -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => Forall (fun b => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) (blocks_MEMBIO a Rm)) W ->
    MEMBIO H LB m' a Rm.
  Proof.
    intros LB W m m' a Rm MB MU WM FX. destruct MB as (X1 & X2 & X3 & X4 & REST).
    assert (FXi : forall i (b : block), nth_error (blocks_MEMBIO a Rm) i = Some b -> disjoint_from W (blk_addr b) (blk_size b)).
    { intros i b Hi. assert (K : Forall (fun iv : Z * Z => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) W).
      { eapply Forall_impl; [| exact FX]. cbn beta. intros iv Fb. exact (proj1 (Forall_forall _ _) Fb b (nth_error_In _ _ Hi)). }
      clear - K. induction W as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv K) as K1. cbn in K1. split; [lia| exact (IH (Forall_inv_tail K))]. }
    pose proof (FXi 0%nat _ eq_refl) as F1. pose proof (FXi 1%nat _ eq_refl) as F2. pose proof (FXi 2%nat _ eq_refl) as F3. pose proof (FXi 3%nat _ eq_refl) as F4.
    cbn [blk_addr blk_size fst snd] in F1, F2, F3, F4. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
    split; [| split; [| split; [| split; [| exact REST]]]];
      (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]; assumption]).
  Qed.

  Hypothesis HH : asan_rt_hyps H.
  (* [comment removed for export] *)
  Definition fswin (iv : Z * Z) : Prop :=
    aceil <= fst iv \/ (as_FSB H <= fst iv /\ snd iv <= as_FSB H + AFS_SIZE) \/ (sh (as_FSB H) <= fst iv /\ snd iv <= sh (as_FSB H + AFS_SIZE)).
  (* [comment removed for export] *)
  Lemma fswin_facts : forall s LBx m0 L W a,
    as_RHEAP H s LBx m0 -> (forall b, In b L -> In b LBx) -> Forall fswin W -> rin_ivs W a ->
    AIMG_TOP <= a /\ ~ in_block L a /\ ~ in_block_sh L a.
  Proof.
    intros s LBx m0 L W a HP SUB FW Ra. acb. pose proof (ah_fsb H HH _ _ _ HP) as (F1 & F2 & F3 & F4).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
    pose proof (sh_aapp_range _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (W1 & W2 & W3). pose proof (aapp_not_shadowland _ _ F4) as NSF.
    destruct (rin_ivs_In _ _ Ra) as (iv & IN & Riv). pose proof (proj1 (Forall_forall _ _) FW iv IN) as K. unfold fswin in K.
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; lia).
    split; [| split].
    - unfold AIMG_TOP, AFS_SIZE in *. destruct K as [K|[[K1 K2]|[K1 K2]]]; lia.
    - intros (b & Hb & R). pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      pose proof (aapp_not_shadowland _ _ D7) as NSb.
      unfold AIMG_TOP, AFS_SIZE, ALOWSH_LO, AHI_LO in *. rewrite ?ASHADOW_BASE_val in *.
      destruct K as [K|[[K1 K2]|[K1 K2]]]; [lia| lia|]. unfold sh, nsh in *. rewrite ?ASHADOW_BASE_val in *. lia.
    - intros (b & Hb & R). pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      pose proof (sh_aapp_range _ _ D7 D3) as (V1 & V2 & V3). pose proof (aapp_not_shadowland _ _ D7) as NSb.
      unfold AIMG_TOP, AFS_SIZE, ALOWSH_LO, AHI_LO in *. rewrite ?ASHADOW_BASE_val in *.
      destruct K as [K|[[K1 K2]|[K1 K2]]]; [unfold sh, nsh in *; rewrite ?ASHADOW_BASE_val in *; lia| |].
      + (* [comment removed for export] *) unfold sh, nsh in *. rewrite ?ASHADOW_BASE_val in *. lia.
      + (* [comment removed for export] *)
        unfold sh, nsh in *. clear - K1 K2 R Riv D2 D6. Z.div_mod_to_equations. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma LIBMID_xfs : forall s m0 LIB LBx SP X m m' M x f' (v' : bool),
    as_RHEAP H s LBx m0 ->
    LIBMID LIB m M -> mid_ctx M = CtxReady x -> xpres H LBx SP X m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) -> Forall fswin X ->
    MEMFLAG m' f' -> rw_cells asegs m' A_vdso_func [C8 (wz (if v' then 0 else P_cgt_init))] ->
    LIBMID LIB m' (mkMID f' (mid_ctx M) (mid_err M) (mid_E M) v').
  Proof.
    intros s m0 LIB LBx SP X m m' M x f' v' HP LM CX XP SUBL SUBE FW MF' VD'.
    eapply LIBMID_xagree; [exact LM| exact CX| exact XP| exact SUBL| exact SUBE| | | | | | exact MF'| exact VD'|].
    - intros a K HX. exfalso. pose proof (proj1 (fswin_facts _ _ _ _ _ _ HP SUBL FW K)). pose proof (LIBX_below a HX). lia.
    - intros a K R. pose proof (proj1 (fswin_facts _ _ _ _ _ _ HP SUBL FW K)). unfold AIMG_TOP in *. lia.
    - intros a K. exact (proj1 (proj2 (fswin_facts _ _ _ _ _ _ HP SUBL FW K))).
    - intros a K. exact (proj2 (proj2 (fswin_facts _ _ _ _ _ _ HP SUBL FW K))).
    - intros a K. exact (proj2 (proj2 (fswin_facts _ _ _ _ _ _ HP SUBE FW K))).
    - intros a K. exact (proj1 (proj2 (fswin_facts _ _ _ _ _ _ HP SUBE FW K))).
  Qed.
  (* [comment removed for export] *)
  Lemma LIBMID_xfs0 : forall s m0 LIB LBx SP X m m' M x,
    as_RHEAP H s LBx m0 ->
    LIBMID LIB m M -> mid_ctx M = CtxReady x -> xpres H LBx SP X m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) -> Forall fswin X ->
    LIBMID LIB m' M.
  Proof.
    intros s m0 LIB LBx SP X m m' M x HP LM CX XP SUBL SUBE FW. pose proof LM as (_ & MF & _ & _ & _ & VD & _).
    pose proof (magree_of_xpres _ _ _ _ _ _ XP) as AG.
    assert (XA : forall a, rin_ivs X a -> AIMG_TOP <= a) by (intros a K; exact (proj1 (fswin_facts _ _ _ _ _ _ HP SUBL FW K))).
    pose proof (LIBMID_xfs s m0 LIB LBx SP X m m' M x (mid_flag M) (mid_vdso M) HP LM CX XP SUBL SUBE FW) as K.
    destruct M as [f c e E v]; cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. apply K.
    - destruct MF as (fb & MF1 & MF2). exists fb. split; [| exact MF2].
      eapply rw_cells_agree; [exact AG| exact MF1|]. intros a Ha. unfold in_range in Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
      split; [right; left; unfold aimg_client, A_mem_inited in *; lia| intros R; pose proof (XA a R); unfold A_mem_inited, AIMG_TOP in *; lia].
    - eapply rw_cells_agree; [exact AG| exact VD|]. intros a Ha. unfold in_range in Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
      split; [right; left; unfold aimg_client, A_vdso_func in *; lia| intros R; pose proof (XA a R); unfold A_vdso_func, AIMG_TOP in *; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma LIBMID_xobj : forall s m0 LIB LBx SP X W Lc m m' M x,
    as_RHEAP H s LBx m0 ->
    LIBMID LIB m M -> mid_ctx M = CtxReady x -> xpres H LBx SP X m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) -> (forall b, In b Lc -> In b LBx) ->
    (forall b b', In b (LIB ++ mid_errblocks M) -> In b' Lc -> blk_id b <> blk_id b') ->
    Forall fswin W -> (forall a, rin_ivs X a -> in_block Lc a \/ rin_ivs W a) ->
    LIBMID LIB m' M.
  Proof.
    intros s m0 LIB LBx SP X W Lc m m' M x HP LM CX XP SUBL SUBE SUBC DJ FW HX. pose proof LM as (_ & MF & _ & _ & _ & VD & _).
    pose proof (magree_of_xpres _ _ _ _ _ _ XP) as AG. acb. assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
    assert (XA : forall a, rin_ivs X a -> AIMG_TOP <= a).
    { intros a K. destruct (HX a K) as [B|R]; [exact (proj1 (in_block_where H HH _ _ _ _ _ HP SUBC B))| exact (proj1 (fswin_facts _ _ _ _ _ _ HP SUBL FW R))]. }
    (* [comment removed for export] *)
    assert (OBJ : forall a L, (forall b, In b L -> In b LBx) -> (forall b b', In b L -> In b' Lc -> blk_id b <> blk_id b') ->
              in_block Lc a -> ~ in_block L a /\ ~ in_block_sh L a).
    { intros a L SL DL (b' & Hb' & R'). split.
      - intros (b & Hb & R). pose proof (ah_disj H HH _ _ _ b b' HP (SL _ Hb) (SUBC _ Hb') (DL _ _ Hb Hb')) as D. lia.
      - intros (b & Hb & R). pose proof (ah_blocks H HH _ _ _ _ HP (SUBC _ Hb')) as (_ & _ & E3 & _ & _ & _ & E7).
        pose proof (ah_blocks H HH _ _ _ _ HP (SL _ Hb)) as (_ & _ & D3 & _ & _ & _ & D7).
        pose proof (sh_aapp_range _ _ D7 D3) as (V1 & V2 & V3). pose proof (aapp_not_shadowland _ _ E7) as NS.
        unfold ALOWSH_LO, AHI_LO, AIMG_TOP in *. rewrite S0 in V1. lia. }
    assert (SUBL2 : forall b, In b LIB -> In b LBx) by exact SUBL.
    assert (DJL : forall b b', In b LIB -> In b' Lc -> blk_id b <> blk_id b') by (intros b b' Hb Hb'; apply DJ; [apply in_or_app; left; exact Hb| exact Hb']).
    assert (DJE : forall b b', In b (mid_errblocks M) -> In b' Lc -> blk_id b <> blk_id b') by (intros b b' Hb Hb'; apply DJ; [apply in_or_app; right; exact Hb| exact Hb']).
    assert (X1 : forall a, rin_ivs X a -> rin_ivs LIBX a -> (A_mem_inited <= a < A_mem_inited + 1) \/ (A_vdso_func <= a < A_vdso_func + 8)).
    { intros a R HXL. exfalso. pose proof (XA a R). pose proof (LIBX_below a HXL). lia. }
    assert (X2 : forall a, rin_ivs X a -> ~ (0x571000 <= a < 0x5ea000)) by (intros a R RR; pose proof (XA a R); unfold AIMG_TOP in *; lia).
    assert (X3 : forall a, rin_ivs X a -> ~ in_block LIB a).
    { intros a R. destruct (HX a R) as [B|Rw]; [exact (proj1 (OBJ a LIB SUBL2 DJL B))| exact (proj1 (proj2 (fswin_facts _ _ _ _ _ _ HP SUBL2 FW Rw)))]. }
    assert (X4 : forall a, rin_ivs X a -> ~ in_block_sh LIB a).
    { intros a R. destruct (HX a R) as [B|Rw]; [exact (proj2 (OBJ a LIB SUBL2 DJL B))| exact (proj2 (proj2 (fswin_facts _ _ _ _ _ _ HP SUBL2 FW Rw)))]. }
    assert (X5 : forall a, rin_ivs X a -> ~ in_block_sh (mid_errblocks M) a).
    { intros a R. destruct (HX a R) as [B|Rw]; [exact (proj2 (OBJ a _ SUBE DJE B))| exact (proj2 (proj2 (fswin_facts _ _ _ _ _ _ HP SUBE FW Rw)))]. }
    assert (X6 : forall a, rin_ivs X a -> ~ in_block (mid_errblocks M) a).
    { intros a R. destruct (HX a R) as [B|Rw]; [exact (proj1 (OBJ a _ SUBE DJE B))| exact (proj1 (proj2 (fswin_facts _ _ _ _ _ _ HP SUBE FW Rw)))]. }
    pose proof (LIBMID_xagree H LIB LBx SP X m m' M x (mid_flag M) (mid_vdso M) LM CX XP SUBL SUBE X1 X2 X3 X4 X5) as K.
    destruct M as [f c e E v]; cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. apply K; clear K.
    - destruct MF as (fb & MF1 & MF2). exists fb. split; [| exact MF2].
      eapply rw_cells_agree; [exact AG| exact MF1|]. intros a Ha. unfold in_range in Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
      split; [right; left; unfold aimg_client, A_mem_inited in *; lia| intros R; pose proof (XA a R); unfold A_mem_inited, AIMG_TOP in *; lia].
    - eapply rw_cells_agree; [exact AG| exact VD|]. intros a Ha. unfold in_range in Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
      split; [right; left; unfold aimg_client, A_vdso_func in *; lia| intros R; pose proof (XA a R); unfold A_vdso_func, AIMG_TOP in *; lia].
    - exact X6.
  Qed.
End K.

(* [comment removed for export] *)
Section RC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HX : asan_rt_hyps_x H.
  Hypothesis RAISE : araise_stmt H.
  Let HH : asan_rt_hyps H := proj1 HX.
  Let SM6 : stack_malloc_6_stmt H := proj1 (proj2 (proj2 (proj2 (proj2 HX)))).
  Let SF6 : stack_free_6_stmt H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).
  Let SSF8 : set_shadow_f8_stmt := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))))).
  Let PERM : rheap_perm H := HHx_rheap_perm H HX.

  (* [comment removed for export] *)
  Variables (PF9new : ctxphase -> list (Z * list Z)) (PF9free : list (Z * list Z)).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LIB LB : list block) (LF : list fframe)
            (M : libmid) (x : ctxinfo) (st mb lo B : Z) (S : storerep) (R : membio) (ds : list byte) (errv : word) (CH : list (Z * Z)).
  Hypotheses (VIS0 : as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                         F (Z_to_bv 64 P_OSSL_ECHSTORE_read_echconfiglist) fc None m (seg_rom asegs))
             (A0 : a0 = Z_to_bv 64 st) (A1 : a1 = Z_to_bv 64 mb)
             (SO : STOREobj LB m st S) (SE : es_entries S = 0) (SEO : es_entries_o S = None) (STL : st + STORE_SIZE <= lo) (SSH : STORE_shad m st S)
             (MBO : MEMBIO H LB m mb R) (MP0 : mb_pos R = 0) (MN0 : mb_nread R = 0) (MBB : MEMBIO_below mb R lo) (MBS : MEMBIO_sep mb R)
             (MSH : MEMBIO_shad m mb R) (PAY : PAYLOAD_shad m R)
             (DS : bytes_at asegs m (mb_buf R) ds) (DSL : zlength ds = mb_len R)
             (PAYL : 1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB /\ forall b, In b LIB -> blk_id b <> pD)
             (PAYL2 : 1 <= mb_len R -> forall pD, In (pD, mb_buf R, mb_len R) LB -> pD <> es_id S)
             (NDsm : List.NoDup (map blk_id ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R)))
             (LM : LIBMID LIB m M) (SUBL : forall b, In b LIB -> In b LB) (CTX : mid_ctx M = CtxReady x) (MF1 : mid_flag M = 1)
             (DJ6 : forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id b <> blk_id b')
             (HP : as_RHEAP H s (mid_errblocks M ++ LB) m) (KREL : as_AKREL H s (mkCfg msF mo))
             (BUD : lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + DECODE_BYTES + ERRSTR_BYTES <= as_LIVE_MAX H)
             (BUDC : Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + DECODE_CNT + ERRSTR_CNT <= as_LIVE_CNT_MAX H)
             (AUX : as_rauxv_ok H m B) (SPB : bv_unsigned sp <= B) (BHI : B < 2^64) (SPA : bv_unsigned sp mod 16 = 0)
             (ST : stk asegs m lo (bv_unsigned sp)) (CEIL : aceil <= lo) (LO : lo <= bv_unsigned sp - READCFG_STACK M) (ST0 : stack0 m lo (bv_unsigned sp))
             (ERR : rw_cells asegs m (errno_addr tp) [C4 errv]) (MI : mem_inv asegs m) (TP : tp = Z_to_bv 64 ATP) (AC : ACONST m)
             (MCO : mid_closed_ok H M)
             (RFS : as_RFS H LF m) (LFB : (length LF + READCFG_LF <= READCFG_MAXLIVE)%nat) (ATH : athr_cells m)
             (CHN : as_chain H m (bv_unsigned s0) CH) (CHB : forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp')
             (PF : pf_ok (as_TR H) (PF_readcfg PF9new PF9free M) (bv_unsigned ra) CH) (ALW : READCFG_COST H M <= as_AL H s)
             (RAE : bv_unsigned ra mod 2 = 0).

  (* [comment removed for export] *)
  Definition E0 : list block := mid_errblocks M.
  Definition L0 : list block := mid_errblocks M ++ LB.
  Definition ESP : Z := bv_unsigned sp.
  Definition S1 : Z := rp_s1 (bv_unsigned sp).
  (* [comment removed for export] *)
  Definition KG : Z := bv_unsigned sp - 448 - rp_s1 (bv_unsigned sp).
  Definition POST : config -> Prop := readcfg_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LIB LB LF M st S mb R ds lo B m mo.
  (* [comment removed for export] *)
  Definition XF : list (Z * Z) := [(st, st + STORE_SIZE)] ++ MEMBIO_foot mb R ++ ERR_XE ++ VDSO_X ++ errph_foot (mid_err M).
  (* [comment removed for export] *)
  Definition SAVES : list cell := arp_saves s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.
  (* [comment removed for export] *)
  Definition CH1 : list (Z * Z) := (bv_unsigned sp, bv_unsigned ra) :: CH.
  (* [comment removed for export] *)
  Definition LF1 (ff fp : Z) : list fframe := (6, ff, fp) :: LF.

  Local Ltac img_static := unfold A_malloc_impl, A_realloc_impl, A_free_impl, A_got_CRYPTO_malloc, A_mem_buf_method, O_METH_BREAD, A_mem_inited; cbn; lia.

  (* [comment removed for export] *)
  Lemma rc_facts :
       S = store_empty (es_id S) /\ In (es_id S, st, STORE_SIZE) L0 /\ ablock_range H st STORE_SIZE
    /\ (forall b, In b L0 -> ablock_range H (blk_addr b) (blk_size b)) /\ (forall b, In b LB -> In b L0)
    /\ List.NoDup (map blk_id L0) /\ 9152 <= READCFG_STACK M /\ 0 <= lo /\ MEMFLAG m 1
    /\ (forall b', In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> In b' L0)
    /\ (forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) ->
          blk_addr b + blk_size b + 16 <= blk_addr b' \/ blk_addr b' + blk_size b' + 16 <= blk_addr b)
    /\ afsb_ok H /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000
    /\ rp_s1 (bv_unsigned sp) mod 32 = 0 /\ bv_unsigned sp - 464 <= rp_s1 (bv_unsigned sp) <= bv_unsigned sp - 448 /\ bv_unsigned sp < 2^64.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    assert (SUB0 : forall b, In b LB -> In b L0) by (intros b Hb; unfold L0; apply in_or_app; right; exact Hb).
    pose proof SO as (SC & SIN & _).
    assert (OBJ : forall b', In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> In b' L0).
    { intros b' Hb'. apply SUB0. destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _). unfold blocks_MEMBIO in Hb'.
      destruct Hb' as [<-|[<-|[<-|[<-|[<-|[]]]]]]; assumption. }
    pose proof (aword_range sp) as SPR. pose proof (rp_s1_al (bv_unsigned sp) SPA) as [Q1 Q2].
    assert (ACB : 0x7fff7f800000 <= aceil <= 0x7fffff800000) by (clear; acb; lia).
    repeat match goal with |- _ /\ _ => split end.
    - exact (store_empty_eq S SE SEO).
    - apply SUB0. exact SIN.
    - exact (ah_blocks H HH _ _ _ _ HP (SUB0 _ SIN)).
    - intros b Hb. exact (ah_blocks H HH _ _ _ _ HP Hb).
    - exact SUB0.
    - exact (ah_nodup H HH _ _ _ HP).
    - apply readcfg_stack_lo.
    - destruct ST as [? _]; assumption.
    - destruct LM as (_ & MF & _). rewrite MF1 in MF. exact MF.
    - exact OBJ.
    - intros b b' Hb Hb'. exact (ah_disj H HH _ _ _ b b' HP (SUB0 _ (SUBL _ Hb)) (OBJ _ Hb') (DJ6 _ _ Hb Hb')).
    - exact (ah_fsb H HH _ _ _ HP).
    - exact (proj1 ACB).
    - exact (proj2 ACB).
    - exact Q1.
    - clear - Q2; lia.
    - clear - Q2; lia.
    - clear - SPR; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma errph_foot_apart : forall b', In b' L0 -> (forall b, In b LIB -> blk_id b <> blk_id b') ->
    Forall (fun iv : Z * Z => blk_addr b' + blk_size b' <= fst iv \/ snd iv <= blk_addr b') (errph_foot (mid_err M)).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros b' Hb' NE. destruct LM as (_ & _ & _ & EPm & _). rewrite CTX in EPm. cbn [ERRPH_mid] in EPm.
    destruct (mid_err M) as [|c]; cbn [errph_foot]; [apply Forall_nil|]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
    cbn [ERRPH] in EPm. destruct EPm as [_ CHc]. pose proof CHc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    pose proof (ah_disj H HH _ _ _ (ec_es c) b' HP ltac:(unfold L0; apply in_or_app; right; exact (SUBL _ I5)) Hb' (NE _ I5)) as D.
    rewrite Z5 in D. unfold ERRST_SIZE in *. clear - D. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rc_stack_gen : forall cph eph,
       RAISE_STACK eph + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) AREALLOC_STACK)
    /\ LAD_STACK + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) AREALLOC_STACK)
    /\ CZALLOC_STACK + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) AREALLOC_STACK)
    /\ CFREE_STACK + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) AREALLOC_STACK)
    /\ AFS_STACK + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) AREALLOC_STACK).
  Proof. clear. intros [|?] [|?]; repeat split; vm_compute; discriminate. Qed.
  Lemma rc_stack : RAISE_STACK (mid_err M) + 464 <= READCFG_STACK M /\ LAD_STACK + 464 <= READCFG_STACK M /\ CZALLOC_STACK + 464 <= READCFG_STACK M
                   /\ CFREE_STACK + 464 <= READCFG_STACK M /\ AFS_STACK + 464 <= READCFG_STACK M.
  Proof. clear. unfold READCFG_STACK, mid_stack. apply rc_stack_gen. Qed.


  (* [comment removed for export] *)
  Definition XSF (ff fp : Z) : list (Z * Z) := [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 6); (sh ff, sh ff + fshn 6)].

  (* [comment removed for export] *)
  Lemma rp_post_S0 : forall m' msF' mo' (s' : as_St H) (rv : Z) (M' : libmid) (R' : membio) (LE : list block) (XSq : list (Z * Z))
      (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 errv' : word),
    as_VIS H s' msF' = MS (mkR ra sp gp (Z_to_bv 64 ATP) u0 u1 u2 s0 s1 (Z_to_bv 64 rv) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                       F (ret_pc ra) fc None m' (seg_rom asegs) ->
    (rv = 0 \/ rv = 1) -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' -> mem_inv asegs m' -> ACONST m' ->
    stk asegs m' lo (bv_unsigned sp) -> stack0 m' lo (bv_unsigned sp) ->
    rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv'] -> as_rauxv_ok H m' B ->
    as_RHEAP H s' (mid_errblocks M' ++ LE ++ LB) m' -> LIBMID (LE ++ LIB) m' M' -> mid_step M M' -> mid_newlib_ok M M' LE -> mid_ctx M' = mid_ctx M ->
    Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M') <= ERRSTR_BYTES ->
    MEMBIO H LB m' mb R' -> MEMBIO_shad m' mb R' -> mb_static R R' -> bytes_at asegs m' (mb_buf R) ds ->
    rw_cells asegs m' st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> STORE_shad m' st S ->
    as_RFS H LF m' -> Forall (fs_scratch H LF) XSq ->
    xpres H LB (bv_unsigned sp) (XSq ++ XF) m m' ->
    as_AL H s' >= as_AL H s - READCFG_COST H M ->
    as_SR H POST (mkCfg msF' mo').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros m' msF' mo' s' rv M' R' LE XSq u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 errv'.
    intros VIS' RV KREL' MP' MI' AC' ST' ST0' ERR' AUX' HP' LM' STEP' NEW' CTX' EC' EB' MBO' MSH' MST' DS' SC' SSH' RFS' FRESH XP' AL'.
    pose proof SO as (_ & SINB & _).
    apply (ah_done H HH). unfold POST, readcfg_post. cbn [cfg_ms cfg_model]. rewrite TP.
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', errv', s', rv, M', S, R', LE, [], XSq.
    cbv zeta. cbn [app].
    split; [exact VIS'|]. split; [exact RV|]. split; [exact KREL'|]. split; [exact MP'|].
    split; [exact MI'|]. split; [exact AC'|]. split; [exact ST'|]. split; [exact ST0'|]. split; [exact ERR'|]. split; [exact AUX'|]. split; [exact HP'|].
    split; [exact LM'|]. split; [exact STEP'|]. split; [exact NEW'|]. split; [exact CTX'|].
    split; [unfold STOREobj, ENTRIES; rewrite SE, SEO; split; [exact SC'| split; [apply in_or_app; right; exact SINB| reflexivity]]|].
    split; [exact SSH'|]. split; [reflexivity|]. split; [unfold blocks_STORE; rewrite SEO; apply Permutation_refl|].
    split; [cbn; unfold DECODE_CNT; clear; lia|]. split; [cbn; unfold DECODE_BYTES; clear; lia|].
    split; [exact EC'|]. split; [exact EB'|].
    split; [unfold blocks_STORE; rewrite SEO; cbn; constructor; [intros []| constructor]|].
    split; [eapply MEMBIO_mono; [exact MBO'| intros b Hb; apply in_or_app; right; exact Hb]|].
    split; [exact MSH'|]. split; [exact (mb_static_blocks mb R R' MST')|]. split; [exact DS'|].
    split; [exact FRESH|]. split; [exact RFS'|].
    split; [exact (ah_thr H HH _ _ _ HP')|].
    split; [unfold XF in XP'; exact XP'| exact AL'].
  Qed.



  Lemma outside_of_not_rin : forall W a, ~ rin_ivs W a -> outside W a.
  Proof.
    induction W as [|[l h] W IH]; intros a K; [exact I|]. cbn in K |- *. split; [intros Rz; apply K; left; exact Rz| apply IH; intros Rz; apply K; right; exact Rz].
  Qed.
  (* [comment removed for export] *)
  Lemma fswin_cw : forall L iv, fswin H iv -> aclient_write_ok H L iv.
  Proof.
    intros L iv [K|[K|K]]; [left; exact K| right; right; right; right; left; exact K| right; right; right; right; right; left; exact K].
  Qed.
  (* [comment removed for export] *)
  Lemma client_not_frame : forall s' L L' m0 a, as_RHEAP H s' L m0 -> (forall b, In b L' -> In b L) -> aclient_addr H L' (bv_unsigned sp) a -> lo <= a < bv_unsigned sp -> False.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros s' L L' m0 a HP' SUB' HC Ra. acb. pose proof (ah_fsb H HH _ _ _ HP') as (F1 & F2 & F3 & F4).
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; lia).
    unfold aclient_addr, aimg_client, in_block, in_block_sh in HC.
    destruct HC as [K|[K|[(b & Hb & Rb)|[(b & Hb & Rb)|[K|[K|K]]]]]].
    - lia.
    - unfold AIMG_TOP in *. lia.
    - pose proof (ah_blocks H HH _ _ _ _ HP' (SUB' _ Hb)) as (_ & _ & _ & _ & D5 & _). lia.
    - pose proof (ah_blocks H HH _ _ _ _ HP' (SUB' _ Hb)) as (_ & _ & D3 & _ & _ & _ & D7). pose proof (sh_aapp_range _ _ D7 D3) as (V1 & V2 & V3). lia.
    - lia.
    - pose proof (sh_mono _ _ F2). lia.
    - unfold AHI_LO in K. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rp_exit : forall m1 msF1 mo1 (s1' : as_St H) (rv : Z) (M' : libmid) (R' : membio) (LE : list block) (ff fp rb : Z)
      (fj1 fj2 jg : list byte) (slots : list cell) (XSq : list (Z * Z))
      (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s2v s3v s4v s6v s7v s9v s11v u3 u4 u5 u6 errv1 : word),
    as_VIS H s1' msF1 = MS (mkR rax (Z_to_bv 64 S1) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1) b0 b1 b2 b3 b4 b5 b6 b7
                                s2v s3v s4v (Z_to_bv 64 rv) s6v s7v (Z_to_bv 64 ff) s9v (Z_to_bv 64 ff) s11v u3 u4 u5 u6)
                        F (Z_to_bv 64 AEXIT) fc None m1 (seg_rom asegs) ->
    (rv = 0 \/ rv = 1) -> as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 -> mem_inv asegs m1 -> ACONST m1 ->
    stk asegs m1 lo S1 -> stack0 m1 lo (bv_unsigned sp) ->
    cells_size slots = 344%nat -> rw_cells asegs m1 S1 slots -> rw_cells asegs m1 (S1 + 344) [CB (Z.to_nat KG) jg] -> rw_cells asegs m1 (bv_unsigned sp + -104) SAVES ->
    rw_cells asegs m1 ff (arp_fframe S1 fj1 rb fj2 fp) -> as_RFS H (LF1 ff fp) m1 ->
    rw_cells asegs m1 (errno_addr (Z_to_bv 64 ATP)) [C4 errv1] -> as_rauxv_ok H m1 B ->
    as_RHEAP H s1' (mid_errblocks M' ++ LE ++ LB) m1 -> LIBMID (LE ++ LIB) m1 M' -> mid_step M M' -> mid_newlib_ok M M' LE -> mid_ctx M' = mid_ctx M ->
    Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M') <= ERRSTR_BYTES ->
    MEMBIO H LB m1 mb R' -> MEMBIO_shad m1 mb R' -> mb_static R R' -> bytes_at asegs m1 (mb_buf R) ds ->
    rw_cells asegs m1 st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> STORE_shad m1 st S ->
    Forall (fs_scratch H LF) XSq -> (forall a, rin_ivs (XSF ff fp) a -> rin_ivs XSq a) ->
    xpres H LB (bv_unsigned sp) (XSq ++ XF) m m1 ->
    as_AL H s1' >= as_AL H s - READCFG_COST H M ->
    as_SR H POST (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros m1 msF1 mo1 s1' rv M' R' LE ff fp rb fj1 fj2 jg slots XSq rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s2v s3v s4v s6v s7v s9v s11v u3 u4 u5 u6 errv1.
    intros VIS1 RV KREL1 MP1 MI1 AC1 STK1 ST01 SLZ SL1 GP1 SV1 FRM1 RFS1 ERR1 AUX1 HP1 LM1 STEP1 NEW1 CTX1 EC1 EB1 MBO1 MSH1 MST1 DS1 SC1 SSH1 FSq INCq XP1 AL1.
    destruct rc_facts as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR).
    pose proof rc_stack as (_ & _ & _ & _ & STKA). fold S1 in Q1, Q2.
    pose proof (fresh_of_RFS H HH _ _ _ _ _ RFS1) as FRESH.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    pose proof MST1 as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    pose proof MBO1 as MB0. destruct MB0 as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _).
    rewrite ?T3, ?T4, ?T5, ?T6, ?T7, ?T8, ?T9 in I1. rewrite ?T3, ?T4, ?T5, ?T6, ?T7, ?T8, ?T9 in I2. rewrite ?T3, ?T4, ?T5, ?T6, ?T7, ?T8, ?T9 in I3. rewrite ?T3, ?T4, ?T5, ?T6, ?T7, ?T8, ?T9 in I4.
    pose proof (BLK0 _ (SUB0 _ I1)) as (_ & E12 & _ & E1a & E1b & E1f & E1c). pose proof (BLK0 _ (SUB0 _ I2)) as (_ & E22 & _ & E2a & E2b & E2f & E2c).
    pose proof (BLK0 _ (SUB0 _ I3)) as (_ & E32 & _ & E3a & E3b & E3f & E3c). pose proof (BLK0 _ (SUB0 _ I4)) as (_ & E42 & _ & E4a & E4b & E4f & E4c).
    cbn [blk_addr blk_size fst snd] in E12, E1a, E1b, E1f, E1c, E22, E2a, E2b, E2f, E2c, E32, E3a, E3b, E3f, E3c, E42, E4a, E4b, E4f, E4c.
    pose proof SBR as (_ & SB2 & _ & SBa & SBb & SBf & SBc). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, STORE_SIZE, AIMG_TOP, AFS_SIZE in *.
    assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) <= 0xc04000 - 4) by (clear; vm_compute; split; discriminate).
    assert (S0 : sh 0xc04000 = 0x80178800) by reflexivity.
    pose proof (sh_add8 ff 512) as SH8. replace (ff + 8 * 512) with (ff + 4096) in SH8 by (clear; lia).
    pose proof (sh_mono (as_FSB H) ff ltac:(clear - FF5; lia)) as SHL. pose proof (sh_mono (ff + 4096) (as_FSB H + 11571200) FF6) as SHU.
    pose proof (sh_aapp_range _ _ FB3 ltac:(clear; lia)) as (W1 & W2 & W3). unfold nsh in W2. unfold AIMG_TOP in W1.
    pose proof (aapp_not_shadowland _ _ FB3) as NSF.
    (* [comment removed for export] *)
    set (WX := [(ff, ff + 4096); (S1 - AFS_STACK, S1); (fp, fp + 1); (sh ff, sh ff + 512)]).
    assert (FW : Forall (fswin H) WX).
    { subst WX. unfold fswin, AFS_SIZE. apply Forall_cons; [right; left; cbn; clear - FF5 FF6; lia|]. apply Forall_cons; [left; cbn; unfold AFS_STACK; clear - CEIL LO STK0 Q2; lia|].
      apply Forall_cons; [right; left; cbn; clear - FP3 FP4 FF5; lia|]. apply Forall_cons; [| apply Forall_nil].
      right; right. cbn. clear - SHL SHU SH8. lia. }
    assert (CW : forall L, Forall (aclient_write_ok H L) WX) by (intros L; eapply Forall_impl; [intros iv; apply fswin_cw| exact FW]).
    assert (S0K : Forall stack0_ok WX).
    { subst WX. apply Forall_cons; [eapply stack0_ok_aapp; [exact FB3| clear - FF5; lia| clear - FF6; lia]|].
      apply Forall_cons; [apply stack0_ok_app; unfold AHI_LO, AFS_STACK; clear - CEIL LO STK0 Q2 ACB; lia|].
      apply Forall_cons; [eapply stack0_ok_aapp; [exact FB3| clear - FP3; lia| clear - FP4 FF5; lia]|].
      apply Forall_cons; [apply stack0_ok_sh'; [clear - FF1; lia| clear; lia| clear - FF6 FB2; lia]| apply Forall_nil]. }
    (* [comment removed for export] *)
    assert (BW : forall A n, A mod 16 = 0 -> 0 <= n -> 0xc04000 <= A -> A + n <= aceil -> (A + n + 16 <= as_FSB H \/ as_FSB H + 11571200 <= A - 16) -> aapp A n ->
              Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) WX /\ Forall (winX A n) WX).
    { intros A n M16 N0 LA HA AP AA. pose proof (aapp_not_shadowland _ _ AA) as NSA. subst WX. unfold winX, AFS_STACK. split.
      - apply Forall_cons; [cbn; clear - AP FF5 FF6; lia|]. apply Forall_cons; [cbn; clear - HA CEIL LO STK0 Q2; lia|].
        apply Forall_cons; [cbn; clear - AP FP3 FP4 FF5; lia|]. apply Forall_cons; [| apply Forall_nil]. cbn.
        pose proof (sh_mono _ _ FB2) as SHA. unfold ALOWSH_LO, AHI_LO in *. clear - NSA SHL SHU SH8 SHA W3 FF1. unfold sh in *. rewrite ?ASHADOW_BASE_val in *. lia.
      - apply Forall_cons; [cbn; unfold ALOWSH_LO, AHI_LO in *; rewrite ?ASHADOW_BASE_val; clear - NSF FF5 FF6; lia|].
        apply Forall_cons; [cbn; right; left; unfold AHI_LO; clear - CEIL LO STK0 Q2 ACB; lia|].
        apply Forall_cons; [cbn; unfold ALOWSH_LO, AHI_LO in *; rewrite ?ASHADOW_BASE_val; clear - NSF FP3 FP4 FF5; lia|].
        apply Forall_cons; [| apply Forall_nil]. cbn. right; right. unfold sh, nsh. clear - M16 N0 AP FF5 FF6 FF64. Z.div_mod_to_equations. lia. }
    destruct (BW mb 128 E12 ltac:(clear; lia) E1a E1b E1f E1c) as [BW1 BX1]. destruct (BW (mb_bb R) 16 E22 ltac:(clear; lia) E2a E2b E2f E2c) as [BW2 BX2].
    destruct (BW (mb_bm R) 32 E32 ltac:(clear; lia) E3a E3b E3f E3c) as [BW3 BX3]. destruct (BW (mb_rp R) 32 E42 ltac:(clear; lia) E4a E4b E4f E4c) as [BW4 BX4].
    destruct (BW st 24 SB2 ltac:(clear; lia) SBa SBb SBf SBc) as [BWS BXS].
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply aexit; [clear - FF1; lia| clear - FF2 ACB; lia| exact FRM1| exact MI1]|].
    intros msF2 mo2 KREL2 MP2 (m2 & VIS2 & MU2 & WM2 & MI2 & FRM2).
    assert (AW2 : Forall (afs_write_ok H (LF1 ff fp)) [(ff, ff + 8)]).
    { apply Forall_cons; [| apply Forall_nil]. right. exists (6, ff, fp). split; [left; reflexivity| cbn; unfold fsz; cbn; clear; lia]. }
    assert (RFS2 : as_RFS H (LF1 ff fp) m2) by (eapply (ah_RFS_frame H HH); [exact RFS1| exact MU2| exact WM2| exact AW2]).
    assert (AC2 : ACONST m2).
    { eapply ACONST_frame; [exact AC1| exact MU2| exact WM2|]. apply Forall_cons; [eapply aconst_ok_aapp; [exact FB3| cbn; clear - FF5; lia| cbn; clear - FF6; lia]| apply Forall_nil]. }
    assert (STK2 : stk asegs m2 lo S1) by (eapply stk_transport_disjoint; [exact STK1| exact MU2| exact WM2| cbn; clear - FF6 FB2 CEIL Q2; lia]).
    (* [comment removed for export] *)
    pose proof SF6 as SF. unfold stack_free_6_stmt in SF.
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| |].
    { eapply SF with (LF := LF1 ff fp) (lo := lo) (n := ARP_FFREQ) (fp := fp); clear SF.
      - exact RFS2.
      - left; reflexivity.
      - change (Z.to_nat (fsz 6 - 40)) with 4056%nat. unfold wz in FRM2 |- *. exact FRM2.
      - reflexivity.
      - reflexivity.
      - unfold ARP_FFREQ, fsz. clear. cbn. lia.
      - rewrite unsigned_lit by (clear - Q2 LO0 CEIL STK0 LO SPR; lia). exact STK2.
      - exact CEIL.
      - rewrite unsigned_lit by (clear - Q2 LO0 CEIL STK0 LO SPR; lia). clear - LO STKA Q2. lia.
      - exact MI2.
      - exact AC2. }
    clear SF. intros msF3 mo3 KREL3 MP3 PO. unfold stack_free_post in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & VIS3 & MU3 & WM3 & MI3 & ST3 & RFS3 & SHD3 & AC3).
    rewrite (unsigned_lit S1) in MU3, ST3 by (clear - Q2 LO0 CEIL STK0 LO SPR; lia). unfold LF1 in RFS3. rewrite lf_remove_head in RFS3. change (fshn 6) with 512 in MU3.
    (* [comment removed for export] *)
    assert (MU13 : munch WX m1 m3).
    { subst WX. eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]; intros z Hz; cbn in Hz |- *; clear - Hz; lia. }
    pose proof (wmono_trans asegs _ _ _ WM2 WM3) as WM13.
    (* [comment removed for export] *)
    assert (FRW : Forall (fun iv : Z * Z => bv_unsigned sp <= fst iv \/ snd iv <= S1) WX).
    { subst WX. unfold AFS_STACK. apply Forall_cons; [cbn; clear - FF6 FB2 CEIL LO STK0 Q2; lia|]. apply Forall_cons; [cbn; clear; lia|].
      apply Forall_cons; [cbn; clear - FP4 FF5 FF6 FB2 CEIL LO STK0 Q2; lia|]. apply Forall_cons; [| apply Forall_nil]. cbn. pose proof (sh_mono _ _ FB2) as SHA'. clear - SHU SH8 SHA' W3 CEIL LO STK0 Q2 ACB. unfold AHI_LO in W3. lia. }
    assert (T13 : forall A cs, rw_cells asegs m1 A cs -> S1 <= A -> A + Z.of_nat (cells_size cs) <= bv_unsigned sp -> rw_cells asegs m3 A cs).
    { intros A cs RC HA HB. eapply rw_cells_transport; [exact RC| exact MU13| exact WM13|].
      clear - FRW HA HB. induction WX as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv FRW) as K. cbn in K. split; [lia| exact (IH (Forall_inv_tail FRW))]. }
    pose proof (T13 _ _ SV1 ltac:(clear - Q2; lia) ltac:(cbn; clear; lia)) as SV3.
    pose proof (T13 _ _ SL1 ltac:(clear; lia) ltac:(rewrite SLZ; clear - Q2; lia)) as SL3.
    pose proof (T13 _ _ GP1 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold KG; fold S1; clear - Q2; lia)) as GP3.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| eapply aepi; [clear - Q2 CEIL LO STK0 LO0; lia| exact SV3| exact MI3]|].
    intros msF4 mo4 KREL4 MP4 VIS4. cbn beta in VIS4.
    (* [comment removed for export] *)
    assert (STK3 : stk asegs m3 lo (bv_unsigned sp)).
    { assert (FR3 : rw_cells asegs m3 S1 (slots ++ [CB (Z.to_nat KG) jg] ++ SAVES)).
      { apply (proj2 (rw_cells_app asegs m3 S1 slots _)). split; [exact SL3|]. rewrite SLZ.
        apply (proj2 (rw_cells_app asegs m3 _ [CB (Z.to_nat KG) jg] SAVES)). split; [exact GP3|].
        cbn [cells_size csize Nat.add]. replace (S1 + Z.of_nat 344 + Z.of_nat (Z.to_nat KG + 0)) with (bv_unsigned sp + -104) by (unfold KG; fold S1; clear - Q2; lia). exact SV3. }
      pose proof (stk_release asegs m3 lo _ _ ST3 FR3 ltac:(clear - CEIL LO STK0 Q2; lia)) as K.
      rewrite !cells_size_app, SLZ in K. unfold SAVES, arp_saves in K. cbn [cells_size csize Nat.add length] in K.
      replace (S1 + Z.of_nat (344 + (Z.to_nat KG + 0 + 104))) with (bv_unsigned sp) in K by (unfold KG; fold S1; clear - Q2; lia). exact K. }
    assert (XP13 : xpres H LB (bv_unsigned sp) (XSq ++ XF) m1 m3).
    { eapply (xpres_of_munch_gen H); [exact MU13| exact WM13|]. intros a Ha [HC HXa]. subst WX. cbn.
      assert (HXb : ~ rin_ivs (XSF ff fp) a) by (intros K; apply HXa; apply rin_ivs_app; left; exact (INCq a K)).
      unfold XSF in HXb. cbn [rin_ivs fst snd app] in HXb. change (fsz 6) with 4096 in HXb. change (fshn 6) with 512 in HXb. unfold AFS_STACK.
      split; [clear - HXb; lia|]. split; [intros K; eapply (client_not_frame _ _ _ _ a HP SUB0 HC); clear - K Q2 CEIL LO STK0; lia|].
      split; [clear - HXb; lia|]. split; [clear - HXb; lia| exact I]. }
    eapply (rp_post_S0 m3 msF4 mo4 s1' rv M' R' LE XSq); [exact VIS4| exact RV| exact KREL4| | exact MI3| exact AC3| exact STK3| | | | | exact LM1 || idtac| exact STEP1| exact NEW1| exact CTX1| exact EC1| exact EB1
      | | | exact MST1| | | | exact RFS3| exact FSq| eapply xpres_trans; [exact XP1| exact XP13]| exact AL1].
    - eapply (ah_mpres_trans H HH); [| exact MP4]. eapply (ah_mpres_trans H HH); [| exact MP3]. eapply (ah_mpres_trans H HH); [exact MP1| exact MP2].
    - eapply stack0_transport; [exact ST01| exact MU13| exact WM13| exact S0K].
    - eapply rw_cells_transport; [exact ERR1| exact MU13| exact WM13|]. subst WX. unfold AFS_STACK. cbn -[Z.add Z.mul Z.sub Z.opp errno_addr sh].
      clear - ERNG FF1 CEIL LO STK0 Q2 ACB FP1 SHL W1 S0. lia.
    - eapply (ah_rauxv_frame H HH); [exact AUX1| exact MU13| exact WM13| apply (CW LB)].
    - eapply (ah_RHEAP_frame H HH); [exact HP1| exact MU13| exact WM13| apply CW].
    - (* [comment removed for export] *)
      eapply (LIBMID_xfs0 H HH s1' m1 (LE ++ LIB) (mid_errblocks M' ++ LE ++ LB) S1 WX m1 m3 M' x); [exact HP1| exact LM1| rewrite CTX1; exact CTX| | | | exact FW].
      + eapply (xpres_of_munch_gen H); [exact MU13| exact WM13|]. intros a Ha [_ HXa]. apply outside_of_not_rin. exact HXa.
      + intros b Hb. apply in_or_app. right. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; exact (SUBL _ Hb)].
      + intros b Hb. apply in_or_app. left. exact Hb.
    - eapply AMEMBIO_munch; [exact MBO1| exact MU13| exact WM13|].
      rewrite (mb_static_blocks mb R R' MST1). unfold blocks_MEMBIO. apply Forall_forall. intros iv Hiv.
      apply Forall_cons; [exact (proj1 (Forall_forall _ _) BW1 iv Hiv)|]. apply Forall_cons; [exact (proj1 (Forall_forall _ _) BW2 iv Hiv)|].
      apply Forall_cons; [exact (proj1 (Forall_forall _ _) BW3 iv Hiv)|]. apply Forall_cons; [exact (proj1 (Forall_forall _ _) BW4 iv Hiv)| apply Forall_nil].
    - destruct MSH1 as (X1 & X2 & X3 & X4). unfold MEMBIO_shad in *. rewrite T3 in X2. rewrite T4 in X3. rewrite T5 in X4. rewrite T3, T4, T5. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
      split; [| split; [| split]].
      + eapply addressable_acrossX; [exact X1| exact MU13| exact WM13| clear - E1a; lia| unfold AAPP_HI; clear - E1b ACB; lia| exact BX1].
      + eapply addressable_acrossX; [exact X2| exact MU13| exact WM13| clear - E2a; lia| unfold AAPP_HI; clear - E2b ACB; lia| exact BX2].
      + eapply addressable_acrossX; [exact X3| exact MU13| exact WM13| clear - E3a; lia| unfold AAPP_HI; clear - E3b ACB; lia| exact BX3].
      + eapply addressable_acrossX; [exact X4| exact MU13| exact WM13| clear - E4a; lia| unfold AAPP_HI; clear - E4b ACB; lia| exact BX4].
    - (* [comment removed for export] *)
      pose proof MBO as MBq. destruct MBq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LENR & BUFP & BUFH & _).
      destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      + assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil.
        clear - BUFP BUFH ACB L0Z. lia.
      + destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN _]].
        pose proof (BLK0 _ (SUB0 _ PIN)) as (_ & EP2 & _ & EPa & EPb & EPf & EPc). cbn [blk_addr blk_size fst snd] in EP2, EPa, EPb, EPf, EPc.
        destruct (BW (mb_buf R) (mb_len R) EP2 ltac:(clear - LNZ LENR; lia) EPa EPb EPf EPc) as [BWP _].
        eapply bytes_at_transport; [exact DS1| exact MU13|]. unfold zlength in DSL. rewrite DSL.
        clear - BWP. induction WX as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv BWP) as K. cbn in K. split; [lia| exact (IH (Forall_inv_tail BWP))].
    - eapply rw_cells_transport; [exact SC1| exact MU13| exact WM13|]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ].
      clear - BWS. induction WX as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv BWS) as K. cbn in K. split; [lia| exact (IH (Forall_inv_tail BWS))].
    - rewrite SEQ in SSH1 |- *. apply (proj2 (STORE_shad_empty _ _ _)). apply (proj1 (STORE_shad_empty _ _ _)) in SSH1. destruct SSH1 as [SH1 SH2].
      split; [exact SH1|]. eapply addressable_acrossX; [exact SH2| exact MU13| exact WM13| clear - SBa; lia| exact SH1| exact BXS].
  Qed.

  (* [comment removed for export] *)
  Definition LEDGER (sX : as_St H) (um uf : Z) : Prop := 0 <= um /\ 0 <= uf /\ as_AL H sX >= as_AL H s - as_Cm H um - as_Cf H uf.
  Lemma LEDGER_step : forall sX sY um uf a b, LEDGER sX um uf -> 0 <= a -> 0 <= b -> as_AL H sY >= as_AL H sX - as_Cm H a - as_Cf H b -> LEDGER sY (um + a) (uf + b).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros sX sY um uf a b (U0 & F0 & L) A0' B0 L'. pose proof (ah_costs H HH) as (_ & _ & _ & _ & SAM & SAF).
    pose proof (SAM um a U0 A0'). pose proof (SAF uf b F0 B0). split; [lia|]. split; [lia|]. lia.
  Qed.
  Lemma errph_cost_nonneg : forall ph, 0 <= errph_cost H ph.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM. intros [|c]; cbn [errph_cost]; [| lia]. unfold ERRINIT_COST, ERRINIT_BYTES. pose proof (ah_costs H HH) as (CM0 & _ & CF0 & _). pose proof (CM0 (2^16) ltac:(lia)). pose proof (CF0 (2^16) ltac:(lia)). lia. Qed.
  Lemma LEDGER_pay : forall sX um uf a b, LEDGER sX um uf -> 0 <= a -> 0 <= b -> um + a <= DECODE_CUM_BYTES -> uf + b <= DECODE_CUM_BYTES -> as_Cm H a + as_Cf H b <= as_AL H sX.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros sX um uf a b (U0 & F0 & L) A0' B0 UA UB. pose proof (ah_costs H HH) as (CM0 & CMM & CF0 & CFM & SAM & SAF).
    unfold READCFG_COST in ALW. pose proof (errph_cost_nonneg (mid_err M)).
    pose proof (SAM um a U0 A0'). pose proof (SAF uf b F0 B0). pose proof (CMM (um + a) DECODE_CUM_BYTES ltac:(lia)). pose proof (CFM (uf + b) DECODE_CUM_BYTES ltac:(lia)). lia.
  Qed.
  Lemma LEDGER_post : forall sX um uf, LEDGER sX um uf -> um <= DECODE_CUM_BYTES -> uf <= DECODE_CUM_BYTES -> as_AL H sX >= as_AL H s - READCFG_COST H M.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros sX um uf (U0 & F0 & L) UA UB. pose proof (ah_costs H HH) as (CM0 & CMM & CF0 & CFM & _). unfold READCFG_COST.
    pose proof (errph_cost_nonneg (mid_err M)). pose proof (CMM um DECODE_CUM_BYTES ltac:(lia)). pose proof (CFM uf DECODE_CUM_BYTES ltac:(lia)). lia.
  Qed.
  Lemma errph_bytes_range : forall ph, 0 <= errph_bytes ph <= 2^16 /\ 0 <= errph_cnt ph <= ERRINIT_CNT.
  Proof. clear. intros [|c]; cbn; unfold ERRINIT_BYTES, ERRINIT_CNT; lia. Qed.

  (* [comment removed for export] *)
  Lemma arp_raise :
    forall (spw gpw t0' t1' t2' s0w s1w a0w a1w a2w a3w a4w a5w a6w a7w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t3' t4' t5' t6' : word)
           (Fx : bvmap 5 word) (fcx : bv 32) (msFx : machine_state) (mx : mem) (mox : Model) (sx : as_St H) (LIBc Lc : list block) (LFc : list fframe)
           (Mx : libmid) (xx : ctxinfo) (lox Bx : Z) (errvx : word) (CHc : list (Z * Z)) (ra1 ra2 ra3 line reason : Z) (Q : config -> Prop),
      as_VIS H sx msFx = MS (mkR (Z_to_bv 64 ra1) spw gpw (Z_to_bv 64 ATP) t0' t1' t2' s0w s1w a0w a1w a2w a3w a4w a5w a6w a7w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t3' t4' t5' t6')
                           Fx (Z_to_bv 64 P_ERR_new) fcx None mx (seg_rom asegs) ->
      as_RHEAP H sx (mid_errblocks Mx ++ Lc) mx -> as_AKREL H sx (mkCfg msFx mox) ->
      LIBMID LIBc mx Mx -> (forall b, In b LIBc -> In b Lc) -> mid_ctx Mx = CtxReady xx -> mid_flag Mx = 1 ->
      lb_bytes (mid_errblocks Mx ++ Lc) + errph_bytes (mid_err Mx) + ERRDEBUG_BYTES <= as_LIVE_MAX H ->
      Z.of_nat (length (mid_errblocks Mx ++ Lc)) + errph_cnt (mid_err Mx) + 2 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H mx Bx -> bv_unsigned spw <= Bx -> bv_unsigned spw mod 16 = 0 ->
      stk asegs mx lox (bv_unsigned spw) -> aceil <= lox -> lox <= bv_unsigned spw - RAISE_STACK (mid_err Mx) -> errph_sh0 (mid_err Mx) mx lox spw ->
      rw_cells asegs mx (errno_addr (Z_to_bv 64 ATP)) [C4 errvx] -> mem_inv asegs mx -> ACONST mx ->
      as_RFS H LFc mx -> (length LFc + ERRPH_LF (mid_err Mx) <= AFS_MAXLIVE)%nat ->
      as_chain H mx (bv_unsigned s0w) CHc -> (forall fp' ra', In (fp', ra') CHc -> bv_unsigned spw + 16 <= fp') ->
      pf_ok (as_TR H) (PF_errnew (mid_err Mx)) ra1 CHc -> pf_ok (as_TR H) PF_errdebug ra2 CHc -> pf_ok (as_TR H) PF_errseterr ra3 CHc ->
      errph_closed_ok H (mid_err Mx) -> RAISE_COST H (mid_err Mx) <= as_AL H sx ->
      0 <= line < 2^31 -> 0 < reason < 2^23 ->
      0 <= ra1 < 2^64 -> ra1 mod 2 = 0 -> 0 <= ra2 < 2^64 -> ra2 mod 2 = 0 -> 0 <= ra3 < 2^64 -> ra3 mod 2 = 0 ->
      arp_glue ra1 ra2 P_ERR_set_debug ARP_FILE line ARP_FUNC -> arp_glue ra2 ra3 P_ERR_set_error AERR_LIB_SSL reason 0 ->
      (forall (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (msF' : machine_state) (m' : mem) (mo' : Model) (s' : as_St H) (errv' : word)
              (LE : list block) (M' : libmid) (c : errchain) (XS : list (Z * Z)),
         as_VIS H s' msF' = MS (mkR (Z_to_bv 64 ra3) spw gpw (Z_to_bv 64 ATP) u0 u1 u2 s0w s1w b0 b1 b2 b3 b4 b5 b6 b7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6)
                             Fx (ret_pc (Z_to_bv 64 ra3)) fcx None m' (seg_rom asegs) ->
         as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mox mo' -> mem_inv asegs m' -> ACONST m' -> stk asegs m' lox (bv_unsigned spw) -> as_rauxv_ok H m' Bx ->
         as_RHEAP H s' (mid_errblocks M' ++ LE ++ Lc) m' ->
         LIBMID (LE ++ LIBc) m' M' -> mid_step Mx M' -> mid_newlib_ok Mx M' LE ->
         mid_flag M' = 1 -> mid_ctx M' = CtxReady xx -> mid_err M' = ErrReady c -> mid_vdso M' = mid_vdso Mx -> errph_delta (mid_err Mx) LE c ->
         Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M') <= ERRSTR_BYTES ->
         rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv'] ->
         Forall (fs_scratch H LFc) XS -> xpres H Lc (bv_unsigned spw) (XS ++ ERR_XE ++ memflag_foot ++ errph_foot (mid_err Mx)) mx m' ->
         as_RFS H LFc m' -> as_AL H s' >= as_AL H sx - RAISE_COST H (mid_err Mx) ->
         as_SR H Q (mkCfg msF' mo')) ->
      as_SR H Q (mkCfg msFx mox).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros until Q. intros VISx HPx KRELx LMx SUBx CXx F1x BYx CNx AUXx SPBx SPAx STx CEILx LOx SH0x ERRx MIx ACx RFx LFBx CHNx CHBx P1 P2 P3 CLO ALx LNR REAS R1 R1E R2 R2E R3 R3E G1 G2 K.
    pose proof LMx as (IM & MF & CP & EPm & EX & VD & CL & FIT & GM & GE & GX & MM & MB & HT & RL & SH & BL).
    destruct Mx as [f cph eph E v]. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. subst cph f.
    unfold mid_errblocks in *. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. cbn [ERRPH_mid] in EPm.
    assert (EP : ERRPH Lc mx eph) by (eapply ERRPH_mono; [exact EPm| exact SUBx]).
    assert (CPc : CTXPH Lc mx (CtxReady xx)) by (eapply (CTXPH_mono LIBc Lc SUBx); exact CP).
    unfold arp_glue in G1, G2. unfold araise_stmt in RAISE.
    eapply RAISE with (lo := lox) (B := Bx) (LB := Lc) (s := sx) (ph := eph) (E := E) (x := xx) (errv := errvx) (LF := LFc) (CH := CHc)
      (file := ARP_FILE) (fs := S_ARP_FILE) (fsl := K_ARP_FILE) (func := ARP_FUNC) (gs := S_ARP_FUNC) (gsl := K_ARP_FUNC)
      (line := line) (lib := AERR_LIB_SSL) (reason := reason) (ra1 := ra1) (ra2 := ra2) (ra3 := ra3).
    all: try first [exact VISx| exact HPx| exact KRELx| exact AUXx| exact SPBx| exact SPAx| exact STx| exact CEILx| exact LOx| exact SH0x| exact ERRx| exact MIx| exact ACx| exact MF| exact IM| exact GM| exact RL
                    | exact EP| exact EX| exact BL| exact SH| exact CPc| exact RFx| exact LFBx| exact CHNx| exact CHBx| exact P1| exact P2| exact P3| exact CLO| exact ALx
                    | exact R_ARP_FILE| exact R_ARP_FUNC| exact LNR| exact REAS| exact R1| exact R1E| exact R2| exact R2E| exact R3| exact R3E].
    all: lazymatch goal with
         | |- lb_bytes _ + raise_bytes _ <= _ => unfold raise_bytes; clear - BYx; lia
         | |- Z.of_nat _ + raise_cnt _ <= _ => unfold raise_cnt; clear - CNx; lia
         | |- Z_to_bv 64 ATP = _ => reflexivity
         | |- _ <> [] => discriminate
         | |- Z.of_nat (length S_ARP_FILE) < _ => rewrite S_ARP_FILE_len; clear; lia
         | |- Z.of_nat (length S_ARP_FUNC) < _ => rewrite S_ARP_FUNC_len; clear; lia
         | |- 0 < ARP_FILE => unfold ARP_FILE; clear; lia
         | |- 0 < ARP_FUNC => unfold ARP_FUNC; clear; lia
         | |- 0 < AERR_LIB_SSL < 256 => unfold AERR_LIB_SSL; clear; lia
         | |- AERR_LIB_SSL <> 2 => unfold AERR_LIB_SSL; clear; lia
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mq : mem), mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_debug) _ _ _ _) _ =>
             intros; eapply G1; assumption
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mq : mem), mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_error) _ _ _ _) _ =>
             intros; eapply G2; assumption
         | |- ?G => idtac "ARP_RAISE_LEFT" G
         end.
    (* [comment removed for export] *)
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 msF' m' mo' s' errv' LBN c p1 p2 Ad1 Ad2
           VIS' KREL' MP' MI' AC' ST' AUX' HP' MF' IM' GM' RL' ERR' DL RSZ EP' CP' EST' SHC' XS SCR XP' RF' AL'.
    set (n1 := Z.of_nat (length S_ARP_FILE) + 1) in *. set (n2 := Z.of_nat (length S_ARP_FUNC) + 1) in *.
    set (E' := errst_raise E Ad1 p1 n1 line Ad2 p2 n2 AERR_LIB_SSL reason) in *.
    pose proof (errst_fits_raise E Ad1 p1 n1 line Ad2 p2 n2 AERR_LIB_SSL reason FIT RSZ) as FIT'. change (errst_fits E') in FIT'.
    pose proof (LIBMID_errcall H HH sx mx s' LIBc Lc (bv_unsigned spw) XS LFc LBN mx m' (mkMID 1 (CtxReady xx) eph E v) xx c E'
                  HPx SUBx LMx eq_refl RFx SCR XP' HP' CP' EP' DL EST' FIT' SHC' MF') as LM'.
    cbn [mid_vdso] in LM'.
    assert (LEN' : length (es_slots E') = 16%nat) by exact (proj1 (proj1 EST')).
    pose proof (errst_fits_bounds E' LEN' FIT') as [EC' EB'].
    eapply (K u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 msF' m' mo' s' errv' LBN (mkMID 1 (CtxReady xx) (ErrReady c) E' v) c XS);
      cbn [mid_flag mid_ctx mid_err mid_E mid_vdso mid_errblocks]; try reflexivity.
    all: try first [exact VIS'| exact KREL'| exact MP'| exact MI'| exact AC'| exact ST'| exact AUX'| exact HP'| exact LM'| exact DL| exact EC'| exact EB'| exact ERR'| exact SCR| exact XP'| exact RF'| exact AL'].
    - (* [comment removed for export] *) unfold mid_step. cbn [mid_flag mid_ctx mid_err mid_vdso]. split; [reflexivity|]. split; [intros b Hb; exact Hb|].
      split; [| intros Hv; exact Hv]. intros c0 ->. cbn [errph_delta] in DL. destruct DL as [-> _]. reflexivity.
    - (* [comment removed for export] *) unfold mid_newlib_ok. cbn [mid_ctx mid_err]. exists [], LBN. split; [apply Permutation_refl|]. split; [reflexivity|].
      destruct eph as [|c0]; [exact DL|]. cbn [errph_delta] in DL. destruct DL as [_ ->]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition XR (Mq : libmid) (XS : list (Z * Z)) : list (Z * Z) := XS ++ ERR_XE ++ memflag_foot ++ errph_foot (mid_err Mq).
  Definition avoids (X : list (Z * Z)) (a n : Z) : Prop := Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) X.
  Definition shavoids (X : list (Z * Z)) (a n : Z) : Prop := Forall (fun iv : Z * Z => sh a + nsh n <= fst iv \/ snd iv <= sh a) X.

  Lemma app_vs_sh' : forall A n Bk k, aapp A n -> 0 <= n -> aapp Bk k -> 0 <= k -> A + n <= sh Bk \/ sh Bk + nsh k <= A.
  Proof.
    clear. intros A n Bk k APA Hn APB Hk. acb. pose proof (sh_aapp_range Bk k APB Hk) as (X1 & X2 & X3).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in X1.
    clear APB. destruct APA as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO, AIMG_TOP in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma es_facts : forall LIBq mq Mq xq c0, LIBMID LIBq mq Mq -> mid_ctx Mq = CtxReady xq -> mid_err Mq = ErrReady c0 ->
    In (ec_es c0) LIBq /\ blk_size (ec_es c0) = ERRST_SIZE.
  Proof.
    clear. intros LIBq mq Mq xq c0 LMq CXq EQ. destruct LMq as (_ & _ & _ & EPm & _). rewrite CXq, EQ in EPm. cbn [ERRPH_mid ERRPH] in EPm.
    destruct EPm as [_ CHc]. pose proof CHc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _). split; [exact I5| exact Z5].
  Qed.

  Section XRW.
    (* [comment removed for export] *)
    Variables (Mq : libmid) (xq : ctxinfo) (sq : as_St H) (L : list block) (mq : mem) (LFq : list fframe) (mf : mem) (XS : list (Z * Z)) (LIBq : list block) (ml : mem).
    Hypothesis HPq : as_RHEAP H sq L mq.
    Hypothesis RFq : as_RFS H LFq mf.
    Hypothesis FXS : Forall (fs_scratch H LFq) XS.
    Hypothesis LMq : LIBMID LIBq ml Mq.
    Hypothesis CTXq : mid_ctx Mq = CtxReady xq.
    Hypothesis SUBq : forall b, In b LIBq -> In b L.

    Lemma es_in : forall c0, mid_err Mq = ErrReady c0 -> In (ec_es c0) L /\ blk_size (ec_es c0) = ERRST_SIZE.
    Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM HPq RFq FXS LMq CTXq SUBq. intros c0 EQ. destruct (es_facts _ _ _ _ _ LMq CTXq EQ) as [I5 Z5]. split; [exact (SUBq _ I5)| exact Z5]. Qed.
    Lemma errph_belowM : errph_below (mid_err Mq) aceil.
    Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM HPq RFq FXS LMq CTXq SUBq. destruct LMq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BL). exact BL. Qed.

    (* [comment removed for export] *)
    Lemma XR_block : forall b, In b L -> (forall c0, mid_err Mq = ErrReady c0 -> blk_id (ec_es c0) <> blk_id b) ->
      avoids (XR Mq XS) (blk_addr b) (blk_size b) /\ shavoids (XR Mq XS) (blk_addr b) (blk_size b).
    Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM HPq RFq FXS LMq CTXq SUBq.
      intros b Hb HES. acb. destruct b as [[q A] n]. cbn [blk_id blk_addr blk_size fst snd] in *.
      pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in B1, B2, B3, B4, B5, B6, B7.
      pose proof (aapp_bounds _ _ B7 B3) as (Q1 & Q2 & Q3 & Q4 & _). pose proof (sh_aapp_range _ _ B7 B3) as (S1' & S2 & S3).
      assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in S1'.
      unfold XR, avoids, shavoids. split; (apply Forall_app; split; [| apply Forall_app; split; [| apply Forall_app; split]]).
      - eapply Forall_impl; [| exact FXS]. cbn beta. intros iv SC. exact (fsobj_scratch H HH LFq A n mf iv RFq (fsobj_block H HH _ _ _ LFq _ _ _ HPq Hb) ltac:(lia) B3 ltac:(lia) B7 SC).
      - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
          A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
        unfold AIMG_TOP in B4. cbn [app]. clear - B4. repeat (apply Forall_cons; [right; cbn; lia|]). apply Forall_nil.
      - unfold memflag_foot, A_mem_inited. unfold AIMG_TOP in B4. clear - B4. apply Forall_cons; [right; cbn; lia| apply Forall_nil].
      - destruct (mid_err Mq) as [|c0] eqn:EQ; cbn [errph_foot]; [apply Forall_nil|]. destruct (es_in c0 EQ) as [IE SZ].
        pose proof (ah_disj H HH _ _ _ _ _ HPq IE Hb (HES c0 eq_refl)) as DJ. cbn [blk_addr blk_size fst snd] in DJ. rewrite SZ in DJ.
        apply Forall_cons; [cbn [fst snd]; clear - DJ; lia| apply Forall_nil].
      - eapply Forall_impl; [| exact FXS]. cbn beta. intros iv SC. exact (fsobj_scratch_sh H HH LFq A n mf iv RFq (fsobj_block H HH _ _ _ LFq _ _ _ HPq Hb) ltac:(lia) B3 ltac:(lia) SC).
      - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
          A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
        cbn [app]. clear - S1'. repeat (apply Forall_cons; [right; cbn; lia|]). apply Forall_nil.
      - unfold memflag_foot, A_mem_inited. clear - S1'. apply Forall_cons; [right; cbn; lia| apply Forall_nil].
      - destruct (mid_err Mq) as [|c0] eqn:EQ; cbn [errph_foot]; [apply Forall_nil|]. destruct (es_in c0 EQ) as [IE SZ].
        pose proof (ah_blocks H HH _ _ _ _ HPq IE) as (_ & _ & E3 & _ & _ & _ & E7). rewrite SZ in E3, E7.
        apply Forall_cons; [cbn [fst snd]; pose proof (app_vs_sh' _ _ _ _ E7 E3 B7 B3); lia| apply Forall_nil].
    Qed.
    (* [comment removed for export] *)
    Lemma XR_stack : forall a n, aceil <= a -> avoids (XR Mq XS) a n.
    Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM HPq RFq FXS LMq CTXq SUBq.
      intros a n Ha. unfold XR, avoids. apply Forall_app. split.
      - eapply Forall_impl; [| exact (fs_scratch_range_Forall H HH _ _ _ RFq FXS)]. cbn beta. intros iv K. lia.
      - eapply (raise_foot_frame (mid_err Mq) a n aceil); [apply Z.le_refl| exact Ha| exact errph_belowM].
    Qed.
    (* [comment removed for export] *)
    Lemma XR_low : Forall (fun iv : Z * Z => snd iv <= aceil) (XR Mq XS).
    Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM HPq RFq FXS LMq CTXq SUBq.
      acb. unfold XR. apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split]].
      - eapply Forall_impl; [| exact (fs_scratch_range_Forall H HH _ _ _ RFq FXS)]. cbn beta. intros iv K. lia.
      - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
          A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
        cbn [app]. clear - ACEILB. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
      - unfold memflag_foot, A_mem_inited. clear - ACEILB. apply Forall_cons; [cbn; lia| apply Forall_nil].
      - destruct (mid_err Mq) as [|c0] eqn:EQ; cbn [errph_foot]; [apply Forall_nil|]. destruct (es_in c0 EQ) as [IE SZ].
        pose proof (ah_blocks H HH _ _ _ _ HPq IE) as (_ & _ & _ & _ & E5 & _). rewrite SZ in E5. apply Forall_cons; [cbn [fst snd]; exact E5| apply Forall_nil].
    Qed.
    (* [comment removed for export] *)
    Lemma XR_stack0 : Forall stack0_ok (XR Mq XS).
    Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM HPq RFq FXS LMq CTXq SUBq.
      acb. unfold XR. pose proof (RFS_fsb H HH _ _ RFq) as (F1 & F2 & F3 & F4).
      assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. assert (LEA : AIMG_TOP <= aceil) by (unfold AIMG_TOP; lia). pose proof (sh_mono AIMG_TOP aceil LEA) as SM. rewrite S0 in SM.
      apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split]].
      - eapply Forall_impl; [| exact FXS]. intros iv SC. unfold stack0_ok. destruct SC as [->|(k & ff & fp & FF & EE)]; cbn [fst snd].
        + pose proof (aapp_not_shadowland _ _ F4). pose proof (sh_aapp_range _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (FS1 & _). rewrite S0 in FS1. unfold AFS_FLAGS, AFS_SIZE, ALOWSH_LO in *. lia.
        + pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
          pose proof (aapp_not_shadowland _ _ P9) as FNS. pose proof (sh_aapp_range _ _ P9 ltac:(unfold AFS_SIZE; lia)) as (FS1 & FS2 & FS3). rewrite S0 in FS1.
          pose proof (fsz_pos k ltac:(lia)).
          destruct EE as [-> |[-> | ->]]; cbn [fst snd]; unfold AFS_FLAGS, AFS_SIZE, AFS_HDR, ALOWSH_LO in *; [lia| lia|].
          right. assert (LE1 : ff + fsz k <= as_FSB H + 11571200) by (clear - P6; lia). pose proof (sh_mono _ _ LE1) as SM1. pose proof (sh_mono _ _ P8) as SM2.
          assert (E8 : sh (ff + fsz k) = sh ff + fshn k) by (unfold fshn, fsz, sh; clear - M8; Z.div_mod_to_equations; nia). rewrite <- E8. clear - SM1 SM2. lia.
      - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
          A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
        cbn [app]. clear - SM. repeat (apply Forall_cons; [right; cbn; lia|]). apply Forall_nil.
      - unfold memflag_foot, A_mem_inited. clear - SM. apply Forall_cons; [right; cbn; lia| apply Forall_nil].
      - destruct (mid_err Mq) as [|c0] eqn:EQ; cbn [errph_foot]; [apply Forall_nil|]. destruct (es_in c0 EQ) as [IE SZ].
        pose proof (ah_blocks H HH _ _ _ _ HPq IE) as (_ & _ & E3 & _ & _ & _ & E7). rewrite SZ in E3, E7.
        apply Forall_cons; [eapply stack0_ok_aapp; [exact E7| cbn; lia| cbn; lia]| apply Forall_nil].
    Qed.
    (* [comment removed for export] *)
    Lemma XR_ff : forall ff fp, In (6, ff, fp) LFq -> avoids (XR Mq XS) ff 4096 /\ shavoids (XR Mq XS) ff 4096.
    Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM HPq RFq FXS LMq CTXq SUBq.
      intros ff fp FIN. acb.
      pose proof (ah_RFS_range H HH _ _ RFq) as [AFq ARq]. pose proof (ARq (6, ff, fp) FIN) as AR. cbn [ff_class ff_addr ff_flag fst snd] in AR.
      destruct AR as (_ & R1 & R2 & R3 & R4). change (fsz 6) with 4096 in R2, R3. destruct AFq as (F1 & F2 & F3 & F4).
      assert (FO : fsobj H LFq ff 4096) by (right; exists (6, ff, fp); split; [exact FIN| cbn [ff_addr ff_class fst snd]; change (fsz 6) with 4096; lia]).
      assert (APff : aapp ff 4096) by (eapply aapp_sub; [exact F4| unfold AFS_HDR in R1; lia| exact R2]).
      assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. pose proof (sh_aapp_range _ _ APff ltac:(lia)) as (V1 & V2 & V3). rewrite S0 in V1.
      unfold XR, avoids, shavoids. unfold AFS_HDR, AFS_SIZE, AIMG_TOP in *. split; (apply Forall_app; split; [| apply Forall_app; split; [| apply Forall_app; split]]).
      - eapply Forall_impl; [| exact FXS]. cbn beta. intros iv SC. exact (fsobj_scratch H HH LFq ff 4096 mf iv RFq FO ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia) APff SC).
      - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
          A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
        cbn [app]. clear - R1 F1. repeat (apply Forall_cons; [right; cbn; lia|]). apply Forall_nil.
      - unfold memflag_foot, A_mem_inited. clear - R1 F1. apply Forall_cons; [right; cbn; lia| apply Forall_nil].
      - destruct (mid_err Mq) as [|c0] eqn:EQ; cbn [errph_foot]; [apply Forall_nil|]. destruct (es_in c0 EQ) as [IE SZ].
        pose proof (ah_blocks H HH _ _ _ _ HPq IE) as (_ & _ & _ & _ & _ & E6 & _). rewrite SZ in E6. unfold AFS_SIZE in E6.
        apply Forall_cons; [cbn [fst snd]; clear - E6 R1 R2; lia| apply Forall_nil].
      - eapply Forall_impl; [| exact FXS]. cbn beta. intros iv SC. exact (fsobj_scratch_sh H HH LFq ff 4096 mf iv RFq FO ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia) SC).
      - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
          A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
        cbn [app]. clear - V1. repeat (apply Forall_cons; [right; cbn; lia|]). apply Forall_nil.
      - unfold memflag_foot, A_mem_inited. clear - V1. apply Forall_cons; [right; cbn; lia| apply Forall_nil].
      - destruct (mid_err Mq) as [|c0] eqn:EQ; cbn [errph_foot]; [apply Forall_nil|]. destruct (es_in c0 EQ) as [IE SZ].
        pose proof (ah_blocks H HH _ _ _ _ HPq IE) as (_ & _ & E3 & _ & _ & _ & E7). rewrite SZ in E3, E7.
        apply Forall_cons; [cbn [fst snd]; pose proof (app_vs_sh' _ _ _ _ E7 E3 APff ltac:(lia)); unfold nsh in *; lia| apply Forall_nil].
    Qed.
  End XRW.

  (* [comment removed for export] *)
  Lemma chain_keepX : forall LBx SP X mA mB cur CHq,
    as_chain H mA cur CHq -> xpres H LBx SP X mA mB -> (forall fpq raq, In (fpq, raq) CHq -> SP + 16 <= fpq) -> aceil <= SP ->
    Forall (fun iv : Z * Z => snd iv <= aceil) X -> as_chain H mB cur CHq.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros LBx SP X mA mB cur CHq C XP HS CE FX. eapply (ah_chain_ext H HH); [exact C|].
    intros fpq raq a IN Ha. pose proof (HS _ _ IN). pose proof (ah_chain_range H HH _ _ _ _ _ C IN) as (R1 & R2 & R3). acb.
    apply XP; [lia|]. split; [left; lia|]. intros K. destruct (rin_ivs_In _ _ K) as (iv & I & Riv).
    pose proof (proj1 (Forall_forall _ _) FX iv I) as Bq. cbn beta in Bq. lia.
  Qed.
  Lemma fs_scratch_mono : forall f LFq iv, fs_scratch H (f :: LFq) iv -> fs_scratch H LFq iv.
  Proof.
    clear. intros f LFq iv [K|(k & ff & fp & FF & E)]; [left; exact K| right]. exists k, ff, fp. split; [| exact E].
    destruct FF as (A1' & A2' & A3'). split; [exact A1'|]. split; [exact A2'|]. intros g Hg. apply A3'. right. exact Hg.
  Qed.

  (* [comment removed for export] *)
  Lemma rp_raiseW :
    forall (t0' t1' t2' a0w a1w a2w a3w a4w a5w a6w a7w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t3' t4' t5' t6' : word)
           (msFx : machine_state) (mx : mem) (mox : Model) (sx : as_St H) (Lx LIBq : list block) (Mq : libmid) (ff fp : Z) (errvx : word)
           (ra1 ra2 ra3 line reason : Z) (Q : config -> Prop),
      as_VIS H sx msFx = MS (mkR (Z_to_bv 64 ra1) (Z_to_bv 64 S1) gp (Z_to_bv 64 ATP) t0' t1' t2' sp (Z_to_bv 64 S1) a0w a1w a2w a3w a4w a5w a6w a7w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t3' t4' t5' t6')
                           F (Z_to_bv 64 P_ERR_new) fc None mx (seg_rom asegs) ->
      as_RHEAP H sx (mid_errblocks Mq ++ Lx ++ LB) mx -> as_AKREL H sx (mkCfg msFx mox) ->
      LIBMID LIBq mx Mq -> (forall b, In b LIBq -> In b (Lx ++ LB)) -> mid_ctx Mq = CtxReady x -> mid_flag Mq = 1 ->
      lb_bytes (mid_errblocks Mq ++ Lx ++ LB) + errph_bytes (mid_err Mq) + ERRDEBUG_BYTES <= as_LIVE_MAX H ->
      Z.of_nat (length (mid_errblocks Mq ++ Lx ++ LB)) + errph_cnt (mid_err Mq) + 2 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H mx B -> stk asegs mx lo S1 -> lo <= S1 - RAISE_STACK (mid_err Mq) -> stack0 mx lo (bv_unsigned sp) ->
      rw_cells asegs mx (errno_addr (Z_to_bv 64 ATP)) [C4 errvx] -> mem_inv asegs mx -> ACONST mx ->
      as_RFS H (LF1 ff fp) mx -> (length (LF1 ff fp) + ERRPH_LF (mid_err Mq) <= AFS_MAXLIVE)%nat ->
      as_chain H mx (bv_unsigned sp) CH1 ->
      pf_ok (as_TR H) (PF_errnew (mid_err Mq)) ra1 CH1 -> pf_ok (as_TR H) PF_errdebug ra2 CH1 -> pf_ok (as_TR H) PF_errseterr ra3 CH1 ->
      errph_closed_ok H (mid_err Mq) -> RAISE_COST H (mid_err Mq) <= as_AL H sx ->
      0 <= line < 2^31 -> 0 < reason < 2^23 ->
      0 <= ra1 < 2^64 -> ra1 mod 2 = 0 -> 0 <= ra2 < 2^64 -> ra2 mod 2 = 0 -> 0 <= ra3 < 2^64 -> ra3 mod 2 = 0 ->
      arp_glue ra1 ra2 P_ERR_set_debug ARP_FILE line ARP_FUNC -> arp_glue ra2 ra3 P_ERR_set_error AERR_LIB_SSL reason 0 ->
      (forall (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (msF' : machine_state) (m' : mem) (mo' : Model) (s' : as_St H) (errv' : word)
              (LE : list block) (M' : libmid) (c : errchain) (XS : list (Z * Z)),
         as_VIS H s' msF' = MS (mkR (Z_to_bv 64 ra3) (Z_to_bv 64 S1) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1) b0 b1 b2 b3 b4 b5 b6 b7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6)
                             F (ret_pc (Z_to_bv 64 ra3)) fc None m' (seg_rom asegs) ->
         as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mox mo' -> mem_inv asegs m' -> ACONST m' -> stk asegs m' lo S1 -> as_rauxv_ok H m' B ->
         as_RHEAP H s' (mid_errblocks M' ++ LE ++ Lx ++ LB) m' ->
         LIBMID (LE ++ LIBq) m' M' -> mid_step Mq M' -> mid_newlib_ok Mq M' LE ->
         mid_flag M' = 1 -> mid_ctx M' = CtxReady x -> mid_err M' = ErrReady c -> mid_vdso M' = mid_vdso Mq -> errph_delta (mid_err Mq) LE c ->
         Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M') <= ERRSTR_BYTES ->
         rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv'] ->
         Forall (fs_scratch H LF) XS -> xpres H LB (bv_unsigned sp) (XS ++ ERR_XE ++ errph_foot (mid_err Mq)) mx m' ->
         as_RFS H (LF1 ff fp) m' -> as_AL H s' >= as_AL H sx - RAISE_COST H (mid_err Mq) ->
         (* [comment removed for export] *)
         (forall A cs, rw_cells asegs mx A cs -> S1 <= A -> A + Z.of_nat (cells_size cs) <= bv_unsigned sp -> rw_cells asegs m' A cs) ->
         (forall cs, rw_cells asegs mx ff cs -> Z.of_nat (cells_size cs) <= 4096 -> rw_cells asegs m' ff cs) ->
         (forall cs, rw_cells asegs mx (sh ff) cs -> Z.of_nat (cells_size cs) <= 512 -> rw_cells asegs m' (sh ff) cs) ->
         (forall b' A cs, In b' (Lx ++ LB) -> (forall c0, mid_err Mq = ErrReady c0 -> blk_id (ec_es c0) <> blk_id b') ->
            blk_addr b' <= A -> A + Z.of_nat (cells_size cs) <= blk_addr b' + blk_size b' -> rw_cells asegs mx A cs -> rw_cells asegs m' A cs) ->
         (forall b' A bs, In b' (Lx ++ LB) -> (forall c0, mid_err Mq = ErrReady c0 -> blk_id (ec_es c0) <> blk_id b') ->
            blk_addr b' <= A -> A + Z.of_nat (length bs) <= blk_addr b' + blk_size b' -> bytes_at asegs mx A bs -> bytes_at asegs m' A bs) ->
         (forall b' A n, In b' (Lx ++ LB) -> (forall c0, mid_err Mq = ErrReady c0 -> blk_id (ec_es c0) <> blk_id b') ->
            blk_addr b' <= A -> A + n <= blk_addr b' + blk_size b' -> A mod 8 = 0 -> 0 <= n -> addressable mx A n -> addressable m' A n) ->
         (stack0 mx lo (bv_unsigned sp) -> stack0 m' lo (bv_unsigned sp)) ->
         as_chain H m' (bv_unsigned sp) CH1 ->
         as_SR H Q (mkCfg msF' mo')) ->
      as_SR H Q (mkCfg msFx mox).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros until Q. intros VISx HPx KRELx LMx SUBx CXx F1x BYx CNx AUXx STx LOx ST0x ERRx MIx ACx RFx LFBx CHNx P1 P2 P3 CLO ALx LNR REAS R1 R1E R2 R2E R3 R3E G1 G2 K.
    destruct rc_facts as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). fold S1 in Q1, Q2.
    assert (CHBx : forall fp' ra', In (fp', ra') CH1 -> S1 + 16 <= fp').
    { intros fp' ra' [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
    eapply (arp_raise (Z_to_bv 64 S1) gp t0' t1' t2' sp (Z_to_bv 64 S1) a0w a1w a2w a3w a4w a5w a6w a7w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t3' t4' t5' t6'
              F fc msFx mx mox sx LIBq (Lx ++ LB) (LF1 ff fp) Mq x lo B errvx CH1 ra1 ra2 ra3 line reason Q VISx HPx KRELx LMx SUBx CXx F1x BYx CNx AUXx).
    all: rewrite ?unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    all: try first [exact STx| exact CEIL| exact LOx| exact ERRx| exact MIx| exact ACx| exact RFx| exact LFBx| exact CHBx| exact P1| exact P2| exact P3| exact CLO| exact ALx
                    | exact LNR| exact REAS| exact R1| exact R1E| exact R2| exact R2E| exact R3| exact R3E| exact G1| exact G2].
    all: lazymatch goal with
         | |- _ <= B => clear - SPB Q2; lia
         | |- _ mod 16 = 0 => clear - Q1; Z.div_mod_to_equations; lia
         | |- as_chain _ _ _ _ => exact CHNx
         | |- errph_sh0 _ _ _ _ => eapply (errph_sh0_sub (mid_err Mq) mx lo sp (Z_to_bv 64 S1));
                                   [destruct (mid_err Mq); [exact ST0x| exact I]| rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q2 CEIL LO STK0; lia
                                   | rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia]
         | |- _ => idtac
         end.
    (* [comment removed for export] *)
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 msF' m' mo' s' errv' LE M' c XS VIS' KREL' MP' MI' AC' ST' AUX' HP' LM' STEP' NEW' F' CX' ME' VD' DL' EC' EB' ERR' FXS XP' RF' AL'.
    rewrite ?unsigned_lit in ST', XP' by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    assert (SUBq : forall b, In b LIBq -> In b (mid_errblocks Mq ++ Lx ++ LB)) by (intros b Hb; apply in_or_app; right; exact (SUBx _ Hb)).
    pose proof (XR_block Mq x sx _ mx _ mx XS LIBq mx HPx RFx FXS LMx CXx SUBq) as XB.
    pose proof (XR_stack Mq x sx _ mx _ mx XS LIBq mx HPx RFx FXS LMx CXx SUBq) as XSK.
    pose proof (XR_low Mq x sx _ mx _ mx XS LIBq mx HPx RFx FXS LMx CXx SUBq) as XL.
    pose proof (XR_stack0 Mq x sx _ mx _ mx XS LIBq mx HPx RFx FXS LMx CXx SUBq) as X0.
    pose proof (XR_ff Mq x sx _ mx _ mx XS LIBq mx HPx RFx FXS LMx CXx SUBq ff fp (or_introl eq_refl)) as [XFa XFs].
    fold (XR Mq XS) in XP'.
    pose proof (fresh_frame_facts H _ _ _ _ (fresh_of_RFS H HH _ _ _ _ _ RFx)) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    assert (MFx : MEMFLAG mx 1) by (destruct LMx as (_ & MFq & _); rewrite F1x in MFq; exact MFq).
    assert (MF' : MEMFLAG m' 1) by (destruct LM' as (_ & MFq & _); rewrite F' in MFq; exact MFq).
    eapply (K u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 msF' m' mo' s' errv' LE M' c XS); clear K.
    all: try first [exact VIS'| exact KREL'| exact MP'| exact MI'| exact AC'| exact ST'| exact AUX'| exact HP'| exact LM'| exact STEP'| exact NEW'| exact F'| exact CX'| exact ME'| exact VD'| exact DL'
                    | exact EC'| exact EB'| exact ERR'| exact RF'| exact AL'].
    - (* [comment removed for export] *) eapply Forall_impl; [| exact FXS]. intros iv. apply fs_scratch_mono.
    - (* [comment removed for export] *)
      apply (axpres_drop_memflag H LB (bv_unsigned sp) (XS ++ ERR_XE ++ errph_foot (mid_err Mq)) mx m'); [| exact MFx| exact MF'].
      eapply xpres_weaken; [exact XP'| clear - Q2; lia| intros b Hb; apply in_or_app; right; exact Hb|].
      intros q Hq. unfold XR in Hq. apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; right; apply rin_ivs_app; left; exact Hq|].
      apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; right; apply rin_ivs_app; right; apply rin_ivs_app; left; exact Hq|].
      apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; exact Hq|].
      apply rin_ivs_app; right; apply rin_ivs_app; right; apply rin_ivs_app; right; exact Hq.
    - (* [comment removed for export] *) intros A cs RC HA HB. eapply (xpres_rw_cells' H); [exact XP'| exact RC| left; exact HA| apply XSK; clear - HA Q2 CEIL LO STK0; lia].
    - (* [comment removed for export] *) intros cs RC SZ. eapply (xpres_rw_cells' H); [exact XP'| exact RC| |].
      + right; right; right; right; left. unfold AFS_SIZE. clear - FF5 FF6 SZ. lia.
      + eapply Forall_impl; [| exact XFa]. cbn beta. intros iv K. clear - K SZ. lia.
    - (* [comment removed for export] *) intros cs RC SZ. eapply (xpres_rw_cells' H); [exact XP'| exact RC| |].
      + right; right; right; right; right; left. unfold AFS_SIZE.
        pose proof (sh_mono (as_FSB H) ff ltac:(clear - FF5; lia)) as Y1. pose proof (sh_mono (ff + 4096) _ FF6) as Y2.
        pose proof (sh_add8 ff 512) as Y3. replace (ff + 8 * 512) with (ff + 4096) in Y3 by (clear; lia). clear - Y1 Y2 Y3 SZ. lia.
      + eapply Forall_impl; [| exact XFs]. cbn beta. intros iv K. unfold nsh in K. clear - K SZ. lia.
    - (* [comment removed for export] *) intros b' A cs Hb' NE HA HB RC. destruct (XB b' ltac:(apply in_or_app; right; exact Hb') NE) as [AV _].
      eapply (xpres_rw_cells' H); [exact XP'| exact RC| right; right; left; exists b'; split; [exact Hb'| split; [exact HA| exact HB]]|].
      eapply Forall_impl; [| exact AV]. cbn beta. intros iv K. clear - K HA HB. lia.
    - (* [comment removed for export] *) intros b' A bs Hb' NE HA HB RC. destruct (XB b' ltac:(apply in_or_app; right; exact Hb') NE) as [AV _].
      eapply (xpres_bytes_at' H); [exact XP'| exact RC| right; right; left; exists b'; split; [exact Hb'| split; [exact HA| exact HB]]|].
      eapply Forall_impl; [| exact AV]. cbn beta. intros iv K. clear - K HA HB. lia.
    - (* [comment removed for export] *) intros b' A n Hb' NE HA HB A8 N0 AD. destruct (XB b' ltac:(apply in_or_app; right; exact Hb') NE) as [_ SAV].
      pose proof (ah_blocks H HH _ _ _ _ HPx ltac:(apply in_or_app; right; exact Hb')) as (D1 & D2 & D3 & _).
      eapply (blk_addressable_xpres H); [exact XP'| exact Hb'| exact HA| exact HB| clear - D1; lia| clear - D2; Z.div_mod_to_equations; lia| exact A8| exact N0| | exact AD].
      eapply Forall_impl; [| exact SAV]. cbn beta. intros iv K.
      pose proof (sh_mono (blk_addr b') A HA). assert (LE2 : sh A + nsh n <= sh (blk_addr b') + nsh (blk_size b')).
      { unfold sh, nsh. clear - HA HB D2 A8 N0. Z.div_mod_to_equations. lia. }
      clear - K H0 LE2. lia.
    - (* [comment removed for export] *) intros S00. eapply (stack0_xpres H); [exact XP'| exact S00| exact X0].
    - (* [comment removed for export] *) eapply chain_keepX; [exact CHNx| exact XP'| exact CHBx| clear - Q2 CEIL LO STK0; lia| exact XL].
  Qed.

  (* [comment removed for export] *)
  Lemma poke_carry : forall (ff fp : Z) (mA mB : mem) (sq : as_St H) (Lq : list block) (k : Z),
    fresh_frame H LF 6 ff fp -> 0 <= k < 512 ->
    munch [(sh ff + k, sh ff + k + 1)] mA mB -> wmono asegs mA mB ->
    as_RHEAP H sq Lq mA ->
       as_RHEAP H sq Lq mB
    /\ (as_rauxv_ok H mA B -> as_rauxv_ok H mB B)
    /\ (as_RFS H (LF1 ff fp) mA -> as_RFS H (LF1 ff fp) mB)
    /\ (forall LIBq Mq xq, LIBMID LIBq mA Mq -> mid_ctx Mq = CtxReady xq -> (forall b, In b LIBq -> In b Lq) -> (forall b, In b (mid_errblocks Mq) -> In b Lq) -> LIBMID LIBq mB Mq)
    /\ (forall A cs, rw_cells asegs mA A cs -> aceil <= A -> rw_cells asegs mB A cs)
    /\ (forall cs, rw_cells asegs mA ff cs -> Z.of_nat (cells_size cs) <= 4096 -> rw_cells asegs mB ff cs)
    /\ (forall b A cs, In b Lq -> blk_addr b <= A -> A + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b -> rw_cells asegs mA A cs -> rw_cells asegs mB A cs)
    /\ (forall b A bs, In b Lq -> blk_addr b <= A -> A + Z.of_nat (length bs) <= blk_addr b + blk_size b -> bytes_at asegs mA A bs -> bytes_at asegs mB A bs)
    /\ (forall b A n, In b Lq -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> addressable mA A n -> addressable mB A n)
    /\ (forall errvq, rw_cells asegs mA (errno_addr (Z_to_bv 64 ATP)) [C4 errvq] -> rw_cells asegs mB (errno_addr (Z_to_bv 64 ATP)) [C4 errvq])
    /\ (stack0 mA lo (bv_unsigned sp) -> stack0 mB lo (bv_unsigned sp))
    /\ (ACONST mA -> ACONST mB)
    /\ (forall loq hiq, stk asegs mA loq hiq -> aceil <= loq -> stk asegs mB loq hiq)
    /\ (forall cur CHq, as_chain H mA cur CHq -> (forall fpq raq, In (fpq, raq) CHq -> S1 + 16 <= fpq) -> as_chain H mB cur CHq)
    /\ (forall b A n, In b Lq -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> accessible mA A n -> accessible mB A n)
    /\ (forall X m0, xpres H LB (bv_unsigned sp) X m0 mA -> (forall a, sh ff + k <= a < sh ff + k + 1 -> rin_ivs X a) -> xpres H LB (bv_unsigned sp) X m0 mB)
    /\ (forall R', (forall b, In b LB -> In b Lq) -> mb_static R R' -> MEMBIO H LB mA mb R' -> MEMBIO H LB mB mb R')
    /\ (forall R', (forall b, In b LB -> In b Lq) -> mb_static R R' -> MEMBIO H LB mA mb R' -> MEMBIO_shad mA mb R' -> MEMBIO_shad mB mb R').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros ff fp mA mB sq Lq k FRESH KR MU WM HPq.
    destruct rc_facts as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). fold S1 in Q1, Q2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    assert (S0 : sh 0xc04000 = 0x80178800) by reflexivity.
    pose proof (sh_add8 ff 512) as SH8. replace (ff + 8 * 512) with (ff + 4096) in SH8 by (clear; lia).
    pose proof (sh_mono (as_FSB H) ff ltac:(clear - FF5; lia)) as SHL. pose proof (sh_mono (ff + 4096) (as_FSB H + 11571200) FF6) as SHU. pose proof (sh_mono _ _ FB2) as SHA.
    unfold AFS_SIZE in FB3. pose proof (sh_aapp_range _ _ FB3 ltac:(clear; lia)) as (W1 & W2 & W3). unfold nsh in W2. unfold AIMG_TOP in W1. pose proof (aapp_not_shadowland _ _ FB3) as NSF.
    assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) <= 0xc04000 - 4) by (clear; vm_compute; split; discriminate).
    set (W := [(sh ff + k, sh ff + k + 1)]) in *.
    assert (FW : Forall (fswin H) W) by (subst W; apply Forall_cons; [right; right; cbn; unfold AFS_SIZE; clear - SHL SHU SH8 KR; lia| apply Forall_nil]).
    (* [comment removed for export] *)
    assert (APP : forall A n, (A + n <= ALOWSH_LO \/ AHI_LO <= A) -> disjoint_from W A n).
    { intros A n AN. subst W. cbn. unfold ALOWSH_LO, AHI_LO in *. rewrite ?ASHADOW_BASE_val in *. clear - AN SHL SHU SH8 KR W1 W3 SHA S0. unfold sh in *. rewrite ?ASHADOW_BASE_val in *. split; [lia| exact I]. }
    assert (BWq : forall b A n, In b Lq -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> disjoint_from W A n /\ Forall (winX A n) W).
    { intros b A n Hb HA HB. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7). pose proof (aapp_not_shadowland _ _ D7) as NSb.
      split; [apply APP; clear - NSb HA HB; lia|]. subst W. apply Forall_cons; [| apply Forall_nil]. unfold winX. cbn. right; right.
      unfold AFS_SIZE in D6. unfold sh, nsh. clear - D2 D6 HA HB FF5 FF6 FF64 KR. Z.div_mod_to_equations. lia. }
    repeat match goal with |- _ /\ _ => split end.
    - eapply (ah_RHEAP_frame H HH); [exact HPq| exact MU| exact WM| eapply Forall_impl; [intros iv; apply fswin_cw| exact FW]].
    - intros AUXq. eapply (ah_rauxv_frame H HH); [exact AUXq| exact MU| exact WM| eapply Forall_impl; [intros iv; apply (fswin_cw LB)| exact FW]].
    - intros RFq. eapply (ah_RFS_frame H HH); [exact RFq| exact MU| exact WM|]. subst W. apply Forall_cons; [| apply Forall_nil].
      left. cbn. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, ALOWSH_LO, AHI_LO in *. clear - NSF SHL SHU SH8 SHA KR W1 W3 S0. unfold sh in *. rewrite ?ASHADOW_BASE_val in *. lia.
    - intros LIBq Mq xq LMq CXq SLq SEq. eapply (LIBMID_xfs0 H HH sq mA LIBq Lq S1 W mA mB Mq xq); [exact HPq| exact LMq| exact CXq| | exact SLq| exact SEq| exact FW].
      eapply (xpres_of_munch_gen H); [exact MU| exact WM|]. intros a Ha [_ HXa]. apply outside_of_not_rin. exact HXa.
    - intros A cs RC HA. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. apply APP. right. unfold AHI_LO. clear - HA ACB; lia.
    - intros cs RC SZ. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. apply APP. clear - NSF FF5 FF6 SZ. lia.
    - intros b A cs Hb HA HB RC. eapply rw_cells_transport; [exact RC| exact MU| exact WM| exact (proj1 (BWq b A _ Hb HA HB))].
    - intros b A bs Hb HA HB RC. eapply bytes_at_transport; [exact RC| exact MU| exact (proj1 (BWq b A _ Hb HA HB))].
    - intros b A n Hb HA HB N0 AD. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      eapply addressable_acrossX; [exact AD| exact MU| exact WM| clear - D1 HA; lia| unfold AAPP_HI; clear - D5 HB ACB; lia| exact (proj2 (BWq b A n Hb HA HB))].
    - intros errvq RC. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. apply APP. left. unfold ALOWSH_LO. clear - ERNG. cbn. lia.
    - intros S00. eapply stack0_transport; [exact S00| exact MU| exact WM|]. subst W. apply Forall_cons; [| apply Forall_nil].
      replace (sh ff + k) with (sh (ff + 8 * k)) by (rewrite sh_add8; reflexivity). apply stack0_ok_sh'; [clear - FF1 KR; lia| clear; lia| clear - FF6 FB2 KR; lia].
    - intros ACq. eapply ACONST_frame; [exact ACq| exact MU| exact WM|]. subst W. apply Forall_cons; [| apply Forall_nil].
      apply aconst_ok_high; cbn [fst snd]; clear - SHL W1 S0 KR; unfold sh in *; rewrite ?ASHADOW_BASE_val in *; unfold AIMG_TOP; lia.
    - intros loq hiq STq HLO. eapply stk_transport_disjoint; [exact STq| exact MU| exact WM|]. apply APP. right. unfold AHI_LO. clear - HLO ACB; lia.
    - intros cur CHq C HS. eapply (achain_below H HH mA mB _ _ _ (S1 + 16)); [exact C| exact HS| exact MU|].
      subst W. apply Forall_cons; [left; cbn; clear - SHU SHA W3 KR SH8 Q2 CEIL LO STK0 ACB; unfold AHI_LO in W3; lia| apply Forall_nil].
    - intros b A n Hb HA HB N0 ACC. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      eapply accessible_transport; [exact ACC| exact MU|]. intros y Hy. subst W. cbn. split; [| exact I].
      unfold AFS_SIZE in D6. clear - Hy HA HB D6 FF5 FF6 KR. unfold sh. Z.div_mod_to_equations. lia.
    - intros X m0 XP HXi. eapply xpres_trans; [exact XP|]. eapply (xpres_of_munch_gen H); [exact MU| exact WM|].
      intros a Ha [_ HXa]. subst W. cbn. split; [| exact I]. intros Ra. apply HXa. apply HXi. exact Ra.
    - intros R' SLQ MST MB. eapply (AMEMBIO_munch H LB W mA mB); [exact MB| exact MU| exact WM|].
      subst W. apply Forall_cons; [| apply Forall_nil]. apply Forall_forall. intros b Hb. cbn [fst snd].
      rewrite (mb_static_blocks mb R R' MST) in Hb.
      assert (HbL : In b LB) by (destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _); unfold blocks_MEMBIO in Hb; destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption).
      pose proof (ah_blocks H HH _ _ _ _ HPq (SLQ _ HbL)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7). pose proof (aapp_not_shadowland _ _ D7) as NSb.
      unfold ALOWSH_LO, AHI_LO in NSb, W3. clear - NSb SHL SHU SHA SH8 W1 W3 S0 KR. unfold sh in *. rewrite ?ASHADOW_BASE_val in *. lia.
    - intros R' SLQ MST MB MSHq. destruct MSHq as (X1 & X2 & X3 & X4). pose proof MB as MBq. destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
      unfold MEMBIO_shad. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
      assert (TA : forall b A n, In b Lq -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> addressable mA A n -> addressable mB A n).
      { intros b A n Hb HA HB N0 AD. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
        eapply addressable_acrossX; [exact AD| exact MU| exact WM| clear - D1 HA; lia| unfold AAPP_HI; clear - D5 HB ACB; lia| exact (proj2 (BWq b A n Hb HA HB))]. }
      split; [| split; [| split]].
      + eapply (TA (mb_id R', mb, 128)); [apply SLQ; exact J1| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X1].
      + eapply (TA (mb_bbid R', mb_bb R', 16)); [apply SLQ; exact J2| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X2].
      + eapply (TA (mb_bmid R', mb_bm R', 32)); [apply SLQ; exact J3| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X3].
      + eapply (TA (mb_rpid R', mb_rp R', 32)); [apply SLQ; exact J4| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X4].
  Qed.

  (* [comment removed for export] *)
  Lemma stk_carry : forall (mA mB : mem) (sq : as_St H) (Lq : list block) (l h : Z),
    lo <= l -> h <= bv_unsigned sp ->
    munch [(l, h)] mA mB -> wmono asegs mA mB ->
    as_RHEAP H sq Lq mA -> (forall b, In b LB -> In b Lq) ->
       as_RHEAP H sq Lq mB
    /\ (as_rauxv_ok H mA B -> as_rauxv_ok H mB B)
    /\ (forall LFq, as_RFS H LFq mA -> as_RFS H LFq mB)
    /\ (forall LIBq Mq xq, LIBMID LIBq mA Mq -> mid_ctx Mq = CtxReady xq -> (forall b, In b LIBq -> In b Lq) -> (forall b, In b (mid_errblocks Mq) -> In b Lq) -> LIBMID LIBq mB Mq)
    /\ (forall A cs, rw_cells asegs mA A cs -> h <= A -> rw_cells asegs mB A cs)
    /\ (forall ffq cs, ffq + 4096 <= aceil -> rw_cells asegs mA ffq cs -> Z.of_nat (cells_size cs) <= 4096 -> rw_cells asegs mB ffq cs)
    /\ (forall ffq cs, 0 <= ffq -> ffq + 4096 <= aceil -> rw_cells asegs mA (sh ffq) cs -> Z.of_nat (cells_size cs) <= 512 -> rw_cells asegs mB (sh ffq) cs)
    /\ (forall b A cs, In b Lq -> blk_addr b <= A -> A + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b -> rw_cells asegs mA A cs -> rw_cells asegs mB A cs)
    /\ (forall b A bs, In b Lq -> blk_addr b <= A -> A + Z.of_nat (length bs) <= blk_addr b + blk_size b -> bytes_at asegs mA A bs -> bytes_at asegs mB A bs)
    /\ (forall b A n, In b Lq -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> addressable mA A n -> addressable mB A n)
    /\ (forall b A n, In b Lq -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> accessible mA A n -> accessible mB A n)
    /\ (forall errvq, rw_cells asegs mA (errno_addr (Z_to_bv 64 ATP)) [C4 errvq] -> rw_cells asegs mB (errno_addr (Z_to_bv 64 ATP)) [C4 errvq])
    /\ (stack0 mA lo (bv_unsigned sp) -> stack0 mB lo (bv_unsigned sp))
    /\ (ACONST mA -> ACONST mB)
    /\ (forall cur CHq bnd, as_chain H mA cur CHq -> (forall fpq raq, In (fpq, raq) CHq -> bnd <= fpq) -> h + 16 <= bnd -> as_chain H mB cur CHq)
    /\ (forall X m0, xpres H LB (bv_unsigned sp) X m0 mA -> xpres H LB (bv_unsigned sp) X m0 mB)
    /\ (forall R', mb_static R R' -> MEMBIO H LB mA mb R' -> MEMBIO H LB mB mb R')
    /\ (forall R', mb_static R R' -> MEMBIO H LB mA mb R' -> MEMBIO_shad mA mb R' -> MEMBIO_shad mB mb R').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros mA mB sq Lq l h L1 L2 MU WM HPq SLQ.
    destruct rc_facts as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). fold S1 in Q1, Q2.
    assert (S0 : sh 0xc04000 = 0x80178800) by reflexivity.
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
    assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) <= 0xc04000 - 4) by (clear; vm_compute; split; discriminate).
    assert (AL : aceil <= l) by (clear - CEIL L1; lia).
    set (W := [(l, h)]) in *.
    assert (FW : Forall (fswin H) W) by (subst W; apply Forall_cons; [left; cbn; exact AL| apply Forall_nil]).
    (* [comment removed for export] *)
    assert (LOW : forall A n, A + n <= aceil -> disjoint_from W A n) by (intros A n AN; subst W; cbn; split; [clear - AN AL; lia| exact I]).
    assert (HIGH : forall A n, h <= A -> disjoint_from W A n) by (intros A n AN; subst W; cbn; split; [clear - AN; lia| exact I]).
    assert (BWq : forall b A n, In b Lq -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> disjoint_from W A n /\ Forall (winX A n) W).
    { intros b A n Hb HA HB. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      split; [apply LOW; clear - D5 HA HB; lia|]. subst W. apply Forall_cons; [| apply Forall_nil]. unfold winX. cbn. right; left.
      unfold AHI_LO. clear - AL ACB. lia. }
    repeat match goal with |- _ /\ _ => split end.
    - eapply (ah_RHEAP_frame H HH); [exact HPq| exact MU| exact WM| eapply Forall_impl; [intros iv; apply fswin_cw| exact FW]].
    - intros AUXq. eapply (ah_rauxv_frame H HH); [exact AUXq| exact MU| exact WM| eapply Forall_impl; [intros iv; apply (fswin_cw LB)| exact FW]].
    - intros LFq RFq. eapply (ah_RFS_frame H HH); [exact RFq| exact MU| exact WM|]. subst W. apply Forall_cons; [| apply Forall_nil].
      left. cbn. pose proof AFSB as (_ & A2 & _). unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *. clear - A2 AL ACB. lia.
    - intros LIBq Mq xq LMq CXq SLq SEq. eapply (LIBMID_xfs0 H HH sq mA LIBq Lq S1 W mA mB Mq xq); [exact HPq| exact LMq| exact CXq| | exact SLq| exact SEq| exact FW].
      eapply (xpres_of_munch_gen H); [exact MU| exact WM|]. intros a Ha [_ HXa]. apply outside_of_not_rin. exact HXa.
    - intros A cs RC HA. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. apply HIGH. exact HA.
    - intros ffq cs FQ RC SZ. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. apply LOW. clear - FQ SZ. lia.
    - intros ffq cs FQ0 FQ RC SZ. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. apply LOW.
      pose proof (sh_add8 ffq 512) as SH8. replace (ffq + 8 * 512) with (ffq + 4096) in SH8 by (clear; lia).
      pose proof (sh_mono (ffq + 4096) aceil FQ) as Y. clear - Y SH8 SZ SHC. lia.
    - intros b A cs Hb HA HB RC. eapply rw_cells_transport; [exact RC| exact MU| exact WM| exact (proj1 (BWq b A _ Hb HA HB))].
    - intros b A bs Hb HA HB RC. eapply bytes_at_transport; [exact RC| exact MU| exact (proj1 (BWq b A _ Hb HA HB))].
    - intros b A n Hb HA HB N0 AD. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      eapply addressable_acrossX; [exact AD| exact MU| exact WM| clear - D1 HA; lia| unfold AAPP_HI; clear - D5 HB ACB; lia| exact (proj2 (BWq b A n Hb HA HB))].
    - intros b A n Hb HA HB N0 ACC. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      eapply accessible_transport; [exact ACC| exact MU|]. intros y Hy. subst W. cbn. split; [| exact I].
      assert (Y1 : y <= aceil) by (clear - Hy HB D5; lia).
      pose proof (sh_mono y aceil Y1) as SX. clear - SX SHC AL. lia.
    - intros errvq RC. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. apply LOW. clear - ERNG ACB. cbn. lia.
    - intros S00. eapply stack0_transport; [exact S00| exact MU| exact WM|]. subst W. apply Forall_cons; [| apply Forall_nil].
      apply stack0_ok_app. unfold AHI_LO. clear - AL ACB. lia.
    - intros ACq. eapply ACONST_frame; [exact ACq| exact MU| exact WM|]. subst W. apply Forall_cons; [| apply Forall_nil].
      apply aconst_ok_high; cbn [fst snd]; clear - AL ACB; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
    - intros cur CHq bnd C HS HB. eapply (achain_below H HH mA mB _ _ _ bnd); [exact C| exact HS| exact MU|].
      subst W. apply Forall_cons; [left; cbn [fst snd]; clear - HB; lia| apply Forall_nil].
    - intros X m0 XP. eapply xpres_trans; [exact XP|]. eapply (xpres_of_munch_gen H); [exact MU| exact WM|].
      intros a Ha [Ca _]. subst W. cbn. split; [| exact I]. intros [K1 K2].
      exact (client_not_frame _ _ _ _ _ HP SUB0 Ca ltac:(clear - K1 K2 L1 L2; lia)).
    - intros R' MST MB. eapply (AMEMBIO_munch H LB W mA mB); [exact MB| exact MU| exact WM|].
      subst W. apply Forall_cons; [| apply Forall_nil]. apply Forall_forall. intros b Hb. cbn [fst snd]. left.
      rewrite (mb_static_blocks mb R R' MST) in Hb.
      assert (HbL : In b LB) by (destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _); unfold blocks_MEMBIO in Hb; destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption).
      pose proof (ah_blocks H HH _ _ _ _ HPq (SLQ _ HbL)) as (_ & _ & _ & _ & D5 & _). clear - D5 AL. lia.
    - intros R' MST MB MSHq. destruct MSHq as (X1 & X2 & X3 & X4). pose proof MB as MBq. destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
      unfold MEMBIO_shad. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
      assert (TA : forall b A n, In b Lq -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> addressable mA A n -> addressable mB A n).
      { intros b A n Hb HA HB N0 AD. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
        eapply addressable_acrossX; [exact AD| exact MU| exact WM| clear - D1 HA; lia| unfold AAPP_HI; clear - D5 HB ACB; lia| exact (proj2 (BWq b A n Hb HA HB))]. }
      split; [| split; [| split]].
      + eapply (TA (mb_id R', mb, 128)); [apply SLQ; exact J1| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X1].
      + eapply (TA (mb_bbid R', mb_bb R', 16)); [apply SLQ; exact J2| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X2].
      + eapply (TA (mb_bmid R', mb_bm R', 32)); [apply SLQ; exact J3| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X3].
      + eapply (TA (mb_rpid R', mb_rp R', 32)); [apply SLQ; exact J4| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X4].
  Qed.

  (* [comment removed for export] *)
  Lemma xnil_carry : forall (ff fp : Z) (mA mB : mem) (sq : as_St H) (Lh Lq : list block),
    fresh_frame H LF 6 ff fp ->
    xpres H Lq S1 [] mA mB -> as_RHEAP H sq Lh mA -> (forall b, In b Lq -> In b Lh) -> (forall b, In b LB -> In b Lq) ->
       (as_RFS H (LF1 ff fp) mA -> as_RFS H (LF1 ff fp) mB)
    /\ (forall LIBq Mq xq, LIBMID LIBq mA Mq -> mid_ctx Mq = CtxReady xq -> (forall b, In b LIBq -> In b Lq) -> (forall b, In b (mid_errblocks Mq) -> In b Lq) -> LIBMID LIBq mB Mq)
    /\ (forall A cs, rw_cells asegs mA A cs -> S1 <= A -> rw_cells asegs mB A cs)
    /\ (forall cs, rw_cells asegs mA ff cs -> Z.of_nat (cells_size cs) <= 4096 -> rw_cells asegs mB ff cs)
    /\ (forall cs, rw_cells asegs mA (sh ff) cs -> Z.of_nat (cells_size cs) <= 512 -> rw_cells asegs mB (sh ff) cs)
    /\ (forall b A cs, In b Lq -> blk_addr b <= A -> A + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b -> rw_cells asegs mA A cs -> rw_cells asegs mB A cs)
    /\ (forall b A bs, In b Lq -> blk_addr b <= A -> A + Z.of_nat (length bs) <= blk_addr b + blk_size b -> bytes_at asegs mA A bs -> bytes_at asegs mB A bs)
    /\ (forall b A n, In b Lq -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> A mod 8 = 0 -> 0 <= n -> addressable mA A n -> addressable mB A n)
    /\ (forall b A n, In b Lq -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> accessible mA A n -> accessible mB A n)
    /\ (stack0 mA lo (bv_unsigned sp) -> stack0 mB lo (bv_unsigned sp))
    /\ (forall cur CHq, as_chain H mA cur CHq -> (forall fpq raq, In (fpq, raq) CHq -> S1 + 16 <= fpq) -> as_chain H mB cur CHq)
    /\ (forall X m0, xpres H LB (bv_unsigned sp) X m0 mA -> xpres H LB (bv_unsigned sp) X m0 mB)
    /\ (forall R', mb_static R R' -> MEMBIO H LB mA mb R' -> MEMBIO H LB mB mb R')
    /\ (forall R', mb_static R R' -> MEMBIO H LB mA mb R' -> MEMBIO_shad mA mb R' -> MEMBIO_shad mB mb R').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros ff fp mA mB sq Lh Lq FRESH XP HPq SQH SLQ.
    destruct rc_facts as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). fold S1 in Q1, Q2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    pose proof (sh_add8 ff 512) as SH8. replace (ff + 8 * 512) with (ff + 4096) in SH8 by (clear; lia).
    pose proof (sh_mono (as_FSB H) ff ltac:(clear - FF5; lia)) as SHL. pose proof (sh_mono (ff + 4096) (as_FSB H + 11571200) FF6) as SHU.
    assert (AS1 : aceil <= S1) by (clear - CEIL LO STK0 Q2; lia).
    repeat match goal with |- _ /\ _ => split end.
    - intros RFq. eapply (RFS_via_xpres H HH); [exact RFq| exact XP| apply Forall_nil].
    - intros LIBq Mq xq LMq CXq SLq SEq. eapply (LIBMID_xpres0 H LIBq Lq S1); [exact LMq| exact CXq| exact XP| exact SLq| exact SEq].
    - intros A cs RC HA. eapply (xpres_rw_cells' H); [exact XP| exact RC| left; exact HA| apply Forall_nil].
    - intros cs RC SZ. eapply (xpres_rw_cells' H); [exact XP| exact RC| | apply Forall_nil]. right; right; right; right; left. unfold AFS_SIZE. cbn [fst snd]. clear - FF5 FF6 SZ. lia.
    - intros cs RC SZ. eapply (xpres_rw_cells' H); [exact XP| exact RC| | apply Forall_nil]. right; right; right; right; right; left. unfold AFS_SIZE. cbn [fst snd].
      clear - SHL SHU SH8 SZ. lia.
    - intros b A cs Hb HA HB RC. eapply (xpres_rw_cells' H); [exact XP| exact RC| right; right; left; exists b; split; [exact Hb| split; [exact HA| exact HB]]| apply Forall_nil].
    - intros b A bs Hb HA HB RC. eapply (xpres_bytes_at' H); [exact XP| exact RC| right; right; left; exists b; split; [exact Hb| split; [exact HA| exact HB]]| apply Forall_nil].
    - intros b A n Hb HA HB A8 N0 AD. pose proof (ah_blocks H HH _ _ _ _ HPq (SQH _ Hb)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      eapply (ashobj_addressable_xpres H HH sq Lh Lq mA mB S1 []); [exact HPq| exact SQH| exact AS1| | unfold AAPP_HI; clear - D5 HB ACB; lia| exact AD| exact XP| apply Forall_nil].
      left. exists b. split; [exact Hb| split; [exact HA| exact HB]].
    - intros b A n Hb HA HB N0 ACC.
      eapply (ashobj_accessible_xpres_sub H HH sq Lh Lq mA mB S1 []); [exact HPq| exact SQH| exact AS1| | exact ACC| exact XP| apply Forall_nil].
      left. exists b. split; [exact Hb| split; [exact HA| exact HB]].
    - intros S00. eapply (stack0_xpres H); [exact XP| exact S00| apply Forall_nil].
    - intros cur CHq C HS. eapply chain_keepX; [exact C| exact XP| exact HS| exact AS1| apply Forall_nil].
    - intros X m0 XA. eapply xpres_trans; [exact XA|]. eapply xpres_weaken; [exact XP| clear - Q2; lia| exact SLQ| intros q Hq; destruct Hq].
    - intros R' MST MB. eapply (AMEMBIO_xpres H LB Lq S1 []); [exact MB| | exact XP| apply Forall_nil].
      intros b Hb. apply SLQ. rewrite (mb_static_blocks mb R R' MST) in Hb. destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _). unfold blocks_MEMBIO in Hb.
      destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption.
    - intros R' MST MB MSHq. destruct MSHq as (X1 & X2 & X3 & X4). pose proof MB as MBq. destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & K1 & K2 & K3 & K4 & _).
      pose proof K1 as (_ & _ & _ & _ & K1b & _). pose proof K2 as (_ & _ & _ & _ & K2b & _). pose proof K3 as (_ & _ & _ & _ & K3b & _). pose proof K4 as (_ & _ & _ & _ & K4b & _).
      unfold MEMBIO_shad. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
      split; [| split; [| split]].
      + eapply (ashobj_addressable_xpres H HH sq Lh Lq mA mB S1 []); [exact HPq| exact SQH| exact AS1| left; exists (mb_id R', mb, 128); split; [apply SLQ; exact J1| cbn; clear; lia]
          | unfold AAPP_HI; clear - K1b ACB; lia| exact X1| exact XP| apply Forall_nil].
      + eapply (ashobj_addressable_xpres H HH sq Lh Lq mA mB S1 []); [exact HPq| exact SQH| exact AS1| left; exists (mb_bbid R', mb_bb R', 16); split; [apply SLQ; exact J2| cbn; clear; lia]
          | unfold AAPP_HI; clear - K2b ACB; lia| exact X2| exact XP| apply Forall_nil].
      + eapply (ashobj_addressable_xpres H HH sq Lh Lq mA mB S1 []); [exact HPq| exact SQH| exact AS1| left; exists (mb_bmid R', mb_bm R', 32); split; [apply SLQ; exact J3| cbn; clear; lia]
          | unfold AAPP_HI; clear - K3b ACB; lia| exact X3| exact XP| apply Forall_nil].
      + eapply (ashobj_addressable_xpres H HH sq Lh Lq mA mB S1 []); [exact HPq| exact SQH| exact AS1| left; exists (mb_rpid R', mb_rp R', 32); split; [apply SLQ; exact J4| cbn; clear; lia]
          | unfold AAPP_HI; clear - K4b ACB; lia| exact X4| exact XP| apply Forall_nil].
  Qed.

  Lemma djF : forall (W : list (Z * Z)) a n, Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
  Proof.
    clear. induction W as [|[l h] W IH]; intros a n HF; [exact I|]. inversion HF as [|y l' Hy Hl]; subst.
    cbn [fst snd] in Hy. cbn. split; [lia| apply IH; exact Hl].
  Qed.
  Lemma outF : forall (W : list (Z * Z)) y, Forall (fun iv : Z * Z => y < fst iv \/ snd iv <= y) W -> outside W y.
  Proof.
    clear. induction W as [|[l h] W IH]; intros y HF; [exact I|]. inversion HF as [|z l' Hy Hl]; subst.
    cbn [fst snd] in Hy. cbn. split; [lia| apply IH; exact Hl].
  Qed.
  Lemma djF_inv : forall (W : list (Z * Z)) a n iv, disjoint_from W a n -> In iv W -> a + n <= fst iv \/ snd iv <= a.
  Proof.
    clear. induction W as [|[l h] W IH]; intros a n iv DJ Hiv; [destruct Hiv|]. cbn in DJ. destruct DJ as [D1 D2].
    destruct Hiv as [<-|Hiv]; [cbn; exact D1| exact (IH _ _ _ D2 Hiv)].
  Qed.

  (* [comment removed for export] *)
  Lemma fsw_carry : forall (W : list (Z * Z)) (mA mB : mem) (sq : as_St H) (Lq : list block),
    Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= bv_unsigned sp) \/ (as_FSB H <= fst iv /\ snd iv <= as_FSB H + AFS_SIZE)
                              \/ (sh (as_FSB H) <= fst iv /\ snd iv <= sh (as_FSB H + AFS_SIZE))) W ->
    munch W mA mB -> wmono asegs mA mB ->
    as_RHEAP H sq Lq mA -> (forall b, In b LB -> In b Lq) ->
       as_RHEAP H sq Lq mB
    /\ (as_rauxv_ok H mA B -> as_rauxv_ok H mB B)
    /\ (forall LIBq Mq xq, LIBMID LIBq mA Mq -> mid_ctx Mq = CtxReady xq -> (forall b, In b LIBq -> In b Lq) -> (forall b, In b (mid_errblocks Mq) -> In b Lq) -> LIBMID LIBq mB Mq)
    /\ (forall A cs, rw_cells asegs mA A cs -> aceil <= A -> Forall (fun iv : Z * Z => lo <= fst iv -> A + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= A) W -> rw_cells asegs mB A cs)
    /\ (forall b A cs, In b Lq -> blk_addr b <= A -> A + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b -> rw_cells asegs mA A cs -> rw_cells asegs mB A cs)
    /\ (forall b A bs, In b Lq -> blk_addr b <= A -> A + Z.of_nat (length bs) <= blk_addr b + blk_size b -> bytes_at asegs mA A bs -> bytes_at asegs mB A bs)
    /\ (forall b A n, In b Lq -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> addressable mA A n -> addressable mB A n)
    /\ (forall b A n, In b Lq -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> accessible mA A n -> accessible mB A n)
    /\ (forall errvq, rw_cells asegs mA (errno_addr (Z_to_bv 64 ATP)) [C4 errvq] -> rw_cells asegs mB (errno_addr (Z_to_bv 64 ATP)) [C4 errvq])
    /\ (stack0 mA lo (bv_unsigned sp) -> stack0 mB lo (bv_unsigned sp))
    /\ (ACONST mA -> ACONST mB)
    /\ (forall cur CHq bnd, as_chain H mA cur CHq -> (forall fpq raq, In (fpq, raq) CHq -> bnd <= fpq) -> aceil + 16 <= bnd ->
          Forall (fun iv : Z * Z => lo <= fst iv -> snd iv + 16 <= bnd) W -> as_chain H mB cur CHq)
    /\ (forall X m0, xpres H LB (bv_unsigned sp) X m0 mA -> (forall a, rin_ivs W a -> a < aceil -> rin_ivs X a) -> xpres H LB (bv_unsigned sp) X m0 mB)
    /\ (forall R', mb_static R R' -> MEMBIO H LB mA mb R' -> MEMBIO H LB mB mb R')
    /\ (forall R', mb_static R R' -> MEMBIO H LB mA mb R' -> MEMBIO_shad mA mb R' -> MEMBIO_shad mB mb R').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros W mA mB sq Lq FW0 MU WM HPq SLQ.
    destruct rc_facts as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). fold S1 in Q1, Q2.
    pose proof AFSB as (A1' & A2 & A3 & A4). unfold AIMG_TOP in A1'.
    assert (S0 : sh 0xc04000 = 0x80178800) by reflexivity.
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
    pose proof (sh_aapp_range _ _ A4 ltac:(unfold AFS_SIZE; clear; lia)) as (W1 & W2 & W3). unfold nsh in W2. unfold AIMG_TOP in W1. rewrite S0 in W1.
    pose proof (sh_mono _ _ A2) as SHA.
    pose proof (aapp_not_shadowland _ _ A4) as NSF.
    assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) <= 0xc04000 - 4) by (clear; vm_compute; split; discriminate).
    assert (FW : Forall (fswin H) W).
    { eapply Forall_impl; [| exact FW0]. cbn beta. intros iv [[K1 K2]|[K|K]]; [left; clear - K1 CEIL; lia| right; left; exact K| right; right; exact K]. }
    (* [comment removed for export] *)
    assert (LOWq : forall A n, aapp A n -> A + n <= aceil -> (A + n + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= A - 16) -> disjoint_from W A n).
    { intros A n AP AQ AF. apply djF. eapply Forall_impl; [| exact FW0]. cbn beta. pose proof (aapp_not_shadowland _ _ AP) as NS.
      intros iv [[K1 K2]|[[K1 K2]|[K1 K2]]].
      - left. clear - K1 AQ CEIL. lia.
      - clear - K1 K2 AF. lia.
      - clear - K1 K2 NS W1 W3 SHA. unfold ALOWSH_LO, AHI_LO in *. lia. }
    assert (BWq : forall b A n, In b Lq -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> disjoint_from W A n /\ Forall (winX A n) W).
    { intros b A n Hb HA HB N0. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      split.
      - apply (ECH_AKit.disjoint_from_sub W (blk_addr b) (blk_size b)); [| exact HA| exact HB| exact N0]. apply LOWq; [exact D7| exact D5| exact D6].
      - eapply Forall_impl; [| exact FW0]. cbn beta. pose proof (aapp_not_shadowland _ _ D7) as NS.
        intros iv [[K1 K2]|[[K1 K2]|[K1 K2]]]; unfold winX.
        + right; left. unfold AHI_LO. clear - K1 CEIL ACB. lia.
        + (* [comment removed for export] *)
          unfold ALOWSH_LO, AHI_LO, AFS_SIZE in *. clear - K1 K2 NSF. rewrite ?ASHADOW_BASE_val. lia.
        + (* [comment removed for export] *)
          right; right. unfold AFS_SIZE in *. unfold nsh, sh in *. clear - K1 K2 D2 D6 HA HB N0. Z.div_mod_to_equations. lia. }
    repeat match goal with |- _ /\ _ => split end.
    - eapply (ah_RHEAP_frame H HH); [exact HPq| exact MU| exact WM| eapply Forall_impl; [intros iv; apply fswin_cw| exact FW]].
    - intros AUXq. eapply (ah_rauxv_frame H HH); [exact AUXq| exact MU| exact WM| eapply Forall_impl; [intros iv; apply (fswin_cw LB)| exact FW]].
    - intros LIBq Mq xq LMq CXq SLq SEq. eapply (LIBMID_xfs0 H HH sq mA LIBq Lq S1 W mA mB Mq xq); [exact HPq| exact LMq| exact CXq| | exact SLq| exact SEq| exact FW].
      eapply (xpres_of_munch_gen H); [exact MU| exact WM|]. intros a Ha [_ HXa]. apply outside_of_not_rin. exact HXa.
    - intros A cs RC HA FX. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. apply djF.
      apply Forall_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FW0 iv Hiv) as K. pose proof (proj1 (Forall_forall _ _) FX iv Hiv) as KX. cbn beta in K, KX. cbn beta.
      destruct K as [[K1 K2]|[[K1 K2]|[K1 K2]]]; [exact (KX K1)| right; unfold AFS_SIZE in *; clear - K2 A2 HA; lia| right; clear - K2 SHA SHC HA; lia].
    - intros b A cs Hb HA HB RC. eapply rw_cells_transport; [exact RC| exact MU| exact WM| exact (proj1 (BWq b A _ Hb HA HB ltac:(clear; lia)))].
    - intros b A bs Hb HA HB RC. eapply bytes_at_transport; [exact RC| exact MU| exact (proj1 (BWq b A _ Hb HA HB ltac:(clear; lia)))].
    - intros b A n Hb HA HB N0 AD. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      eapply addressable_acrossX; [exact AD| exact MU| exact WM| clear - D1 HA; lia| unfold AAPP_HI; clear - D5 HB ACB; lia| exact (proj2 (BWq b A n Hb HA HB N0))].
    - intros b A n Hb HA HB N0 ACC. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      pose proof (sh_aapp_range _ _ D7 D3) as (V1 & V2 & V3). pose proof (aapp_not_shadowland _ _ D7) as NS.
      eapply accessible_transport; [exact ACC| exact MU|]. intros y Hy. apply outF. eapply Forall_impl; [| exact FW0]. cbn beta.
      assert (Y1 : AIMG_TOP <= y) by (clear - Hy HA D4; lia). assert (Y2 : y <= aceil) by (clear - Hy HB D5; lia).
      pose proof (conj (sh_mono _ _ Y1) (sh_mono _ _ Y2)) as SX. rewrite S0 in SX.
      intros iv [[K1 K2]|[[K1 K2]|[K1 K2]]].
      + left. clear - K1 SX SHC CEIL. lia.
      + (* [comment removed for export] *) unfold ALOWSH_LO, AHI_LO, AFS_SIZE in *. clear - K1 K2 NSF SX W3. lia.
      + (* [comment removed for export] *)
        unfold AFS_SIZE in *. clear - K1 K2 Hy HA HB D6. unfold sh in *. rewrite ?ASHADOW_BASE_val in *. Z.div_mod_to_equations. lia.
    - intros errvq RC. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. apply djF. eapply Forall_impl; [| exact FW0]. cbn beta.
      intros iv [[K1 K2]|[[K1 K2]|[K1 K2]]]; left; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
        [clear - K1 ERNG CEIL ACB; lia| clear - K1 ERNG A1'; lia| clear - K1 ERNG W1; lia].
    - intros S00. eapply stack0_transport; [exact S00| exact MU| exact WM|]. eapply Forall_impl; [| exact FW0]. cbn beta.
      intros iv [[K1 K2]|[[K1 K2]|[K1 K2]]].
      + destruct iv as [l h]. cbn [fst snd] in K1, K2. apply stack0_ok_app. unfold AHI_LO. clear - K1 CEIL ACB. lia.
      + destruct iv as [l h]. cbn [fst snd] in K1, K2. eapply (stack0_ok_aapp _ _ _ _ A4); [exact K1| exact K2].
      + destruct iv as [l h]. cbn [fst snd] in K1, K2. right. cbn [snd]. clear - K2 SHA. lia.
    - intros ACq. eapply ACONST_frame; [exact ACq| exact MU| exact WM|]. eapply Forall_impl; [| exact FW0]. cbn beta.
      intros iv [[K1 K2]|[[K1 K2]|[K1 K2]]]; destruct iv as [l h]; cbn [fst snd] in K1, K2.
      + apply aconst_ok_hi. unfold AHI_LO. clear - K1 CEIL ACB. lia.
      + eapply (aconst_ok_aapp _ _ _ _ A4); [exact K1| exact K2].
      + apply aconst_ok_high; [clear - K1 W1 S0; unfold AIMG_TOP; lia| right; left; clear - K1 W1; lia].
    - intros cur CHq bnd C HS HB FX. eapply (achain_below H HH mA mB _ _ _ bnd); [exact C| exact HS| exact MU|].
      apply Forall_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FW0 iv Hiv) as K. pose proof (proj1 (Forall_forall _ _) FX iv Hiv) as KX. cbn beta in K, KX. cbn beta.
      left. destruct K as [[K1 K2]|[[K1 K2]|[K1 K2]]]; [pose proof (KX K1) as KK; clear - KK; lia| unfold AFS_SIZE in *; clear - K2 A2 HB; lia| clear - K2 SHA SHC HB; lia].
    - intros X m0 XP HXW. eapply xpres_trans; [exact XP|]. eapply (xpres_of_munch_gen H); [exact MU| exact WM|].
      intros a Ha [Ca HXa]. apply outside_of_not_rin. intros RW. destruct (rin_ivs_In _ _ RW) as (iv & Hiv & Ra).
      pose proof (proj1 (Forall_forall _ _) FW0 iv Hiv) as K. cbn beta in K.
      destruct K as [[K1 K2]|[[K1 K2]|[K1 K2]]].
      + exact (client_not_frame _ _ _ _ _ HP SUB0 Ca ltac:(clear - K1 K2 Ra; lia)).
      + apply HXa. apply HXW; [exact RW| unfold AFS_SIZE in *; clear - K2 Ra A2; lia].
      + apply HXa. apply HXW; [exact RW| clear - K2 Ra SHA SHC; lia].
    - intros R' MST MB. eapply (AMEMBIO_munch H LB W mA mB); [exact MB| exact MU| exact WM|].
      apply Forall_forall. intros iv Hiv. apply Forall_forall. intros b Hb. cbn beta.
      rewrite (mb_static_blocks mb R R' MST) in Hb.
      assert (HbL : In b LB) by (destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _); unfold blocks_MEMBIO in Hb; destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption).
      pose proof (ah_blocks H HH _ _ _ _ HPq (SLQ _ HbL)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      exact (djF_inv _ _ _ _ (LOWq _ _ D7 D5 D6) Hiv).
    - intros R' MST MB MSHq. destruct MSHq as (X1 & X2 & X3 & X4). pose proof MB as MBq. destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
      unfold MEMBIO_shad. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
      assert (TA : forall b A n, In b Lq -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> addressable mA A n -> addressable mB A n).
      { intros b A n Hb HA HB N0 AD. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
        eapply addressable_acrossX; [exact AD| exact MU| exact WM| clear - D1 HA; lia| unfold AAPP_HI; clear - D5 HB ACB; lia| exact (proj2 (BWq b A n Hb HA HB N0))]. }
      split; [| split; [| split]].
      + eapply (TA (mb_id R', mb, 128)); [apply SLQ; exact J1| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X1].
      + eapply (TA (mb_bbid R', mb_bb R', 16)); [apply SLQ; exact J2| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X2].
      + eapply (TA (mb_bmid R', mb_bm R', 32)); [apply SLQ; exact J3| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X3].
      + eapply (TA (mb_rpid R', mb_rp R', 32)); [apply SLQ; exact J4| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X4].
  Qed.

  (* [comment removed for export] *)
  Lemma lad_exit_carry : forall (ff fp : Z) (mA mB : mem) (sq : as_St H) (Lh : list block),
    fresh_frame H LF 6 ff fp ->
    xpres H L0 S1 ((ff + 2256, ff + 2256 + 8) :: (S1 + 184, S1 + 192) :: MEMBIO_foot mb R) mA mB ->
    as_RHEAP H sq Lh mA -> (forall b, In b L0 -> In b Lh) ->
       (forall A cs, rw_cells asegs mA A cs -> S1 <= A -> (A + Z.of_nat (cells_size cs) <= S1 + 184 \/ S1 + 192 <= A) -> rw_cells asegs mB A cs)
    /\ (forall fk1 fk2 rb0 rb, rw_cells asegs mA ff (arp_fframe S1 fk1 rb0 fk2 fp) -> rw_cells asegs mB (ff + 2256) [C8 (wz rb)] ->
          rw_cells asegs mB ff (arp_fframe S1 fk1 rb fk2 fp))
    /\ (forall sa sb sc sb2 sc2 sd se sr0 sr sg, rw_cells asegs mA (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sb2 sc2 sd se sr0 sg) -> rw_cells asegs mB (sh (ff + 2256)) [C1 sr] ->
          rw_cells asegs mB (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sb2 sc2 sd se sr sg))
    /\ (rw_cells asegs mA st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> rw_cells asegs mB st [C8 (wz 0); C8 (wz 0); C8 (wz 0)])
    /\ (addressable mA st STORE_SIZE -> addressable mB st STORE_SIZE)
    /\ (stack0 mA lo (bv_unsigned sp) -> stack0 mB lo (bv_unsigned sp))
    /\ (LIBMID LIB mA M -> LIBMID LIB mB M)
    /\ (xpres H LB (bv_unsigned sp) (XSF ff fp ++ MEMBIO_foot mb R) m mA -> xpres H LB (bv_unsigned sp) (XSF ff fp ++ MEMBIO_foot mb R) m mB).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros ff fp mA mB sq Lh FRESH XP HPq SQH.
    destruct rc_facts as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). fold S1 in Q1, Q2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AIMG_TOP in AF1. unfold AFS_SIZE in AF2.
    assert (S0 : sh 0xc04000 = 0x80178800) by reflexivity.
    assert (SHF : Z.shiftr ff 3 + ASHB = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (APff : aapp ff 4096) by (eapply aapp_sub; [exact FB3| clear - FF5; lia| unfold AFS_SIZE; clear - FF6; lia]).
    pose proof (aapp_not_shadowland _ _ APff) as NSff. pose proof (aapp_not_shadowland _ _ AF4) as NSF.
    pose proof (sh_aapp_range _ _ APff ltac:(clear; lia)) as (W1 & W2 & W3). unfold nsh in W2. unfold AIMG_TOP in W1. rewrite S0 in W1.
    pose proof (sh_add8 ff 282) as SH280. replace (ff + 8 * 282) with (ff + 2256) in SH280 by (clear; lia).
    pose proof (sh_add8 ff 512) as SH512. replace (ff + 8 * 512) with (ff + 4096) in SH512 by (clear; lia).
    pose proof (sh_mono (as_FSB H) ff ltac:(clear - FF5; lia)) as SY1. pose proof (sh_mono (ff + 4096) _ FF6) as SY2.
    pose proof MBO as MBq. destruct MBq as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _).
    pose proof (BLK0 _ (SUB0 _ I1)) as (E11 & _ & _ & E1a & E1b & E1f & E1c). pose proof (BLK0 _ (SUB0 _ I3)) as (E31 & _ & _ & E3a & E3b & E3f & E3c).
    cbn [blk_addr blk_size fst snd] in E11, E1a, E1b, E1f, E1c, E31, E3a, E3b, E3f, E3c. unfold BIO_SIZE, BUFMEM_SIZE, AFS_SIZE, AIMG_TOP in E1a, E1b, E1f, E3a, E3b, E3f.
    pose proof (aapp_not_shadowland _ _ E1c) as NS1. pose proof (aapp_not_shadowland _ _ E3c) as NS3. unfold BIO_SIZE in NS1. unfold BUFMEM_SIZE in NS3.
    assert (AS1 : aceil <= S1) by (clear - CEIL LO STK0 Q2; lia).
    (* [comment removed for export] *)
    assert (SHA : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; acb; lia).
    assert (XWsh : forall A n, ASHADOW_BASE + 0xc04000 / 8 <= A -> A + n <= sh aceil -> Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) ((ff + 2256, ff + 2256 + 8) :: (S1 + 184, S1 + 192) :: MEMBIO_foot mb R)).
    { intros A n HA HB. assert (SHC : sh aceil < AHI_LO) by exact W3.
      unfold MEMBIO_foot. unfold ALOWSH_LO, AHI_LO in *. rewrite ?ASHADOW_BASE_val in *.
      apply Forall_cons; [cbn [fst snd]; clear - HA HB NSff SHC; unfold sh in *; rewrite ?ASHADOW_BASE_val in *; lia|].
      apply Forall_cons; [cbn [fst snd]; left; clear - HB SHA AS1; lia|].
      apply Forall_cons; [cbn [fst snd]; clear - HA HB NS1 SHC; unfold BIO_SIZE; unfold sh in *; rewrite ?ASHADOW_BASE_val in *; lia|].
      apply Forall_cons; [cbn [fst snd]; clear - HA HB NS3 SHC; unfold BUFMEM_SIZE; unfold sh in *; rewrite ?ASHADOW_BASE_val in *; lia| apply Forall_nil]. }
    assert (XWapp : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) ((ff + 2256, ff + 2256 + 8) :: (S1 + 184, S1 + 192) :: MEMBIO_foot mb R)).
    { unfold MEMBIO_foot. apply Forall_cons; [cbn [fst snd]; clear - NSff; lia|]. apply Forall_cons; [cbn [fst snd]; right; unfold AHI_LO in *; clear - AS1 ACB; lia|]. apply Forall_cons; [cbn [fst snd]; clear - NS1; unfold BIO_SIZE; lia|].
      apply Forall_cons; [cbn [fst snd]; clear - NS3; unfold BUFMEM_SIZE; lia| apply Forall_nil]. }
    assert (XWhi : forall A n, S1 <= A -> (A + n <= S1 + 184 \/ S1 + 192 <= A) -> Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) ((ff + 2256, ff + 2256 + 8) :: (S1 + 184, S1 + 192) :: MEMBIO_foot mb R)).
    { intros A n HA HI. unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE. apply Forall_cons; [cbn [fst snd]; clear - HA AS1 FF6 AF2; lia|].
      apply Forall_cons; [cbn [fst snd]; exact HI|].
      apply Forall_cons; [cbn [fst snd]; clear - HA AS1 E1b; lia|]. apply Forall_cons; [cbn [fst snd]; clear - HA AS1 E3b; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    assert (XWst : Forall (fun iv : Z * Z => st + STORE_SIZE <= fst iv \/ snd iv <= st) ((ff + 2256, ff + 2256 + 8) :: (S1 + 184, S1 + 192) :: MEMBIO_foot mb R)).
    { pose proof SBR as (_ & _ & _ & _ & SBb & SBf & _). unfold AFS_SIZE in SBf. unfold MEMBIO_foot.
      pose proof (ah_disj H HH _ _ _ (es_id S, st, STORE_SIZE) (mb_id R, mb, BIO_SIZE) HP (OBJ0 _ (or_introl eq_refl)) (OBJ0 _ ltac:(right; left; reflexivity))
                    (nodup_ids_app_ne_s [(es_id S, st, STORE_SIZE)] (blocks_MEMBIO mb R) _ _ NDsm (or_introl eq_refl) ltac:(unfold blocks_MEMBIO; left; reflexivity))) as D1.
      pose proof (ah_disj H HH _ _ _ (es_id S, st, STORE_SIZE) (mb_bmid R, mb_bm R, BUFMEM_SIZE) HP (OBJ0 _ (or_introl eq_refl)) (OBJ0 _ ltac:(right; right; right; left; reflexivity))
                    (nodup_ids_app_ne_s [(es_id S, st, STORE_SIZE)] (blocks_MEMBIO mb R) _ _ NDsm (or_introl eq_refl) ltac:(unfold blocks_MEMBIO; right; right; left; reflexivity))) as D3.
      cbn [blk_addr blk_size fst snd] in D1, D3.
      apply Forall_cons; [cbn [fst snd]; clear - SBf FF5 FF6; lia|]. apply Forall_cons; [cbn [fst snd]; left; clear - STL LO STK0 Q2; lia|]. apply Forall_cons; [cbn [fst snd]; clear - D1; lia|]. apply Forall_cons; [cbn [fst snd]; clear - D3; lia| apply Forall_nil]. }
    repeat match goal with |- _ /\ _ => split end.
    - intros A cs RC HA HI. eapply (xpres_rw_cells' H); [exact XP| exact RC| left; exact HA| apply XWhi; [exact HA| exact HI]].
    - intros fk1 fk2 rb0 rb FRM RB. unfold arp_fframe in FRM |- *.
      change (rw_cells asegs mA ff ([C8 (wz AFRAME_MAGIC); C8 (wz ARP_DESCR); C8 (wz P_ech_read_priv_echconfiglist); C8 (wz S1); CB 2224 fk1] ++ [C8 (wz rb0)] ++ [CB 1824 fk2; C8 (wz fp)])) in FRM.
      apply (proj1 (rw_cells_app asegs mA _ _ _)) in FRM. destruct FRM as [F1 F23]. apply (proj1 (rw_cells_app asegs mA _ _ _)) in F23. destruct F23 as [_ F3].
      cbn [cells_size csize Nat.add app] in F1, F3. replace (ff + Z.of_nat 2256 + Z.of_nat 8) with (ff + 2264) in F3 by (clear; lia).
      change (rw_cells asegs mB ff ([C8 (wz AFRAME_MAGIC); C8 (wz ARP_DESCR); C8 (wz P_ech_read_priv_echconfiglist); C8 (wz S1); CB 2224 fk1] ++ [C8 (wz rb)] ++ [CB 1824 fk2; C8 (wz fp)])).
      apply (proj2 (rw_cells_app asegs mB _ _ _)). split.
      + eapply (xpres_rw_cells' H); [exact XP| exact F1| right; right; right; right; left; cbn [cells_size csize Nat.add]; unfold AFS_SIZE; clear - FF5 FF6; lia|].
        unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE. cbn [cells_size csize Nat.add].
        apply Forall_cons; [cbn [fst snd]; clear; lia|]. apply Forall_cons; [cbn [fst snd]; clear - FF2 FF6 AF2 AS1; lia|]. apply Forall_cons; [cbn [fst snd]; clear - E1f FF5 FF6; lia|]. apply Forall_cons; [cbn [fst snd]; clear - E3f FF5 FF6; lia| apply Forall_nil].
      + apply (proj2 (rw_cells_app asegs mB _ _ _)). cbn [cells_size csize Nat.add]. replace (ff + Z.of_nat 2256) with (ff + 2256) by (clear; lia). split; [exact RB|].
        replace (ff + 2256 + Z.of_nat 8) with (ff + 2264) by (clear; lia).
        eapply (xpres_rw_cells' H); [exact XP| exact F3| right; right; right; right; left; cbn [cells_size csize Nat.add]; unfold AFS_SIZE; clear - FF5 FF6; lia|].
        unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE. cbn [cells_size csize Nat.add].
        apply Forall_cons; [cbn [fst snd]; clear; lia|]. apply Forall_cons; [cbn [fst snd]; clear - FF2 FF6 AF2 AS1; lia|]. apply Forall_cons; [cbn [fst snd]; clear - E1f FF5 FF6; lia|]. apply Forall_cons; [cbn [fst snd]; clear - E3f FF5 FF6; lia| apply Forall_nil].
    - intros sa sb sc sb2 sc2 sd se sr0 sr sg FSH SB. unfold arp_fshadow in FSH |- *. rewrite SHF in FSH |- *. rewrite SH280 in SB.
      change (rw_cells asegs mA (sh ff) ([CB 4 sa; C1 sb; CB 3 sc; C1 sb2; C1 sc2; CB 256 sd; CB 16 se] ++ [C1 sr0] ++ [CB 229 sg])) in FSH.
      apply (proj1 (rw_cells_app asegs mA _ _ _)) in FSH. destruct FSH as [F1 F23]. apply (proj1 (rw_cells_app asegs mA _ _ _)) in F23. destruct F23 as [_ F3].
      cbn [cells_size csize Nat.add app] in F1, F3. replace (sh ff + Z.of_nat 282 + Z.of_nat 1) with (sh ff + 283) in F3 by (clear; lia).
      change (rw_cells asegs mB (sh ff) ([CB 4 sa; C1 sb; CB 3 sc; C1 sb2; C1 sc2; CB 256 sd; CB 16 se] ++ [C1 sr] ++ [CB 229 sg])).
      apply (proj2 (rw_cells_app asegs mB _ _ _)). split.
      + eapply (xpres_rw_cells' H); [exact XP| exact F1| right; right; right; right; right; left; cbn [cells_size csize Nat.add]; unfold AFS_SIZE; clear - SY1 SY2 SH512; lia|].
        cbn [cells_size csize Nat.add]. apply XWsh; [clear - W1; unfold sh in *; rewrite ?ASHADOW_BASE_val in *; lia| pose proof (sh_mono (ff + 4096) aceil FF2) as Y; clear - Y SH512; lia].
      + apply (proj2 (rw_cells_app asegs mB _ _ _)). cbn [cells_size csize Nat.add]. replace (sh ff + Z.of_nat 282) with (sh ff + 282) by (clear; lia). split; [exact SB|].
        replace (sh ff + 282 + Z.of_nat 1) with (sh ff + 283) by (clear; lia).
        eapply (xpres_rw_cells' H); [exact XP| exact F3| right; right; right; right; right; left; cbn [cells_size csize Nat.add]; unfold AFS_SIZE; clear - SY1 SY2 SH512; lia|].
        cbn [cells_size csize Nat.add]. apply XWsh; [clear - W1; unfold sh in *; rewrite ?ASHADOW_BASE_val in *; lia| pose proof (sh_mono (ff + 4096) aceil FF2) as Y; clear - Y SH512; lia].
    - intros SC. eapply (xpres_rw_cells' H); [exact XP| exact SC| right; right; left; exists (es_id S, st, STORE_SIZE); split; [exact SIN| cbn; unfold STORE_SIZE; clear; lia]|].
      cbn [cells_size csize Nat.add]. eapply Forall_impl; [| exact XWst]. cbn beta. intros iv K. unfold STORE_SIZE in K. clear - K. lia.
    - intros SAD. pose proof SBR as (_ & _ & _ & _ & SBb & _).
      eapply (ashobj_addressable_xpres H HH sq Lh L0 mA mB S1 _); [exact HPq| exact SQH| exact AS1| left; exists (es_id S, st, STORE_SIZE); split; [exact SIN| cbn; clear; lia]
        | unfold AAPP_HI; clear - SBb ACB; lia| exact SAD| exact XP| exact XWapp].
    - intros S00. eapply (stack0_xpres H); [exact XP| exact S00|]. unfold MEMBIO_foot.
      apply Forall_cons; [eapply (stack0_ok_aapp _ _ _ _ APff); clear; lia|]. apply Forall_cons; [apply stack0_ok_app; unfold AHI_LO in *; clear - AS1 ACB; lia|].
      apply Forall_cons; [eapply (stack0_ok_aapp _ _ _ _ E1c); clear; lia|].
      apply Forall_cons; [eapply (stack0_ok_aapp _ _ _ _ E3c); clear; lia| apply Forall_nil].
    - intros LMA. destruct (nd_app _ _ ND0) as [DJE _].
      eapply (LIBMID_xobj H HH s m LIB L0 S1 _ [(ff + 2256, ff + 2256 + 8); (S1 + 184, S1 + 192)] (blocks_MEMBIO mb R) mA mB M x);
        [exact HP| exact LMA| exact CTX| exact XP| intros b Hb; exact (SUB0 _ (SUBL _ Hb))| | | | |].
      + intros b Hb. unfold L0. apply in_or_app. left. exact Hb.
      + intros b Hb. apply OBJ0. right. exact Hb.
      + intros b b' Hb Hb'. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (DJ6 _ _ Hb (or_intror Hb'))|].
        apply DJE; [exact Hb| destruct MBO as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _); unfold blocks_MEMBIO in Hb'; destruct Hb' as [<-|[<-|[<-|[<-|[]]]]]; assumption].
      + apply Forall_cons; [right; left; cbn [fst snd]; unfold AFS_SIZE; clear - FF5 FF6; lia| apply Forall_cons; [left; cbn [fst snd]; clear - AS1; lia| apply Forall_nil]].
      + intros a Ha. cbn [rin_ivs fst snd] in Ha. destruct Ha as [Ha|[Ha|Ha]]; [right; cbn; left; exact Ha| right; cbn; right; left; exact Ha| left].
        unfold MEMBIO_foot in Ha. cbn [rin_ivs fst snd] in Ha. unfold blocks_MEMBIO.
        destruct Ha as [Ha|[Ha|[]]]; [exists (mb_id R, mb, BIO_SIZE); split; [left; reflexivity| cbn; exact Ha]| exists (mb_bmid R, mb_bm R, BUFMEM_SIZE); split; [right; right; left; reflexivity| cbn; exact Ha]].
    - intros XA. eapply xpres_trans; [exact XA|].
      apply (xpres_drop_nonclient H LB (bv_unsigned sp) (XSF ff fp ++ MEMBIO_foot mb R) [(S1 + 184, S1 + 192)]).
      + eapply xpres_weaken; [exact XP| clear - Q2; lia| exact SUB0|].
        intros q Hq. cbn [rin_ivs fst snd] in Hq. apply rin_ivs_app. destruct Hq as [Hq|[Hq|Hq]].
        * left. apply rin_ivs_app. left. unfold XSF. cbn [rin_ivs fst snd]. right; right; left. change (fsz 6) with 4096. clear - Hq. lia.
        * right. cbn [rin_ivs fst snd]. left. exact Hq.
        * left. apply rin_ivs_app. right. exact Hq.
      + intros q Hq HC. cbn [rin_ivs fst snd] in Hq. destruct Hq as [Hq|[]].
        eapply (client_not_frame _ _ _ _ q HP SUB0 HC). clear - Hq AS1 CEIL LO STK0 Q2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pf_site : forall site PFg, (forall e, In e (pf_shift site PFg) -> In e (PF_readcfg PF9new PF9free M)) ->
    pf_ok (as_TR H) PFg site CH1.
  Proof using PF. intros site PFg INC. unfold CH1. eapply pf_ok_call; [exact PF| exact INC]. Qed.

  (* [comment removed for export] *)
  Lemma rp_fail595 :
    forall m1 msF1 mo1 (s1' : as_St H) (p : bptr) (A n0 : Z) (lb : list byte) (R' : membio) (ff fp rb : Z) (fj1 fj2 jg : list byte) (pre post : list cell)
           (sa : list byte) (sb : byte) (sc : list byte) (sb2 sc2 : byte) (sd se : list byte) (sr : byte) (sg : list byte) (um uf : Z)
           (u0 u1 u2 b3 b4 b5 b6 b7 s2v s5v s6v s7v s8v s9v s11v u3 u4 u5 u6 errv1 : word),
      as_VIS H s1' msF1 = MS (mkR (Z_to_bv 64 ALD_RF) (Z_to_bv 64 S1) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1) (Z_to_bv 64 A) (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 140) b3 b4 b5 b6 b7
                                  s2v (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) (Z_to_bv 64 A) s5v s6v s7v s8v s9v (Z_to_bv 64 A) s11v u3 u4 u5 u6)
                          F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs) ->
      as_RHEAP H s1' ((p, A, n0) :: L0) m1 -> as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 -> mem_inv asegs m1 -> ACONST m1 ->
      0 <= n0 <= 512 * 33 -> rw_cells asegs m1 A [CB (Z.to_nat n0) lb] -> addressable m1 A n0 ->
      MEMBIO H LB m1 mb R' -> MEMBIO_shad m1 mb R' -> mb_static R R' -> bytes_at asegs m1 (mb_buf R) ds ->
      stk asegs m1 lo S1 -> stack0 m1 lo (bv_unsigned sp) ->
      cells_size pre = 152%nat -> cells_size post = 176%nat -> rw_cells asegs m1 S1 (pre ++ [C8 (wz ff); C8 (wz ff)] ++ post) ->
      rw_cells asegs m1 (S1 + 344) [CB (Z.to_nat KG) jg] -> rw_cells asegs m1 (bv_unsigned sp + -104) SAVES ->
      rw_cells asegs m1 ff (arp_fframe S1 fj1 rb fj2 fp) -> rw_cells asegs m1 (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sb2 sc2 sd se sr sg) -> as_RFS H (LF1 ff fp) m1 ->
      rw_cells asegs m1 (errno_addr (Z_to_bv 64 ATP)) [C4 errv1] -> as_rauxv_ok H m1 B ->
      LIBMID LIB m1 M -> rw_cells asegs m1 st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> STORE_shad m1 st S ->
      as_chain H m1 (bv_unsigned sp) CH1 ->
      xpres H LB (bv_unsigned sp) (XSF ff fp ++ MEMBIO_foot mb R) m m1 ->
      LEDGER s1' um uf -> um + 2^16 + 64 <= DECODE_CUM_BYTES -> uf + n0 + 2^16 + 64 <= DECODE_CUM_BYTES ->
      as_SR H POST (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros m1 msF1 mo1 s1' p A n0 lb R' ff fp rb fj1 fj2 jg pre post sa sb sc sb2 sc2 sd se sr sg um uf u0 u1 u2 b3 b4 b5 b6 b7 s2v s5v s6v s7v s8v s9v s11v u3 u4 u5 u6 errv1.
    intros VIS1 HP1 KREL1 MP1 MI1 AC1 N0R LBc AD1 MBO1 MSH1 MST1 DS1 STK1 ST01 PREZ POSTZ SL1 GP1 SV1 FRM1 FSH1 RFS1 ERR1 AUX1 LM1 SC1 SSH1 CHN1 XA1 LED UMB UFB.
    destruct rc_facts as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). fold S1 in Q1, Q2.
    pose proof rc_stack as (STKR & STKL & STKZ & STKF & STKA).
    pose proof (fresh_of_RFS H HH _ _ _ _ _ RFS1) as FRESH.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    assert (SHF : Z.shiftr ff 3 + ASHB = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (APff : aapp ff 4096) by (eapply aapp_sub; [exact FB3| clear - FF5; lia| unfold AFS_SIZE; clear - FF6; lia]).
    destruct (lad_head_facts H HX L0 _ _ _ _ _ HP1) as (BR & NIP & DISJ & BLK & SV).
    pose proof MST1 as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    assert (KEEPB : forall b, In b (blocks_MEMBIO mb R') -> In b LB).
    { intros b Hb. rewrite (mb_static_blocks mb R R' MST1) in Hb. destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _). unfold blocks_MEMBIO in Hb.
      destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption. }
    assert (SUBLB0 : forall b, In b LIB -> In b L0) by (intros b Hb; exact (SUB0 _ (SUBL _ Hb))).
    assert (SUBE0 : forall b, In b (mid_errblocks M) -> In b L0) by (intros b Hb; unfold L0; apply in_or_app; left; exact Hb).
    assert (CHB1 : forall fp' ra', In (fp', ra') CH1 -> S1 + 16 <= fp').
    { intros fp' ra' [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
    pose proof LM1 as (IM1 & _ & _ & _ & _ & _ & _ & _ & GM1 & _).
    pose proof (errph_bytes_range (mid_err M)) as [EBR ECR].
    (* [comment removed for export] *)
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := (p, A, n0) :: L0) (s := s1') (p := p) (A := A) (n := n0) (errv := errv1) (CH := CH1) (bs := lb); clear CF.
      all: try first [exact VIS1| exact HP1| exact KREL1| exact AUX1| exact MI1| exact CEIL| exact AC1| exact CHN1| exact LBc| exact AD1| exact IM1| exact GM1| exact ERR1].
      all: lazymatch goal with
           | |- In _ _ => left; reflexivity
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - SPB Q2; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact STK1
           | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKF Q2; lia
           | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact (CHB1 _ _ Hin)
           | |- pf_ok _ _ _ _ => unfold ALD_RF; rewrite unsigned_lit by (clear; lia); apply pf_site;
                                 intros e He; unfold PF_readcfg, PF_read_priv; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact He
           | |- as_Cf H _ <= as_AL H _ => pose proof (LEDGER_pay s1' um uf 0 n0 LED ltac:(clear; lia) ltac:(clear - N0R; lia) ltac:(clear - UMB; lia) ltac:(clear - UFB EBR; lia)) as PAYq;
                                             pose proof (ah_costs H HH) as (CM0 & _); pose proof (CM0 0 ltac:(clear; lia)) as CMz; clear - PAYq CMz; lia
           | |- @eq _ _ _ => reflexivity
           | |- ?G => idtac "F595_CF_LEFT" G
           end. }
    clear CF. intros [msF2 mo2] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & s2' & VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & HP2 & IM2 & GM2 & AL2).
    rewrite (proj1 (ah_lb_remove H HH)) in XP2, HP2 by exact NIP.
    rewrite (unsigned_lit S1) in ST2, XP2 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    assert (LED2 : LEDGER s2' um (uf + n0)).
    { pose proof (LEDGER_step s1' s2' um uf 0 n0 LED ltac:(clear; lia) ltac:(clear - N0R; lia)) as K. rewrite Z.add_0_r in K. apply K.
      pose proof (ah_costs H HH) as (CM0 & _). pose proof (CM0 0 ltac:(clear; lia)) as CMz. clear - AL2 CMz. lia. }
    (* [comment removed for export] *)
    assert (T12s : forall A' cs, rw_cells asegs m1 A' cs -> S1 <= A' -> rw_cells asegs m2 A' cs).
    { intros A' cs RC HA. eapply (xpres_rw_cells' H); [exact XP2| exact RC| left; exact HA| apply Forall_nil]. }
    pose proof (T12s _ _ SL1 ltac:(clear; lia)) as SL2. pose proof (T12s _ _ GP1 ltac:(clear; lia)) as GP2. pose proof (T12s _ _ SV1 ltac:(clear - Q2; lia)) as SV2.
    assert (FRM2 : rw_cells asegs m2 ff (arp_fframe S1 fj1 rb fj2 fp)).
    { eapply (xpres_rw_cells' H); [exact XP2| exact FRM1| | apply Forall_nil]. right; right; right; right; left. unfold AFS_SIZE.
      unfold arp_fframe. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]. clear - FF5 FF6. lia. }
    assert (FSH2 : rw_cells asegs m2 (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sb2 sc2 sd se sr sg)).
    { eapply (xpres_rw_cells' H); [exact XP2| exact FSH1| | apply Forall_nil]. right; right; right; right; right; left. rewrite SHF. unfold AFS_SIZE.
      unfold arp_fshadow. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ].
      pose proof (sh_mono (as_FSB H) ff ltac:(clear - FF5; lia)) as Y1. pose proof (sh_mono (ff + 4096) _ FF6) as Y2.
      pose proof (sh_add8 ff 512) as Y3. replace (ff + 8 * 512) with (ff + 4096) in Y3 by (clear; lia). clear - Y1 Y2 Y3. lia. }
    assert (SC2 : rw_cells asegs m2 st [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
    { eapply (xpres_rw_cells' H); [exact XP2| exact SC1| | apply Forall_nil]. right; right; left. exists (es_id S, st, STORE_SIZE). split; [exact SIN| cbn; unfold STORE_SIZE; clear; lia]. }
    assert (MBO2 : MEMBIO H LB m2 mb R') by (eapply (AMEMBIO_xpres H LB L0 S1 []); [exact MBO1| intros b Hb; exact (SUB0 _ (KEEPB _ Hb))| exact XP2| apply Forall_nil]).
    pose proof SBR as (_ & SB2 & _ & SBa & SBb & SBf & SBc).
    rewrite SEQ in SSH1. apply (proj1 (STORE_shad_empty _ _ _)) in SSH1. destruct SSH1 as [SHhi SAD1].
    assert (SAD2 : addressable m2 st STORE_SIZE).
    { eapply (ashobj_addressable_xpres H HH s1' _ L0 m1 m2 S1 []); [exact HP1| intros b Hb; right; exact Hb| clear - CEIL LO STK0 Q2; lia| left; exists (es_id S, st, STORE_SIZE); split; [exact SIN| cbn; clear; lia]
        | exact SHhi| exact SAD1| exact XP2| apply Forall_nil]. }
    assert (MSH2 : MEMBIO_shad m2 mb R').
    { destruct MSH1 as (X1 & X2 & X3 & X4). pose proof MBO1 as MBq. destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & K1 & K2 & K3 & K4 & _).
      pose proof K1 as (_ & _ & _ & _ & K1b & _). pose proof K2 as (_ & _ & _ & _ & K2b & _). pose proof K3 as (_ & _ & _ & _ & K3b & _). pose proof K4 as (_ & _ & _ & _ & K4b & _).
      unfold MEMBIO_shad. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
      split; [| split; [| split]].
      - eapply (ashobj_addressable_xpres H HH s1' _ L0 m1 m2 S1 []); [exact HP1| intros b Hb; right; exact Hb| clear - CEIL LO STK0 Q2; lia| left; exists (mb_id R', mb, 128); split; [apply SUB0; exact J1| cbn; clear; lia]
          | unfold AAPP_HI; clear - K1b ACB; lia| exact X1| exact XP2| apply Forall_nil].
      - eapply (ashobj_addressable_xpres H HH s1' _ L0 m1 m2 S1 []); [exact HP1| intros b Hb; right; exact Hb| clear - CEIL LO STK0 Q2; lia| left; exists (mb_bbid R', mb_bb R', 16); split; [apply SUB0; exact J2| cbn; clear; lia]
          | unfold AAPP_HI; clear - K2b ACB; lia| exact X2| exact XP2| apply Forall_nil].
      - eapply (ashobj_addressable_xpres H HH s1' _ L0 m1 m2 S1 []); [exact HP1| intros b Hb; right; exact Hb| clear - CEIL LO STK0 Q2; lia| left; exists (mb_bmid R', mb_bm R', 32); split; [apply SUB0; exact J3| cbn; clear; lia]
          | unfold AAPP_HI; clear - K3b ACB; lia| exact X3| exact XP2| apply Forall_nil].
      - eapply (ashobj_addressable_xpres H HH s1' _ L0 m1 m2 S1 []); [exact HP1| intros b Hb; right; exact Hb| clear - CEIL LO STK0 Q2; lia| left; exists (mb_rpid R', mb_rp R', 32); split; [apply SUB0; exact J4| cbn; clear; lia]
          | unfold AAPP_HI; clear - K4b ACB; lia| exact X4| exact XP2| apply Forall_nil]. }
    assert (DS2 : bytes_at asegs m2 (mb_buf R) ds).
    { pose proof MBO as MBq. destruct MBq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LENR & BUFP & BUFH & _).
      destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      - assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil. clear - BUFP BUFH ACB L0Z. lia.
      - destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN _]].
        eapply (xpres_bytes_at' H); [exact XP2| exact DS1| | apply Forall_nil]. right; right; left. exists (pD, mb_buf R, mb_len R). split; [exact (SUB0 _ PIN)| cbn; unfold zlength in DSL; rewrite DSL; clear; lia]. }
    assert (ST02 : stack0 m2 lo (bv_unsigned sp)) by (eapply (stack0_xpres H); [exact XP2| exact ST01| apply Forall_nil]).
    assert (RFS2 : as_RFS H (LF1 ff fp) m2) by (eapply (RFS_via_xpres H HH); [exact RFS1| exact XP2| apply Forall_nil]).
    assert (LM2 : LIBMID LIB m2 M) by (eapply (LIBMID_xpres0 H LIB L0 S1); [exact LM1| exact CTX| exact XP2| exact SUBLB0| exact SUBE0]).
    assert (CHN2 : as_chain H m2 (bv_unsigned sp) CH1) by (eapply chain_keepX; [exact CHN1| exact XP2| exact CHB1| clear - CEIL LO STK0 Q2; lia| apply Forall_nil]).
    assert (XA2 : xpres H LB (bv_unsigned sp) (XSF ff fp ++ MEMBIO_foot mb R) m m2).
    { eapply xpres_trans; [exact XA1|]. eapply xpres_weaken; [exact XP2| clear - Q2; lia| exact SUB0| intros q Hq; destruct Hq]. }
    clear T12s XP2 SL1 GP1 SV1 FRM1 FSH1 SC1 MBO1 SAD1 MSH1 DS1 ST01 RFS1 LM1 CHN1 XA1 ERR1 AUX1 AC1 MI1 STK1 KREL1 VIS1 HP1 LBc AD1 IM1 GM1.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 ALD_RF)) with (Z_to_bv 64 ALD_RF) in VIS2 by (symmetry; apply ret_pc_even; [unfold ALD_RF; lia| reflexivity]).
    rewrite app_assoc in SL2. apply (proj1 (rw_cells_app asegs m2 S1 _ post)) in SL2. destruct SL2 as [SL2 SLb2].
    replace (S1 + Z.of_nat (cells_size (pre ++ [C8 (wz ff); C8 (wz ff)]))) with (S1 + 168) in SLb2 by (rewrite cells_size_app, PREZ; cbn [cells_size csize Nat.add]; clear; lia).
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply ald_seg5 with (pre := pre);
      [clear - Q2 CEIL LO STK0 LO0; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| unfold AIMG_TOP; clear - FF1; lia| clear - FF6 FB2; lia| exact APff| clear - CEIL LO STK0 Q2; lia| exact PREZ
      | exact SL2| exact FSH2| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 (m3 & VIS3 & MU3 & WM3 & MI3 & SL3 & FSH3).
    rewrite SHF in MU3. replace (sh ff + 282 + 1) with (sh ff + 282 + 1) in MU3 by reflexivity.
    pose proof (poke_carry ff fp m2 m3 s2' L0 282 FRESH ltac:(clear; lia) ltac:(replace (sh ff + 282 + 1) with (sh ff + 283) by (clear; lia); exact MU3) WM3 HP2)
      as (HP3 & TAUX & TRFS & TLM & Tstk & Tff & Tblk & Tbytes & Tad & Terr & Tst0 & Tac & Tstk2 & Tch & Tacc & Txa & Tmb & Tms).
    pose proof (TAUX AUX2) as AUX3. pose proof (TRFS RFS2) as RFS3. pose proof (TLM LIB M x LM2 CTX SUBLB0 SUBE0) as LM3.
    pose proof (Tstk _ _ GP2 ltac:(clear - CEIL LO STK0 Q2; lia)) as GP3. pose proof (Tstk _ _ SLb2 ltac:(clear - CEIL LO STK0 Q2; lia)) as SLb3. pose proof (Tstk _ _ SV2 ltac:(clear - CEIL LO STK0 Q2; lia)) as SV3.
    pose proof (Tff _ FRM2 ltac:(unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as FRM3.
    pose proof (Tblk (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] SIN ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC2) as SC3.
    pose proof (Tad (es_id S, st, STORE_SIZE) st STORE_SIZE SIN ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD2) as SAD3.
    pose proof (Terr _ ERR2) as ERR3. pose proof (Tst0 ST02) as ST03. pose proof (Tac AC2) as AC3. pose proof (Tstk2 _ _ ST2 CEIL) as STK3.
    pose proof (Tch _ _ CHN2 CHB1) as CHN3.
    assert (MBO3 : MEMBIO H LB m3 mb R').
    { destruct MBO2 as (X1 & X2 & X3 & X4 & REST). pose proof REST as (J1 & J2 & J3 & J4 & _).
      split; [| split; [| split; [| split; [| exact REST]]]].
      - eapply (Tblk (mb_id R', mb, BIO_SIZE)); [apply SUB0; exact J1| apply Z.le_refl| cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]; unfold BIO_SIZE; clear; lia| exact X1].
      - eapply (Tblk (mb_bbid R', mb_bb R', BIOBUFMEM_SIZE)); [apply SUB0; exact J2| apply Z.le_refl| cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]; unfold BIOBUFMEM_SIZE; clear; lia| exact X2].
      - eapply (Tblk (mb_bmid R', mb_bm R', BUFMEM_SIZE)); [apply SUB0; exact J3| apply Z.le_refl| cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]; unfold BUFMEM_SIZE; clear; lia| exact X3].
      - eapply (Tblk (mb_rpid R', mb_rp R', BUFMEM_SIZE)); [apply SUB0; exact J4| apply Z.le_refl| cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]; unfold BUFMEM_SIZE; clear; lia| exact X4]. }
    assert (MSH3 : MEMBIO_shad m3 mb R').
    { destruct MSH2 as (X1 & X2 & X3 & X4). pose proof MBO2 as MBq. destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _). unfold MEMBIO_shad.
      split; [| split; [| split]].
      - eapply (Tad (mb_id R', mb, BIO_SIZE)); [apply SUB0; exact J1| apply Z.le_refl| apply Z.le_refl| unfold BIO_SIZE; clear; lia| exact X1].
      - eapply (Tad (mb_bbid R', mb_bb R', BIOBUFMEM_SIZE)); [apply SUB0; exact J2| apply Z.le_refl| apply Z.le_refl| unfold BIOBUFMEM_SIZE; clear; lia| exact X2].
      - eapply (Tad (mb_bmid R', mb_bm R', BUFMEM_SIZE)); [apply SUB0; exact J3| apply Z.le_refl| apply Z.le_refl| unfold BUFMEM_SIZE; clear; lia| exact X3].
      - eapply (Tad (mb_rpid R', mb_rp R', BUFMEM_SIZE)); [apply SUB0; exact J4| apply Z.le_refl| apply Z.le_refl| unfold BUFMEM_SIZE; clear; lia| exact X4]. }
    assert (DS3 : bytes_at asegs m3 (mb_buf R) ds).
    { pose proof MBO as MBq. destruct MBq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LENR & BUFP & BUFH & _).
      destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      - assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil. clear - BUFP BUFH ACB L0Z. lia.
      - destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN _]].
        eapply (Tbytes (pD, mb_buf R, mb_len R)); [exact (SUB0 _ PIN)| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DS2]. }
    assert (XA3 : xpres H LB (bv_unsigned sp) (XSF ff fp ++ MEMBIO_foot mb R) m m3).
    { eapply xpres_trans; [exact XA2|]. eapply (xpres_of_munch_gen H); [exact MU3| exact WM3|]. intros a Ha [_ HXa]. cbn. split; [| exact I].
      intros Ra. apply HXa. apply rin_ivs_app. left. unfold XSF. cbn [rin_ivs fst snd]. right; right; right; left.
      change (fshn 6) with 512. clear - Ra. lia. }
    clear TAUX TRFS TLM Tstk Tff Tblk Tbytes Tad Terr Tst0 Tac Tstk2 Tch Tacc Txa Tmb Tms AUX2 RFS2 LM2 GP2 SV2 FRM2 SC2 SAD2 ERR2 ST02 AC2 ST2 CHN2 MBO2 MSH2 DS2 XA2 MU3 WM3 SL2 SLb2 FSH2 MI2 HP2.
    (* [comment removed for export] *)
    eapply (rp_raiseW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ msF3 m3 mo3 s2' [] LIB M ff fp errv1 ALD_R595 A595_R2 A595_R3 595 AR_INTERNAL_ERROR);
      cbn [app].
    all: try first [exact VIS3| exact HP3| exact KREL3| exact LM3| exact SUBL| exact CTX| exact MF1| exact AUX3| exact STK3| exact ST03| exact ERR3| exact MI3| exact AC3| exact RFS3| exact CHN3| exact MCO
                    | exact arp_g595a| exact arp_g595b].
    all: lazymatch goal with
         | |- lb_bytes _ + _ + _ <= _ => pose proof BUD as BUDq; unfold mid_bytes in BUDq; rewrite CTX in BUDq; cbn [ctxph_bytes] in BUDq; unfold DECODE_BYTES, ERRDEBUG_BYTES, ERRSTR_BYTES in *; clear - BUDq; lia
         | |- Z.of_nat _ + _ + _ <= _ => pose proof BUDC as BUDq; unfold mid_cnt in BUDq; rewrite CTX in BUDq; cbn [ctxph_cnt] in BUDq; unfold DECODE_CNT, ERRSTR_CNT in *; clear - BUDq; lia
         | |- lo <= _ => clear - LO STKR Q2; lia
         | |- (length _ + _ <= _)%nat => unfold LF1; cbn [length]; unfold READCFG_LF, READCFG_MAXLIVE, AFS_MAXLIVE in LFB |- *; destruct (mid_err M); cbn [ERRPH_LF]; clear - LFB; lia
         | |- pf_ok _ (PF_errnew _) _ _ => apply pf_site; intros e He; unfold PF_readcfg, PF_read_priv, pf_raise; do 3 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; left; exact He
         | |- pf_ok _ PF_errdebug _ _ => apply pf_site; intros e He; unfold PF_readcfg, PF_read_priv, pf_raise; do 3 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact He
         | |- pf_ok _ PF_errseterr _ _ => apply pf_site; intros e He; unfold PF_readcfg, PF_read_priv, pf_raise; do 3 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact He
         | |- RAISE_COST _ _ <= _ => unfold RAISE_COST, raise_bytes, ERRDEBUG_BYTES; apply (LEDGER_pay s2' um (uf + n0) _ _ LED2); [clear - EBR; lia| clear - EBR; lia| clear - UMB EBR; lia| clear - UFB EBR; lia]
         | |- 0 <= 595 < _ => clear; lia
         | |- 0 < AR_INTERNAL_ERROR < _ => unfold AR_INTERNAL_ERROR; clear; lia
         | |- 0 <= _ < 2 ^ 64 => unfold ALD_R595, A595_R2, A595_R3; clear; lia
         | |- _ mod 2 = 0 => reflexivity
         | |- ?G => first [match G with forall _, _ => idtac end| idtac "F595_RAISE_LEFT" G]
         end.
    (* [comment removed for export] *)
    intros w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 msF4 m4 mo4 s4' errv4 LE M' c XS VIS4 KREL4 MP4 MI4 AC4 ST4 AUX4 HP4 LM4 STEP4 NEW4 F4 CX4 ME4 VD4 DL4 EC4 EB4 ERR4 FXS4 XP4 RFS4 AL4
           Ts Tf Tsh Tb Tby Ta T0 CHN4.
    cbn [app] in HP4, Tb, Tby, Ta.
    assert (LED4 : LEDGER s4' (um + raise_bytes (mid_err M)) (uf + n0 + (errph_bytes (mid_err M) + ERRDEBUG_BYTES))).
    { eapply LEDGER_step; [exact LED2| unfold raise_bytes, ERRDEBUG_BYTES; clear - EBR; lia| unfold ERRDEBUG_BYTES; clear - EBR; lia| unfold RAISE_COST in AL4; clear - AL4; lia]. }
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply a595c; exact MI4|]. intros msF5 mo5 KREL5 MP5 VIS5. cbn beta in VIS5.
    assert (ESNE : forall cq b', mid_err M = ErrReady cq -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id (ec_es cq) <> blk_id b').
    { intros cq b' EQ Hb'. destruct (es_facts _ _ _ _ _ LM3 CTX EQ) as [I5 _]. exact (DJ6 _ _ I5 Hb'). }
    pose proof MBO as MBq. destruct MBq as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _ & _ & _ & _ & _ & LENR & BUFP & BUFH & _).
    eapply (rp_exit m4 msF5 mo5 s4' 0 M' R' LE ff fp rb fj1 fj2 jg (pre ++ [C8 (wz ff); C8 (wz ff)] ++ post) (XSF ff fp ++ XS)).
    all: try first [exact VIS5| exact KREL5| exact MI4| exact AC4| exact ST4| exact RFS4| exact ERR4| exact AUX4| exact HP4| exact LM4| exact STEP4| exact NEW4| exact EC4| exact EB4| exact MST1| exact CHN4].
    - left; reflexivity.
    - eapply (ah_mpres_trans H HH); [| exact MP5]. eapply (ah_mpres_trans H HH); [| exact MP4]. eapply (ah_mpres_trans H HH); [| exact MP3]. eapply (ah_mpres_trans H HH); [exact MP1| exact MP2].
    - exact (T0 ST03).
    - rewrite !cells_size_app, PREZ, POSTZ. reflexivity.
    - rewrite app_assoc. apply (proj2 (rw_cells_app asegs m4 S1 _ post)). split.
      + apply Ts; [exact SL3| clear; lia| rewrite cells_size_app, PREZ; cbn; clear - Q2; lia].
      + replace (S1 + Z.of_nat (cells_size (pre ++ [C8 (wz ff); C8 (wz ff)]))) with (S1 + 168) by (rewrite cells_size_app, PREZ; cbn [cells_size csize Nat.add]; clear; lia).
        apply Ts; [exact SLb3| clear; lia| rewrite POSTZ; clear - Q2; lia].
    - apply Ts; [exact GP3| clear; lia| cbn [cells_size csize Nat.add]; unfold KG; fold S1; clear - Q2; lia].
    - apply Ts; [exact SV3| clear - Q2; lia| unfold SAVES, arp_saves; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia].
    - apply Tf; [exact FRM3| unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia].
    - rewrite CX4, CTX. reflexivity.
    - (* [comment removed for export] *) destruct MBO3 as (X1 & X2 & X3 & X4 & REST). pose proof REST as (J1 & J2 & J3 & J4 & _).
      split; [| split; [| split; [| split; [| exact REST]]]].
      + eapply (Tb (mb_id R', mb, BIO_SIZE)); [exact J1| intros cq EQ; cbn [blk_id fst snd]; rewrite T6; apply (ESNE cq (mb_id R, mb, BIO_SIZE) EQ); right; unfold blocks_MEMBIO; left; reflexivity| apply Z.le_refl
          | cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]; unfold BIO_SIZE; clear; lia| exact X1].
      + eapply (Tb (mb_bbid R', mb_bb R', BIOBUFMEM_SIZE)); [exact J2| intros cq EQ; cbn [blk_id fst snd]; rewrite T7; apply (ESNE cq (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE) EQ); right; unfold blocks_MEMBIO; right; left; reflexivity| apply Z.le_refl
          | cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]; unfold BIOBUFMEM_SIZE; clear; lia| exact X2].
      + eapply (Tb (mb_bmid R', mb_bm R', BUFMEM_SIZE)); [exact J3| intros cq EQ; cbn [blk_id fst snd]; rewrite T8; apply (ESNE cq (mb_bmid R, mb_bm R, BUFMEM_SIZE) EQ); right; unfold blocks_MEMBIO; right; right; left; reflexivity| apply Z.le_refl
          | cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]; unfold BUFMEM_SIZE; clear; lia| exact X3].
      + eapply (Tb (mb_rpid R', mb_rp R', BUFMEM_SIZE)); [exact J4| intros cq EQ; cbn [blk_id fst snd]; rewrite T9; apply (ESNE cq (mb_rpid R, mb_rp R, BUFMEM_SIZE) EQ); right; unfold blocks_MEMBIO; right; right; right; left; reflexivity| apply Z.le_refl
          | cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]; unfold BUFMEM_SIZE; clear; lia| exact X4].
    - (* [comment removed for export] *) destruct MSH3 as (Y1 & Y2 & Y3 & Y4). pose proof MBO3 as MBq. destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
      pose proof (BLK0 _ (SUB0 _ J1)) as (_ & M1 & _). pose proof (BLK0 _ (SUB0 _ J2)) as (_ & M2 & _). pose proof (BLK0 _ (SUB0 _ J3)) as (_ & M3 & _). pose proof (BLK0 _ (SUB0 _ J4)) as (_ & M4 & _).
      cbn [blk_addr fst snd] in M1, M2, M3, M4. unfold MEMBIO_shad.
      split; [| split; [| split]].
      + eapply (Ta (mb_id R', mb, BIO_SIZE)); [exact J1| intros cq EQ; cbn [blk_id fst snd]; rewrite T6; apply (ESNE cq (mb_id R, mb, BIO_SIZE) EQ); right; unfold blocks_MEMBIO; left; reflexivity| apply Z.le_refl| apply Z.le_refl
          | clear - M1; Z.div_mod_to_equations; lia| unfold BIO_SIZE; clear; lia| exact Y1].
      + eapply (Ta (mb_bbid R', mb_bb R', BIOBUFMEM_SIZE)); [exact J2| intros cq EQ; cbn [blk_id fst snd]; rewrite T7; apply (ESNE cq (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE) EQ); right; unfold blocks_MEMBIO; right; left; reflexivity| apply Z.le_refl| apply Z.le_refl
          | clear - M2; Z.div_mod_to_equations; lia| unfold BIOBUFMEM_SIZE; clear; lia| exact Y2].
      + eapply (Ta (mb_bmid R', mb_bm R', BUFMEM_SIZE)); [exact J3| intros cq EQ; cbn [blk_id fst snd]; rewrite T8; apply (ESNE cq (mb_bmid R, mb_bm R, BUFMEM_SIZE) EQ); right; unfold blocks_MEMBIO; right; right; left; reflexivity| apply Z.le_refl| apply Z.le_refl
          | clear - M3; Z.div_mod_to_equations; lia| unfold BUFMEM_SIZE; clear; lia| exact Y3].
      + eapply (Ta (mb_rpid R', mb_rp R', BUFMEM_SIZE)); [exact J4| intros cq EQ; cbn [blk_id fst snd]; rewrite T9; apply (ESNE cq (mb_rpid R, mb_rp R, BUFMEM_SIZE) EQ); right; unfold blocks_MEMBIO; right; right; right; left; reflexivity| apply Z.le_refl| apply Z.le_refl
          | clear - M4; Z.div_mod_to_equations; lia| unfold BUFMEM_SIZE; clear; lia| exact Y4].
    - (* [comment removed for export] *) destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      + assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil. clear - BUFP BUFH ACB L0Z. lia.
      + destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN PNL]].
        eapply (Tby (pD, mb_buf R, mb_len R)); [exact PIN| intros cq EQ; destruct (es_facts _ _ _ _ _ LM3 CTX EQ) as [I5 _]; cbn [blk_id fst snd]; exact (PNL _ I5)
          | cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DS3].
    - (* [comment removed for export] *) pose proof SO as (_ & SINB & _).
      eapply (Tb (es_id S, st, STORE_SIZE)); [exact SINB| intros cq EQ; apply (ESNE cq _ EQ); left; reflexivity| cbn; clear; lia| cbn; unfold STORE_SIZE; clear; lia| exact SC3].
    - (* [comment removed for export] *) pose proof SO as (_ & SINB & _). rewrite SEQ. apply (proj2 (STORE_shad_empty _ _ _)). split; [exact SHhi|].
      eapply (Ta (es_id S, st, STORE_SIZE)); [exact SINB| intros cq EQ; apply (ESNE cq _ EQ); left; reflexivity| apply Z.le_refl| apply Z.le_refl| clear - SB2; Z.div_mod_to_equations; lia| unfold STORE_SIZE; clear; lia| exact SAD3].
    - apply Forall_app. split; [unfold XSF; apply (fs_scratch_of_fresh H); exact FRESH| exact FXS4].
    - intros a Ha. apply rin_ivs_app. left. exact Ha.
    - (* [comment removed for export] *) eapply xpres_trans.
      + eapply xpres_weaken; [exact XA3| apply Z.le_refl| intros b Hb; exact Hb|].
        intros q Hq. apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; apply rin_ivs_app; left; exact Hq|].
        apply rin_ivs_app; right. unfold XF. apply rin_ivs_app; right. apply rin_ivs_app; left. exact Hq.
      + eapply xpres_weaken; [exact XP4| apply Z.le_refl| intros b Hb; exact Hb|].
        intros q Hq. apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; apply rin_ivs_app; right; exact Hq|].
        apply rin_ivs_app; right. unfold XF. apply rin_ivs_app; right. apply rin_ivs_app; right.
        apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; exact Hq|]. apply rin_ivs_app; right. apply rin_ivs_app; right. exact Hq.
    - eapply LEDGER_post; [exact LED4| unfold raise_bytes, ERRDEBUG_BYTES; clear - UMB EBR; lia| unfold ERRDEBUG_BYTES; clear - UFB EBR; lia].
  Qed.

  Definition zero3_at (raC : Z) (f10 : Z -> word -> word) : Prop :=
    forall (s0w gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q ff A : Z) (w144 w168 w176 w192 w200 w208 w216 w224 w232 : word),
      0 <= q -> q + 464 <= 2^64 ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 (wz ff) (wz ff) w168 w176 (wz A) w192 w200 w208 w216 w224 w232) ->
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AFM_ERRL_R1) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 A) s3 s4 (Z_to_bv 64 0) s6 (Z_to_bv 64 0) (Z_to_bv 64 ff) s9 (f10 ff s10) (Z_to_bv 64 0) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_free_all) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 raC) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 raC)) fc None m (seg_rom asegs)).

  Lemma zero3_at_ZERO3 : zero3_at AFM_ZERO3 (fun _ w => w).
  Proof.
    intros until w232. intros Qz0 Qz1 SLz MIz.
    eapply evt_mono; [eapply arp_zero3; [exact Qz0| exact Qz1| exact SLz| exact MIz]|].
    intros ms' E. exact E.
  Qed.

  Lemma zero3_599 : zero3_at (A599_R2 + 24) (fun ff _ => Z_to_bv 64 ff).
  Proof.
    intros until w232. intros Qz0 Qz1 SLz MIz.
    replace (ret_pc (Z_to_bv 64 (A599_R2 + 24))) with (Z_to_bv 64 (A599_R2 + 24)) by (symmetry; apply ret_pc_even; [unfold A599_R2; lia| reflexivity]).
    unfold A599_R2, AFM_ERRL_R1, P_BIO_free_all. unfold arp_sg2, wz in SLz.
    go. step.
    apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rp_fail_lbuf :
    forall (line reason raA raB raC : Z) (f10 : Z -> word -> word),
      0 <= line < 2^31 -> 0 < reason < 2^23 -> 0 <= raA < 2^64 -> raA mod 2 = 0 -> 0 <= raB < 2^64 -> raB mod 2 = 0 -> 0 <= raC < 2^64 -> raC mod 2 = 0 ->
      arp_glue raA raB P_ERR_set_debug ARP_FILE line ARP_FUNC -> arp_glue raB raC P_ERR_set_error AERR_LIB_SSL reason 0 -> zero3_at raC f10 ->
      pf_ok (as_TR H) (PF_errnew (mid_err M)) raA CH1 -> pf_ok (as_TR H) PF_errdebug raB CH1 -> pf_ok (as_TR H) PF_errseterr raC CH1 ->
    forall m1 msF1 mo1 (s1' : as_St H) (p : bptr) (A nA : Z) (lb : list byte) (R' : membio) (ff fp rb : Z) (fj1 fj2 jg : list byte) (pre post : list cell)
           (w144 w168 w176 w192 w200 w208 w216 w224 w232 : word) (um uf : Z)
           (u0 u1 u2 a0v a1v a2v b3 b4 b5 b6 b7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v u3 u4 u5 u6 errv1 : word),
      as_VIS H s1' msF1 = MS (mkR (Z_to_bv 64 raA) (Z_to_bv 64 S1) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1) a0v a1v a2v b3 b4 b5 b6 b7
                                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v u3 u4 u5 u6)
                          F (Z_to_bv 64 P_ERR_new) fc None m1 (seg_rom asegs) ->
      as_RHEAP H s1' ((p, A, nA) :: L0) m1 -> as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 -> mem_inv asegs m1 -> ACONST m1 ->
      0 <= nA <= 512 * 33 -> rw_cells asegs m1 A [CB (Z.to_nat nA) lb] -> addressable m1 A nA ->
      MEMBIO H LB m1 mb R' -> MEMBIO_shad m1 mb R' -> mb_static R R' -> bytes_at asegs m1 (mb_buf R) ds ->
      stk asegs m1 lo S1 -> stack0 m1 lo (bv_unsigned sp) ->
      cells_size pre = 144%nat -> cells_size post = 104%nat ->
      rw_cells asegs m1 S1 (pre ++ arp_sg2 w144 (wz ff) (wz ff) w168 w176 (wz A) w192 w200 w208 w216 w224 w232 ++ post) ->
      rw_cells asegs m1 (S1 + 344) [CB (Z.to_nat KG) jg] -> rw_cells asegs m1 (bv_unsigned sp + -104) SAVES ->
      rw_cells asegs m1 ff (arp_fframe S1 fj1 rb fj2 fp) -> as_RFS H (LF1 ff fp) m1 ->
      rw_cells asegs m1 (errno_addr (Z_to_bv 64 ATP)) [C4 errv1] -> as_rauxv_ok H m1 B ->
      LIBMID LIB m1 M -> rw_cells asegs m1 st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> STORE_shad m1 st S ->
      as_chain H m1 (bv_unsigned sp) CH1 ->
      xpres H LB (bv_unsigned sp) (XSF ff fp ++ MEMBIO_foot mb R) m m1 ->
      LEDGER s1' um uf -> um + 2^16 + 64 <= DECODE_CUM_BYTES -> uf + nA + 2^16 + 64 <= DECODE_CUM_BYTES ->
      f10 ff s10v = Z_to_bv 64 ff ->
      as_SR H POST (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros line reason raA raB raC f10 LNR REAS RA1 RA1E RA2 RA2E RA3 RA3E GA GB Z3 P1 P2 P3.
    intros m1 msF1 mo1 s1' p A nA lb R' ff fp rb fj1 fj2 jg pre post w144 w168 w176 w192 w200 w208 w216 w224 w232 um uf
           u0 u1 u2 a0v a1v a2v b3 b4 b5 b6 b7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v u3 u4 u5 u6 errv1.
    intros VIS1 HP1 KREL1 MP1 MI1 AC1 NAR LBc1 AD1 MBO1 MSH1 MST1 DS1 STK1 ST01 PREZ POSTZ SL1 GP1 SV1 FRM1 RFS1 ERR1 AUX1 LM1 SC1 SSH1 CHN1 XA1 LED UMB UFB F10.
    destruct rc_facts as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). fold S1 in Q1, Q2.
    pose proof rc_stack as (STKR & STKL & STKZ & STKF & STKA).
    pose proof (fresh_of_RFS H HH _ _ _ _ _ RFS1) as FRESH.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    destruct (lad_head_facts H HX L0 _ _ _ _ _ HP1) as (BR & NIP & DISJ & BLK & SV).
    pose proof BR as (BRa & BRm & _ & BRt & BRc & BRf & BRp).
    pose proof MST1 as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    assert (SUBLB0 : forall b, In b LIB -> In b L0) by (intros b Hb; exact (SUB0 _ (SUBL _ Hb))).
    assert (CHB1 : forall fp' ra', In (fp', ra') CH1 -> S1 + 16 <= fp').
    { intros fp' ra' [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
    pose proof LM1 as (IM1 & _ & _ & _ & _ & _ & _ & _ & GM1 & _).
    pose proof (errph_bytes_range (mid_err M)) as [EBR ECR].
    pose proof (ah_costs H HH) as (CM0 & _). pose proof (CM0 0 ltac:(clear; lia)) as CMz.
    pose proof SO as (_ & SINB & _).
    pose proof MBO as MBq. destruct MBq as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _ & _ & _ & _ & _ & LENR & BUFP & BUFH & _).
    rewrite SEQ in SSH1. apply (proj1 (STORE_shad_empty _ _ _)) in SSH1. destruct SSH1 as [SHhi SAD1].
    pose proof SBR as (_ & SB2 & _).
    assert (SLZ : cells_size (pre ++ arp_sg2 w144 (wz ff) (wz ff) w168 w176 (wz A) w192 w200 w208 w216 w224 w232 ++ post) = 344%nat).
    { rewrite !cells_size_app, PREZ, POSTZ. cbn. reflexivity. }
    assert (HPp : as_RHEAP H s1' (mid_errblocks M ++ [(p, A, nA)] ++ LB) m1) by (eapply PERM; [exact HP1| unfold L0; apply Permutation_middle]).
    (* [comment removed for export] *)
    assert (ESNE : forall cq b', mid_err M = ErrReady cq -> In b' ((p, A, nA) :: (es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id (ec_es cq) <> blk_id b').
    { intros cq b' EQ Hb'. destruct (es_facts _ _ _ _ _ LM1 CTX EQ) as [I5 _]. destruct Hb' as [<-|Hb']; [| exact (DJ6 _ _ I5 Hb')].
      cbn [blk_id fst snd]. intros E. apply NIP. rewrite <- E. exact (in_map blk_id _ _ (SUB0 _ (SUBL _ I5))). }
    (* [comment removed for export] *)
    eapply (rp_raiseW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ msF1 m1 mo1 s1' [(p, A, nA)] LIB M ff fp errv1 raA raB raC line reason);
      cbn [app].
    all: try first [exact VIS1| exact HPp| exact KREL1| exact LM1| exact CTX| exact MF1| exact AUX1| exact STK1| exact ST01| exact ERR1| exact MI1| exact AC1| exact RFS1| exact CHN1| exact MCO
                    | exact GA| exact GB| exact P1| exact P2| exact P3| exact LNR| exact REAS| exact RA1| exact RA1E| exact RA2| exact RA2E| exact RA3| exact RA3E].
    all: lazymatch goal with
         | |- forall b, In b LIB -> _ => intros b Hb; right; exact (SUBL _ Hb)
         | |- lb_bytes _ + _ + _ <= _ => pose proof BUD as BUDq; unfold mid_bytes in BUDq; rewrite CTX in BUDq; cbn [ctxph_bytes] in BUDq;
                                         rewrite lb_bytes_app_s in BUDq; rewrite lb_bytes_app_s, lb_bytes_cons; cbn [blk_size snd];
                                         unfold DECODE_BYTES, ERRDEBUG_BYTES, ERRSTR_BYTES in *; clear - BUDq NAR; lia
         | |- Z.of_nat _ + _ + _ <= _ => pose proof BUDC as BUDq; unfold mid_cnt in BUDq; rewrite CTX in BUDq; cbn [ctxph_cnt] in BUDq;
                                         rewrite length_app in BUDq; rewrite length_app; cbn [length]; unfold DECODE_CNT, ERRSTR_CNT in *; clear - BUDq; lia
         | |- lo <= _ => clear - LO STKR Q2; lia
         | |- (length _ + _ <= _)%nat => unfold LF1; cbn [length]; unfold READCFG_LF, READCFG_MAXLIVE, AFS_MAXLIVE in LFB |- *; destruct (mid_err M); cbn [ERRPH_LF]; clear - LFB; lia
         | |- RAISE_COST _ _ <= _ => unfold RAISE_COST, raise_bytes, ERRDEBUG_BYTES; apply (LEDGER_pay s1' um uf _ _ LED); [clear - EBR; lia| clear - EBR; lia| clear - UMB EBR; lia| clear - UFB EBR NAR; lia]
         | |- ?G => first [match G with forall _, _ => idtac end| idtac "F599_RAISE_LEFT" G]
         end.
    (* [comment removed for export] *)
    intros w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 msF2 m2 mo2 s2' errv2 LE M' c XS VIS2 KREL2 MP2 MI2 AC2 ST2 AUX2 HP2 LM2 STEP2 NEW2 F2 CX2 ME2 VD2 DL2 EC2 EB2 ERR2 FXS2 XP2 RFS2 AL2
           Ts Tf Tsh Tb Tby Ta T0 CHN2.
    cbn [app] in HP2, Tb, Tby, Ta.
    assert (LED2 : LEDGER s2' (um + raise_bytes (mid_err M)) (uf + (errph_bytes (mid_err M) + ERRDEBUG_BYTES))).
    { eapply LEDGER_step; [exact LED| unfold raise_bytes, ERRDEBUG_BYTES; clear - EBR; lia| unfold ERRDEBUG_BYTES; clear - EBR; lia| unfold RAISE_COST in AL2; clear - AL2; lia]. }
    set (L2 := mid_errblocks M' ++ LE ++ (p, A, nA) :: LB) in *.
    assert (SUBLB2 : forall b, In b LB -> In b L2) by (intros b Hb; unfold L2; apply in_or_app; right; apply in_or_app; right; right; exact Hb).
    assert (SUBLE2 : forall b, In b (LE ++ LIB) -> In b L2).
    { intros b Hb. unfold L2. apply in_or_app; right. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; right; exact (SUBL _ Hb)]. }
    assert (SUBE2 : forall b, In b (mid_errblocks M') -> In b L2) by (intros b Hb; unfold L2; apply in_or_app; left; exact Hb).
    assert (INlb2 : In (p, A, nA) L2) by (unfold L2; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    pose proof LM2 as (IM2 & _ & _ & _ & _ & _ & _ & _ & GM2 & _).
    (* [comment removed for export] *)
    pose proof (Ts _ _ SL1 ltac:(clear; lia) ltac:(rewrite SLZ; clear - Q2; lia)) as SL2.
    pose proof (Ts _ _ GP1 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold KG; fold S1; clear - Q2; lia)) as GP2.
    pose proof (Ts _ _ SV1 ltac:(clear - Q2; lia) ltac:(unfold SAVES, arp_saves; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as SV2.
    pose proof (Tf _ FRM1 ltac:(unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as FRM2.
    pose proof (Tb (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] ltac:(right; exact SINB) ltac:(intros cq EQ; apply (ESNE cq _ EQ); right; left; reflexivity)
                   ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC1) as SC2.
    pose proof (Ta (es_id S, st, STORE_SIZE) st STORE_SIZE ltac:(right; exact SINB) ltac:(intros cq EQ; apply (ESNE cq _ EQ); right; left; reflexivity)
                   ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(clear - SB2; Z.div_mod_to_equations; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD1) as SAD2.
    pose proof (Tb (p, A, nA) A [CB (Z.to_nat nA) lb] ltac:(left; reflexivity) ltac:(intros cq EQ; apply (ESNE cq _ EQ); left; reflexivity)
                   ltac:(apply Z.le_refl) ltac:(cbn; clear - NAR; lia) LBc1) as LBc2.
    pose proof (Ta (p, A, nA) A nA ltac:(left; reflexivity) ltac:(intros cq EQ; apply (ESNE cq _ EQ); left; reflexivity)
                   ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(clear - BRm; Z.div_mod_to_equations; lia) ltac:(clear - NAR; lia) AD1) as AD2.
    pose proof (T0 ST01) as ST02.
    assert (MBO2 : MEMBIO H LB m2 mb R').
    { destruct MBO1 as (X1 & X2 & X3 & X4 & REST). pose proof REST as (J1 & J2 & J3 & J4 & _).
      split; [| split; [| split; [| split; [| exact REST]]]].
      - eapply (Tb (mb_id R', mb, BIO_SIZE)); [right; exact J1| intros cq EQ; cbn [blk_id fst snd]; rewrite T6; apply (ESNE cq (mb_id R, mb, BIO_SIZE) EQ); right; right; unfold blocks_MEMBIO; left; reflexivity| apply Z.le_refl
          | cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]; unfold BIO_SIZE; clear; lia| exact X1].
      - eapply (Tb (mb_bbid R', mb_bb R', BIOBUFMEM_SIZE)); [right; exact J2| intros cq EQ; cbn [blk_id fst snd]; rewrite T7; apply (ESNE cq (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE) EQ); right; right; unfold blocks_MEMBIO; right; left; reflexivity| apply Z.le_refl
          | cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]; unfold BIOBUFMEM_SIZE; clear; lia| exact X2].
      - eapply (Tb (mb_bmid R', mb_bm R', BUFMEM_SIZE)); [right; exact J3| intros cq EQ; cbn [blk_id fst snd]; rewrite T8; apply (ESNE cq (mb_bmid R, mb_bm R, BUFMEM_SIZE) EQ); right; right; unfold blocks_MEMBIO; right; right; left; reflexivity| apply Z.le_refl
          | cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]; unfold BUFMEM_SIZE; clear; lia| exact X3].
      - eapply (Tb (mb_rpid R', mb_rp R', BUFMEM_SIZE)); [right; exact J4| intros cq EQ; cbn [blk_id fst snd]; rewrite T9; apply (ESNE cq (mb_rpid R, mb_rp R, BUFMEM_SIZE) EQ); right; right; unfold blocks_MEMBIO; right; right; right; left; reflexivity| apply Z.le_refl
          | cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]; unfold BUFMEM_SIZE; clear; lia| exact X4]. }
    assert (MSH2 : MEMBIO_shad m2 mb R').
    { destruct MSH1 as (Y1 & Y2 & Y3 & Y4). pose proof MBO1 as MBq. destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
      pose proof (BLK0 _ (SUB0 _ J1)) as (_ & M1 & _). pose proof (BLK0 _ (SUB0 _ J2)) as (_ & M2 & _). pose proof (BLK0 _ (SUB0 _ J3)) as (_ & M3 & _). pose proof (BLK0 _ (SUB0 _ J4)) as (_ & M4 & _).
      cbn [blk_addr fst snd] in M1, M2, M3, M4. unfold MEMBIO_shad.
      split; [| split; [| split]].
      - eapply (Ta (mb_id R', mb, BIO_SIZE)); [right; exact J1| intros cq EQ; cbn [blk_id fst snd]; rewrite T6; apply (ESNE cq (mb_id R, mb, BIO_SIZE) EQ); right; right; unfold blocks_MEMBIO; left; reflexivity| apply Z.le_refl| apply Z.le_refl
          | clear - M1; Z.div_mod_to_equations; lia| unfold BIO_SIZE; clear; lia| exact Y1].
      - eapply (Ta (mb_bbid R', mb_bb R', BIOBUFMEM_SIZE)); [right; exact J2| intros cq EQ; cbn [blk_id fst snd]; rewrite T7; apply (ESNE cq (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE) EQ); right; right; unfold blocks_MEMBIO; right; left; reflexivity| apply Z.le_refl| apply Z.le_refl
          | clear - M2; Z.div_mod_to_equations; lia| unfold BIOBUFMEM_SIZE; clear; lia| exact Y2].
      - eapply (Ta (mb_bmid R', mb_bm R', BUFMEM_SIZE)); [right; exact J3| intros cq EQ; cbn [blk_id fst snd]; rewrite T8; apply (ESNE cq (mb_bmid R, mb_bm R, BUFMEM_SIZE) EQ); right; right; unfold blocks_MEMBIO; right; right; left; reflexivity| apply Z.le_refl| apply Z.le_refl
          | clear - M3; Z.div_mod_to_equations; lia| unfold BUFMEM_SIZE; clear; lia| exact Y3].
      - eapply (Ta (mb_rpid R', mb_rp R', BUFMEM_SIZE)); [right; exact J4| intros cq EQ; cbn [blk_id fst snd]; rewrite T9; apply (ESNE cq (mb_rpid R, mb_rp R, BUFMEM_SIZE) EQ); right; right; unfold blocks_MEMBIO; right; right; right; left; reflexivity| apply Z.le_refl| apply Z.le_refl
          | clear - M4; Z.div_mod_to_equations; lia| unfold BUFMEM_SIZE; clear; lia| exact Y4]. }
    assert (DS2 : bytes_at asegs m2 (mb_buf R) ds).
    { destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      - assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil. clear - BUFP BUFH ACB L0Z. lia.
      - destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN PNL]].
        eapply (Tby (pD, mb_buf R, mb_len R)); [right; exact PIN| intros cq EQ; destruct (es_facts _ _ _ _ _ LM1 CTX EQ) as [I5 _]; cbn [blk_id fst snd]; exact (PNL _ I5)
          | cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DS1]. }
    assert (XA2 : xpres H LB (bv_unsigned sp) ((XSF ff fp ++ XS) ++ XF) m m2).
    { eapply xpres_trans.
      + eapply xpres_weaken; [exact XA1| apply Z.le_refl| intros b Hb; exact Hb|].
        intros q Hq. apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; apply rin_ivs_app; left; exact Hq|].
        apply rin_ivs_app; right. unfold XF. apply rin_ivs_app; right. apply rin_ivs_app; left. exact Hq.
      + eapply xpres_weaken; [exact XP2| apply Z.le_refl| intros b Hb; exact Hb|].
        intros q Hq. apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; apply rin_ivs_app; right; exact Hq|].
        apply rin_ivs_app; right. unfold XF. apply rin_ivs_app; right. apply rin_ivs_app; right.
        apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; exact Hq|]. apply rin_ivs_app; right. apply rin_ivs_app; right. exact Hq. }
    clear Ts Tf Tsh Tb Tby Ta T0 SL1 GP1 SV1 FRM1 SC1 SAD1 LBc1 AD1 ST01 MBO1 MSH1 DS1 XA1 XP2 VIS1 HP1 HPp KREL1 MI1 AC1 STK1 RFS1 ERR1 AUX1 LM1 CHN1 IM1 GM1.
    (* [comment removed for export] *)
    pose proof (proj1 (rw_cells_app asegs m2 _ pre _) SL2) as [_ SLbc]. rewrite PREZ in SLbc. change (Z.of_nat 144) with 144 in SLbc.
    pose proof (proj1 (rw_cells_app asegs m2 _ _ post) SLbc) as [SLb _]. clear SLbc.
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply Z3 with (m := m2) (q := S1) (ff := ff);
      [clear - Q2 CEIL LO STK0 LO0; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| exact SLb| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 VIS3. cbn beta in VIS3. clear SLb.
    (* [comment removed for export] *)
    destruct (ACONST_shbase m2 AC2) as [GSB2 SHB2].
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| eapply abio_free_all_null with (lo := lo);
      [exact GSB2| exact SHB2| rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact ST2| exact CEIL
      | rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKA Q2; unfold AFS_STACK in STKA; lia| exact MI2
      | rewrite unsigned_lit by (unfold AFM_ERRL_R1; clear; lia); reflexivity]|].
    intros msF4 mo4 KREL4 MP4 (m3 & VIS4 & MU3 & WM3 & MI3 & ST3).
    rewrite (unsigned_lit S1) in MU3, ST3 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    pose proof (stk_carry m2 m3 s2' L2 (S1 + -48) S1 ltac:(clear - LO STKA Q2; unfold AFS_STACK in STKA; lia) ltac:(clear - Q2; lia) MU3 WM3 HP2 SUBLB2)
      as (HP3 & TAUX & TRFS & TLM & Ts & Tf & Tsh & Tb & Tby & Ta & Tacc & Terr & T0 & Tac & Tch & Txa & Tmb & Tms).
    pose proof (TAUX AUX2) as AUX3. pose proof (TRFS _ RFS2) as RFS3. pose proof (TLM _ M' x LM2 CX2 SUBLE2 SUBE2) as LM3.
    pose proof (Ts _ _ SL2 ltac:(clear; lia)) as SL3. pose proof (Ts _ _ GP2 ltac:(clear; lia)) as GP3. pose proof (Ts _ _ SV2 ltac:(clear - Q2; lia)) as SV3.
    pose proof (Tf ff _ ltac:(clear - FF6 FB2; lia) FRM2 ltac:(unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as FRM3.
    pose proof (Tb (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] (SUBLB2 _ SINB) ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC2) as SC3.
    pose proof (Ta (es_id S, st, STORE_SIZE) st STORE_SIZE (SUBLB2 _ SINB) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD2) as SAD3.
    pose proof (Tb (p, A, nA) A [CB (Z.to_nat nA) lb] INlb2 ltac:(apply Z.le_refl) ltac:(cbn; clear - NAR; lia) LBc2) as LBc3.
    pose proof (Ta (p, A, nA) A nA INlb2 ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(clear - NAR; lia) AD2) as AD3.
    pose proof (Terr _ ERR2) as ERR3. pose proof (T0 ST02) as ST03. pose proof (Tac AC2) as AC3. pose proof (Tch _ _ (S1 + 16) CHN2 CHB1 ltac:(clear; lia)) as CHN3. pose proof (Txa _ _ XA2) as XA3.
    pose proof (Tmb R' MST1 MBO2) as MBO3. pose proof (Tms R' MST1 MBO2 MSH2) as MSH3.
    assert (DS3 : bytes_at asegs m3 (mb_buf R) ds).
    { destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      - assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil. clear - BUFP BUFH ACB L0Z. lia.
      - destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN _]].
        eapply (Tby (pD, mb_buf R, mb_len R)); [exact (SUBLB2 _ PIN)| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DS2]. }
    clear TAUX TRFS TLM Ts Tf Tsh Tb Tby Ta Tacc Terr T0 Tac Tch Txa Tmb Tms AUX2 RFS2 LM2 SL2 GP2 SV2 FRM2 SC2 SAD2 LBc2 AD2 ERR2 ST02 AC2 CHN2 XA2 MBO2 MSH2 DS2 MU3 WM3 MI2 ST2 HP2 GSB2 SHB2 IM2 GM2.
    pose proof LM3 as (IM3 & _ & _ & _ & _ & _ & _ & _ & GM3 & _).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply aerrl2; exact MI3|]. intros msF5 mo5 KREL5 MP5 VIS5. cbn beta in VIS5.
    pose proof (acfree_null_spec H HH) as CF0. unfold cfree_null_stmt in CF0.
    eapply (ah_seq H HH).
    { eapply CF0 with (lo := lo) (B := B) (LB := L2) (s := s2') (errv := errv2) (CH := CH1); clear CF0.
      all: try first [exact VIS5| exact HP3| exact KREL5| exact AUX3| exact MI3| exact CEIL| exact AC3| exact CHN3| exact IM3| exact GM3| exact ERR3].
      all: lazymatch goal with
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - SPB Q2; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact ST3
           | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKF Q2; lia
           | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact (CHB1 _ _ Hin)
           | |- as_Cf H 0 <= as_AL H _ => pose proof (LEDGER_pay s2' _ _ 0 0 LED2 ltac:(clear; lia) ltac:(clear; lia) ltac:(unfold raise_bytes, ERRDEBUG_BYTES; clear - UMB EBR; lia) ltac:(unfold ERRDEBUG_BYTES; clear - UFB EBR NAR; lia)) as PAYq;
                                            clear - PAYq CMz; lia
           | |- @eq _ _ _ => reflexivity
           | |- ?G => idtac "F599_CF0_LEFT" G
           end. }
    clear CF0. intros [msF6 mo6] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & s4' & VIS6 & KREL6 & MP6 & MI4 & AC4 & ST4 & ERR4 & AUX4 & XP4 & HP4 & IM4 & GM4 & AL4).
    rewrite (unsigned_lit S1) in ST4, XP4 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    assert (LED4 : LEDGER s4' (um + raise_bytes (mid_err M)) (uf + (errph_bytes (mid_err M) + ERRDEBUG_BYTES))).
    { pose proof (LEDGER_step s2' s4' _ _ 0 0 LED2 ltac:(clear; lia) ltac:(clear; lia)) as K. rewrite !Z.add_0_r in K. apply K. clear - AL4 CMz. lia. }
    pose proof (xnil_carry ff fp m3 m4 s2' L2 L2 FRESH XP4 HP3 ltac:(intros b Hb; exact Hb) SUBLB2)
      as (TRFS & TLM & Ts & Tf & Tsh & Tb & Tby & Ta & Tacc & T0 & Tch & Txa & Tmb & Tms).
    pose proof (TRFS RFS3) as RFS4. pose proof (TLM _ M' x LM3 CX2 SUBLE2 SUBE2) as LM4.
    pose proof (Ts _ _ SL3 ltac:(clear; lia)) as SL4. pose proof (Ts _ _ GP3 ltac:(clear; lia)) as GP4. pose proof (Ts _ _ SV3 ltac:(clear - Q2; lia)) as SV4.
    pose proof (Tf _ FRM3 ltac:(unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as FRM4.
    pose proof (Tb (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] (SUBLB2 _ SINB) ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC3) as SC4.
    pose proof (Ta (es_id S, st, STORE_SIZE) st STORE_SIZE (SUBLB2 _ SINB) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(clear - SB2; Z.div_mod_to_equations; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD3) as SAD4.
    pose proof (Tb (p, A, nA) A [CB (Z.to_nat nA) lb] INlb2 ltac:(apply Z.le_refl) ltac:(cbn; clear - NAR; lia) LBc3) as LBc4.
    pose proof (Ta (p, A, nA) A nA INlb2 ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(clear - BRm; Z.div_mod_to_equations; lia) ltac:(clear - NAR; lia) AD3) as AD4.
    pose proof (T0 ST03) as ST04. pose proof (Tch _ _ CHN3 CHB1) as CHN4. pose proof (Txa _ _ XA3) as XA4.
    pose proof (Tmb R' MST1 MBO3) as MBO4. pose proof (Tms R' MST1 MBO3 MSH3) as MSH4.
    assert (DS4 : bytes_at asegs m4 (mb_buf R) ds).
    { destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      - assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil. clear - BUFP BUFH ACB L0Z. lia.
      - destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN _]].
        eapply (Tby (pD, mb_buf R, mb_len R)); [exact (SUBLB2 _ PIN)| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DS3]. }
    clear TRFS TLM Ts Tf Tsh Tb Tby Ta Tacc T0 Tch Txa Tmb Tms RFS3 LM3 SL3 GP3 SV3 FRM3 SC3 SAD3 LBc3 AD3 ST03 CHN3 XA3 MBO3 MSH3 DS3 XP4 HP3 AUX3 ERR3 AC3 MI3 ST3 IM3 GM3.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply aerrl3; exact MI4|]. intros msF7 mo7 KREL7 MP7 VIS7. cbn beta in VIS7.
    assert (HP4h : as_RHEAP H s4' ((p, A, nA) :: mid_errblocks M' ++ LE ++ LB) m4).
    { eapply PERM; [exact HP4|]. unfold L2. apply Permutation_sym.
      replace (mid_errblocks M' ++ LE ++ (p, A, nA) :: LB) with ((mid_errblocks M' ++ LE) ++ (p, A, nA) :: LB) by (rewrite <- app_assoc; reflexivity).
      replace (mid_errblocks M' ++ LE ++ LB) with ((mid_errblocks M' ++ LE) ++ LB) by (rewrite <- app_assoc; reflexivity). apply Permutation_middle. }
    destruct (lad_head_facts H HX (mid_errblocks M' ++ LE ++ LB) _ _ _ _ _ HP4h) as (_ & NIP4 & _ & _ & _).
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := (p, A, nA) :: mid_errblocks M' ++ LE ++ LB) (s := s4') (p := p) (A := A) (n := nA) (errv := errv2) (CH := CH1) (bs := lb); clear CF.
      all: try first [exact VIS7| exact HP4h| exact KREL7| exact AUX4| exact MI4| exact CEIL| exact AC4| exact CHN4| exact LBc4| exact AD4| exact IM4| exact GM4| exact ERR4].
      all: lazymatch goal with
           | |- In _ _ => left; reflexivity
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - SPB Q2; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact ST4
           | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKF Q2; lia
           | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact (CHB1 _ _ Hin)
           | |- pf_ok _ _ _ _ => unfold AERRL_R3; rewrite unsigned_lit by (clear; lia); apply pf_site;
                                 intros e He; unfold PF_readcfg, PF_read_priv; do 19 (apply in_or_app; right); exact He
           | |- as_Cf H _ <= as_AL H _ => pose proof (LEDGER_pay s4' _ _ 0 nA LED4 ltac:(clear; lia) ltac:(clear - NAR; lia) ltac:(unfold raise_bytes, ERRDEBUG_BYTES; clear - UMB EBR; lia) ltac:(unfold ERRDEBUG_BYTES; clear - UFB EBR NAR; lia)) as PAYq;
                                            clear - PAYq CMz; lia
           | |- @eq _ _ _ => reflexivity
           | |- ?G => idtac "F599_CF_LEFT" G
           end. }
    clear CF. intros [msF8 mo8] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m5 & s5' & VIS8 & KREL8 & MP8 & MI5 & AC5 & ST5 & ERR5 & AUX5 & XP5 & HP5 & IM5 & GM5 & AL5).
    rewrite (proj1 (ah_lb_remove H HH)) in XP5, HP5 by exact NIP4.
    rewrite (unsigned_lit S1) in ST5, XP5 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    assert (LED5 : LEDGER s5' (um + raise_bytes (mid_err M)) (uf + (errph_bytes (mid_err M) + ERRDEBUG_BYTES) + nA)).
    { pose proof (LEDGER_step s4' s5' _ _ 0 nA LED4 ltac:(clear; lia) ltac:(clear - NAR; lia)) as K. rewrite Z.add_0_r in K. apply K. clear - AL5 CMz. lia. }
    set (L5 := mid_errblocks M' ++ LE ++ LB) in *.
    assert (SUBLB5 : forall b, In b LB -> In b L5) by (intros b Hb; unfold L5; apply in_or_app; right; apply in_or_app; right; exact Hb).
    assert (SUBLE5 : forall b, In b (LE ++ LIB) -> In b L5).
    { intros b Hb. unfold L5. apply in_or_app; right. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; exact (SUBL _ Hb)]. }
    assert (SUBE5 : forall b, In b (mid_errblocks M') -> In b L5) by (intros b Hb; unfold L5; apply in_or_app; left; exact Hb).
    pose proof (xnil_carry ff fp m4 m5 s4' ((p, A, nA) :: L5) L5 FRESH XP5 HP4h ltac:(intros b Hb; right; exact Hb) SUBLB5)
      as (TRFS & TLM & Ts & Tf & Tsh & Tb & Tby & Ta & Tacc & T0 & Tch & Txa & Tmb & Tms).
    pose proof (TRFS RFS4) as RFS5. pose proof (TLM _ M' x LM4 CX2 SUBLE5 SUBE5) as LM5.
    pose proof (Ts _ _ SL4 ltac:(clear; lia)) as SL5. pose proof (Ts _ _ GP4 ltac:(clear; lia)) as GP5. pose proof (Ts _ _ SV4 ltac:(clear - Q2; lia)) as SV5.
    pose proof (Tf _ FRM4 ltac:(unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as FRM5.
    pose proof (Tb (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] (SUBLB5 _ SINB) ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC4) as SC5.
    pose proof (Ta (es_id S, st, STORE_SIZE) st STORE_SIZE (SUBLB5 _ SINB) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(clear - SB2; Z.div_mod_to_equations; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD4) as SAD5.
    pose proof (T0 ST04) as ST05. pose proof (Tch _ _ CHN4 CHB1) as CHN5. pose proof (Txa _ _ XA4) as XA5.
    pose proof (Tmb R' MST1 MBO4) as MBO5. pose proof (Tms R' MST1 MBO4 MSH4) as MSH5.
    assert (DS5 : bytes_at asegs m5 (mb_buf R) ds).
    { destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      - assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil. clear - BUFP BUFH ACB L0Z. lia.
      - destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN _]].
        eapply (Tby (pD, mb_buf R, mb_len R)); [exact (SUBLB5 _ PIN)| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DS4]. }
    clear TRFS TLM Ts Tf Tsh Tb Tby Ta Tacc T0 Tch Txa Tmb Tms.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL8| exact VIS8| eapply aerrl4; exact MI5|]. intros msF9 mo9 KREL9 MP9 VIS9. cbn beta in VIS9. rewrite F10 in VIS9.
    eapply (rp_exit m5 msF9 mo9 s5' 0 M' R' LE ff fp rb fj1 fj2 jg (pre ++ arp_sg2 w144 (wz ff) (wz ff) w168 w176 (wz A) w192 w200 w208 w216 w224 w232 ++ post) (XSF ff fp ++ XS)).
    all: try first [exact VIS9| exact KREL9| exact MI5| exact AC5| exact ST5| exact ST05| exact SLZ| exact SL5| exact GP5| exact SV5| exact FRM5| exact RFS5| exact ERR5| exact AUX5| exact HP5| exact LM5
                    | exact STEP2| exact NEW2| exact EC2| exact EB2| exact MBO5| exact MSH5| exact MST1| exact DS5| exact SC5| exact CHN5| exact XA5].
    - left; reflexivity.
    - eapply (ah_mpres_trans H HH); [| exact MP9]. eapply (ah_mpres_trans H HH); [| exact MP8]. eapply (ah_mpres_trans H HH); [| exact MP7]. eapply (ah_mpres_trans H HH); [| exact MP6].
      eapply (ah_mpres_trans H HH); [| exact MP5]. eapply (ah_mpres_trans H HH); [| exact MP4]. eapply (ah_mpres_trans H HH); [| exact MP3]. eapply (ah_mpres_trans H HH); [exact MP1| exact MP2].
    - rewrite CX2, CTX. reflexivity.
    - (* [comment removed for export] *) rewrite SEQ. apply (proj2 (STORE_shad_empty _ _ _)). split; [exact SHhi| exact SAD5].
    - apply Forall_app. split; [unfold XSF; apply (fs_scratch_of_fresh H); exact FRESH| exact FXS2].
    - intros a Ha. apply rin_ivs_app. left. exact Ha.
    - eapply LEDGER_post; [exact LED5| unfold raise_bytes, ERRDEBUG_BYTES; clear - UMB EBR; lia| unfold ERRDEBUG_BYTES; clear - UFB EBR NAR; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_fail599 :
    forall m1 msF1 mo1 (s1' : as_St H) (p : bptr) (A nA : Z) (lb : list byte) (R' : membio) (ff fp rb : Z) (fj1 fj2 jg : list byte) (pre post : list cell)
           (w144 w168 w176 w192 w200 w208 w216 w224 w232 : word) (um uf : Z)
           (u0 u1 u2 a0v a1v a2v b3 b4 b5 b6 b7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v u3 u4 u5 u6 errv1 : word),
      as_VIS H s1' msF1 = MS (mkR (Z_to_bv 64 ALD_RN) (Z_to_bv 64 S1) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1) a0v a1v a2v b3 b4 b5 b6 b7
                                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v u3 u4 u5 u6)
                          F (Z_to_bv 64 P_ERR_new) fc None m1 (seg_rom asegs) ->
      as_RHEAP H s1' ((p, A, nA) :: L0) m1 -> as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 -> mem_inv asegs m1 -> ACONST m1 ->
      0 <= nA <= 512 * 33 -> rw_cells asegs m1 A [CB (Z.to_nat nA) lb] -> addressable m1 A nA ->
      MEMBIO H LB m1 mb R' -> MEMBIO_shad m1 mb R' -> mb_static R R' -> bytes_at asegs m1 (mb_buf R) ds ->
      stk asegs m1 lo S1 -> stack0 m1 lo (bv_unsigned sp) ->
      cells_size pre = 144%nat -> cells_size post = 104%nat ->
      rw_cells asegs m1 S1 (pre ++ arp_sg2 w144 (wz ff) (wz ff) w168 w176 (wz A) w192 w200 w208 w216 w224 w232 ++ post) ->
      rw_cells asegs m1 (S1 + 344) [CB (Z.to_nat KG) jg] -> rw_cells asegs m1 (bv_unsigned sp + -104) SAVES ->
      rw_cells asegs m1 ff (arp_fframe S1 fj1 rb fj2 fp) -> as_RFS H (LF1 ff fp) m1 ->
      rw_cells asegs m1 (errno_addr (Z_to_bv 64 ATP)) [C4 errv1] -> as_rauxv_ok H m1 B ->
      LIBMID LIB m1 M -> rw_cells asegs m1 st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> STORE_shad m1 st S ->
      as_chain H m1 (bv_unsigned sp) CH1 ->
      xpres H LB (bv_unsigned sp) (XSF ff fp ++ MEMBIO_foot mb R) m m1 ->
      LEDGER s1' um uf -> um + 2^16 + 64 <= DECODE_CUM_BYTES -> uf + nA + 2^16 + 64 <= DECODE_CUM_BYTES ->
      as_SR H POST (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros. eapply (rp_fail_lbuf 599 AR_INTERNAL_ERROR ALD_RN A599_R2 (A599_R2 + 24) (fun ff _ => Z_to_bv 64 ff)); try eassumption; try reflexivity.
    all: lazymatch goal with
         | |- arp_glue _ _ P_ERR_set_debug _ _ _ => exact arp_g599a
         | |- arp_glue _ _ P_ERR_set_error _ _ _ => exact arp_g599b
         | |- zero3_at _ _ => exact zero3_599
         | |- pf_ok _ (PF_errnew _) _ _ => apply pf_site; intros e He; unfold PF_readcfg, PF_read_priv, pf_raise; do 5 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; left; exact He
         | |- pf_ok _ PF_errdebug _ _ => apply pf_site; intros e He; unfold PF_readcfg, PF_read_priv, pf_raise; do 5 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact He
         | |- pf_ok _ PF_errseterr _ _ => unfold pf_ok, PF_errseterr; apply Forall_nil
         | |- _ => unfold AR_INTERNAL_ERROR, ALD_RN, A599_R2; clear; lia
         end.
  Qed.

  (* [comment removed for export] *)
  Definition rp_okK : Prop :=
    forall (k n : Z) (m' : mem) (msF' : machine_state) (mo' : Model) (s' : as_St H) (p : bptr) (A : Z) (R' : membio) (junk : list byte)
           (ff fp : Z) (fj1 fj2 jg j0 j1 j3 j4 : list byte) (e5 : list byte) (um uf : Z)
           (rax u0 u1 u2 b2 b3 b4 b5 b6 b7 s10v u3 u4 u5 u6 errv' : word),
      0 <= k <= 31 -> n = mb_len R - 512 * k -> 1 <= n <= 512 -> mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN ->
      as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1) (Z_to_bv 64 (-8)) (Z_to_bv 64 (OSSL_ECH_MAX_ECHCONFIG_LEN - 1)) b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 512) (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) (Z_to_bv 64 A) (Z_to_bv 64 (- (512 * k))) (Z_to_bv 64 (mb_len R)) (Z_to_bv 64 n)
                                  (Z_to_bv 64 (32 - k)) (Z_to_bv 64 (ff + 2256)) s10v (Z_to_bv 64 (512 * k)) u3 u4 u5 u6)
                          F (Z_to_bv 64 AFM_PC0) fc None m' (seg_rom asegs) ->
      as_RHEAP H s' ((p, A, 512 * (k + 1)) :: L0) m' -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' -> mem_inv asegs m' -> ACONST m' ->
      bytes_at asegs m' A ds -> rw_cells asegs m' A [CB (Z.to_nat (mb_len R)) ds; CB (Z.to_nat (512 * (k + 1) - mb_len R)) junk] -> addressable m' A (512 * (k + 1)) ->
      MEMBIO H LB m' mb R' -> MEMBIO_shad m' mb R' -> mb_static R R' -> mb_pos R' = mb_len R -> bytes_at asegs m' (mb_buf R) ds -> PAYLOAD_shad m' R ->
      stk asegs m' lo S1 -> stack0 m' lo (bv_unsigned sp) ->
      rw_cells asegs m' S1 (arp_slotsL j0 j1 j3 j4 st ff (Z.shiftr ff 3 + ASHB) A) ->
      rw_cells asegs m' (S1 + 344) [CB (Z.to_nat KG) jg] -> rw_cells asegs m' (bv_unsigned sp + -104) SAVES ->
      rw_cells asegs m' ff (arp_fframe S1 fj1 n fj2 fp) ->
      rw_cells asegs m' (Z.shiftr ff 3 + ASHB) (arp_fshadow (poison_bytes 4 0xf1) (b8 0xf8) (poison_bytes 3 0xf2) (b8 0xf8) (b8 0xf2) (poison_bytes 256 0xf8) (poison_bytes 16 0xf2) (b8 0xf8) e5) ->
      as_RFS H (LF1 ff fp) m' ->
      rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv'] -> as_rauxv_ok H m' B ->
      LIBMID LIB m' M -> rw_cells asegs m' st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> STORE_shad m' st S ->
      as_chain H m' (bv_unsigned sp) CH1 ->
      xpres H LB (bv_unsigned sp) (XSF ff fp ++ MEMBIO_foot mb R) m m' ->
      LEDGER s' um uf -> um <= 512 + lad_cm 32 -> uf <= lad_cf 32 ->
      as_SR H POST (mkCfg msF' mo').
  Lemma slotsL_set_A : forall (mA mB : mem) (q : Z) (j0 j1 j3 j4 : list byte) (stq ffq shq Aq Aq' : Z),
    rw_cells asegs mA q (arp_slotsL j0 j1 j3 j4 stq ffq shq Aq) ->
    (forall A cs, rw_cells asegs mA A cs -> q <= A -> (A + Z.of_nat (cells_size cs) <= q + 184 \/ q + 192 <= A) -> rw_cells asegs mB A cs) ->
    rw_cells asegs mB (q + 184) [C8 (wz Aq')] ->
    rw_cells asegs mB q (arp_slotsL j0 j1 j3 j4 stq ffq shq Aq').
  Proof.
    intros mA mB q j0 j1 j3 j4 stq ffq shq Aq Aq' SL T SA. unfold arp_slotsL in *.
    set (P1 := [CB 16 j0; CB 80 j1; C8 (wz 0); C8 (wz (ffq + 80)); C8 (wz (ffq + 64)); C8 (wz 0); C8 (wz stq); C8 (wz (ffq + 32));
                C8 (wz (shq + 10)); C8 (wz ffq); C8 (wz ffq); C8 (wz ARP_FILE); C8 (wz ASHB)]).
    set (P3 := [CB 24 j3; C8 (wz ffq); CB 120 j4]).
    change (rw_cells asegs mA q (P1 ++ [C8 (wz Aq)] ++ P3)) in SL. change (rw_cells asegs mB q (P1 ++ [C8 (wz Aq')] ++ P3)).
    assert (Z1 : Z.of_nat (cells_size P1) = 184) by reflexivity.
    assert (Z3 : Z.of_nat (cells_size P3) = 152) by reflexivity.
    apply (proj1 (rw_cells_app asegs mA _ _ _)) in SL. destruct SL as [SA1 SL]. apply (proj1 (rw_cells_app asegs mA _ _ _)) in SL. destruct SL as [_ SA3].
    rewrite Z1 in SA3. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SA3.
    apply (proj2 (rw_cells_app asegs mB _ _ _)). split; [apply (T _ _ SA1); [lia| left; rewrite Z1; lia]|].
    rewrite Z1. apply (proj2 (rw_cells_app asegs mB _ _ _)). split; [exact SA|].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. apply (T _ _ SA3); lia.
  Qed.

  Lemma slotsL_file_A : forall mq q (j0 j1 j3 j4 : list byte) (stq ffq shq Aq : Z),
    rw_cells asegs mq q (arp_slotsL j0 j1 j3 j4 stq ffq shq Aq) ->
    rw_cells asegs mq (q + 168) [C8 (wz ARP_FILE)] /\ rw_cells asegs mq (q + 184) [C8 (wz Aq)].
  Proof.
    intros mq q j0 j1 j3 j4 stq ffq shq Aq SL. unfold arp_slotsL in SL.
    change (rw_cells asegs mq q ([CB 16 j0; CB 80 j1; C8 (wz 0); C8 (wz (ffq + 80)); C8 (wz (ffq + 64)); C8 (wz 0); C8 (wz stq); C8 (wz (ffq + 32));
                                 C8 (wz (shq + 10)); C8 (wz ffq); C8 (wz ffq)] ++ [C8 (wz ARP_FILE)] ++ [C8 (wz ASHB)] ++ [C8 (wz Aq)] ++
                                [CB 24 j3; C8 (wz ffq); CB 120 j4])) in SL.
    apply (proj1 (rw_cells_app asegs mq _ _ _)) in SL. destruct SL as [_ SL].
    apply (proj1 (rw_cells_app asegs mq _ _ _)) in SL. destruct SL as [F1 SL].
    apply (proj1 (rw_cells_app asegs mq _ _ _)) in SL. destruct SL as [_ SL].
    apply (proj1 (rw_cells_app asegs mq _ _ _)) in SL. destruct SL as [F3 _].
    split.
    - match type of F1 with rw_cells _ _ ?a _ => replace (q + 168) with a by (cbn [cells_size csize Nat.add]; lia) end. exact F1.
    - match type of F3 with rw_cells _ _ ?a _ => replace (q + 184) with a by (cbn [cells_size csize Nat.add]; lia) end. exact F3.
  Qed.


  (* [comment removed for export] *)
  Lemma rp_b2b : rp_okK -> as_SR H POST (mkCfg msF mo).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM.
    intros KOK.
    destruct rc_facts as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). fold S1 in Q1, Q2.
    pose proof rc_stack as (STKR & STKL & STKZ & STKF & STKA).
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AIMG_TOP in AF1. unfold AFS_SIZE in AF2. pose proof (aapp_not_shadowland _ _ AF4) as NSF.
    assert (SUBLB0 : forall b, In b LIB -> In b L0) by (intros b Hb; exact (SUB0 _ (SUBL _ Hb))).
    assert (SUBE0 : forall b, In b (mid_errblocks M) -> In b L0) by (intros b Hb; unfold L0; apply in_or_app; left; exact Hb).
    assert (CHB1 : forall fp' ra', In (fp', ra') CH1 -> S1 + 16 <= fp').
    { intros fp' ra' [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
    pose proof (errph_bytes_range (mid_err M)) as [EBR ECR].
    pose proof (ah_costs H HH) as (CM0 & CMmono & CF0 & CFmono & CMadd & CFadd). pose proof (CM0 0 ltac:(clear; lia)) as CMz. pose proof (CF0 0 ltac:(clear; lia)) as CFz.
    pose proof SO as (SC0 & SINB & _). rewrite SEQ in SC0. cbn [es_entries store_empty] in SC0.
    pose proof SSH as SSHq. rewrite SEQ in SSHq. apply (proj1 (STORE_shad_empty _ _ _)) in SSHq. destruct SSHq as [SHhi SAD0].
    pose proof SBR as (SB1 & SB2 & _ & SBa & SBb & SBf & SBc).
    pose proof MBO as MBq. destruct MBq as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & XB1 & _ & _ & _ & _ & LENR & BUFP & BUFH & _).
    pose proof (BLK0 _ (SUB0 _ I1)) as (E11 & _ & _ & E1a & E1b & _). cbn [blk_addr blk_size fst snd] in E11, E1a, E1b. unfold BIO_SIZE in E1b.
    pose proof LM as (IM0 & _ & _ & _ & _ & _ & _ & _ & GM0 & _ & _ & MM0 & _).
    pose proof VIS0 as VIS00. rewrite A0, A1, TP in VIS00. pose proof ERR as ERR0. rewrite TP in ERR0.
    (* [comment removed for export] *)
    destruct (ACONST_uar m AC) as [GU0 UAR0]. destruct (ACONST_shbase m AC) as [GSB0 SHB0].
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS00| eapply arp_seg1a with (lo := lo);
      [clear - SB1 SBb ACB; unfold STORE_SIZE in SBb; lia| clear - E11 E1b ACB; lia| exact SPA| exact GU0| exact UAR0| exact GSB0| exact SHB0| exact ST| exact CEIL| clear - LO STK0; lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & jj & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1). fold S1 in VIS1.
    pose proof (stk_carry m m1 s L0 (bv_unsigned sp + -448) (bv_unsigned sp) ltac:(clear - LO STK0; lia) ltac:(clear; lia) MU1 WM1 HP SUB0)
      as (HP1 & TAUX & TRFS & TLM & Ts & Tf & Tsh & Tb & Tby & Ta & Tacc & Terr & T0 & Tac & Tch & Txa & Tmb & Tms).
    pose proof (TAUX AUX) as AUX1. pose proof (TRFS _ RFS) as RFS1. pose proof (TLM _ M x LM CTX SUBLB0 SUBE0) as LM1.
    pose proof (Tb (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] SIN ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC0) as SC1.
    pose proof (Ta (es_id S, st, STORE_SIZE) st STORE_SIZE SIN ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD0) as SAD1.
    pose proof (Terr _ ERR0) as ERR1. pose proof (T0 ST0) as ST01. pose proof (Tac AC) as AC1.
    pose proof (Tch _ _ (bv_unsigned sp + 16) CHN CHB ltac:(clear; lia)) as CHNc1.
    assert (XA0 : xpres H LB (bv_unsigned sp) [] m m) by (apply xpres_refl). pose proof (Txa [] m XA0) as XA1.
    pose proof (Tmb R (mb_static_refl R) MBO) as MBO1. pose proof (Tms R (mb_static_refl R) MBO MSH) as MSH1.
    assert (DS1 : bytes_at asegs m1 (mb_buf R) ds).
    { destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      - assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil. clear - BUFP BUFH ACB L0Z. lia.
      - destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN _]].
        eapply (Tby (pD, mb_buf R, mb_len R)); [exact (SUB0 _ PIN)| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DS]. }
    assert (PAYa1 : 1 <= mb_len R -> accessible m1 (mb_buf R) (mb_len R)).
    { intros L1. destruct (PAYL L1) as [pD [PIN _]]. destruct PAY as (Y1 & _ & _).
      eapply (Tacc (pD, mb_buf R, mb_len R)); [exact (SUB0 _ PIN)| apply Z.le_refl| apply Z.le_refl| clear - L1; lia| exact Y1]. }
    clear TAUX TRFS TLM Ts Tf Tsh Tb Tby Ta Tacc Terr T0 Tac Tch Txa Tmb Tms.
    (* [comment removed for export] *)
    pose proof (proj1 (rw_cells_app asegs m1 _ [C8 (Z_to_bv 64 0); CB 336 jj] SAVES) FR1) as [FRa SV1]. cbn [cells_size csize Nat.add] in SV1.
    replace (bv_unsigned sp + -448 + Z.of_nat 344) with (bv_unsigned sp + -104) in SV1 by (clear; lia).
    assert (CHN1 : as_chain H m1 (bv_unsigned sp) CH1).
    { pose proof SV1 as SVq. unfold SAVES, arp_saves in SVq.
      change (rw_cells asegs m1 (bv_unsigned sp + -104) ([C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra])) in SVq.
      apply (proj1 (rw_cells_app asegs m1 _ _ _)) in SVq. destruct SVq as [_ LK]. cbn [cells_size csize Nat.add] in LK.
      replace (bv_unsigned sp + -104 + Z.of_nat 88) with (bv_unsigned sp - 16) in LK by (clear; lia).
      unfold CH1. rewrite <- (Z_to_bv_bv_unsigned s0) in LK. rewrite <- (Z_to_bv_bv_unsigned ra) in LK.
      eapply (ah_chain_cons H HH); [exact CHNc1| apply aword_range| apply aword_range| exact SPA| clear - CEIL LO STK0; lia| clear - SPR; lia| exact LK]. }
    clear CHNc1.
    (* [comment removed for export] *)
    pose proof (rw_cells_flatten asegs m1 _ _ FRa) as FRb. cbn [cells_size csize cells_bytes cbytes Nat.add app] in FRb. rewrite app_nil_r in FRb.
    assert (KGR : 0 <= KG <= 16 /\ S1 + KG = bv_unsigned sp - 448) by (unfold KG; fold S1; clear - Q2; lia).
    assert (CV : lo <= bv_unsigned sp + -448 - Z.of_nat (Z.to_nat KG)) by (clear - KGR Q2 LO STK0; lia).
    destruct (stk_carve asegs m1 lo (bv_unsigned sp + -448) (Z.to_nat KG) ST1 CV) as [STK1 [jg0 GK]]. clear CV.
    replace (bv_unsigned sp + -448 - Z.of_nat (Z.to_nat KG)) with S1 in STK1, GK by (clear - KGR; lia).
    replace (bv_unsigned sp + -448) with (S1 + Z.of_nat (Z.to_nat KG)) in FRb by (clear - KGR; lia).
    pose proof (rw_cells_CB_join asegs m1 S1 _ _ _ _ GK FRb) as ALL1.
    destruct (rw_cells_CB_split asegs m1 S1 _ 344 _ ALL1 ltac:(clear; lia)) as [SL1 GP1].
    replace (Z.to_nat KG + 344 - 344)%nat with (Z.to_nat KG) in GP1 by (clear; lia). change (Z.of_nat 344) with 344 in GP1.
    set (jg := skipn 344 (jg0 ++ le8 (Z_to_bv 64 0) ++ jj)) in GP1. clearbody jg.
    set (js0 := firstn 344 (jg0 ++ le8 (Z_to_bv 64 0) ++ jj)) in SL1. clearbody js0.
    destruct (rw_cells_CB_split asegs m1 S1 344 16 js0 SL1 ltac:(clear; lia)) as [SLa SLb]. change (344 - 16)%nat with 328%nat in SLb. change (Z.of_nat 16) with 16 in SLb.
    assert (SLQ1 : rw_cells asegs m1 S1 [CB 16 (firstn 16 js0); CB 328 (skipn 16 js0)]).
    { apply (proj2 (rw_cells_app asegs m1 S1 [CB 16 (firstn 16 js0)] [CB 328 (skipn 16 js0)])). split; [exact SLa| cbn [cells_size csize Nat.add]; exact SLb]. }
    clear FRa FRb GK ALL1 SL1 SLa SLb FR1.
    (* [comment removed for export] *)
    pose proof SM6 as SM. unfold stack_malloc_6_stmt, stack_malloc_stmt_n in SM.
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply SM with (lo := lo) (LF := LF);
      [exact RFS1| unfold READCFG_LF, READCFG_MAXLIVE in LFB; clear - LFB; lia| rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact STK1| exact CEIL
      | rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKA Q2; lia| exact MI1| reflexivity| exact AC1| exact (ah_thr H HH _ _ _ HP1)]|].
    clear SM. intros msF2 mo2 KREL2 MP2 PO. unfold stack_malloc_post in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & ff & fp & fj1 & fj2 & VIS2 & MU2 & WM2 & MI2 & ST2 & RFS2 & FRM2 & SHD2 & FPC2 & AC2).
    rewrite (unsigned_lit S1) in MU2, ST2 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    change (as_RFS H ((6, ff, fp) :: LF) m2) in RFS2. fold (LF1 ff fp) in RFS2.
    pose proof (fresh_of_RFS H HH _ _ _ _ _ RFS2) as FRESH.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FF2, FF6, FRM2. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    change (Z.to_nat (4096 - 40)) with 4056%nat in FRM2.
    assert (SHF : Z.shiftr ff 3 + ASHB = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (APff : aapp ff 4096) by (eapply aapp_sub; [exact FB3| clear - FF5; lia| unfold AFS_SIZE; clear - FF6; lia]). pose proof (aapp_not_shadowland _ _ APff) as NSff.
    pose proof (SHAD_rw_cells _ _ _ SHD2) as SHC2. rewrite <- SHF in SHC2.
    replace (length (poison_bytes (Z.to_nat (fshn 6)) 0)) with 512%nat in SHC2 by reflexivity.
    (* [comment removed for export] *)
    pose proof (sh_mono (as_FSB H) ff ltac:(clear - FF5; lia)) as SY1. pose proof (sh_mono (ff + 4096) _ FF6) as SY2.
    pose proof (sh_add8 ff 512) as SY3. replace (ff + 8 * 512) with (ff + 4096) in SY3 by (clear; lia).
    match type of MU2 with munch ?Wx _ _ =>
      assert (FW2 : Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= bv_unsigned sp) \/ (as_FSB H <= fst iv /\ snd iv <= as_FSB H + AFS_SIZE)
                                              \/ (sh (as_FSB H) <= fst iv /\ snd iv <= sh (as_FSB H + AFS_SIZE))) Wx) end.
    { apply Forall_cons; [left; cbn [fst snd]; clear - LO STKA Q2; unfold AFS_STACK in *; lia|].
      apply Forall_cons; [right; left; cbn [fst snd]; unfold AFS_FLAGS, AFS_SIZE; clear; lia|].
      apply Forall_cons; [right; left; cbn [fst snd]; unfold AFS_SIZE; clear - FP3 FP4; lia|].
      apply Forall_cons; [right; left; cbn [fst snd]; change (fsz 6) with 4096; unfold AFS_SIZE; clear - FF5 FF6; lia|].
      apply Forall_cons; [right; right; cbn [fst snd]; change (fshn 6) with 512; unfold AFS_SIZE; clear - SY1 SY2 SY3; lia| apply Forall_nil]. }
    pose proof (fsw_carry _ m1 m2 s L0 FW2 MU2 WM2 HP1 SUB0) as (HP2 & TAUX & TLM & Ts & Tb & Tby & Ta & Tacc & Terr & T0 & Tac & Tch & Txa & Tmb & Tms).
    pose proof (TAUX AUX1) as AUX2. pose proof (TLM _ M x LM1 CTX SUBLB0 SUBE0) as LM2.
    assert (W2lo : Forall (fun iv : Z * Z => lo <= fst iv -> iv = (S1 - AFS_STACK, S1))
                     [(S1 - AFS_STACK, S1); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 6); (sh ff, sh ff + fshn 6)]).
    { apply Forall_cons; [intros _; reflexivity|].
      apply Forall_cons; [cbn [fst snd]; intros K; exfalso; clear - K AF2 CEIL; lia|]. apply Forall_cons; [cbn [fst snd]; intros K; exfalso; clear - K FP4 AF2 CEIL; unfold AFS_HDR in FP4; lia|].
      apply Forall_cons; [cbn [fst snd]; intros K; exfalso; clear - K FF6 AF2 CEIL; lia|].
      apply Forall_cons; [cbn [fst snd]; intros K; exfalso; pose proof (sh_mono _ _ AF2) as Y; assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia); clear - K SY2 SY3 Y SHC CEIL; lia| apply Forall_nil]. }
    assert (W2hi : forall A n, S1 <= A -> Forall (fun iv : Z * Z => lo <= fst iv -> A + n <= fst iv \/ snd iv <= A)
                     [(S1 - AFS_STACK, S1); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 6); (sh ff, sh ff + fshn 6)]).
    { intros A n HA. eapply Forall_impl; [| exact W2lo]. cbn beta. intros iv K1 K2. rewrite (K1 K2). cbn [fst snd]. right. exact HA. }
    assert (AS1 : aceil <= S1) by (clear - CEIL LO STK0 Q2; lia).
    pose proof (Ts S1 _ SLQ1 AS1 (W2hi S1 _ ltac:(clear; lia))) as SLQ2.
    pose proof (Ts (S1 + 344) _ GP1 ltac:(clear - AS1; lia) (W2hi (S1 + 344) _ ltac:(clear; lia))) as GP2.
    pose proof (Ts (bv_unsigned sp + -104) _ SV1 ltac:(clear - AS1 Q2; lia) (W2hi (bv_unsigned sp + -104) _ ltac:(clear - KGR; lia))) as SV2.
    pose proof (Tb (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] SIN ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC1) as SC2.
    pose proof (Ta (es_id S, st, STORE_SIZE) st STORE_SIZE SIN ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD1) as SAD2.
    pose proof (Terr _ ERR1) as ERR2. pose proof (T0 ST01) as ST02.
    assert (W2ch : Forall (fun iv : Z * Z => lo <= fst iv -> snd iv + 16 <= S1 + 16) [(S1 - AFS_STACK, S1); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 6); (sh ff, sh ff + fshn 6)]).
    { eapply Forall_impl; [| exact W2lo]. cbn beta. intros iv K1 K2. rewrite (K1 K2). cbn [fst snd]. clear. lia. }
    pose proof (Tch _ _ (S1 + 16) CHN1 CHB1 ltac:(clear - CEIL LO STK0 Q2; lia) W2ch) as CHN2.
    assert (XA2 : xpres H LB (bv_unsigned sp) (XSF ff fp ++ MEMBIO_foot mb R) m m2).
    { apply Txa; [eapply xpres_weaken; [exact XA1| apply Z.le_refl| intros b Hb; exact Hb| intros q Hq; destruct Hq]|].
      intros a Ra LOW. cbn [rin_ivs fst snd] in Ra. apply rin_ivs_app. left. unfold XSF. cbn [rin_ivs fst snd].
      destruct Ra as [Ra|Ra]; [exfalso; clear - Ra LOW STKA LO Q2 CEIL; unfold AFS_STACK in *; lia| exact Ra]. }
    pose proof (Tmb R (mb_static_refl R) MBO1) as MBO2. pose proof (Tms R (mb_static_refl R) MBO1 MSH1) as MSH2.
    assert (DS2 : bytes_at asegs m2 (mb_buf R) ds).
    { destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      - assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil. clear - BUFP BUFH ACB L0Z. lia.
      - destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN _]].
        eapply (Tby (pD, mb_buf R, mb_len R)); [exact (SUB0 _ PIN)| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DS1]. }
    assert (PAYa2 : 1 <= mb_len R -> accessible m2 (mb_buf R) (mb_len R)).
    { intros L1. destruct (PAYL L1) as [pD [PIN _]]. eapply (Tacc (pD, mb_buf R, mb_len R)); [exact (SUB0 _ PIN)| apply Z.le_refl| apply Z.le_refl| clear - L1; lia| exact (PAYa1 L1)]. }
    clear TAUX TLM Ts Tb Tby Ta Tacc Terr T0 Tac Tch Txa Tmb Tms W2lo W2hi W2ch AUX1 LM1 SLQ1 GP1 SV1 SC1 SAD1 ERR1 ST01 CHN1 XA1 MBO1 MSH1 DS1 PAYa1 MU2 WM2 HP1 RFS1 AC1 MI1 STK1 ST1 VIS1 MU1 WM1 FW2.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 ARP_RSM)) with (Z_to_bv 64 ARP_RSM) in VIS2 by (symmetry; apply ret_pc_even; [unfold ARP_RSM; lia| reflexivity]).
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply arp_seg1b with (q := S1) (ff := ff) (fp := fp) (st := st) (mb := mb);
      [exact SSF8| clear - SB1 SBb ACB; unfold STORE_SIZE in SBb; lia| clear - E11 E1b ACB; lia| clear - FF1; unfold AIMG_TOP; lia| exact FF2| exact FF64| exact APff
      | clear - CEIL LO STK0 Q2; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| exact SLQ2| exact FRM2| exact SHC2| exact MI2| exact AC2]|].
    intros msF3 mo3 KREL3 MP3 (m3 & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & s4w & s5w & j1 & j2 & j3 & j4 & fk1 & fk2 & e5
                                 & VIS3 & MU3 & WM3 & MI3 & SL3 & FRM3 & FSH3 & AC3). set (j0 := firstn 16 js0) in *. clearbody j0.
    rewrite SHF in FSH3.
    match type of MU3 with munch ?Wx _ _ =>
      assert (FW3 : Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= bv_unsigned sp) \/ (as_FSB H <= fst iv /\ snd iv <= as_FSB H + AFS_SIZE)
                                              \/ (sh (as_FSB H) <= fst iv /\ snd iv <= sh (as_FSB H + AFS_SIZE))) Wx) end.
    { apply Forall_cons; [left; cbn [fst snd]; clear - CEIL LO STK0 Q2; lia|].
      apply Forall_cons; [right; left; cbn [fst snd]; unfold AFS_SIZE; clear - FF5 FF6; lia|].
      apply Forall_cons; [right; right; cbn [fst snd]; rewrite SHF; unfold AFS_SIZE; clear - SY1 SY2 SY3; lia| apply Forall_nil]. }
    pose proof (fsw_carry _ m2 m3 s L0 FW3 MU3 WM3 HP2 SUB0) as (HP3 & TAUX & TLM & Ts & Tb & Tby & Ta & Tacc & Terr & T0 & Tac & Tch & Txa & Tmb & Tms).
    pose proof (TAUX AUX2) as AUX3. pose proof (TLM _ M x LM2 CTX SUBLB0 SUBE0) as LM3.
    match type of MU3 with munch ?Wx _ _ =>
      assert (W3lo : Forall (fun iv : Z * Z => lo <= fst iv -> iv = (S1, S1 + 344)) Wx) end.
    { apply Forall_cons; [intros _; reflexivity|].
      apply Forall_cons; [cbn [fst snd]; intros K; exfalso; clear - K FF6 AF2 CEIL; lia|].
      apply Forall_cons; [cbn [fst snd]; intros K; exfalso; pose proof (sh_mono _ _ AF2) as Y; assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia); rewrite SHF in K; clear - K SY2 SY3 Y SHC CEIL; lia| apply Forall_nil]. }
    assert (W3hi : forall A n, S1 + 344 <= A -> Forall (fun iv : Z * Z => lo <= fst iv -> A + n <= fst iv \/ snd iv <= A) [(S1, S1 + 344); (ff, ff + 4096); (Z.shiftr ff 3 + ASHB, Z.shiftr ff 3 + ASHB + 512)]).
    { intros A n HA. eapply Forall_impl; [| exact W3lo]. cbn beta. intros iv K1 K2. rewrite (K1 K2). cbn [fst snd]. right. exact HA. }
    pose proof (Ts (S1 + 344) _ GP2 ltac:(clear - AS1; lia) (W3hi (S1 + 344) _ ltac:(clear; lia))) as GP3.
    pose proof (Ts (bv_unsigned sp + -104) _ SV2 ltac:(clear - AS1 Q2; lia) (W3hi (bv_unsigned sp + -104) _ ltac:(clear - KGR; lia))) as SV3.
    pose proof (Tb (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] SIN ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC2) as SC3.
    pose proof (Ta (es_id S, st, STORE_SIZE) st STORE_SIZE SIN ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD2) as SAD3.
    pose proof (Terr _ ERR2) as ERR3. pose proof (T0 ST02) as ST03.
    assert (W3ch : Forall (fun iv : Z * Z => lo <= fst iv -> snd iv + 16 <= S1 + 344 + 16) [(S1, S1 + 344); (ff, ff + 4096); (Z.shiftr ff 3 + ASHB, Z.shiftr ff 3 + ASHB + 512)]).
    { eapply Forall_impl; [| exact W3lo]. cbn beta. intros iv K1 K2. rewrite (K1 K2). cbn [fst snd]. clear. lia. }
    assert (CHB3 : forall fp' ra', In (fp', ra') CH1 -> S1 + 344 + 16 <= fp').
    { intros fp' ra' [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
    pose proof (Tch _ _ (S1 + 344 + 16) CHN2 CHB3 ltac:(clear - AS1; lia) W3ch) as CHN3.
    assert (XA3 : xpres H LB (bv_unsigned sp) (XSF ff fp ++ MEMBIO_foot mb R) m m3).
    { apply Txa; [exact XA2|]. intros a Ra LOW. cbn [rin_ivs fst snd] in Ra. apply rin_ivs_app. left. unfold XSF. cbn [rin_ivs fst snd]. change (fsz 6) with 4096. change (fshn 6) with 512.
      rewrite SHF in Ra. destruct Ra as [Ra|[Ra|[Ra|[]]]]; [exfalso; clear - Ra LOW AS1; lia| right; right; left; exact Ra| right; right; right; left; exact Ra]. }
    pose proof (Tmb R (mb_static_refl R) MBO2) as MBO3. pose proof (Tms R (mb_static_refl R) MBO2 MSH2) as MSH3.
    assert (DS3 : bytes_at asegs m3 (mb_buf R) ds).
    { destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      - assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil. clear - BUFP BUFH ACB L0Z. lia.
      - destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN _]].
        eapply (Tby (pD, mb_buf R, mb_len R)); [exact (SUB0 _ PIN)| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DS2]. }
    assert (PAYa3 : 1 <= mb_len R -> accessible m3 (mb_buf R) (mb_len R)).
    { intros L1. destruct (PAYL L1) as [pD [PIN _]]. eapply (Tacc (pD, mb_buf R, mb_len R)); [exact (SUB0 _ PIN)| apply Z.le_refl| apply Z.le_refl| clear - L1; lia| exact (PAYa2 L1)]. }
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia). pose proof (sh_mono _ _ AF2) as SYA.
    assert (STK3 : stk asegs m3 lo S1).
    { eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]. apply djF.
      apply Forall_cons; [cbn [fst snd]; left; clear - AS1 CEIL; lia|].
      apply Forall_cons; [cbn [fst snd]; right; clear - FF6 AF2 CEIL; lia|].
      apply Forall_cons; [cbn [fst snd]; right; rewrite SHF; clear - SY2 SY3 SYA SHC CEIL; lia| apply Forall_nil]. }
    assert (RFS3 : as_RFS H (LF1 ff fp) m3).
    { eapply (ah_RFS_frame H HH); [exact RFS2| exact MU3| exact WM3|].
      apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE; clear - AF2 AS1 ACB; lia|].
      apply Forall_cons; [right; exists (6, ff, fp); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (fsz 6) with 4096; clear; lia]|].
      apply Forall_cons; [left; rewrite SHF; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, ALOWSH_LO, AHI_LO in *; pose proof (sh_aapp_range _ _ AF4 ltac:(unfold AFS_SIZE; clear; lia)) as (V1 & V2 & V3);
                          clear - NSF SY1 SY2 SY3 SYA V1 V3 SHC AF1; assert (S0 : sh 0xc04000 = 0x80178800) by reflexivity; unfold AIMG_TOP, AFS_SIZE, AHI_LO in *; rewrite S0 in V1; lia| apply Forall_nil]. }
    pose proof LM3 as (IM3 & MFq3 & _ & _ & _ & _ & _ & _ & GM3 & _). rewrite MF1 in MFq3.
    clear TAUX TLM Ts Tb Tby Ta Tacc Terr T0 Tac Tch Txa Tmb Tms W3lo W3hi W3ch FW3 AUX2 LM2 GP2 SV2 SC2 SAD2 ERR2 ST02 CHN2 XA2 MBO2 MSH2 DS2 PAYa2 SLQ2 FRM2 SHC2 SHD2 FPC2 MU3 WM3 HP2 RFS2 ST2 AC2 MI2 VIS2 KREL2.
    (* [comment removed for export] *)
    pose proof (aczalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (ah_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := L0) (s := s) (num := 512) (size := 1) (v := 1) (errv := errv) (CH := CH1); clear CZ.
      all: try first [exact VIS3| exact HP3| exact KREL3| exact AUX3| exact MI3| exact CEIL| exact AC3| exact CHN3| exact IM3| exact GM3| exact ERR3| exact MFq3].
      all: lazymatch goal with
           | |- Z_to_bv 64 OSSL_ECH_BUFCHUNK = _ => reflexivity
           | |- 1 = 1 => reflexivity
           | |- 1 <= 512 * 1 <= _ => clear; lia
           | |- lb_bytes _ + _ <= _ => pose proof BUD as BUDq; unfold mid_bytes in BUDq; rewrite CTX in BUDq; cbn [ctxph_bytes] in BUDq; unfold DECODE_BYTES, ERRSTR_BYTES in BUDq;
                                        unfold L0; clear - BUDq EBR; lia
           | |- Z.of_nat _ + _ <= _ => pose proof BUDC as BUDq; unfold mid_cnt in BUDq; rewrite CTX in BUDq; cbn [ctxph_cnt] in BUDq; unfold DECODE_CNT, ERRSTR_CNT in BUDq;
                                        unfold L0; clear - BUDq ECR; lia
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - SPB Q2; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact STK3
           | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKZ Q2; lia
           | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact (CHB1 _ _ Hin)
           | |- pf_ok _ _ _ _ => unfold ARP_R1; rewrite unsigned_lit by (clear; lia); apply pf_site; intros e He; unfold PF_readcfg, PF_read_priv; apply in_or_app; left; exact He
           | |- as_Cm H _ <= as_AL H _ => pose proof ALW as ALq; unfold READCFG_COST in ALq; pose proof (CMmono (512 * 1) DECODE_CUM_BYTES ltac:(unfold DECODE_CUM_BYTES; clear; lia)) as Y1;
                                          pose proof (CF0 DECODE_CUM_BYTES ltac:(unfold DECODE_CUM_BYTES; clear; lia)) as Y2; pose proof (errph_cost_nonneg (mid_err M)) as Y3; clear - ALq Y1 Y2 Y3; lia
           | |- Z_to_bv 64 ATP = _ => reflexivity
           | |- ?G => idtac "B2B_CZ_LEFT" G
           end. }
    clear CZ. intros [msF4 mo4] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & cc1 & cc2 & cc3 & cc4 & cc5 & cc6 & cc7 & w3 & w4 & w5 & w6 & m4 & errv4 & A & p & s4' & VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & XP4 & BRA & HP4 & ZK4 & AD4 & MF4 & IM4 & GM4 & AL4).
    rewrite (unsigned_lit S1) in ST4, XP4 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    pose proof BRA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7). unfold AIMG_TOP in BA4.
    destruct (lad_head_facts H HX L0 _ _ _ _ _ HP4) as (_ & NIPA & DISJA & _ & _).
    assert (SQ4 : forall b, In b LB -> In b ((p, A, 512 * 1) :: L0)) by (intros b Hb; right; exact (SUB0 _ Hb)).
    assert (XP4n : xpres H L0 S1 [] m3 m4).
    { apply (axpres_drop_memflag H L0 S1 [] m3 m4); [rewrite app_nil_r; exact XP4| exact MFq3| exact MF4]. }
    assert (LED4 : LEDGER s4' (512 * 1) 0) by (split; [clear; lia| split; [clear; lia| clear - AL4 CFz; lia]]).
    pose proof (xnil_carry ff fp m3 m4 s L0 L0 FRESH XP4n HP3 ltac:(intros b Hb; exact Hb) SUB0) as (TRFS & TLM & Ts & Tf & Tsh & Tb & Tby & Ta & Tacc & T0 & Tch & Txa & Tmb & Tms).
    pose proof (TRFS RFS3) as RFS4. pose proof (TLM _ M x LM3 CTX SUBLB0 SUBE0) as LM4.
    pose proof (Ts _ _ SL3 ltac:(clear; lia)) as SL4. pose proof (Ts _ _ GP3 ltac:(clear; lia)) as GP4. pose proof (Ts _ _ SV3 ltac:(clear - Q2; lia)) as SV4.
    pose proof (Tf _ FRM3 ltac:(unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as FRM4.
    pose proof (Tsh _ FSH3 ltac:(unfold arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia)) as FSH4.
    pose proof (Tb (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] SIN ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC3) as SC4.
    pose proof (Ta (es_id S, st, STORE_SIZE) st STORE_SIZE SIN ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(clear - SB2; Z.div_mod_to_equations; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD3) as SAD4.
    pose proof (T0 ST03) as ST04. pose proof (Tch _ _ CHN3 CHB1) as CHN4. pose proof (Txa _ _ XA3) as XA4.
    pose proof (Tmb R (mb_static_refl R) MBO3) as MBO4. pose proof (Tms R (mb_static_refl R) MBO3 MSH3) as MSH4.
    assert (DS4 : bytes_at asegs m4 (mb_buf R) ds).
    { destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      - assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil. clear - BUFP BUFH ACB L0Z. lia.
      - destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN _]].
        eapply (Tby (pD, mb_buf R, mb_len R)); [exact (SUB0 _ PIN)| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DS3]. }
    assert (PAYa4 : 1 <= mb_len R -> accessible m4 (mb_buf R) (mb_len R)).
    { intros L1. destruct (PAYL L1) as [pD [PIN _]]. eapply (Tacc (pD, mb_buf R, mb_len R)); [exact (SUB0 _ PIN)| apply Z.le_refl| apply Z.le_refl| clear - L1; lia| exact (PAYa3 L1)]. }
    clear TRFS TLM Ts Tf Tsh Tb Tby Ta Tacc T0 Tch Txa Tmb Tms RFS3 LM3 SL3 GP3 SV3 FRM3 FSH3 SC3 SAD3 ST03 CHN3 XA3 MBO3 MSH3 DS3 PAYa3 XP4 XP4n HP3 AUX3 ERR3 AC3 MI3 STK3 VIS3 KREL3 IM3 GM3 MFq3.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 ARP_R1)) with (Z_to_bv 64 ARP_R1) in VIS4 by (symmetry; apply ret_pc_even; [unfold ARP_R1; lia| reflexivity]).
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply arp_seg2 with (q := S1) (fp := fp); [clear - BA1 BA5 ACB; lia| clear - AS1 ACB; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| exact SL4| exact MI4]|].
    intros msF5 mo5 KREL5 MP5 (m5 & j2' & VIS5 & MU5 & WM5 & MI5 & SL5).
    assert (FWs5 : Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= bv_unsigned sp) \/ (as_FSB H <= fst iv /\ snd iv <= as_FSB H + AFS_SIZE)
                                              \/ (sh (as_FSB H) <= fst iv /\ snd iv <= sh (as_FSB H + AFS_SIZE))) [(S1, S1 + 344)]).
    { apply Forall_cons; [left; cbn [fst snd]; clear - CEIL LO STK0 Q2; lia| apply Forall_nil]. }
    pose proof (fsw_carry _ m4 m5 s4' ((p, A, 512 * 1) :: L0) FWs5 MU5 WM5 HP4 SQ4) as (HP5 & TAUX & TLM & Ts & Tb & Tby & Ta & Tacc & Terr & T0 & Tac & Tch & Txa & Tmb & Tms).
    pose proof (TAUX AUX4) as AUX5. pose proof (TLM _ M x LM4 CTX ltac:(intros b Hb; right; exact (SUBLB0 _ Hb)) ltac:(intros b Hb; right; exact (SUBE0 _ Hb))) as LM5.
    pose proof (Ts (S1 + 344) _ GP4 ltac:(clear - AS1; lia) ltac:(apply Forall_cons; [cbn [fst snd]; intros _; right; clear; lia| apply Forall_nil])) as GP5.
    pose proof (Ts (bv_unsigned sp + -104) _ SV4 ltac:(clear - AS1 Q2; lia) ltac:(apply Forall_cons; [cbn [fst snd]; intros _; right; clear - KGR; lia| apply Forall_nil])) as SV5.
    pose proof (Tb (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC4) as SC5.
    pose proof (Ta (es_id S, st, STORE_SIZE) st STORE_SIZE (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD4) as SAD5.
    pose proof (Tb (p, A, 512 * 1) A [CB (Z.to_nat (512 * 1)) (zeros (Z.to_nat (512 * 1)))] (or_introl eq_refl) ltac:(apply Z.le_refl) ltac:(cbn; clear; lia) ZK4) as ZK5.
    pose proof (Ta (p, A, 512 * 1) A (512 * 1) (or_introl eq_refl) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(clear; lia) AD4) as AD5.
    pose proof (Terr _ ERR4) as ERR5. pose proof (T0 ST04) as ST05. pose proof (Tac AC4) as AC5.
    pose proof (Tch _ _ (S1 + 344 + 16) CHN4 CHB3 ltac:(clear - AS1; lia) ltac:(apply Forall_cons; [cbn [fst snd]; intros _; clear; lia| apply Forall_nil])) as CHN5.
    assert (XA5 : xpres H LB (bv_unsigned sp) (XSF ff fp ++ MEMBIO_foot mb R) m m5).
    { apply Txa; [exact XA4|]. intros a Ra LOW. cbn [rin_ivs fst snd] in Ra. exfalso. clear - Ra LOW AS1. lia. }
    pose proof (Tmb R (mb_static_refl R) MBO4) as MBO5. pose proof (Tms R (mb_static_refl R) MBO4 MSH4) as MSH5.
    assert (DS5 : bytes_at asegs m5 (mb_buf R) ds).
    { destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      - assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil. clear - BUFP BUFH ACB L0Z. lia.
      - destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN _]].
        eapply (Tby (pD, mb_buf R, mb_len R)); [exact (SQ4 _ PIN)| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DS4]. }
    assert (PAYa5 : 1 <= mb_len R -> accessible m5 (mb_buf R) (mb_len R)).
    { intros L1. destruct (PAYL L1) as [pD [PIN _]]. eapply (Tacc (pD, mb_buf R, mb_len R)); [exact (SQ4 _ PIN)| apply Z.le_refl| apply Z.le_refl| clear - L1; lia| exact (PAYa4 L1)]. }
    assert (FRM5 : rw_cells asegs m5 ff (arp_fframe S1 fk1 0 fk2 fp)).
    { eapply rw_cells_transport; [exact FRM4| exact MU5| exact WM5| cbn [disjoint_from]; split; [left; unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - FF6 AF2 AS1; lia| exact I]]. }
    assert (FSH5 : rw_cells asegs m5 (sh ff) (arp_fshadow (poison_bytes 4 0xf1) (b8 0xf8) (poison_bytes 3 0xf2) (b8 0xf8) (b8 0xf2) (poison_bytes 256 0xf8) (poison_bytes 16 0xf2) (b8 0) e5)).
    { eapply rw_cells_transport; [exact FSH4| exact MU5| exact WM5| cbn [disjoint_from]; split; [left; unfold arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SY2 SY3 SYA SHC AS1; lia| exact I]]. }
    assert (RFS5 : as_RFS H (LF1 ff fp) m5).
    { eapply (ah_RFS_frame H HH); [exact RFS4| exact MU5| exact WM5|]. apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE; clear - AF2 AS1 ACB; lia| apply Forall_nil]. }
    assert (STK5 : stk asegs m5 lo S1).
    { eapply stk_transport_disjoint; [exact ST4| exact MU5| exact WM5|]. cbn [disjoint_from]. split; [left; clear - AS1 CEIL; lia| exact I]. }
    clear TAUX TLM Ts Tb Tby Ta Tacc Terr T0 Tac Tch Txa Tmb Tms FWs5 AUX4 LM4 GP4 SV4 SC4 SAD4 ZK4 AD4 ERR4 ST04 CHN4 XA4 MBO4 MSH4 DS4 PAYa4 FRM4 FSH4 RFS4 ST4 SL4 MU5 WM5 HP4 MI4 AC4 VIS4 KREL4.
    pose proof LM5 as (IM5 & _ & _ & _ & _ & _ & _ & _ & GM5 & _ & _ & MM5 & _).
    (* [comment removed for export] *)
    pose proof (abioeof_mem_spec H) as EF. unfold bioeof_mem_stmt in EF.
    eapply (ahh_evt_then H HH); [exact KREL5| exact VIS5| eapply EF with (lo := lo) (LB := LB) (a := mb) (R := R);
      [reflexivity| exact MBO5| exact MBB| exact MBS| exact MM5| exact MSH5| exact AC5
      | rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact STK5| exact CEIL
      | rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKL Q2; unfold LAD_STACK in STKL; lia| exact MI5
      | unfold ARP_R2; rewrite unsigned_lit by (clear; lia); reflexivity]|].
    clear EF. intros msF6 mo6 KREL6 MP6 PO. unfold memctrl_post in PO.
    destruct PO as (x0 & x1 & x2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & x3 & x4 & x5 & x6 & m6 & VIS6 & MU6 & WM6 & MI6 & AC6 & STK6 & MBO6).
    rewrite (unsigned_lit S1) in MU6, STK6 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    pose proof (stk_carry m5 m6 s4' ((p, A, 512 * 1) :: L0) lo S1 ltac:(apply Z.le_refl) ltac:(clear - Q2; lia) MU6 WM6 HP5 SQ4)
      as (HP6 & TAUX & TRFS & TLM & Ts & Tf & Tsh & Tb & Tby & Ta & Tacc & Terr & T0 & Tac & Tch & Txa & Tmb & Tms).
    pose proof (TAUX AUX5) as AUX6. pose proof (TRFS _ RFS5) as RFS6. pose proof (TLM _ M x LM5 CTX ltac:(intros b Hb; right; exact (SUBLB0 _ Hb)) ltac:(intros b Hb; right; exact (SUBE0 _ Hb))) as LM6.
    pose proof (Ts _ _ SL5 ltac:(clear; lia)) as SL6. pose proof (Ts _ _ GP5 ltac:(clear; lia)) as GP6. pose proof (Ts _ _ SV5 ltac:(clear - Q2; lia)) as SV6.
    assert (FRM6 : rw_cells asegs m6 ff (arp_fframe S1 fk1 0 fk2 fp)) by (apply (Tf ff); [clear - FF2; lia| exact FRM5| unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]).
    assert (FSH6 : rw_cells asegs m6 (sh ff) (arp_fshadow (poison_bytes 4 0xf1) (b8 0xf8) (poison_bytes 3 0xf2) (b8 0xf8) (b8 0xf2) (poison_bytes 256 0xf8) (poison_bytes 16 0xf2) (b8 0) e5))
      by (apply (Tsh ff); [clear - FF1; lia| clear - FF2; lia| exact FSH5| unfold arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]).
    pose proof (Tb (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC5) as SC6.
    pose proof (Ta (es_id S, st, STORE_SIZE) st STORE_SIZE (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD5) as SAD6.
    pose proof (Tb (p, A, 512 * 1) A [CB (Z.to_nat (512 * 1)) (zeros (Z.to_nat (512 * 1)))] (or_introl eq_refl) ltac:(apply Z.le_refl) ltac:(cbn; clear; lia) ZK5) as ZK6.
    pose proof (Ta (p, A, 512 * 1) A (512 * 1) (or_introl eq_refl) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(clear; lia) AD5) as AD6.
    pose proof (Terr _ ERR5) as ERR6. pose proof (T0 ST05) as ST06. pose proof (Tch _ _ (S1 + 16) CHN5 CHB1 ltac:(clear; lia)) as CHN6. pose proof (Txa _ _ XA5) as XA6.
    pose proof (Tms R (mb_static_refl R) MBO5 MSH5) as MSH6.
    assert (DS6 : bytes_at asegs m6 (mb_buf R) ds).
    { destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      - assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil. clear - BUFP BUFH ACB L0Z. lia.
      - destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN _]].
        eapply (Tby (pD, mb_buf R, mb_len R)); [exact (SQ4 _ PIN)| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DS5]. }
    assert (PAYa6 : 1 <= mb_len R -> accessible m6 (mb_buf R) (mb_len R)).
    { intros L1. destruct (PAYL L1) as [pD [PIN _]]. eapply (Tacc (pD, mb_buf R, mb_len R)); [exact (SQ4 _ PIN)| apply Z.le_refl| apply Z.le_refl| clear - L1; lia| exact (PAYa5 L1)]. }
    clear TAUX TRFS TLM Ts Tf Tsh Tb Tby Ta Tacc Terr T0 Tac Tch Txa Tmb Tms AUX5 RFS5 LM5 SL5 GP5 SV5 FRM5 FSH5 SC5 SAD5 ZK5 AD5 ERR5 ST05 CHN5 XA5 MBO5 MSH5 DS5 PAYa5 STK5 MU6 WM6 HP5 MI5 AC5 VIS5 KREL5 IM5 GM5 MM5.
    assert (RV : mem_ctrl_rv R BIO_CTRL_EOF = (if mb_len R =? 0 then 1 else 0)) by (unfold mem_ctrl_rv, mb_avail; rewrite Z.eqb_refl, MP0, Z.sub_0_r; reflexivity).
    rewrite RV in VIS6. clear RV.
    replace (ret_pc (Z_to_bv 64 ARP_R2)) with (Z_to_bv 64 ARP_R2) in VIS6 by (symmetry; apply ret_pc_even; [unfold ARP_R2; lia| reflexivity]).
    pose proof (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 (ah_mpres_trans H HH _ _ _ MP3 (ah_mpres_trans H HH _ _ _ MP4 (ah_mpres_trans H HH _ _ _ MP5 MP6))))) as MPc6.
    clear MP1 MP2 MP3 MP4 MP5 MP6.
    destruct (Z.eqb_spec (mb_len R) 0) as [L0Z|LNZ].
    + (* [comment removed for export] *)
      eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply ald_segc1 with (q := S1) (e := 1); [clear; lia| clear - AS1 ACB; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| exact SL6| exact MI6]|].
      intros msF7 mo7 KREL7 MP7 (m7 & VIS7 & MU7 & WM7 & MI7 & SL7).
      assert (FWs7 : Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= bv_unsigned sp) \/ (as_FSB H <= fst iv /\ snd iv <= as_FSB H + AFS_SIZE)
                                                \/ (sh (as_FSB H) <= fst iv /\ snd iv <= sh (as_FSB H + AFS_SIZE))) [(S1, S1 + 344)]).
      { apply Forall_cons; [left; cbn [fst snd]; clear - CEIL LO STK0 Q2; lia| apply Forall_nil]. }
      pose proof (fsw_carry _ m6 m7 s4' ((p, A, 512 * 1) :: L0) FWs7 MU7 WM7 HP6 SQ4) as (HP7 & TAUX & TLM & Ts & Tb & Tby & Ta & Tacc & Terr & T0 & Tac & Tch & Txa & Tmb & Tms).
      pose proof (TAUX AUX6) as AUX7. pose proof (TLM _ M x LM6 CTX ltac:(intros b Hb; right; exact (SUBLB0 _ Hb)) ltac:(intros b Hb; right; exact (SUBE0 _ Hb))) as LM7.
      pose proof (Ts (S1 + 344) _ GP6 ltac:(clear - AS1; lia) ltac:(apply Forall_cons; [cbn [fst snd]; intros _; right; clear; lia| apply Forall_nil])) as GP7.
      pose proof (Ts (bv_unsigned sp + -104) _ SV6 ltac:(clear - AS1 Q2; lia) ltac:(apply Forall_cons; [cbn [fst snd]; intros _; right; clear - KGR; lia| apply Forall_nil])) as SV7.
      pose proof (Tb (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC6) as SC7.
      pose proof (Ta (es_id S, st, STORE_SIZE) st STORE_SIZE (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD6) as SAD7.
      pose proof (Tb (p, A, 512 * 1) A [CB (Z.to_nat (512 * 1)) (zeros (Z.to_nat (512 * 1)))] (or_introl eq_refl) ltac:(apply Z.le_refl) ltac:(cbn; clear; lia) ZK6) as ZK7.
      pose proof (Ta (p, A, 512 * 1) A (512 * 1) (or_introl eq_refl) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(clear; lia) AD6) as AD7.
      pose proof (Terr _ ERR6) as ERR7. pose proof (T0 ST06) as ST07. pose proof (Tac AC6) as AC7.
      pose proof (Tch _ _ (S1 + 344 + 16) CHN6 CHB3 ltac:(clear - AS1; lia) ltac:(apply Forall_cons; [cbn [fst snd]; intros _; clear; lia| apply Forall_nil])) as CHN7.
      assert (XA7 : xpres H LB (bv_unsigned sp) (XSF ff fp ++ MEMBIO_foot mb R) m m7).
      { apply Txa; [exact XA6|]. intros a Ra LOW. cbn [rin_ivs fst snd] in Ra. exfalso. clear - Ra LOW AS1. lia. }
      pose proof (Tmb R (mb_static_refl R) MBO6) as MBO7. pose proof (Tms R (mb_static_refl R) MBO6 MSH6) as MSH7.
      assert (DS7 : bytes_at asegs m7 (mb_buf R) ds).
      { assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil. clear - BUFP BUFH ACB L0Z. lia. }
      assert (FRM7 : rw_cells asegs m7 ff (arp_fframe S1 fk1 0 fk2 fp)).
      { eapply rw_cells_transport; [exact FRM6| exact MU7| exact WM7| cbn [disjoint_from]; split; [left; unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - FF6 AF2 AS1; lia| exact I]]. }
      assert (FSH7 : rw_cells asegs m7 (sh ff) (arp_fshadow (poison_bytes 4 0xf1) (b8 0xf8) (poison_bytes 3 0xf2) (b8 0xf8) (b8 0xf2) (poison_bytes 256 0xf8) (poison_bytes 16 0xf2) (b8 0) e5)).
      { eapply rw_cells_transport; [exact FSH6| exact MU7| exact WM7| cbn [disjoint_from]; split; [left; unfold arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SY2 SY3 SYA SHC AS1; lia| exact I]]. }
      assert (RFS7 : as_RFS H (LF1 ff fp) m7).
      { eapply (ah_RFS_frame H HH); [exact RFS6| exact MU7| exact WM7|]. apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE; clear - AF2 AS1 ACB; lia| apply Forall_nil]. }
      assert (STK7 : stk asegs m7 lo S1).
      { eapply stk_transport_disjoint; [exact STK6| exact MU7| exact WM7|]. cbn [disjoint_from]. split; [left; clear - AS1 CEIL; lia| exact I]. }
      clear TAUX TLM Ts Tb Tby Ta Tacc Terr T0 Tac Tch Txa Tmb Tms FWs7 AUX6 LM6 GP6 SV6 SC6 SAD6 ZK6 AD6 ERR6 ST06 CHN6 XA6 MBO6 MSH6 DS6 PAYa6 FRM6 FSH6 RFS6 STK6 SL6 MU7 WM7 HP6 MI6 AC6 VIS6 KREL6.
      pose proof LM7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MM7 & _).
      (* [comment removed for export] *)
      pose proof (abioeof_mem_spec H) as EF. unfold bioeof_mem_stmt in EF.
      eapply (ahh_evt_then H HH); [exact KREL7| exact VIS7| eapply EF with (lo := lo) (LB := LB) (a := mb) (R := R);
        [reflexivity| exact MBO7| exact MBB| exact MBS| exact MM7| exact MSH7| exact AC7
        | rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact STK7| exact CEIL
        | rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKL Q2; unfold LAD_STACK in STKL; lia| exact MI7
        | unfold ALD_FAIL; rewrite unsigned_lit by (clear; lia); reflexivity]|].
      clear EF. intros msF8 mo8 KREL8 MP8 PO. unfold memctrl_post in PO.
      destruct PO as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5' & e6 & e7 & y3 & y4 & y5 & y6 & m8 & VIS8 & MU8 & WM8 & MI8 & AC8 & STK8 & MBO8).
      rewrite (unsigned_lit S1) in MU8, STK8 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
      pose proof (stk_carry m7 m8 s4' ((p, A, 512 * 1) :: L0) lo S1 ltac:(apply Z.le_refl) ltac:(clear - Q2; lia) MU8 WM8 HP7 SQ4)
        as (HP8 & TAUX & TRFS & TLM & Ts & Tf & Tsh & Tb & Tby & Ta & Tacc & Terr & T0 & Tac & Tch & Txa & Tmb & Tms).
      pose proof (TAUX AUX7) as AUX8. pose proof (TRFS _ RFS7) as RFS8. pose proof (TLM _ M x LM7 CTX ltac:(intros b Hb; right; exact (SUBLB0 _ Hb)) ltac:(intros b Hb; right; exact (SUBE0 _ Hb))) as LM8.
      pose proof (Ts _ _ SL7 ltac:(clear; lia)) as SL8. pose proof (Ts _ _ GP7 ltac:(clear; lia)) as GP8. pose proof (Ts _ _ SV7 ltac:(clear - Q2; lia)) as SV8.
      assert (FRM8 : rw_cells asegs m8 ff (arp_fframe S1 fk1 0 fk2 fp)) by (apply (Tf ff); [clear - FF2; lia| exact FRM7| unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]).
      assert (FSH8 : rw_cells asegs m8 (sh ff) (arp_fshadow (poison_bytes 4 0xf1) (b8 0xf8) (poison_bytes 3 0xf2) (b8 0xf8) (b8 0xf2) (poison_bytes 256 0xf8) (poison_bytes 16 0xf2) (b8 0) e5))
        by (apply (Tsh ff); [clear - FF1; lia| clear - FF2; lia| exact FSH7| unfold arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia]).
      pose proof (Tb (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC7) as SC8.
      pose proof (Ta (es_id S, st, STORE_SIZE) st STORE_SIZE (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD7) as SAD8.
      pose proof (Tb (p, A, 512 * 1) A [CB (Z.to_nat (512 * 1)) (zeros (Z.to_nat (512 * 1)))] (or_introl eq_refl) ltac:(apply Z.le_refl) ltac:(cbn; clear; lia) ZK7) as ZK8.
      pose proof (Ta (p, A, 512 * 1) A (512 * 1) (or_introl eq_refl) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(clear; lia) AD7) as AD8.
      pose proof (Terr _ ERR7) as ERR8. pose proof (T0 ST07) as ST08. pose proof (Tch _ _ (S1 + 16) CHN7 CHB1 ltac:(clear; lia)) as CHN8. pose proof (Txa _ _ XA7) as XA8.
      pose proof (Tms R (mb_static_refl R) MBO7 MSH7) as MSH8.
      assert (DS8 : bytes_at asegs m8 (mb_buf R) ds).
      { assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil. clear - BUFP BUFH ACB L0Z. lia. }
      clear TAUX TRFS TLM Ts Tf Tsh Tb Tby Ta Tacc Terr T0 Tac Tch Txa Tmb Tms.
      (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 ALD_FAIL)) with (Z_to_bv 64 ALD_FAIL) in VIS8 by (symmetry; apply ret_pc_even; [unfold ALD_FAIL; lia| reflexivity]).
      eapply (ahh_evt_then H HH); [exact KREL8| exact VIS8| eapply ald_segf; exact MI8|]. intros msF9 mo9 KREL9 MP9 VIS9. cbn beta in VIS9.
      rewrite <- SHF in FSH8.
      eapply (rp_fail595 m8 msF9 mo9 s4' p A (512 * 1) (zeros (Z.to_nat (512 * 1))) R ff fp 0 fk1 fk2 jg [CB 16 j0; CB 128 j1; C8 (wz (Z.shiftr ff 3 + ASHB + 10))] [CB 8 (skipn 8 j2'); C8 (wz ASHB); CB 32 j3; C8 (wz ff); CB 120 j4]
                (poison_bytes 4 0xf1) (b8 0xf8) (poison_bytes 3 0xf2) (b8 0xf8) (b8 0xf2) (poison_bytes 256 0xf8) (poison_bytes 16 0xf2) (b8 0) e5 (512 * 1) 0).
      all: try first [exact VIS9| exact HP8| exact KREL9| exact MI8| exact AC8| exact ZK8| exact AD8| exact MBO8| exact MSH8| exact DS8| exact STK8| exact ST08| exact SL8| exact GP8| exact SV8| exact FRM8| exact FSH8
                      | exact RFS8| exact ERR8| exact AUX8| exact LM8| exact SC8| exact CHN8| exact XA8| exact LED4| apply mb_static_refl].
      all: lazymatch goal with
           | |- as_MPRES _ _ _ => eapply (ah_mpres_trans H HH); [exact MPc6| eapply (ah_mpres_trans H HH); [exact MP7| eapply (ah_mpres_trans H HH); [exact MP8| exact MP9]]]
           | |- 0 <= 512 * 1 <= _ => clear; lia
           | |- cells_size _ = _ => reflexivity
           | |- STORE_shad _ _ _ => rewrite SEQ; apply (proj2 (STORE_shad_empty _ _ _)); split; [exact SHhi| exact SAD8]
           | |- _ <= DECODE_CUM_BYTES => unfold DECODE_CUM_BYTES; clear; lia
           | |- rw_cells asegs _ S1 (_ ++ _ ++ _) => cbn [app]; exact SL8
           | |- ?G => idtac "B2B_F595_LEFT" G
           end.
    + (* [comment removed for export] *)
      assert (LPOS : 1 <= mb_len R) by (clear - LNZ LENR; lia).
      eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply arp_seg3 with (q := S1);
        [clear - BA1 BA5 ACB; lia| clear - AS1 ACB; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| clear - FF1; lia| clear - FF2 ACB; lia| exact SL6| exact MI6]|].
      intros msF7 mo7 KREL7 MP7 (m7 & j1' & VIS7 & MU7 & WM7 & MI7 & SL7).
      assert (FWs7 : Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= bv_unsigned sp) \/ (as_FSB H <= fst iv /\ snd iv <= as_FSB H + AFS_SIZE)
                                                \/ (sh (as_FSB H) <= fst iv /\ snd iv <= sh (as_FSB H + AFS_SIZE))) [(S1, S1 + 344)]).
      { apply Forall_cons; [left; cbn [fst snd]; clear - CEIL LO STK0 Q2; lia| apply Forall_nil]. }
      pose proof (fsw_carry _ m6 m7 s4' ((p, A, 512 * 1) :: L0) FWs7 MU7 WM7 HP6 SQ4) as (HP7 & TAUX & TLM & Ts & Tb & Tby & Ta & Tacc & Terr & T0 & Tac & Tch & Txa & Tmb & Tms).
      pose proof (TAUX AUX6) as AUX7. pose proof (TLM _ M x LM6 CTX ltac:(intros b Hb; right; exact (SUBLB0 _ Hb)) ltac:(intros b Hb; right; exact (SUBE0 _ Hb))) as LM7.
      pose proof (Ts (S1 + 344) _ GP6 ltac:(clear - AS1; lia) ltac:(apply Forall_cons; [cbn [fst snd]; intros _; right; clear; lia| apply Forall_nil])) as GP7.
      pose proof (Ts (bv_unsigned sp + -104) _ SV6 ltac:(clear - AS1 Q2; lia) ltac:(apply Forall_cons; [cbn [fst snd]; intros _; right; clear - KGR; lia| apply Forall_nil])) as SV7.
      pose proof (Tb (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC6) as SC7.
      pose proof (Ta (es_id S, st, STORE_SIZE) st STORE_SIZE (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD6) as SAD7.
      pose proof (Tb (p, A, 512 * 1) A [CB (Z.to_nat (512 * 1)) (zeros (Z.to_nat (512 * 1)))] (or_introl eq_refl) ltac:(apply Z.le_refl) ltac:(cbn; clear; lia) ZK6) as ZK7.
      pose proof (Ta (p, A, 512 * 1) A (512 * 1) (or_introl eq_refl) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(clear; lia) AD6) as AD7.
      pose proof (Terr _ ERR6) as ERR7. pose proof (T0 ST06) as ST07. pose proof (Tac AC6) as AC7.
      pose proof (Tch _ _ (S1 + 344 + 16) CHN6 CHB3 ltac:(clear - AS1; lia) ltac:(apply Forall_cons; [cbn [fst snd]; intros _; clear; lia| apply Forall_nil])) as CHN7.
      assert (XA7 : xpres H LB (bv_unsigned sp) (XSF ff fp ++ MEMBIO_foot mb R) m m7).
      { apply Txa; [exact XA6|]. intros a Ra LOW. cbn [rin_ivs fst snd] in Ra. exfalso. clear - Ra LOW AS1. lia. }
      pose proof (Tmb R (mb_static_refl R) MBO6) as MBO7. pose proof (Tms R (mb_static_refl R) MBO6 MSH6) as MSH7.
      destruct (PAYL LPOS) as [pD [PIN PNL]].
      assert (DS7 : bytes_at asegs m7 (mb_buf R) ds).
      { eapply (Tby (pD, mb_buf R, mb_len R)); [exact (SQ4 _ PIN)| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DS6]. }
      assert (PAYa7 : accessible m7 (mb_buf R) (mb_len R)).
      { eapply (Tacc (pD, mb_buf R, mb_len R)); [exact (SQ4 _ PIN)| apply Z.le_refl| apply Z.le_refl| clear - LPOS; lia| exact (PAYa6 LPOS)]. }
      assert (FRM7 : rw_cells asegs m7 ff (arp_fframe S1 fk1 0 fk2 fp)).
      { eapply rw_cells_transport; [exact FRM6| exact MU7| exact WM7| cbn [disjoint_from]; split; [left; unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - FF6 AF2 AS1; lia| exact I]]. }
      assert (FSH7 : rw_cells asegs m7 (sh ff) (arp_fshadow (poison_bytes 4 0xf1) (b8 0xf8) (poison_bytes 3 0xf2) (b8 0xf8) (b8 0xf2) (poison_bytes 256 0xf8) (poison_bytes 16 0xf2) (b8 0) e5)).
      { eapply rw_cells_transport; [exact FSH6| exact MU7| exact WM7| cbn [disjoint_from]; split; [left; unfold arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SY2 SY3 SYA SHC AS1; lia| exact I]]. }
      assert (RFS7 : as_RFS H (LF1 ff fp) m7).
      { eapply (ah_RFS_frame H HH); [exact RFS6| exact MU7| exact WM7|]. apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE; clear - AF2 AS1 ACB; lia| apply Forall_nil]. }
      assert (STK7 : stk asegs m7 lo S1).
      { eapply stk_transport_disjoint; [exact STK6| exact MU7| exact WM7|]. cbn [disjoint_from]. split; [left; clear - AS1 CEIL; lia| exact I]. }
      clear TAUX TLM Ts Tb Tby Ta Tacc Terr T0 Tac Tch Txa Tmb Tms FWs7 AUX6 LM6 GP6 SV6 SC6 SAD6 ZK6 AD6 ERR6 ST06 CHN6 XA6 MBO6 MSH6 DS6 PAYa6 FRM6 FSH6 RFS6 STK6 SL6 MU7 WM7 HP6 MI6 AC6 VIS6 KREL6.
      pose proof LM7 as (IM7 & _ & _ & _ & _ & _ & _ & _ & GM7 & _ & _ & MM7 & _).
      pose proof (ah_mpres_trans H HH _ _ _ MPc6 MP7) as MPc7. clear MP7.
      (* [comment removed for export] *)
      pose proof FRM7 as FRq. unfold arp_fframe in FRq.
      change (rw_cells asegs m7 ff ([C8 (wz AFRAME_MAGIC); C8 (wz ARP_DESCR); C8 (wz P_ech_read_priv_echconfiglist); C8 (wz S1); CB 2224 fk1] ++ [C8 (wz 0)] ++ [CB 1824 fk2; C8 (wz fp)])) in FRq.
      apply (proj1 (rw_cells_app asegs m7 _ _ _)) in FRq. destruct FRq as [_ FRq]. apply (proj1 (rw_cells_app asegs m7 _ _ _)) in FRq. destruct FRq as [RB7 _].
      cbn [cells_size csize Nat.add app] in RB7. replace (ff + Z.of_nat 2256) with (ff + 2256) in RB7 by (clear; lia).
      pose proof FSH7 as SHq. unfold arp_fshadow in SHq.
      change (rw_cells asegs m7 (sh ff) ([CB 4 (poison_bytes 4 0xf1); C1 (b8 0xf8); CB 3 (poison_bytes 3 0xf2); C1 (b8 0xf8); C1 (b8 0xf2); CB 256 (poison_bytes 256 0xf8); CB 16 (poison_bytes 16 0xf2)] ++ [C1 (b8 0)] ++ [CB 229 e5])) in SHq.
      apply (proj1 (rw_cells_app asegs m7 _ _ _)) in SHq. destruct SHq as [_ SHq]. apply (proj1 (rw_cells_app asegs m7 _ _ _)) in SHq. destruct SHq as [SHB7 _].
      cbn [cells_size csize Nat.add app] in SHB7. replace (sh ff + Z.of_nat 282) with (sh (ff + 2256)) in SHB7 by (rewrite <- (sh_add8 ff 282); f_equal; clear; lia).
      destruct (rw_cells_CB_split asegs m7 A _ 0 _ ZK7 ltac:(clear; lia)) as [PRE7 _].
      assert (PAYL' : 1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB) by (intros _; exists pD; exact PIN).
      eapply (lad_loop H HX sp S1 gp F fc mb lo B R ds LB L0 m7 mo ff (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) (bv_unsigned ra) CH (as_AL H s4') (LF1 ff fp) fp
                MBB MBS DSL SUB0 PAYL') with (fuel := 32%nat) (k := 0) (s := s4') (p := p) (R' := R).
      * (* [comment removed for export] *) pose proof BUD as BUDq. unfold mid_bytes in BUDq. rewrite CTX in BUDq. cbn [ctxph_bytes] in BUDq. unfold DECODE_BYTES, ERRSTR_BYTES in BUDq. unfold L0. clear - BUDq EBR. lia.
      * (* [comment removed for export] *) pose proof BUDC as BUDq. unfold mid_cnt in BUDq. rewrite CTX in BUDq. cbn [ctxph_cnt] in BUDq. unfold DECODE_CNT, ERRSTR_CNT in BUDq. unfold L0. clear - BUDq ECR. lia.
      * (* [comment removed for export] *) pose proof ALW as ALq. unfold READCFG_COST in ALq.
        pose proof (CMadd (512 * 1) (lad_cm 32) ltac:(clear; lia) ltac:(unfold lad_cm; clear; lia)) as Y1.
        pose proof (CMmono (512 * 1 + lad_cm 32) DECODE_CUM_BYTES ltac:(unfold lad_cm, DECODE_CUM_BYTES; clear; lia)) as Y2.
        pose proof (CFmono (lad_cf 32) DECODE_CUM_BYTES ltac:(unfold lad_cf, DECODE_CUM_BYTES; clear; lia)) as Y3.
        pose proof (errph_cost_nonneg (mid_err M)) as Y4. clear - ALq AL4 Y1 Y2 Y3 Y4. lia.
      * exact SPB.
      * exact CEIL.
      * clear - Q2; lia.
      * exact Q1.
      * clear - LO STKL Q2; lia.
      * split; [clear - FF5; unfold AFS_HDR; lia| split; [clear - FF6; unfold AFS_SIZE; lia| clear - FF64; Z.div_mod_to_equations; lia]].
      * exact AFSB.
      * exact CHB.
      * apply pf_site; intros e He; unfold PF_readcfg, PF_read_priv; apply in_or_app; right; apply in_or_app; left; exact He.
      * left; reflexivity.
      * reflexivity.
      * clear; lia.
      * (* [comment removed for export] *) unfold LAD.
        split; [exact HP7|]. split; [exact MBO7|]. split; [apply mb_static_refl|]. split; [rewrite MP0; clear; lia|]. split; [clear - LPOS; lia|].
        split; [exact DS7|]. split; [exact PRE7|].
        split; [exists (zeros (Z.to_nat (512 * 1))); replace (A + 512 * 0) with A by (clear; lia); exact ZK7|].
        split; [exists 0; exact RB7|]. split; [exists errv4; exact ERR7|].
        split; [exact MM7|]. split; [exact IM7|]. split; [exact GM7|]. split; [exact MI7|]. split; [exact STK7|]. split; [exact AUX7|]. split; [apply xpres_refl|].
        split; [exact AC7|]. split; [exact RFS7|]. split; [exact AD7|]. split; [exact MSH7|].
        split; [split; [exact PAYa7| split; [exact (ah_blk_shvis H HH _ _ _ _ _ _ HP7 (or_intror (SUB0 _ PIN)))| destruct PAY as (_ & _ & Y3); exact Y3]]|].
        split; [exact SHB7|]. split; [exact CHN7|].
        split; [unfold lad_cm, lad_cf; replace (256 * 0 * (0 + 3)) with 0 by (clear; lia); replace (256 * 0 * (0 + 1)) with 0 by (clear; lia); clear - CMz CFz; lia|].
        destruct (slotsL_file_A _ _ _ _ _ _ _ _ _ _ SL7) as [SF7 SA7]. split; [exact SF7| eexists; exact SA7].
      * destruct (slotsL_file_A _ _ _ _ _ _ _ _ _ _ SL7) as [_ SA7]. exact SA7.
      * (* [comment removed for export] *) rewrite VIS7. unfold lad_entry, OSSL_ECH_BUFCHUNK. rewrite Z.mul_0_r, Z.add_0_r, Z.opp_0, Z.sub_0_r. reflexivity.
      * exact KREL7.
      * exact MPc7.
      * (* [comment removed for export] *)
        unfold lad_doneK.
        intros k n m9 msF9 mo9 s9' p9 A9 R9 junk s4v u0' u1' u2' b1' b2' b3' b4' b5' b6' b7' u3' u4' u5' u6' KR NEQ NR VIS9 HP9 KREL9 MP9 MBO9 MST9 POS9 DS9 DSA9 JK9 RBc9 [errv9 ERR9] ME9 IM9 GM9 MI9 ST9 AUX9 XP9 AC9 RF9 AD9 MSH9 PAY9 SHB9 CHN9 ALB9 FI9 AS9.
        pose proof (lad_exit_carry ff fp m7 m9 s4' ((p, A, 512 * 1) :: L0) FRESH XP9 HP7 ltac:(intros b Hb; right; exact Hb)) as (Xs & Xfrm & Xfsh & Xsc & Xsad & Xst0 & Xlm & Xxa).
        pose proof (slotsL_set_A m7 m9 S1 _ _ _ _ _ _ _ _ A9 SL7 Xs AS9) as SL9. pose proof (Xs _ _ GP7 ltac:(clear; lia) ltac:(right; clear; lia)) as GP9.
        pose proof (Xs _ _ SV7 ltac:(clear - Q2; lia) ltac:(right; clear - Q2; lia)) as SV9.
        pose proof (Xfrm fk1 fk2 0 n FRM7 RBc9) as FRM9. rewrite <- SHF in FSH7. pose proof (Xfsh _ _ _ _ _ _ _ _ _ _ FSH7 SHB9) as FSH9.
        pose proof (Xsc SC7) as SC9. pose proof (Xsad SAD7) as SAD9. pose proof (Xst0 ST07) as ST09. pose proof (Xlm LM7) as LM9. pose proof (Xxa XA7) as XA9.
        clear Xs Xfrm Xfsh Xsc Xsad Xst0 Xlm Xxa.
        assert (LED9 : LEDGER s9' (512 * 1 + lad_cm 32) (lad_cf 32)).
        { pose proof (CMadd (512 * 1) (lad_cm 32) ltac:(clear; lia) ltac:(unfold lad_cm; clear; lia)) as Y1.
          split; [unfold lad_cm; clear; lia| split; [unfold lad_cf; clear; lia| clear - ALB9 AL4 Y1; lia]]. }
        replace (ret_pc (Z_to_bv 64 ALD_RD)) with (Z_to_bv 64 ALD_RD) in VIS9 by (symmetry; apply ret_pc_even; [unfold ALD_RD; lia| reflexivity]).
        assert (RBD : ff + 2256 + 8 <= Z.shiftr ff 3 + ASHB \/ Z.shiftr ff 3 + ASHB + 512 <= ff + 2256).
        { rewrite SHF. pose proof (sh_aapp_range _ _ APff ltac:(clear; lia)) as (V1 & V2 & V3). unfold nsh in V2.
          unfold ALOWSH_LO, AHI_LO in NSff |- *. clear - NSff V1 V2 V3 SY3. assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in V1. unfold AHI_LO in V3. lia. }
        destruct (Z_lt_ge_dec (mb_len R) OSSL_ECH_MAX_ECHCONFIG_LEN) as [GOK|GBIG].
        -- (* [comment removed for export] *)
           eapply (ahh_evt_then H HH); [exact KREL9| exact VIS9| eapply ald_segE_ok with (K := 512 * k) (n := n) (rbp := ff + 2256) (e := 1);
             [clear; lia| clear - NR; lia| clear - KR; lia| rewrite NEQ; unfold OSSL_ECH_MAX_ECHCONFIG_LEN in *; clear - GOK KR; lia| clear - FF1; lia| clear - FF2 ACB; lia
             | clear - FF1; unfold AIMG_TOP; lia| exact FF2| exact APff| exact RBD| exact RBc9| exact FSH9| exact MI9]|].
           intros msF10 mo10 KREL10 MP10 (m10 & VIS10 & MU10 & WM10 & MI10 & RBc10 & FSH10).
           rewrite SHF in MU10.
           pose proof (poke_carry ff fp m9 m10 s9' ((p9, A9, 512 * (k + 1)) :: L0) 282 FRESH ltac:(clear; lia) ltac:(replace (sh ff + 282 + 1) with (sh ff + 283) by (clear; lia); exact MU10) WM10 HP9)
             as (HP10 & TAUX & TRFS & TLM & Tstk & Tff & Tblk & Tbytes & Tad & Terr & Tst0 & Tac & Tstk2 & Tch & Tacc & Txa & Tmb & Tms).
           replace (n + 512 * k) with (mb_len R) in VIS10 by (clear - NEQ; lia).
           unfold rp_okK in KOK.
           eapply (KOK k n m10 msF10 mo10 s9' p9 A9 R9 junk ff fp fk1 fk2 jg j0 j1' (skipn 8 j3) j4 e5 (512 * 1 + lad_cm 32) (lad_cf 32)).
           all: try first [exact KR| exact NEQ| exact NR| exact GOK| exact VIS10| exact HP10| exact KREL10| exact MI10| exact MST9| exact POS9| exact FSH10| exact LED9].
           all: lazymatch goal with
                | |- as_MPRES _ _ _ => eapply (ah_mpres_trans H HH); [exact MP9| exact MP10]
                | |- ACONST _ => exact (Tac AC9)
                | |- bytes_at asegs _ (mb_buf R) ds => eapply (Tbytes (pD, mb_buf R, mb_len R)); [right; exact (SUB0 _ PIN)| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DS9]
                | |- bytes_at asegs _ _ ds => eapply (Tbytes (p9, A9, 512 * (k + 1))); [left; reflexivity| apply Z.le_refl| cbn; unfold zlength in DSL; rewrite DSL; clear - NEQ NR KR; lia| exact DSA9]
                | |- rw_cells asegs _ _ [CB _ ds; CB _ _] => eapply (Tblk (p9, A9, 512 * (k + 1))); [left; reflexivity| apply Z.le_refl| cbn; clear - NEQ NR KR; lia| exact JK9]
                | |- addressable _ st _ => exact (Tad (es_id S, st, STORE_SIZE) st STORE_SIZE (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD9)
                | |- addressable _ _ _ => eapply (Tad (p9, A9, 512 * (k + 1))); [left; reflexivity| apply Z.le_refl| apply Z.le_refl| clear - KR; lia| exact AD9]
                | |- MEMBIO H LB _ mb _ => exact (Tmb R9 ltac:(intros b Hb; right; exact (SUB0 _ Hb)) MST9 MBO9)
                | |- MEMBIO_shad _ mb _ => exact (Tms R9 ltac:(intros b Hb; right; exact (SUB0 _ Hb)) MST9 MBO9 MSH9)
                | |- PAYLOAD_shad _ R => destruct PAY9 as (Y1 & Y2 & Y3); split; [eapply (Tacc (pD, mb_buf R, mb_len R)); [right; exact (SUB0 _ PIN)| apply Z.le_refl| apply Z.le_refl| clear - LPOS; lia| exact Y1]
                                             | split; [exact (ah_blk_shvis H HH _ _ _ _ _ _ HP10 (or_intror (SUB0 _ PIN)))| exact Y3]]
                | |- stk asegs _ lo S1 => exact (Tstk2 _ _ ST9 CEIL)
                | |- stack0 _ _ _ => exact (Tst0 ST09)
                | |- rw_cells asegs _ S1 _ => exact (Tstk _ _ SL9 AS1)
                | |- rw_cells asegs _ (S1 + 344) _ => exact (Tstk _ _ GP9 ltac:(clear - AS1; lia))
                | |- rw_cells asegs _ (bv_unsigned sp + -104) _ => exact (Tstk _ _ SV9 ltac:(clear - AS1 Q2; lia))
                | |- rw_cells asegs _ _ (arp_fframe _ _ _ _ _) => exact (Tff _ FRM9 ltac:(unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia))
                | |- as_RFS H _ _ => exact (TRFS RF9)
                | |- rw_cells asegs _ (errno_addr _) _ => exact (Terr _ ERR9)
                | |- as_rauxv_ok H _ B => exact (TAUX AUX9)
                | |- LIBMID LIB _ M => exact (TLM LIB M x LM9 CTX ltac:(intros b Hb; right; exact (SUBLB0 _ Hb)) ltac:(intros b Hb; right; exact (SUBE0 _ Hb)))
                | |- rw_cells asegs _ st _ => exact (Tblk (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC9)
                | |- STORE_shad _ st S => rewrite SEQ; apply (proj2 (STORE_shad_empty _ _ _)); split; [exact SHhi| exact (Tad (es_id S, st, STORE_SIZE) st STORE_SIZE (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD9)]
                | |- as_chain H _ _ _ => exact (Tch _ _ CHN9 CHB1)
                | |- xpres H LB _ _ m _ => apply (Txa _ _ XA9); intros a Ha; apply rin_ivs_app; left; unfold XSF; cbn [rin_ivs fst snd]; right; right; right; left; change (fshn 6) with 512; clear - Ha; lia
                | |- _ <= 512 + lad_cm 32 => clear; lia
                | |- _ <= lad_cf 32 => apply Z.le_refl
                | |- ?G => idtac "B2B_KOK_LEFT" G
                end.
        -- (* [comment removed for export] *)
           eapply (ahh_evt_then H HH); [exact KREL9| exact VIS9| eapply ald_segE_big with (K := 512 * k) (n := n) (rbp := ff + 2256) (e := 1);
             [clear; lia| clear - NR; lia| clear - KR; lia| rewrite NEQ; unfold OSSL_ECH_MAX_ECHCONFIG_LEN in *; clear - GBIG KR; lia| clear - FF1; lia| clear - FF2 ACB; lia
             | clear - FF1; unfold AIMG_TOP; lia| exact FF2| exact APff| exact RBD| exact RBc9| exact FSH9| exact MI9]|].
           intros msF10 mo10 KREL10 MP10 (m10 & VIS10 & MU10 & WM10 & MI10 & RBc10 & FSH10).
           rewrite SHF in MU10.
           pose proof (poke_carry ff fp m9 m10 s9' ((p9, A9, 512 * (k + 1)) :: L0) 282 FRESH ltac:(clear; lia) ltac:(replace (sh ff + 282 + 1) with (sh ff + 283) by (clear; lia); exact MU10) WM10 HP9)
             as (HP10 & TAUX & TRFS & TLM & Tstk & Tff & Tblk & Tbytes & Tad & Terr & Tst0 & Tac & Tstk2 & Tch & Tacc & Txa & Tmb & Tms).
           (* [comment removed for export] *)
           pose proof (Tblk (p9, A9, 512 * (k + 1)) A9 [CB (Z.to_nat (mb_len R)) ds; CB (Z.to_nat (512 * (k + 1) - mb_len R)) junk] (or_introl eq_refl) ltac:(apply Z.le_refl)
                         ltac:(cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; clear - NEQ NR KR; lia) JK9) as JK10.
           pose proof (rw_cells_CB_join asegs m10 A9 _ _ _ _ (proj1 (proj1 (rw_cells_app asegs m10 A9 [CB (Z.to_nat (mb_len R)) ds] [CB (Z.to_nat (512 * (k + 1) - mb_len R)) junk]) JK10))
                         ltac:(pose proof (proj2 (proj1 (rw_cells_app asegs m10 A9 [CB (Z.to_nat (mb_len R)) ds] [CB (Z.to_nat (512 * (k + 1) - mb_len R)) junk]) JK10)) as K2;
                               cbn [cells_size csize Nat.add] in K2; rewrite Nat.add_0_r in K2; exact K2)) as LBc10.
           replace (Z.to_nat (mb_len R) + Z.to_nat (512 * (k + 1) - mb_len R))%nat with (Z.to_nat (512 * (k + 1))) in LBc10 by (clear - NEQ NR KR; lia).
           pose proof (Tstk _ _ SL9 AS1) as SL10.
        destruct (arp_slots_split m10 S1 j0 j1' (skipn 8 j3) j4 st ff (Z.shiftr ff 3 + ASHB) A9 SL10)
          as (w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w192 & w200 & w208 & w224 & w232 & w240 & w248 & w256 & w264 & w272 & w280 & w288 & w296 & w304 & w312 & w320 & w328 & w336 & P0 & P1 & P2 & P3).
        unfold arp_sg2L in P2.
        assert (SLX : rw_cells asegs m10 S1 ((CB 16 j0 :: arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (wz 0) (wz (ff + 80)) (wz (ff + 64)) (wz 0) (wz st) (wz (ff + 32)))
                         ++ arp_sg2 (wz (Z.shiftr ff 3 + ASHB + 10)) (wz ff) (wz ff) (wz ARP_FILE) (wz ASHB) (wz A9) w192 w200 w208 (wz ff) w224 w232
                         ++ arp_sg3 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336)).
        { change (rw_cells asegs m10 S1 ([CB 16 j0] ++ (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (wz 0) (wz (ff + 80)) (wz (ff + 64)) (wz 0) (wz st) (wz (ff + 32))
                         ++ (arp_sg2 (wz (Z.shiftr ff 3 + ASHB + 10)) (wz ff) (wz ff) (wz ARP_FILE) (wz ASHB) (wz A9) w192 w200 w208 (wz ff) w224 w232
                         ++ arp_sg3 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336)))).
          apply (proj2 (rw_cells_app asegs m10 S1 _ _)). split; [exact P0|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 16) with 16.
          apply (proj2 (rw_cells_app asegs m10 (S1 + 16) _ _)). split; [exact P1|]. unfold arp_sg1. cbn [cells_size csize Nat.add]. replace (S1 + 16 + Z.of_nat 128) with (S1 + 144) by (clear; lia).
          apply (proj2 (rw_cells_app asegs m10 (S1 + 144) _ _)). split; [exact P2|]. unfold arp_sg2. cbn [cells_size csize Nat.add]. replace (S1 + 144 + Z.of_nat 96) with (S1 + 240) by (clear; lia).
          exact P3. }
        clear P0 P1 P2 P3 SL10.
        eapply (rp_fail599 m10 msF10 mo10 s9' p9 A9 (512 * (k + 1)) (ds ++ junk) R9 ff fp n fk1 fk2 jg
                  (CB 16 j0 :: arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (wz 0) (wz (ff + 80)) (wz (ff + 64)) (wz 0) (wz st) (wz (ff + 32)))
                  (arp_sg3 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336)
                  (wz (Z.shiftr ff 3 + ASHB + 10)) (wz ARP_FILE) (wz ASHB) w192 w200 w208 (wz ff) w224 w232 (512 * 1 + lad_cm 32) (lad_cf 32)).
           all: try first [exact VIS10| exact HP10| exact KREL10| exact MI10| exact MST9| exact FSH10| exact LED9| exact LBc10| exact SLX].
           all: lazymatch goal with
                | |- as_MPRES _ _ _ => eapply (ah_mpres_trans H HH); [exact MP9| exact MP10]
                | |- ACONST _ => exact (Tac AC9)
                | |- 0 <= 512 * (_ + 1) <= _ => clear - KR; lia
                | |- addressable _ st _ => exact (Tad (es_id S, st, STORE_SIZE) st STORE_SIZE (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD9)
                | |- addressable _ _ _ => eapply (Tad (p9, A9, 512 * (k + 1))); [left; reflexivity| apply Z.le_refl| apply Z.le_refl| clear - KR; lia| exact AD9]
                | |- MEMBIO H LB _ mb _ => exact (Tmb R9 ltac:(intros b Hb; right; exact (SUB0 _ Hb)) MST9 MBO9)
                | |- MEMBIO_shad _ mb _ => exact (Tms R9 ltac:(intros b Hb; right; exact (SUB0 _ Hb)) MST9 MBO9 MSH9)
                | |- bytes_at asegs _ (mb_buf R) ds => eapply (Tbytes (pD, mb_buf R, mb_len R)); [right; exact (SUB0 _ PIN)| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DS9]
                | |- stk asegs _ lo S1 => exact (Tstk2 _ _ ST9 CEIL)
                | |- stack0 _ _ _ => exact (Tst0 ST09)
                | |- cells_size (CB 16 _ :: _) = _ => unfold arp_sg1; reflexivity
             | |- cells_size (arp_sg3 _ _ _ _ _ _ _ _ _ _ _ _ _) = _ => reflexivity
                | |- cells_size (arp_sg3 _ _ _ _ _ _ _ _ _) = _ => unfold arp_sg3; reflexivity
                | |- rw_cells asegs _ (S1 + 344) _ => exact (Tstk _ _ GP9 ltac:(clear - AS1; lia))
                | |- rw_cells asegs _ (bv_unsigned sp + -104) _ => exact (Tstk _ _ SV9 ltac:(clear - AS1 Q2; lia))
                | |- rw_cells asegs _ _ (arp_fframe _ _ _ _ _) => exact (Tff _ FRM9 ltac:(unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia))
                | |- as_RFS H _ _ => exact (TRFS RF9)
                | |- rw_cells asegs _ (errno_addr _) _ => exact (Terr _ ERR9)
                | |- as_rauxv_ok H _ B => exact (TAUX AUX9)
                | |- LIBMID LIB _ M => exact (TLM LIB M x LM9 CTX ltac:(intros b Hb; right; exact (SUBLB0 _ Hb)) ltac:(intros b Hb; right; exact (SUBE0 _ Hb)))
                | |- rw_cells asegs _ st _ => exact (Tblk (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC9)
                | |- STORE_shad _ st S => rewrite SEQ; apply (proj2 (STORE_shad_empty _ _ _)); split; [exact SHhi| exact (Tad (es_id S, st, STORE_SIZE) st STORE_SIZE (or_intror SIN) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD9)]
                | |- as_chain H _ _ _ => exact (Tch _ _ CHN9 CHB1)
                | |- xpres H LB _ _ m _ => apply (Txa _ _ XA9); intros a Ha; apply rin_ivs_app; left; unfold XSF; cbn [rin_ivs fst snd]; right; right; right; left; change (fshn 6) with 512; clear - Ha; lia
                | |- _ <= DECODE_CUM_BYTES => unfold lad_cm, lad_cf, DECODE_CUM_BYTES; clear - KR; lia
                | |- ?G => idtac "B2B_F599_LEFT" G
                end.
      * (* [comment removed for export] *)
        unfold lad_capK.
        intros m9 msF9 mo9 s9' p9 A9 rv R9 u0' u1' u2' b1' b2' b3' b4' b5' b6' b7' s5v s7v s10v s11v u3' u4' u5' u6' VIS9 HP9 KREL9 MP9 MBO9 MST9 POS9 KL9 DS9 [junk JK9] [rb9 RBc9] [errv9 ERR9] ME9 IM9 GM9 MI9 ST9 AUX9 XP9 AC9 RF9 AD9 MSH9 PAY9 SHB9 CHN9 ALB9 FI9 AS9.
        pose proof (lad_exit_carry ff fp m7 m9 s4' ((p, A, 512 * 1) :: L0) FRESH XP9 HP7 ltac:(intros b Hb; right; exact Hb)) as (Xs & Xfrm & Xfsh & Xsc & Xsad & Xst0 & Xlm & Xxa).
        pose proof (slotsL_set_A m7 m9 S1 _ _ _ _ _ _ _ _ A9 SL7 Xs AS9) as SL9. pose proof (Xs _ _ GP7 ltac:(clear; lia) ltac:(right; clear; lia)) as GP9.
        pose proof (Xs _ _ SV7 ltac:(clear - Q2; lia) ltac:(right; clear - Q2; lia)) as SV9.
        pose proof (Xfrm fk1 fk2 0 rb9 FRM7 RBc9) as FRM9. rewrite <- SHF in FSH7. pose proof (Xfsh _ _ _ _ _ _ _ _ _ _ FSH7 SHB9) as FSH9.
        pose proof (Xsc SC7) as SC9. pose proof (Xsad SAD7) as SAD9. pose proof (Xst0 ST07) as ST09. pose proof (Xlm LM7) as LM9. pose proof (Xxa XA7) as XA9.
        clear Xs Xfrm Xfsh Xsc Xsad Xst0 Xlm Xxa.
        assert (LED9 : LEDGER s9' (512 * 1 + lad_cm 32) (lad_cf 32)).
        { pose proof (CMadd (512 * 1) (lad_cm 32) ltac:(clear; lia) ltac:(unfold lad_cm; clear; lia)) as Y1.
          split; [unfold lad_cm; clear; lia| split; [unfold lad_cf; clear; lia| clear - ALB9 AL4 Y1; lia]]. }
        replace (ret_pc (Z_to_bv 64 ALD_RC)) with (Z_to_bv 64 ALD_RC) in VIS9 by (symmetry; apply ret_pc_even; [unfold ALD_RC; lia| reflexivity]).
        eapply (ahh_evt_then H HH); [exact KREL9| exact VIS9| eapply ald_segc2; exact MI9|]. intros msF10 mo10 KREL10 MP10 VIS10. cbn beta in VIS10.
        eapply (rp_fail595 m9 msF10 mo10 s9' p9 A9 (512 * 33) junk R9 ff fp rb9 fk1 fk2 jg
                [CB 16 j0; CB 80 j1'; C8 (wz 0); C8 (wz (ff + 80)); C8 (wz (ff + 64)); C8 (wz 0); C8 (wz st); C8 (wz (ff + 32)); C8 (wz (Z.shiftr ff 3 + ASHB + 10))]
                [C8 (wz ARP_FILE); C8 (wz ASHB); C8 (wz A9); CB 24 (skipn 8 j3); C8 (wz ff); CB 120 j4]
                _ _ _ _ _ _ _ _ _ (512 * 1 + lad_cm 32) (lad_cf 32)).
        all: try first [exact VIS10| exact HP9| exact KREL10| exact MI9| exact AC9| exact JK9| exact AD9| exact MBO9| exact MSH9| exact MST9| exact DS9| exact ST9| exact ST09| exact SL9| exact GP9| exact SV9| exact FRM9| exact FSH9
                        | exact RF9| exact ERR9| exact AUX9| exact LM9| exact SC9| exact CHN9| exact XA9| exact LED9].
        all: lazymatch goal with
             | |- rw_cells asegs _ S1 (_ ++ _ ++ _) => unfold arp_slotsL in SL9; cbn [app]; exact SL9
             | |- as_MPRES _ _ _ => eapply (ah_mpres_trans H HH); [exact MP9| exact MP10]
             | |- 0 <= 512 * 33 <= _ => clear; lia
             | |- cells_size _ = _ => reflexivity
             | |- STORE_shad _ _ _ => rewrite SEQ; apply (proj2 (STORE_shad_empty _ _ _)); split; [exact SHhi| exact SAD9]
             | |- _ <= DECODE_CUM_BYTES => unfold lad_cm, lad_cf, DECODE_CUM_BYTES; clear; lia
             | |- ?G => idtac "B2B_CAP_LEFT" G
             end.
  Qed.
End RC.

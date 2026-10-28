(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AKit
  ECH_AStmt_C4.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Definition low_ok (iv : Z * Z) : Prop :=
    snd iv <= AIMG_TOP /\ Forall (fun x : Z * Z => snd iv <= fst x \/ snd x <= fst iv) LIBX.
  Definition scr_ok (LF : list fframe) (iv : Z * Z) : Prop := fs_scratch H LF iv \/ low_ok iv.

  Lemma scr_ok_of_scratch : forall LF XS, Forall (fs_scratch H LF) XS -> Forall (scr_ok LF) XS.
  Proof. intros LF XS FA. eapply Forall_impl; [| exact FA]. intros iv K. left. exact K. Qed.

  Lemma errno_low_ok : low_ok (ARERRNO, ARERRNO + 4).
  Proof.
    unfold low_ok, ARERRNO, ATP, AIMG_TOP, LIBX, LIBX0, LIBXW. cbn [fst snd app].
    split; [lia|]. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
  Qed.
  Lemma scr_ok_errno : forall LF, Forall (scr_ok LF) ERRNO_X.
  Proof. intros LF. apply Forall_cons; [right; apply errno_low_ok| apply Forall_nil]. Qed.

  Lemma rin_ivs_Forall_off : forall X (iv : Z * Z) a,
    Forall (fun x : Z * Z => snd iv <= fst x \/ snd x <= fst iv) X -> rin_ivs X a -> ~ (fst iv <= a < snd iv).
  Proof.
    intros X iv a FA. induction X as [|x X IH]; [intros []|]. cbn. intros [K|K].
    - pose proof (Forall_inv FA) as F1. cbn in F1. lia.
    - exact (IH (Forall_inv_tail FA) K).
  Qed.

  (* [comment removed for export] *)
  Lemma scr_ok_obj : forall LF m0 iv O n,
    as_RFS H LF m0 -> scr_ok LF iv -> ablock_range H O n -> 0 <= n ->
    (O + n <= fst iv \/ snd iv <= O) /\ (sh O + nsh n <= fst iv \/ snd iv <= sh O).
  Proof.
    intros LF m0 iv O n R SC (B1 & B2 & B3 & B4 & B5 & B6 & B7) Hn.
    pose proof (aapp_bounds _ _ B7 Hn) as (Q1 & Q2 & Q3 & Q4 & Q5).
    assert (OB : fsobj H LF O n) by (left; lia).
    destruct SC as [SC|[L1 L2]].
    - split; [eapply (fsobj_scratch H HH); [exact R| exact OB| lia| lia| lia| exact B7| exact SC]
             | eapply (fsobj_scratch_sh H HH); [exact R| exact OB| lia| lia| lia| exact SC]].
    - pose proof (sh_aapp_range _ _ B7 Hn) as (S1 & _). assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
      unfold AIMG_TOP in *. cbn [fst snd] in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma scr_ok_libx : forall LF m0 iv a, as_RFS H LF m0 -> scr_ok LF iv -> rin_ivs LIBX a -> ~ (fst iv <= a < snd iv).
  Proof.
    intros LF m0 iv a R SC HX. pose proof (LIBX_below _ HX) as LA.
    destruct SC as [[->|(k & ff & fp & FF & E)]|[L1 L2]].
    - cbn. pose proof (RFS_fsb H HH _ _ R) as (F1 & _). lia.
    - pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. pose proof (sh_mono AIMG_TOP ff ltac:(unfold AFS_HDR in R1; lia)) as SM.
      destruct E as [->|[->| ->]]; cbn; unfold AIMG_TOP, AFS_HDR, AFS_FLAGS in *; lia.
    - eapply rin_ivs_Forall_off; [exact L2| exact HX].
  Qed.

  (* [comment removed for export] *)
  Lemma lib_magree_scratch : forall LF m0 L lo hi W m m',
    as_RFS H LF m0 -> Forall (fun b => ablock_range H (blk_addr b) (blk_size b)) L ->
    munch ((lo, hi) :: W) m m' -> wmono asegs m m' -> aceil <= lo -> Forall (scr_ok LF) W ->
    magree (lib_addr L) m m'.
  Proof.
    intros LF m0 L lo hi W m m' R PL MU WM CE FW. acb.
    eapply magree_of_munch; [exact MU| exact WM|].
    intros a Ha. clear MU WM. cbn. split.
    - destruct Ha as [HX|[(b & Hb & Hr)|(b & Hb & Hr)]].
      + pose proof (LIBX_below _ HX). unfold AIMG_TOP in *. lia.
      + pose proof (proj1 (Forall_forall _ _) PL _ Hb) as BR. destruct BR as (_ & _ & _ & _ & B5 & _). lia.
      + pose proof (proj1 (Forall_forall _ _) PL _ Hb) as BR. destruct BR as (_ & _ & B3 & _ & _ & _ & B7).
        pose proof (sh_aapp_range _ _ B7 B3) as (_ & S2 & _).
        assert (SC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; lia). lia.
    - induction W as [|iv W IH]; [exact I|]. destruct iv as [wl wh]. cbn. split; [| exact (IH (Forall_inv_tail FW))].
      pose proof (Forall_inv FW) as SC.
      destruct Ha as [HX|[(b & Hb & Hr)|(b & Hb & Hr)]].
      + exact (scr_ok_libx _ _ _ _ R SC HX).
      + pose proof (proj1 (Forall_forall _ _) PL _ Hb) as BR. pose proof BR as (_ & _ & B3 & _).
        pose proof (scr_ok_obj _ _ _ _ _ R SC BR B3) as [D _]. cbn [fst snd] in D. lia.
      + pose proof (proj1 (Forall_forall _ _) PL _ Hb) as BR. pose proof BR as (_ & _ & B3 & _).
        pose proof (scr_ok_obj _ _ _ _ _ R SC BR B3) as [_ D]. cbn [fst snd] in D. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_scratch_hi : forall LF m0 lo hi W m m' A cs,
    rw_cells asegs m A cs -> munch ((lo, hi) :: W) m m' -> wmono asegs m m' -> aceil <= lo -> lo <= hi -> hi <= A ->
    as_RFS H LF m0 -> Forall (scr_ok LF) W -> rw_cells asegs m' A cs.
  Proof.
    intros LF m0 lo hi W m m' A cs RC MU WM CE LH HA R FW. acb.
    eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. cbn. split; [lia|]. clear MU WM.
    induction W as [|[wl wh] W IH]; [exact I|]. cbn. split; [| exact (IH (Forall_inv_tail FW))].
    pose proof (Forall_inv FW) as SC. destruct SC as [SC|[L1 L2]].
    - pose proof (fs_scratch_range H HH _ _ _ R SC) as K. cbn [fst snd] in K. lia.
    - cbn [fst snd] in L1. unfold AIMG_TOP in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_scratch_img : forall LF m0 lo hi W m m' A cs,
    rw_cells asegs m A cs -> munch ((lo, hi) :: W) m m' -> wmono asegs m m' -> aceil <= lo -> A + Z.of_nat (cells_size cs) <= AIMG_TOP ->
    as_RFS H LF m0 -> Forall (scr_ok LF) W ->
    Forall (fun iv : Z * Z => low_ok iv -> A + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= A) W ->
    rw_cells asegs m' A cs.
  Proof.
    intros LF m0 lo hi W m m' A cs RC MU WM CE HA R FW FL. acb.
    eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. cbn. split; [unfold AIMG_TOP in *; lia|]. clear MU WM.
    induction W as [|[wl wh] W IH]; [exact I|]. cbn. split; [| exact (IH (Forall_inv_tail FW) (Forall_inv_tail FL))].
    pose proof (Forall_inv FW) as SC. destruct SC as [SC|LW].
    - pose proof (fs_scratch_range H HH _ _ _ R SC) as K. cbn [fst snd] in K. lia.
    - pose proof (Forall_inv FL LW) as K. cbn [fst snd] in K. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma disjoint_scratch_img : forall LF m0 lo hi W A n,
    as_RFS H LF m0 -> Forall (scr_ok LF) W -> aceil <= lo -> A + n <= AIMG_TOP ->
    Forall (fun iv : Z * Z => low_ok iv -> A + n <= fst iv \/ snd iv <= A) W -> disjoint_from ((lo, hi) :: W) A n.
  Proof.
    intros LF m0 lo hi W A n R FW CE HA FL. acb. cbn. split; [unfold AIMG_TOP in *; lia|].
    induction W as [|[wl wh] W IH]; [exact I|]. cbn. split; [| exact (IH (Forall_inv_tail FW) (Forall_inv_tail FL))].
    pose proof (Forall_inv FW) as SC. destruct SC as [SC|LW].
    - pose proof (fs_scratch_range H HH _ _ _ R SC) as K. cbn [fst snd] in K. lia.
    - pose proof (Forall_inv FL LW) as K. cbn [fst snd] in K. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma low_img_scratch : forall LF m0 XS A n,
    as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> A + n <= AIMG_TOP ->
    Forall (fun iv : Z * Z => low_ok iv -> A + n <= fst iv \/ snd iv <= A) XS.
  Proof.
    intros LF m0 XS A n R FXS HA. eapply Forall_impl; [| exact FXS]. intros iv SC _.
    pose proof (fs_scratch_range H HH _ _ _ R SC) as K. lia.
  Qed.
  Lemma low_img_errno : forall A n, (A + n <= ARERRNO \/ ARERRNO + 4 <= A) ->
    Forall (fun iv : Z * Z => low_ok iv -> A + n <= fst iv \/ snd iv <= A) ERRNO_X.
  Proof. intros A n HA. apply Forall_cons; [| apply Forall_nil]. intros _. cbn [fst snd]. lia. Qed.

  (* [comment removed for export] *)
  Lemma write_ok_scratch : forall LF LB lo hi XS,
    Forall (fs_scratch H LF) XS -> aceil <= lo -> Forall (aclient_write_ok H LB) ((lo, hi) :: XS ++ ERRNO_X).
  Proof.
    intros LF LB lo hi XS FXS CE. apply Forall_cons; [left; cbn [fst snd]; exact CE|].
    apply Forall_app. split; [eapply (fs_scratch_write_ok_Forall H); exact FXS|].
    apply Forall_cons; [| apply Forall_nil]. right; left. unfold aimg_client_w, ARERRNO, ATLS_PRIV_LO, ATP. cbn [fst snd]. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dj_cons : forall lo hi W A n, (A + n <= lo \/ hi <= A) -> disjoint_from W A n -> disjoint_from ((lo, hi) :: W) A n.
  Proof. intros. cbn. split; assumption. Qed.
  Lemma dj_app : forall W1 W2 A n, disjoint_from W1 A n -> disjoint_from W2 A n -> disjoint_from (W1 ++ W2) A n.
  Proof. intros W1 W2 A n D1 D2. induction W1 as [|[lo hi] W1 IH]; [exact D2|]. cbn in D1 |- *. destruct D1 as [K D1]. split; [exact K| exact (IH D1)]. Qed.
  Lemma dj_nil : forall A n, disjoint_from [] A n.
  Proof. intros. exact I. Qed.
  Lemma dj_of_Forall : forall XS A n, Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) XS -> disjoint_from XS A n.
  Proof.
    intros XS A n FA. induction XS as [|[lo hi] XS IH]; [exact I|]. cbn. pose proof (Forall_inv FA) as K. cbn in K.
    split; [exact K| exact (IH (Forall_inv_tail FA))].
  Qed.

  Lemma dj_scratch_placed : forall LF m0 XS B k A n,
    as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> ablock_range H B k -> B <= A -> A + n <= B + k -> disjoint_from XS A n.
  Proof.
    intros LF m0 XS B k A n R FXS BR HA HB. apply dj_of_Forall. eapply Forall_impl; [| exact FXS]. intros iv SC.
    pose proof BR as (_ & _ & B3 & _). pose proof (scr_ok_obj _ _ _ _ _ R (or_introl SC) BR B3) as [D _]. lia.
  Qed.
  Lemma dj_scratch_placed_sh : forall LF m0 XS B k A n,
    as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> ablock_range H B k -> sh B <= A -> A + n <= sh B + nsh k -> disjoint_from XS A n.
  Proof.
    intros LF m0 XS B k A n R FXS BR HA HB. apply dj_of_Forall. eapply Forall_impl; [| exact FXS]. intros iv SC.
    pose proof BR as (_ & _ & B3 & _). pose proof (scr_ok_obj _ _ _ _ _ R (or_introl SC) BR B3) as [_ D]. lia.
  Qed.
  Lemma dj_scratch_hi : forall LF m0 XS A n, as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> aceil <= A -> disjoint_from XS A n.
  Proof.
    intros LF m0 XS A n R FXS HA. apply dj_of_Forall. eapply Forall_impl; [| exact FXS]. intros iv SC.
    pose proof (fs_scratch_range H HH _ _ _ R SC). lia.
  Qed.
  Lemma dj_scratch_img : forall LF m0 XS A n, as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> A + n <= AIMG_TOP -> disjoint_from XS A n.
  Proof.
    intros LF m0 XS A n R FXS HA. apply dj_of_Forall. eapply Forall_impl; [| exact FXS]. intros iv SC.
    pose proof (fs_scratch_range H HH _ _ _ R SC). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma live_frame_facts : forall LF m0 k ff fp, as_RFS H LF m0 -> In (k, ff, fp) LF ->
    0 <= k <= 10 /\ as_FSB H + AFS_HDR <= ff /\ ff + fsz k <= as_FSB H + AFS_SIZE /\ ff mod fsz k = 0 /\ ff mod 8 = 0
    /\ as_FSB H + AFS_FLAGS <= fp /\ fp < as_FSB H + AFS_HDR
    /\ AIMG_TOP <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil /\ aapp (as_FSB H) AFS_SIZE.
  Proof.
    intros LF m0 k ff fp R IN. pose proof (ah_RFS_range H HH _ _ R) as [(F1 & F2 & F3 & F4) FR].
    pose proof (FR _ IN) as (K & R1 & R2 & R3 & R4). cbn [ff_class ff_addr ff_flag fst snd] in K, R1, R2, R3, R4.
    assert (M8 : ff mod 8 = 0).
    { unfold fsz in R3. pose proof (Z.pow_nonneg 2 k ltac:(lia)) as P.
      apply Z.mod_divide in R3; [| pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)); lia]. destruct R3 as [q Hq].
      apply Z.mod_divide; [lia|]. exists (q * 8 * 2 ^ k). lia. }
    repeat split; try assumption; lia.
  Qed.
  Lemma scratch_off_live : forall LF m0 k ff fp iv, as_RFS H LF m0 -> In (k, ff, fp) LF -> fs_scratch H LF iv ->
       (ff + fsz k <= fst iv \/ snd iv <= ff)
    /\ (sh ff + fshn k <= fst iv \/ snd iv <= sh ff)
    /\ (fp + 1 <= fst iv \/ snd iv <= fp).
  Proof.
    intros LF m0 k ff fp iv R IN SC. acb.
    pose proof (live_frame_facts _ _ _ _ _ R IN) as (K & R1 & R2 & R3 & M8 & R4 & R5 & F1 & F2 & F4).
    pose proof (fsz_pos k ltac:(lia)) as FZ.
    unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in *.
    assert (APF : aapp ff (fsz k)) by (eapply aapp_sub; [exact F4| lia| lia]).
    assert (APP : aapp fp 1) by (eapply aapp_sub; [exact F4| lia| lia]).
    pose proof (aapp_bounds _ _ APF ltac:(lia)) as (_ & _ & T1 & T0 & _). unfold AAPP_HI in T1.
    rewrite (fshn_nsh k) by lia.
    destruct SC as [->|(k' & ff' & fp' & FF & E)].
    - cbn [fst snd]. pose proof (aapp_disjoint_sh (as_FSB H) 11571200 ff (fsz k) F4 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as S1. unfold AFS_FLAGS. lia.
    - pose proof FF as (_ & _ & FFL). destruct (FFL _ IN) as [D1 D2]. cbn [ff_addr ff_class ff_flag fst snd] in D1, D2.
      pose proof (fresh_frame_facts H _ _ _ _ FF) as (K' & Q1 & Q2 & M64' & M8' & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in K', Q1, Q2, P1, P2, P3, P4, P5, P6, P7, P8, P9.
      pose proof (fsz_pos k' ltac:(lia)) as FZ'.
      assert (APF' : aapp ff' (fsz k')) by (eapply aapp_sub; [exact P9| lia| lia]).
      assert (APP' : aapp fp' 1) by (eapply aapp_sub; [exact P9| lia| lia]).
      pose proof (aapp_bounds _ _ APF' ltac:(lia)) as (_ & _ & T2 & _). pose proof (aapp_bounds _ _ APP ltac:(lia)) as (_ & _ & T3 & _).
      unfold AAPP_HI in T2, T3.
      destruct E as [->|[->| ->]]; cbn [fst snd].
      + split; [lia|]. split; [| lia].
        pose proof (aapp_disjoint_sh ff' (fsz k') ff (fsz k) APF' ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)). lia.
      + split; [lia|]. split; [| lia].
        pose proof (aapp_disjoint_sh fp' 1 ff (fsz k) APP' ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)). lia.
      + rewrite (fshn_nsh k') by lia. split; [| split].
        * pose proof (aapp_disjoint_sh ff (fsz k) ff' (fsz k') APF ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)). lia.
        * unfold sh, nsh. unfold fsz in *. clear - D1 M8 M8' FZ FZ'. Z.div_mod_to_equations. nia.
        * pose proof (aapp_disjoint_sh fp 1 ff' (fsz k') APP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)). lia.
  Qed.
  Lemma dj_scratch_live : forall LF m0 XS k ff fp A n,
    as_RFS H LF m0 -> In (k, ff, fp) LF -> Forall (fs_scratch H LF) XS -> ff <= A -> A + n <= ff + fsz k -> disjoint_from XS A n.
  Proof.
    intros LF m0 XS k ff fp A n R IN FXS HA HB. apply dj_of_Forall. eapply Forall_impl; [| exact FXS]. intros iv SC.
    pose proof (scratch_off_live _ _ _ _ _ _ R IN SC) as (D & _ & _). lia.
  Qed.
  Lemma dj_scratch_live_sh : forall LF m0 XS k ff fp A n,
    as_RFS H LF m0 -> In (k, ff, fp) LF -> Forall (fs_scratch H LF) XS -> sh ff <= A -> A + n <= sh ff + fshn k -> disjoint_from XS A n.
  Proof.
    intros LF m0 XS k ff fp A n R IN FXS HA HB. apply dj_of_Forall. eapply Forall_impl; [| exact FXS]. intros iv SC.
    pose proof (scratch_off_live _ _ _ _ _ _ R IN SC) as (_ & D & _). lia.
  Qed.
  Lemma dj_scratch_live_flag : forall LF m0 XS k ff fp,
    as_RFS H LF m0 -> In (k, ff, fp) LF -> Forall (fs_scratch H LF) XS -> disjoint_from XS fp 1.
  Proof.
    intros LF m0 XS k ff fp R IN FXS. apply dj_of_Forall. eapply Forall_impl; [| exact FXS]. intros iv SC.
    pose proof (scratch_off_live _ _ _ _ _ _ R IN SC) as (_ & _ & D). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma magree_libx : forall LF m0 W m m',
    as_RFS H LF m0 -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv \/ scr_ok LF iv) W -> magree (lib_addr []) m m'.
  Proof.
    intros LF m0 W m m' R MU WM FW. eapply magree_of_munch; [exact MU| exact WM|].
    intros a [HX|[(b & Hb & _)|(b & Hb & _)]]; [| destruct Hb| destruct Hb]. clear MU WM.
    pose proof (LIBX_below _ HX) as LA.
    induction W as [|[lo hi] W IH]; [exact I|]. cbn. split; [| exact (IH (Forall_inv_tail FW))].
    pose proof (Forall_inv FW) as [K|K]; [cbn in K; lia| exact (scr_ok_libx _ _ _ _ R K HX)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition app_ok (iv : Z * Z) : Prop := AIMG_TOP <= fst iv /\ fst iv <= snd iv /\ aapp (fst iv) (snd iv - fst iv).
  Definition lit_ok (iv : Z * Z) : Prop := low_ok iv \/ app_ok iv.

  (* [comment removed for export] *)
  Lemma dj_foot_sh : forall LF m0 lo hi XS LIT B k A n,
    as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> Forall lit_ok LIT -> aceil <= lo -> ablock_range H B k ->
    sh B <= A -> A + n <= sh B + nsh k -> disjoint_from ((lo, hi) :: XS ++ LIT) A n.
  Proof.
    intros LF m0 lo hi XS LIT B k A n R FXS FL CE BR HA HB. acb. pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (sh_aapp_range _ _ B7 B3) as (S1 & S2 & S3). assert (SC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; lia).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
    apply dj_cons; [lia|]. apply dj_app; [eapply dj_scratch_placed_sh; eassumption|].
    apply dj_of_Forall. eapply Forall_impl; [| exact FL]. intros iv [[L1 L2]|(P1 & P2 & P3)]; [unfold AIMG_TOP in *; lia|].
    pose proof (aapp_bounds _ _ B7 B3) as (_ & _ & T1 & _).
    pose proof (aapp_disjoint_sh (fst iv) (snd iv - fst iv) B k P3 ltac:(lia) ltac:(lia) B3). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma dj_foot_img : forall LF m0 lo hi XS LIT A n,
    as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> Forall lit_ok LIT -> aceil <= lo -> A + n <= AIMG_TOP ->
    Forall (fun iv : Z * Z => low_ok iv -> A + n <= fst iv \/ snd iv <= A) LIT -> disjoint_from ((lo, hi) :: XS ++ LIT) A n.
  Proof.
    intros LF m0 lo hi XS LIT A n R FXS FL CE HA FLL. acb.
    apply dj_cons; [unfold AIMG_TOP in *; lia|]. apply dj_app; [eapply dj_scratch_img; eassumption|].
    apply dj_of_Forall. induction LIT as [|iv LIT IH]; [apply Forall_nil|]. apply Forall_cons; [| exact (IH (Forall_inv_tail FL) (Forall_inv_tail FLL))].
    pose proof (Forall_inv FL) as [LW|(P1 & P2 & P3)]; [exact (Forall_inv FLL LW)| lia].
  Qed.
  (* [comment removed for export] *)
  Lemma dj_foot_hi : forall LF m0 lo hi XS LIT A n,
    as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> Forall lit_ok LIT -> aceil <= lo -> lo <= hi -> hi <= A ->
    disjoint_from ((lo, hi) :: XS ++ LIT) A n.
  Proof.
    intros LF m0 lo hi XS LIT A n R FXS FL CE LH HA. acb.
    apply dj_cons; [lia|]. apply dj_app; [eapply dj_scratch_hi; [exact R| exact FXS| lia]|].
    apply dj_of_Forall. eapply Forall_impl; [| exact FL]. intros iv [[L1 L2]|(P1 & P2 & P3)]; [unfold AIMG_TOP in *; lia|].
    pose proof (aapp_below_aceil _ _ P3). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma dj_foot_blk : forall LF m0 lo hi XS LIT B k A n,
    as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> Forall lit_ok LIT -> aceil <= lo -> ablock_range H B k ->
    B <= A -> A + n <= B + k -> Forall (fun iv : Z * Z => app_ok iv -> A + n <= fst iv \/ snd iv <= A) LIT ->
    disjoint_from ((lo, hi) :: XS ++ LIT) A n.
  Proof.
    intros LF m0 lo hi XS LIT B k A n R FXS FL CE BR HA HB FLA. acb. pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    apply dj_cons; [lia|]. apply dj_app; [eapply dj_scratch_placed; eassumption|].
    apply dj_of_Forall. induction LIT as [|iv LIT IH]; [apply Forall_nil|]. apply Forall_cons; [| exact (IH (Forall_inv_tail FL) (Forall_inv_tail FLA))].
    pose proof (Forall_inv FL) as [[L1 L2]|AP]; [unfold AIMG_TOP in *; lia| exact (Forall_inv FLA AP)].
  Qed.

  (* [comment removed for export] *)
  Lemma lib_shad_foot : forall LF m0 L lo hi XS LIT m m',
    as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> Forall lit_ok LIT -> aceil <= lo ->
    Forall (fun b => ablock_range H (blk_addr b) (blk_size b)) L ->
    lib_shad L m -> munch ((lo, hi) :: XS ++ LIT) m m' -> wmono asegs m m' -> lib_shad L m'.
  Proof.
    intros LF m0 L lo hi XS LIT m m' R FXS FL CE PL SH MU WM. unfold lib_shad in *. apply Forall_forall. intros b Hb.
    eapply addressable_transport; [exact (proj1 (Forall_forall _ _) SH _ Hb)| exact MU| exact WM|].
    eapply dj_foot_sh; [exact R| exact FXS| exact FL| exact CE| exact (proj1 (Forall_forall _ _) PL _ Hb)| lia| lia].
  Qed.
  Lemma magree_libx_foot : forall LF m0 lo hi XS LIT m m',
    as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> Forall lit_ok LIT -> aceil <= lo ->
    munch ((lo, hi) :: XS ++ LIT) m m' -> wmono asegs m m' -> magree (lib_addr []) m m'.
  Proof.
    intros LF m0 lo hi XS LIT m m' R FXS FL CE MU WM. acb. eapply magree_libx; [exact R| exact MU| exact WM|].
    apply Forall_cons; [left; cbn [fst snd]; unfold AIMG_TOP in *; lia|]. apply Forall_app. split.
    - eapply Forall_impl; [| exact FXS]. intros iv K. right. left. exact K.
    - eapply Forall_impl; [| exact FL]. intros iv [K|(P1 & _)]; [right; right; exact K| left; exact P1].
  Qed.
  Lemma CTX_statics_foot : forall LF m0 lo hi XS LIT m m' x,
    as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> Forall lit_ok LIT -> aceil <= lo ->
    munch ((lo, hi) :: XS ++ LIT) m m' -> wmono asegs m m' -> CTX_statics m x -> CTX_statics m' x.
  Proof. intros. eapply (CTX_statics_frame []); [eassumption| eapply magree_libx_foot; eassumption]. Qed.
  Lemma ERR_statics_foot : forall LF m0 lo hi XS LIT m m' c,
    as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> Forall lit_ok LIT -> aceil <= lo ->
    munch ((lo, hi) :: XS ++ LIT) m m' -> wmono asegs m m' -> ERR_statics m c -> ERR_statics m' c.
  Proof. intros. eapply (ERR_statics_frame []); [eassumption| eapply magree_libx_foot; eassumption]. Qed.
  (* [comment removed for export] *)
  Lemma ERR_chain_foot : forall LF m0 LB lo hi XS LIT m m' c,
    as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> Forall lit_ok LIT -> aceil <= lo -> chain_apl H c -> chain_sep c ->
    Forall (fun iv : Z * Z => app_ok iv -> blk_addr (ec_es c) <= fst iv /\ snd iv <= blk_addr (ec_es c) + ERRST_SIZE) LIT ->
    munch ((lo, hi) :: XS ++ LIT) m m' -> wmono asegs m m' -> ERR_chain LB m c -> ERR_chain LB m' c.
  Proof.
    intros LF m0 LB lo hi XS LIT m m' c R FXS FL CE CA SEP FLA MU WM EC. unfold ERR_chain, sa_cells in *.
    destruct EC as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
    pose proof (Forall_inv CA) as A2. pose proof (Forall_inv (Forall_inv_tail CA)) as A3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CA))) as A4.
    cbv beta in A2, A3, A4. rewrite Z2 in A2. rewrite Z3 in A3. rewrite Z4 in A4. unfold chain_sep, ERRST_SIZE, O_MKEY_ERR in *.
    destruct SEP as (S2 & S3 & S4).
    assert (DJ : forall B k A n, ablock_range H B k -> B <= A -> A + n <= B + k ->
                 (B + k <= blk_addr (ec_es c) \/ blk_addr (ec_es c) + 904 <= B) -> disjoint_from ((lo, hi) :: XS ++ LIT) A n).
    { intros B k A n BR HA HB HS. eapply dj_foot_blk; [exact R| exact FXS| exact FL| exact CE| exact BR| exact HA| exact HB|].
      eapply Forall_impl; [| exact FLA]. intros iv K AP. specialize (K AP). lia. }
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - eapply rw_cells_transport; [exact K2| exact MU| exact WM|]. eapply (DJ _ _ _ _ A2); cbn; lia.
    - eapply rw_cells_transport; [exact K3| exact MU| exact WM|]. eapply (DJ _ _ _ _ A3); cbn; lia.
    - eapply rw_cells_transport; [exact K4| exact MU| exact WM|]. eapply (DJ _ _ _ _ A4); cbn; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma RFS_stack : forall LF m m' lo hi, as_RFS H LF m -> munch [(lo, hi)] m m' -> wmono asegs m m' -> aceil <= lo -> as_RFS H LF m'.
  Proof.
    intros LF m m' lo hi R MU WM CE. pose proof (RFS_fsb H HH _ _ R) as (F1 & F2 & F3 & F4). acb.
    eapply (ah_RFS_frame H HH); [exact R| exact MU| exact WM|].
    apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma munch_cons_compose : forall Wa Wb W m m1 m2,
    munch Wa m m1 -> munch Wb m1 m2 -> (forall a, outside W a -> outside Wa a) -> (forall a, outside W a -> outside Wb a) -> munch W m m2.
  Proof.
    intros Wa Wb W m m1 m2 MA MB IA IB x Hx. rewrite (MB x (IB _ Hx)). exact (MA x (IA _ Hx)).
  Qed.
  (* [comment removed for export] *)
  Lemma munch_then_stack : forall lo hi hi' W m m1 m2,
    munch ((lo, hi) :: W) m m1 -> munch [(lo, hi')] m1 m2 -> hi' <= hi -> munch ((lo, hi) :: W) m m2.
  Proof.
    intros lo hi hi' W m m1 m2 MA MB LE. eapply munch_cons_compose; [exact MA| exact MB| intros a K; exact K|].
    intros a K. cbn in K |- *. destruct K as [K _]. split; [lia| exact I].
  Qed.
  Lemma munch_stack_then : forall lo hi hi' W m m1 m2,
    munch [(lo, hi)] m m1 -> munch ((lo, hi') :: W) m1 m2 -> hi' <= hi -> munch ((lo, hi) :: W) m m2.
  Proof.
    intros lo hi hi' W m m1 m2 MA MB LE. eapply munch_cons_compose; [exact MA| exact MB| |].
    - intros a K. cbn in K |- *. destruct K as [K _]. split; [lia| exact I].
    - intros a K. cbn in K |- *. destruct K as [K1 K2]. split; [lia| exact K2].
  Qed.
  Lemma munch_foot_foot : forall lo hi hi' W1 W2 m m1 m2,
    munch ((lo, hi) :: W1) m m1 -> munch ((lo, hi') :: W2) m1 m2 -> hi' <= hi -> munch ((lo, hi) :: W1 ++ W2) m m2.
  Proof.
    intros lo hi hi' W1 W2 m m1 m2 MA MB LE. eapply munch_cons_compose; [exact MA| exact MB| |].
    - intros a K. cbn in K |- *. destruct K as [K1 K2]. split; [exact K1|].
      clear - K2. induction W1 as [|[u v] W1 IH]; [exact I|]. cbn in K2 |- *. destruct K2 as [K2 K3]. split; [exact K2| exact (IH K3)].
    - intros a K. cbn in K |- *. destruct K as [K1 K2]. split; [lia|].
      clear - K2. induction W1 as [|[u v] W1 IH]; [exact K2|]. cbn in K2. destruct K2 as [_ K3]. exact (IH K3).
  Qed.
  (* [comment removed for export] *)
  Lemma munch_mono : forall W W' m m', munch W m m' -> (forall a, outside W' a -> outside W a) -> munch W' m m'.
  Proof. intros W W' m m' MU INC x Hx. apply MU. apply INC. exact Hx. Qed.
  Lemma outside_app : forall W1 W2 a, outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
  Proof.
    intros W1 W2 a. induction W1 as [|[lo hi] W1 IH]; cbn; [tauto|]. rewrite IH. tauto.
  Qed.
  Lemma outside_cons : forall lo hi W a, outside ((lo, hi) :: W) a <-> ~ (lo <= a < hi) /\ outside W a.
  Proof. intros. cbn. tauto. Qed.

  (* [comment removed for export] *)
  Lemma ERR_chain_cells : forall L1 L2 m m0 c, ERR_chain L1 m c -> ERR_chain L2 m0 c -> ERR_chain L2 m c.
  Proof.
    intros L1 L2 m m0 c (_ & _ & K2 & _ & _ & K3 & _ & _ & K4 & _) (I2 & Z2 & _ & I3 & Z3 & _ & I4 & Z4 & _ & I5 & Z5 & I6 & Z6 & RR).
    unfold ERR_chain. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.
  Lemma ERR_chain_restrict : forall L m c, ERR_chain L m c -> ERR_chain (chain_blocks c) m c.
  Proof.
    intros L m c (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
    unfold ERR_chain, chain_blocks. repeat match goal with |- _ /\ _ => split end; try assumption; cbn; tauto.
  Qed.
  Lemma ERR_chain_frame_chain : forall L m m' c, ERR_chain L m c -> magree (lib_addr (chain_blocks c)) m m' -> ERR_chain L m' c.
  Proof.
    intros L m m' c EC AG. eapply (ERR_chain_cells (chain_blocks c) L); [| exact EC]. eapply ERR_chain_frame; [apply (ERR_chain_restrict L); exact EC| exact AG].
  Qed.
  (* [comment removed for export] *)
  Lemma magree_statics_of : forall L m m', magree (lib_addr L) m m' -> magree (lib_addr []) m m'.
  Proof.
    intros L m m' AG. eapply magree_mono; [exact AG|]. intros a Ha. eapply lib_addr_mono; [| exact Ha]. intros b [].
  Qed.

  (* [comment removed for export] *)
  Lemma chain_apl_of_RHEAP : forall s LB m LIB c,
    as_RHEAP H s LB m -> ERR_chain LIB m c -> (forall b, In b LIB -> In b LB) -> chain_apl H c.
  Proof.
    intros s LB m LIB c HP EC SUB. unfold chain_apl. apply Forall_forall. intros b Hb.
    eapply (ah_blocks H HH); [exact HP|]. apply SUB. eapply chain_blocks_in; [exact EC| exact Hb].
  Qed.
  (* [comment removed for export] *)
  Lemma lib4_foot : forall LF m0 LB lo hi XS LIT m m' c x,
    as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> Forall low_ok LIT -> aceil <= lo -> chain_apl H c ->
    munch ((lo, hi) :: XS ++ LIT) m m' -> wmono asegs m m' ->
    CTX_statics m x -> ERR_statics m c -> ERR_chain LB m c -> lib_shad (chain_blocks c) m ->
    CTX_statics m' x /\ ERR_statics m' c /\ ERR_chain LB m' c /\ lib_shad (chain_blocks c) m'.
  Proof.
    intros LF m0 LB lo hi XS LIT m m' c x R FXS FL CE CA MU WM CS ES EC LS.
    assert (AG : magree (lib_addr (chain_blocks c)) m m').
    { eapply lib_magree_scratch; [exact R| exact CA| exact MU| exact WM| exact CE|].
      apply Forall_app. split; [apply scr_ok_of_scratch; exact FXS| eapply Forall_impl; [| exact FL]; intros iv K; right; exact K]. }
    split; [eapply CTX_statics_frame; [exact CS| eapply magree_statics_of; exact AG]|].
    split; [eapply ERR_statics_frame; [exact ES| eapply magree_statics_of; exact AG]|].
    split; [eapply ERR_chain_frame_chain; [exact EC| exact AG]|].
    eapply lib_shad_frame; [exact LS| exact AG].
  Qed.
  Lemma low_lit_ok : forall LIT, Forall low_ok LIT -> Forall lit_ok LIT.
  Proof. intros LIT FL. eapply Forall_impl; [| exact FL]. intros iv K. left. exact K. Qed.
  Lemma errno_lit : Forall low_ok ERRNO_X.
  Proof. apply Forall_cons; [apply errno_low_ok| apply Forall_nil]. Qed.


  (* [comment removed for export] *)
  Lemma shvis_across : forall W m m' lo hi,
    shvis m lo hi -> munch W m m' -> wmono asegs m m' -> 0 <= lo -> lo <= hi <= AAPP_HI ->
    Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W -> shvis m' lo hi.
  Proof.
    intros W m m' lo hi SV MU WM L0 LH HW. eapply shvis_transport; [exact SV| exact MU| exact WM|].
    pose proof (hull_lo_le lo L0) as (A1 & A2 & A3). pose proof (hull_hi_ge hi ltac:(lia)) as (B1 & B2 & B3).
    assert (S1 : ASHADOW_BASE <= sh (hull_lo lo)) by (unfold sh; Z.div_mod_to_equations; lia).
    assert (HH2 : hull_hi hi <= AAPP_HI) by (unfold hull_hi, AAPP_HI in *; Z.div_mod_to_equations; lia).
    assert (S2 : sh (hull_hi hi) <= AHI_LO) by (unfold sh, AHI_LO, AAPP_HI in *; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    rewrite ASHADOW_BASE_val in S1.
    clear - HW S1 S2. induction W as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv HW) as K1. cbn in K1.
    split; [unfold ALOWSH_LO, AHI_LO in *; lia| exact (IH (Forall_inv_tail HW))].
  Qed.
End S.


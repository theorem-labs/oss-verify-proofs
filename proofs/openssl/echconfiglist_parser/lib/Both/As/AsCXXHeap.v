(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma lb_bytes_cons : forall b LB, lb_bytes (b :: LB) = blk_size b + lb_bytes LB.
Proof. reflexivity. Qed.

Lemma lf_remove_In : forall ff LF f, In f (lf_remove ff LF) -> In f LF.
Proof.
  intros ff LF. induction LF as [|g LF IH]; intros f Hf; cbn in *; [exact Hf|].
  destruct (Z.eqb (ff_addr g) ff); [right; exact Hf|]. destruct Hf as [<-|Hf]; [left; reflexivity| right; apply IH; exact Hf].
Qed.

Lemma lf_remove_head : forall k ff fp LF, lf_remove ff ((k, ff, fp) :: LF) = LF.
Proof. intros. cbn. rewrite Z.eqb_refl. reflexivity. Qed.

Section HH.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Local Ltac hh := pose proof HH as (Lsr & Lakrel & Lmpres & Lalloc & Lcost
                                     & Lrf & Lbr & Lbd & Lnd & Lbsv & Lfsb & Lthr & Laux & Llbr
                                     & Lff & Lfe & Lfr & Lfd & Lfn & Lfsv & Lrel
                                     & Lch
                                     & Lmalloc & Lfree & Lnull0      (* [comment removed for export] *)
                                     & Lfs1 & Lfs4 & Lsetf5
                                     & Lmc & Lms & Lmm & Lmci & Lsl & Lsn).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma ah_done : forall (Q : config -> Prop) c, Q c -> as_SR H Q c.
  Proof. hh. exact (proj1 Lsr). Qed.
  Lemma ah_mono : forall (Q Q' : config -> Prop) c, as_SR H Q c -> (forall c', Q c' -> Q' c') -> as_SR H Q' c.
  Proof. hh. exact (proj1 (proj2 Lsr)). Qed.
  Lemma ah_seq : forall (Q1 Q2 : config -> Prop) c, as_SR H Q1 c -> (forall c', Q1 c' -> as_SR H Q2 c') -> as_SR H Q2 c.
  Proof. hh. exact (proj1 (proj2 (proj2 Lsr))). Qed.
  Lemma ah_lift : forall (P : machine_state -> Prop) (Q : config -> Prop) s msF ms mo,
      as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = ms -> evt asegs P ms ->
      (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> P (as_VIS H s msF') -> as_SR H Q (mkCfg msF' mo')) ->
      as_SR H Q (mkCfg msF mo).
  Proof. hh. exact (proj2 (proj2 (proj2 Lsr))). Qed.
  Lemma ah_halted : forall s c, as_AKREL H s c -> m_halted (cfg_model c) = None.
  Proof. hh. exact (proj1 Lakrel). Qed.
  Lemma ah_vis_shape : forall s R F pc fc rv m ro, exists m', as_VIS H s (MS R F pc fc rv m ro) = MS R F pc fc rv m' ro.
  Proof. hh. exact (proj2 Lakrel). Qed.
  Lemma ah_mpres_refl : forall mo, as_MPRES H mo mo.
  Proof. hh. exact (proj1 Lmpres). Qed.
  Lemma ah_mpres_trans : forall mo1 mo2 mo3, as_MPRES H mo1 mo2 -> as_MPRES H mo2 mo3 -> as_MPRES H mo1 mo3.
  Proof. hh. exact (proj2 Lmpres). Qed.
  (* [comment removed for export] *)
  Lemma ah_alloc : alloc_ok_of_live H. Proof. hh. exact Lalloc. Qed.
  Lemma ah_costs : cost_laws H. Proof. hh. exact Lcost. Qed.
  Lemma ah_RHEAP_frame : RHEAP_frame H. Proof. hh. exact Lrf. Qed.
  Lemma ah_blocks : RHEAP_block_range H. Proof. hh. exact Lbr. Qed.
  Lemma ah_disj : RHEAP_blocks_disjoint H. Proof. hh. exact Lbd. Qed.
  Lemma ah_nodup : RHEAP_blocks_nodup H. Proof. hh. exact Lnd. Qed.
  Lemma ah_blk_shvis : RHEAP_shvis H. Proof. hh. exact Lbsv. Qed.
  Lemma ah_fsb : RHEAP_fsb H. Proof. hh. exact Lfsb. Qed.
  Lemma ah_thr : RHEAP_thr H. Proof. hh. exact Lthr. Qed.
  Lemma ah_rauxv_frame : rauxv_frame H. Proof. hh. exact Laux. Qed.
  Lemma ah_lb_remove : lb_remove_laws H. Proof. hh. exact Llbr. Qed.
  (* [comment removed for export] *)
  Lemma ah_RFS_frame : RFS_frame H. Proof. hh. exact Lff. Qed.
  Lemma ah_RFS_ext : RFS_ext H. Proof. hh. exact Lfe. Qed.
  Lemma ah_RFS_range : RFS_range H. Proof. hh. exact Lfr. Qed.
  Lemma ah_RFS_disj : RFS_disjoint H. Proof. hh. exact Lfd. Qed.
  Lemma ah_RFS_nodup : RFS_nodup H. Proof. hh. exact Lfn. Qed.
  Lemma ah_frm_shvis : RFS_shvis H. Proof. hh. exact Lfsv. Qed.
  Lemma ah_release : frame_release_law H. Proof. hh. exact Lrel. Qed.
  (* [comment removed for export] *)
  Lemma ah_chain_nil : forall m cur, (cur <= aceil \/ cur mod 8 <> 0) -> as_chain H m cur [].
  Proof. hh. exact (proj1 Lch). Qed.
  Lemma ah_chain_cons : forall m cur CH fp ra, as_chain H m cur CH -> 0 <= cur < 2^64 -> 0 <= ra < 2^64 ->
      fp mod 16 = 0 -> aceil + 16 <= fp -> fp < 2^64 ->
      rw_cells asegs m (fp - 16) [C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 ra)] -> as_chain H m fp ((fp, ra) :: CH).
  Proof. hh. exact (proj1 (proj2 Lch)). Qed.
  Lemma ah_chain_ext : forall m m' cur CH, as_chain H m cur CH ->
      (forall fp ra a, In (fp, ra) CH -> fp - 16 <= a < fp -> m' (wa a) = m (wa a)) -> as_chain H m' cur CH.
  Proof. hh. exact (proj1 (proj2 (proj2 Lch))). Qed.
  Lemma ah_chain_range : forall m cur CH fp ra, as_chain H m cur CH -> In (fp, ra) CH -> aceil + 16 <= fp < 2^64 /\ fp mod 8 = 0 /\ 0 <= ra < 2^64.
  Proof. hh. exact (proj2 (proj2 (proj2 Lch))). Qed.
  (* [comment removed for export] *)
  Lemma ah_malloc : malloc_stmt H. Proof. hh. exact Lmalloc. Qed.
  Lemma ah_free : free_stmt H. Proof. hh. exact Lfree. Qed.
  Lemma ah_free_null : free_null_stmt_at H AFREE_STUB. Proof. hh. exact Lnull0. Qed.
  Lemma ah_fs1 : stack_malloc_1_stmt H. Proof. hh. exact Lfs1. Qed.
  Lemma ah_fs4 : stack_malloc_4_stmt H. Proof. hh. exact Lfs4. Qed.
  Lemma ah_setf5 : set_shadow_f5_stmt. Proof. hh. exact Lsetf5. Qed.
  Lemma ah_memcpy : asan_memcpy_stmt. Proof. hh. exact Lmc. Qed.
  Lemma ah_memset : asan_memset_stmt. Proof. hh. exact Lms. Qed.
  Lemma ah_memmove : asan_memmove_stmt. Proof. hh. exact Lmm. Qed.
  Lemma ah_memcpy_icpt : memcpy_icpt_stmt. Proof. hh. exact Lmci. Qed.
  Lemma ah_strlen : strlen_icpt_stmt. Proof. hh. exact Lsl. Qed.
  Lemma ah_strncmp : strncmp_icpt_stmt. Proof. hh. exact Lsn. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma ahh_evt : forall (P : machine_state -> Prop) (Q : config -> Prop) s msF ms mo,
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = ms -> evt asegs P ms ->
    (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> P (as_VIS H s msF') -> Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros P Q s msF ms mo K V E W. eapply ah_lift; [exact K| exact V| exact E|].
    intros msF' mo' K' MP HP. apply ah_done. apply W; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ahh_evt_then : forall (P : machine_state -> Prop) (Q : config -> Prop) s msF ms mo,
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = ms -> evt asegs P ms ->
    (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> P (as_VIS H s msF') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof. intros P Q s msF ms mo K V E W. eapply ah_lift; eassumption. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma apres_refl : forall LB SP m, apres H LB SP m m.
  Proof. intros LB SP m a _ _. auto. Qed.

  Lemma apres_trans : forall LB SP m1 m2 m3, apres H LB SP m1 m2 -> apres H LB SP m2 m3 -> apres H LB SP m1 m3.
  Proof.
    intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2]. split; [congruence| auto].
  Qed.

  Lemma aclient_addr_weaken : forall LB LB' SP SP' a,
    aclient_addr H LB' SP' a -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> aclient_addr H LB SP a.
  Proof.
    intros LB LB' SP SP' a Hc HS HL. unfold aclient_addr in *.
    destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|Hc]]]]; [left; lia| tauto | | | tauto].
    - right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
    - right; right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
  Qed.

  Lemma apres_weaken : forall LB LB' SP SP' m m',
    apres H LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> apres H LB' SP' m m'.
  Proof. intros LB LB' SP SP' m m' HP HS HL a Ha Hc. apply HP; [exact Ha|]. eapply aclient_addr_weaken; eauto. Qed.

  Lemma aclient_range_addr : forall LB SP A n a, aclient_range H LB SP A n -> A <= a < A + n -> aclient_addr H LB SP a.
  Proof.
    intros LB SP A n a HR Ha. unfold aclient_range, aclient_addr in *.
    destruct HR as [K|[K|[(b & Hb & K1 & K2)|[(b & Hb & K1 & K2)|[K|[K|K]]]]]]; [left; lia| right; left; apply K; lia | | | right; right; right; right; lia ..].
    - right; right; left. exists b. split; [exact Hb| lia].
    - right; right; right; left. exists b. split; [exact Hb| lia].
  Qed.

  Lemma apres_bytes_at : forall LB SP m m' A bs,
    apres H LB SP m m' -> bytes_at asegs m A bs -> aclient_range H LB SP A (Z.of_nat (length bs)) -> bytes_at asegs m' A bs.
  Proof.
    intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite <- (HB i Hi). unfold mrd.
    destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply aclient_range_addr; [exact HR|lia])) as [E _]. rewrite E. reflexivity.
  Qed.

  Lemma apres_wr_at : forall LB SP m m' A n,
    apres H LB SP m m' -> wr_at asegs m A n -> aclient_range H LB SP A n -> wr_at asegs m' A n.
  Proof.
    intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
    intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply aclient_range_addr; [exact HR|lia])) as [_ W]. apply W. apply HW. exact Hi.
  Qed.

  Lemma apres_rw_cells : forall LB SP m m' A cs,
    apres H LB SP m m' -> rw_cells asegs m A cs -> aclient_range H LB SP A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
  Proof.
    intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
    - eapply apres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
    - eapply apres_wr_at; eauto.
  Qed.

  Lemma apres_u8arr : forall LB SP m m' A bs,
    apres H LB SP m m' -> u8arr asegs m A bs -> aclient_range H LB SP A (Z.of_nat (length bs)) -> u8arr asegs m' A bs.
  Proof. intros LB SP m m' A bs HP [HB HW] HR. split; [eapply apres_bytes_at; eauto| eapply apres_wr_at; eauto]. Qed.

  Lemma apres_u64arr : forall LB SP m m' A ws,
    apres H LB SP m m' -> u64arr asegs m A ws -> aclient_range H LB SP A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
  Proof.
    intros LB SP m m' A ws HP [HB HW] HR. split; [eapply apres_bytes_at; eauto| eapply apres_wr_at; eauto].
    rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact HR.
  Qed.

  Lemma apres_u32arr : forall LB SP m m' A ws,
    apres H LB SP m m' -> u32arr asegs m A ws -> aclient_range H LB SP A (4 * Z.of_nat (length ws)) -> u32arr asegs m' A ws.
  Proof.
    intros LB SP m m' A ws HP [HB HW] HR. split; [eapply apres_bytes_at; eauto| eapply apres_wr_at; eauto].
    rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia. exact HR.
  Qed.

  Lemma apres_stk : forall LB SP m m' lo hi,
    apres H LB SP m m' -> stk asegs m lo hi -> SP <= lo -> stk asegs m' lo hi.
  Proof.
    intros LB SP m m' lo hi HP (H0 & H1 & HW) HS. split; [exact H0|]. split; [exact H1|].
    intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
    split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma aclient_range_block_sh : forall LB SP p A n, In (p, A, n) LB -> aclient_range H LB SP (sh A) (nsh n).
  Proof. intros LB SP p A n IN. right; right; right; left. exists (p, A, n). split; [exact IN| cbn; lia]. Qed.
  Lemma aclient_range_block : forall LB SP p A n a k, In (p, A, n) LB -> A <= a -> a + k <= A + n -> aclient_range H LB SP a k.
  Proof. intros LB SP p A n a k IN H1 H2. right; right; left. exists (p, A, n). split; [exact IN| cbn; lia]. Qed.

  Lemma apres_SHAD : forall LB SP m m' A sbs,
    apres H LB SP m m' -> SHAD m A sbs -> aclient_range H LB SP (sh A) (Z.of_nat (length sbs)) -> SHAD m' A sbs.
  Proof. intros LB SP m m' A sbs HP (A0 & HA & U) HR. split; [exact A0|]. split; [exact HA|]. eapply apres_u8arr; eauto. Qed.

  Lemma apres_addressable : forall LB SP m m' p A n,
    apres H LB SP m m' -> addressable m A n -> In (p, A, n) LB -> addressable m' A n.
  Proof.
    intros LB SP m m' p A n HP [Hn SH] IN. split; [exact Hn|]. eapply apres_SHAD; eauto.
    rewrite shadow_of_length by lia. eapply aclient_range_block_sh; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma RFS_via_apres : forall LF LB SP m m',
    as_RFS H LF m -> apres H LB SP m m' -> as_RFS H LF m'.
  Proof.
    intros LF LB SP m m' R HP. eapply ah_RFS_ext; [exact R|].
    intros a Ha Hr. apply HP; [exact Ha|]. unfold aclient_addr.
    destruct Hr as [Hr|[Hr|Hr]].
    - right; right; right; right; left. exact Hr.
    - right; left. unfold aimg_client. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP in *. lia.
    - right; right; right; right; right; left. exact Hr.
  Qed.

  (* [comment removed for export] *)
  Lemma chain_via_apres : forall LB SP m m' cur CH,
    as_chain H m cur CH -> apres H LB SP m m' ->
    (forall fp ra, In (fp, ra) CH -> SP + 16 <= fp) -> as_chain H m' cur CH.
  Proof.
    intros LB SP m m' cur CH C HP HS. eapply ah_chain_ext; [exact C|].
    intros fp ra a IN Ha. pose proof (HS _ _ IN). pose proof (ah_chain_range _ _ _ _ _ C IN) as (R1 & R2 & R3).
    apply HP; [| left; lia]. acb. lia.
  Qed.

  Lemma chain_via_munch : forall W m m' cur CH,
    as_chain H m cur CH -> munch W m m' ->
    (forall fp ra, In (fp, ra) CH -> disjoint_from W (fp - 16) 16) -> as_chain H m' cur CH.
  Proof.
    intros W m m' cur CH C MU HD. eapply ah_chain_ext; [exact C|].
    intros fp ra a IN Ha. pose proof (ah_chain_range _ _ _ _ _ C IN) as (R1 & R2 & R3).
    unfold wa. apply MU. rewrite unsigned_lit by (acb; lia).
    eapply disjoint_outside; [apply (HD fp ra); exact IN| lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma apres_of_munch : forall s LB SP W m0 m m',
    as_RHEAP H s LB m0 ->
    munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => aceil <= fst iv /\ snd iv <= SP) W ->
    apres H LB SP m m'.
  Proof.
    intros s LB SP W m0 m m' RH MU WM FW a Ha Hc.
    pose proof (ah_fsb _ _ _ RH) as (F1 & F2 & F3).
    assert (OUT : outside W a).
    { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as [H1 H2]. cbn in H1, H2.
      split; [| apply IH; apply (Forall_inv_tail FW)].
      intros K. unfold aclient_addr in Hc.
      destruct Hc as [Hc|Hc]; [lia|].
      assert (LOW : a < aceil); [| lia].
      destruct Hc as [Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]].
      - acb; unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP in *. lia.
      - pose proof (ah_blocks _ _ _ _ RH Hb) as (_ & _ & _ & _ & R & _). lia.
      - pose proof (ah_blocks _ _ _ _ RH Hb) as (_ & _ & R0 & R1 & R & _).
        pose proof (sh_below_aceil (blk_addr b + blk_size b + 8) ltac:(acb; unfold AIMG_TOP, AAPP_HI in *; lia)).
        unfold nsh, sh in *. rewrite ASHADOW_BASE_val in *. Z.div_mod_to_equations. lia.
      - lia.
      - pose proof (sh_below_aceil (as_FSB H + AFS_SIZE) ltac:(acb; unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; lia)).
        acb; unfold AFS_SIZE in *. lia.
      - acb; unfold AHI_LO in *. lia. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.

  (* [comment removed for export] *)
  Lemma client_frame : forall s LB LF B W m m',
    as_RHEAP H s LB m -> as_RFS H LF m -> ACONST m -> as_rauxv_ok H m B ->
    munch W m m' -> wmono asegs m m' ->
    Forall (aclient_write_ok H LB) W -> Forall (afs_write_ok H LF) W -> Forall aconst_ok W ->
    as_RHEAP H s LB m' /\ as_RFS H LF m' /\ ACONST m' /\ as_rauxv_ok H m' B.
  Proof.
    intros s LB LF B W m m' RH RF AC RA MU WM F1 F2 F3.
    split; [eapply ah_RHEAP_frame; eauto|]. split; [eapply ah_RFS_frame; eauto|].
    split; [eapply ACONST_frame; eauto| eapply ah_rauxv_frame; eauto].
  Qed.

  (* [comment removed for export] *)
  Lemma stack_window_ok : forall LB LF lo' SP,
    aceil <= lo' -> as_FSB H + AFS_SIZE <= aceil ->
    aclient_write_ok H LB (lo', SP) /\ afs_write_ok H LF (lo', SP) /\ aconst_ok (lo', SP).
  Proof.
    intros LB LF lo' SP H1 H2. split; [left; cbn; lia|]. split.
    - left. cbn. acb; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. lia.
    - apply aconst_ok_high; [| right; left]; acb; unfold sh, AIMG_TOP, ASHADOW_BASE in *; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fresh_frame (LF : list fframe) (k ff fp : Z) : Prop :=
    aframe_range H k ff fp /\ afsb_ok H
    /\ forall f, In f LF -> (ff + fsz k <= ff_addr f \/ ff_addr f + fsz (ff_class f) <= ff) /\ fp <> ff_flag f.

  (* [comment removed for export] *)
  Definition fsobj (LF : list fframe) (O n : Z) : Prop :=
    (O + n <= as_FSB H \/ as_FSB H + AFS_SIZE <= O)
    \/ exists f, In f LF /\ ff_addr f <= O /\ O + n <= ff_addr f + fsz (ff_class f).

  Lemma fsz_pos : forall k, 0 <= k -> 64 <= fsz k.
  Proof. intros k Hk. unfold fsz. pose proof (Z.pow_le_mono_r 2 0 k ltac:(lia) Hk). change (2^0) with 1 in H0. nia. Qed.

  Lemma fsz_1 : fsz 1 = 128. Proof. reflexivity. Qed.
  Lemma fsz_4 : fsz 4 = 1024. Proof. reflexivity. Qed.
  Lemma fshn_1 : fshn 1 = 16. Proof. reflexivity. Qed.
  Lemma fshn_4 : fshn 4 = 128. Proof. reflexivity. Qed.

  Lemma fresh_of_RFS : forall LF k ff fp m, as_RFS H ((k, ff, fp) :: LF) m -> fresh_frame LF k ff fp.
  Proof.
    intros LF k ff fp m R. pose proof (ah_RFS_range _ _ R) as [AF AR']. pose proof (AR' (k, ff, fp) (or_introl eq_refl)) as AR. cbn in AR.
    split; [exact AR|]. split; [exact AF|]. intros f IN.
    pose proof (ah_RFS_nodup _ _ R) as ND. cbn in ND. inversion ND; subst.
    assert (NE : ff <> ff_addr f). { intros E. apply H2. apply in_map_iff. exists f. split; [symmetry; exact E| exact IN]. }
    destruct (ah_RFS_disj _ _ (k, ff, fp) f R (or_introl eq_refl) (or_intror IN) NE) as [D1 D2]. cbn in D1, D2.
    split; [exact D1| exact D2].
  Qed.

  (* [comment removed for export] *)
  Lemma fsobj_high : forall LF O n m, as_RFS H LF m -> aceil <= O -> fsobj LF O n.
  Proof. intros LF O n m R HO. left. right. destruct (proj1 (ah_RFS_range _ _ R)) as (F1 & F2 & F3). lia. Qed.

  Lemma RFS_fsb : forall LF m, as_RFS H LF m -> afsb_ok H.
  Proof. intros LF m R. exact (proj1 (ah_RFS_range _ _ R)). Qed.

  Lemma fsobj_outside : forall LF O n, (O + n <= as_FSB H \/ as_FSB H + AFS_SIZE <= O) -> fsobj LF O n.
  Proof. intros LF O n HO. left. exact HO. Qed.

  Lemma fsobj_block : forall s LB m0 LF p A n, as_RHEAP H s LB m0 -> In (p, A, n) LB -> fsobj LF A n.
  Proof.
    intros s LB m0 LF p A n RH IN. left.
    pose proof (ah_blocks _ _ _ _ RH IN) as (_ & _ & _ & _ & _ & G). cbn in G. lia.
  Qed.

  Lemma fsobj_inframe : forall LF f O n, In f LF -> ff_addr f <= O -> O + n <= ff_addr f + fsz (ff_class f) -> fsobj LF O n.
  Proof. intros LF f O n IN H1 H2. right. exists f. auto. Qed.

  Lemma fsobj_sub : forall LF O n O' n', fsobj LF O n -> O <= O' -> O' + n' <= O + n -> fsobj LF O' n'.
  Proof.
    intros LF O n O' n' D H1 H2. destruct D as [D|(f & IN & D1 & D2)]; [left; lia| right]. exists f. split; [exact IN| lia].
  Qed.

  Lemma fsobj_mono : forall LF f O n, fsobj LF O n -> fsobj (f :: LF) O n.
  Proof. intros LF f O n [D|(g & IN & D)]; [left; exact D| right]. exists g. split; [right; exact IN| exact D]. Qed.

  (* [comment removed for export] *)
  Lemma fresh_frame_facts : forall LF k ff fp, fresh_frame LF k ff fp ->
    0 <= k <= 10 /\ AIMG_TOP + AFS_HDR <= ff /\ ff + fsz k <= aceil /\ ff mod 64 = 0 /\ ff mod 8 = 0
    /\ AIMG_TOP + AFS_FLAGS <= fp /\ fp + 1 <= ff /\ as_FSB H + AFS_FLAGS <= fp /\ fp < as_FSB H + AFS_HDR
    /\ as_FSB H + AFS_HDR <= ff /\ ff + fsz k <= as_FSB H + AFS_SIZE /\ AIMG_TOP <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil
    /\ aapp (as_FSB H) AFS_SIZE.
  Proof.
    intros LF k ff fp ((K & R1 & R2 & R3 & R4) & (F1 & F2 & F3 & F4) & _).
    assert (M64 : ff mod 64 = 0).
    { unfold fsz in R3. pose proof (fsz_pos k ltac:(lia)) as FP. unfold fsz in FP.
      destruct (Zle_lt_or_eq 0 k ltac:(lia)) as [Kp| <-].
      - assert (E : 64 * 2 ^ k = 64 * (2 * 2 ^ (k - 1))). { rewrite <- Z.pow_succ_r by lia. f_equal. f_equal. lia. }
        rewrite E in R3. pose proof (Z.pow_nonneg 2 (k-1) ltac:(lia)).
        apply Z.mod_divide in R3; [|lia]. apply Z.mod_divide; [lia|]. destruct R3 as [q Hq]. exists (q * (2 * 2 ^ (k-1))). lia.
      - change (64 * 2 ^ 0) with 64 in R3. exact R3. }
    assert (M8 : ff mod 8 = 0) by (Z.div_mod_to_equations; lia).
    pose proof (fsz_pos k ltac:(lia)).
    repeat split; try exact F4; acb; unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fsobj_windows : forall LF O n k ff fp m,
    as_RFS H LF m -> fsobj LF O n -> fresh_frame LF k ff fp -> 0 <= O -> 0 <= n -> O + n <= AAPP_HI ->
       (O + n <= ff \/ ff + fsz k <= O)
    /\ (sh O + nsh n <= sh ff \/ sh ff + fshn k <= sh O)
    /\ (O + n <= fp \/ fp + 1 <= O)
    /\ (O + n <= as_FSB H \/ as_FSB H + AFS_FLAGS <= O).
  Proof.
    intros LF O n k ff fp m R OB FF HO Hn Htop. pose proof (fresh_frame_facts _ _ _ _ FF) as FA.
    destruct FA as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    assert (DD : (O + n <= ff \/ ff + fsz k <= O) /\ (O + n <= fp \/ fp + 1 <= O) /\ (O + n <= as_FSB H \/ as_FSB H + AFS_FLAGS <= O)).
    { pose proof (fsz_pos k ltac:(lia)). destruct OB as [OB|(f & IN & D1 & D2)].
      - unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. lia.
      - destruct FF as (_ & _ & D). destruct (D f IN) as [DJ NF].
        pose proof (proj2 (ah_RFS_range _ _ R) f IN) as (K' & Q1 & Q2 & Q3 & Q4). pose proof (fsz_pos (ff_class f) ltac:(lia)).
        unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. lia. }
    destruct DD as (D1 & D2 & D3). split; [exact D1|]. split; [| split; [exact D2| exact D3]].
    destruct D1 as [D1|D1].
    - left. unfold sh, nsh. Z.div_mod_to_equations. nia.
    - right. unfold sh, fshn. unfold fsz in D1. Z.div_mod_to_equations. nia.
  Qed.
  (* [comment removed for export] *)
  Lemma disjoint_from_sub : forall W O n a k, disjoint_from W O n -> O <= a -> a + k <= O + n -> disjoint_from W a k.
  Proof.
    induction W as [|[lo hi] W IH]; intros O n a k D H1 H2; cbn in *; [exact I|].
    destruct D as [D1 D2]. split; [lia| exact (IH _ _ _ _ D2 H1 H2)].
  Qed.

  Lemma fshn_nsh : forall k, 0 <= k -> fshn k = nsh (fsz k).
  Proof. intros k Hk. unfold nsh, fsz, fshn. pose proof (Z.pow_nonneg 2 k). Z.div_mod_to_equations. nia. Qed.

  (* [comment removed for export] *)
  Lemma fsobj_disjoint : forall LF O n k ff fp m slo shi,
    as_RFS H LF m -> fsobj LF O n -> fresh_frame LF k ff fp ->
    0 <= O -> 0 <= n -> O + n <= AAPP_HI -> aapp O n -> (O + n <= slo \/ shi <= O) ->
    disjoint_from [(slo, shi); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz k); (sh ff, sh ff + fshn k)]%Z O n.
  Proof.
    intros LF O n k ff fp m slo shi R OB FF HO Hn Htop HHI HS.
    pose proof (fsobj_windows _ _ _ _ _ _ _ R OB FF HO Hn Htop) as (D1 & D2 & D3 & D4).
    pose proof (fresh_frame_facts _ _ _ _ FF) as (K & R1 & R2 & _ & _ & _ & _ & _ & _ & _ & P6 & P7 & P8 & P9).
    pose proof (fsz_pos k ltac:(lia)).
    pose proof (aapp_disjoint_sh O n ff (fsz k) HHI ltac:(acb; unfold AIMG_TOP, AFS_HDR in *; lia) ltac:(acb; unfold AAPP_HI in *; lia) ltac:(lia)) as S2.
    rewrite <- fshn_nsh in S2 by lia.
    cbn. repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fsobj_disjoint_sh : forall LF O n k ff fp m slo shi,
    as_RFS H LF m -> fsobj LF O n -> fresh_frame LF k ff fp ->
    0 <= O -> 0 <= n -> O + n <= AAPP_HI -> aceil <= slo ->
    disjoint_from [(slo, shi); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz k); (sh ff, sh ff + fshn k)]%Z (sh O) (nsh n).
  Proof.
    intros LF O n k ff fp m slo shi R OB FF HO Hn Htop HS.
    pose proof (fsobj_windows _ _ _ _ _ _ _ R OB FF HO Hn Htop) as (D1 & D2 & D3 & D4).
    pose proof (fresh_frame_facts _ _ _ _ FF) as (K & R1 & R2 & _ & _ & P1 & _ & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    pose proof (fsz_pos k ltac:(lia)).
    pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE O n P9 HO Htop Hn) as S1.
    pose proof (sh_nsh_high O n HO Hn Htop) as S3.
    cbn. acb; unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AHI_LO in *. repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Definition fs_scratch (LF : list fframe) (iv : Z * Z) : Prop :=
    iv = (as_FSB H, as_FSB H + AFS_FLAGS)
    \/ exists k ff fp, fresh_frame LF k ff fp /\ (iv = (ff, ff + fsz k) \/ iv = (fp, fp + 1) \/ iv = (sh ff, sh ff + fshn k)).

  Lemma fs_scratch_of_fresh : forall LF k ff fp, fresh_frame LF k ff fp ->
    Forall (fs_scratch LF) [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz k); (sh ff, sh ff + fshn k)]%Z.
  Proof.
    intros LF k ff fp FF. repeat apply Forall_cons; [left; reflexivity| right..| apply Forall_nil]; exists k, ff, fp; auto.
  Qed.

  (* [comment removed for export] *)
  Lemma fsobj_scratch : forall LF O n m iv,
    as_RFS H LF m -> fsobj LF O n -> 0 <= O -> 0 <= n -> O + n <= AAPP_HI -> aapp O n -> fs_scratch LF iv ->
    O + n <= fst iv \/ snd iv <= O.
  Proof.
    intros LF O n m iv R OB HO Hn Htop HHI [->|(k & ff & fp & FF & E)].
    - cbn. destruct OB as [OB|(f & IN & D1 & D2)]; [unfold AFS_FLAGS, AFS_SIZE in *; lia|].
      pose proof (proj2 (ah_RFS_range _ _ R) f IN) as (K' & Q1 & Q2 & Q3 & Q4). unfold AFS_FLAGS, AFS_HDR in *. lia.
    - pose proof (fsobj_windows _ _ _ _ _ _ _ R OB FF HO Hn Htop) as (D1 & D2 & D3 & D4).
      destruct E as [-> |[-> | ->]]; cbn; [lia| lia|].
      pose proof (fresh_frame_facts _ _ _ _ FF) as (K & R1 & R2 & _).
      pose proof (fsz_pos k ltac:(lia)).
      pose proof (aapp_disjoint_sh O n ff (fsz k) HHI ltac:(acb; unfold AIMG_TOP, AFS_HDR in *; lia) ltac:(acb; unfold AAPP_HI in *; lia) ltac:(lia)) as S2.
      rewrite <- fshn_nsh in S2 by lia. lia.
  Qed.

  Lemma fsobj_scratch_sh : forall LF O n m iv,
    as_RFS H LF m -> fsobj LF O n -> 0 <= O -> 0 <= n -> O + n <= AAPP_HI -> fs_scratch LF iv ->
    sh O + nsh n <= fst iv \/ snd iv <= sh O.
  Proof.
    intros LF O n m iv R OB HO Hn Htop [->|(k & ff & fp & FF & E)].
    - cbn. destruct (proj1 (ah_RFS_range _ _ R)) as (F1 & F2 & F3 & F4).
      pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE O n F4 HO Htop Hn). unfold AFS_FLAGS, AFS_SIZE in *. lia.
    - pose proof (fsobj_windows _ _ _ _ _ _ _ R OB FF HO Hn Htop) as (D1 & D2 & D3 & D4).
      pose proof (fresh_frame_facts _ _ _ _ FF) as (K & R1 & R2 & _ & _ & P1 & _ & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE O n P9 HO Htop Hn) as S1.
      pose proof (fsz_pos k ltac:(lia)).
      destruct E as [-> |[-> | ->]]; cbn; acb; unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma athr_cells_frame : forall W m m',
    athr_cells m -> munch W m m' -> wmono asegs m m' -> Forall (fun iv : Z * Z => aceil <= fst iv) W -> athr_cells m'.
  Proof.
    intros W m m' (ctx & T & D & tb & te & C1 & C2 & C3 & C4 & C5 & R) MU WM FW.
    assert (DJ : forall a n, a + n <= aceil -> disjoint_from W a n).
    { intros a n Hn. clear -FW Hn. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion FW; subst. cbn in *.
      split; [lia| apply IH; assumption]. }
    exists ctx, T, D, tb, te. acb; unfold ATSD0, ATP in *.
    repeat match goal with |- _ /\ _ => split end; try lia;
      (eapply rw_cells_transport; [eassumption| exact MU| exact WM| apply DJ; cbn; lia]).
  Qed.
End HH.

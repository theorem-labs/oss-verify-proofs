(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsStack0 AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AKit ECH_AsKit ECH_AC7_kit ECH_ALibMF ECH_ALibOK
  ECH_AC1_zalloc ECH_AC6_buf ECH_AC7_new.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nodup_ids_app_ne7 : forall (l1 l2 : list block) b1 b2,
  List.NoDup (map blk_id (l1 ++ l2)) -> In b1 l1 -> In b2 l2 -> blk_id b1 <> blk_id b2.
Proof.
  induction l1 as [|c l1 IH]; intros l2 b1 b2 ND H1 H2; [destruct H1|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
  destruct H1 as [->|H1]; [| exact (IH _ _ _ ND' H1 H2)].
  intros E. apply NI. rewrite map_app. apply in_or_app. right. rewrite E. apply in_map. exact H2.
Qed.
(* [comment removed for export] *)
Lemma in_app_mid : forall (A : Type) (l1 l2 : list A) (x y : A), In x (l1 ++ l2) -> In x (l1 ++ y :: l2).
Proof. intros A l1 l2 x y Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]; [left; exact Hx| right; right; exact Hx]. Qed.

Lemma lb_bytes_app7 : forall L1 L2, lb_bytes (L1 ++ L2) = lb_bytes L1 + lb_bytes L2.
Proof. induction L1 as [|b L1 IH]; intros L2; [reflexivity|]. cbn [app]. rewrite !lb_bytes_cons, IH. lia. Qed.

Section K.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma ctxph_nonneg : forall ph, 0 <= ctxph_bytes ph /\ 0 <= ctxph_cnt ph /\ 0 <= CNEWEX_STACK ph /\ 0 <= ctxph_cost H ph.
  Proof.
    intros ph. pose proof (ah_costs H HH) as (C1 & C2 & C3 & C4 & _).
    assert (K : 0 <= CTXINIT_COST H) by (unfold CTXINIT_COST; pose proof (C1 CTXINIT_BYTES ltac:(unfold CTXINIT_BYTES; lia)); pose proof (C3 CTXINIT_BYTES ltac:(unfold CTXINIT_BYTES; lia)); lia).
    destruct ph as [|x]; cbn [ctxph_bytes ctxph_cnt ctxph_cost]; unfold CTXINIT_BYTES, CTXINIT_CNT, CNEWEX_STACK, NEWEX_INNER,
      FR_CRYPTO_new_ex_data, FR_ossl_crypto_new_ex_data_ex, AFS_STACK; lia.
  Qed.
  Lemma ctxph_delta_bounds : forall ph LBN x, ctxph_delta ph LBN x -> lb_bytes LBN <= ctxph_bytes ph /\ Z.of_nat (length LBN) <= ctxph_cnt ph.
  Proof.
    intros [|x0] LBN x D; cbn [ctxph_delta ctxph_bytes ctxph_cnt] in *; [lia|]. destruct D as [-> ->]. cbn. unfold lb_bytes. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma METH_of_relro : forall m, arelro_lib m -> METH_mem m.
  Proof.
    intros m RL. unfold METH_mem, O_METH_BREAD, A_mem_buf_method. eapply relro_cell7; [exact RL| lia| cbn; lia| vm_compute; repeat split; reflexivity| vm_compute; reflexivity].
  Qed.
  Lemma arelro_xpres : forall LB SP X m m', arelro_lib m -> xpres H LB SP X m m' ->
    Forall (fun iv : Z * Z => snd iv <= 0x571000 \/ 0x5ea000 <= fst iv) X -> arelro_lib m'.
  Proof.
    intros LB SP X m m' RL XP FX i Hi. destruct (XP i) as [E _]; [lia| | rewrite E; apply RL; exact Hi].
    split; [right; left; unfold aimg_client; lia|].
    clear - FX Hi. induction X as [|[lo hi] X IH]; [intros K; exact K|]. cbn. pose proof (Forall_inv FX) as K1. cbn in K1.
    intros [K|K]; [lia| exact (IH (Forall_inv_tail FX) K)].
  Qed.

  (* [comment removed for export] *)
  Lemma chain_via_xpres : forall LB SP X m m' cur CH,
    as_chain H m cur CH -> xpres H LB SP X m m' -> (forall fp ra, In (fp, ra) CH -> SP + 16 <= fp) ->
    (forall a, rin_ivs X a -> a < aceil) -> as_chain H m' cur CH.
  Proof.
    intros LB SP X m m' cur CH C XP HS HX. eapply (ah_chain_ext H HH); [exact C|].
    intros fp ra a IN Ha. pose proof (HS _ _ IN). pose proof (ah_chain_range H HH _ _ _ _ _ C IN) as (R1 & R2 & R3). acb.
    apply XP; [lia|]. split; [left; lia|]. intros K. pose proof (HX _ K). lia.
  Qed.
  Lemma rin_memflag_low : forall a, rin_ivs memflag_foot a -> a < aceil.
  Proof. intros a Ha. acb. unfold memflag_foot, A_mem_inited in Ha. cbn in Ha. lia. Qed.

  (* [comment removed for export] *)
  Lemma lib_addr_where : forall s LBx m0 L a,
    as_RHEAP H s LBx m0 -> (forall b, In b L -> In b LBx) -> lib_addr L a ->
    (a < AIMG_TOP /\ alibx_ok a) \/ (in_block L a /\ AIMG_TOP <= a < aceil) \/ (in_block_sh L a /\ sh AIMG_TOP <= a < sh aceil).
  Proof.
    intros s LBx m0 L a HP SUB [HX|[(b & Hb & R)|(b & Hb & R)]].
    - left. split; [apply LIBX_below; exact HX| apply alo_libx_proof; exact HX].
    - right; left. pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & _ & D4 & D5 & _). split; [exists b; split; assumption| lia].
    - right; right. pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & D3 & _ & _ & _ & D7).
      pose proof (sh_aapp_range _ _ D7 D3) as (S1 & S2 & S3). split; [exists b; split; assumption| lia].
  Qed.

  (* [comment removed for export] *)
  Definition win_lib_ok (L : list block) (iv : Z * Z) : Prop :=
    aceil <= fst iv \/ (AIMG_TOP <= fst iv /\ (snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) /\ forall a, in_block L a -> a < fst iv \/ snd iv <= a).
  Lemma lib_addr_outside : forall s LBx m0 L W a,
    as_RHEAP H s LBx m0 -> (forall b, In b L -> In b LBx) -> Forall (win_lib_ok L) W -> lib_addr L a -> outside W a.
  Proof.
    intros s LBx m0 L W a HP SUB FW HL. pose proof (lib_addr_where s LBx m0 L a HP SUB HL) as CASES.
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. acb.
    clear HL. unfold win_lib_ok in FW. induction W as [|[lo hi] W IH]; [exact I|]. cbn. pose proof (Forall_inv FW) as K. cbn [fst snd] in K.
    split; [| exact (IH (Forall_inv_tail FW))].
    destruct K as [K|(K1 & K2 & K3)].
    - destruct CASES as [[C _]|[[_ C]|[_ C]]]; unfold AIMG_TOP in *; lia.
    - destruct CASES as [[C _]|[[C _]|[_ C]]]; [lia| destruct (K3 _ C); lia| unfold ALOWSH_LO, AHI_LO in *; lia].
  Qed.
  Lemma magree_lib_munch : forall s LBx m0 L W m m',
    as_RHEAP H s LBx m0 -> (forall b, In b L -> In b LBx) -> munch W m m' -> wmono asegs m m' -> Forall (win_lib_ok L) W ->
    magree (lib_addr L) m m'.
  Proof. intros s LBx m0 L W m m' HP SUB MU WM FW. eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha. eapply lib_addr_outside; eassumption. Qed.

  (* [comment removed for export] *)
  Lemma magree_mf_of_xpres : forall s LBx m0 L SP m m',
    as_RHEAP H s LBx m0 -> (forall b, In b L -> In b LBx) -> xpres H LBx SP memflag_foot m m' -> magree (lib_addr_mf L) m m'.
  Proof.
    intros s LBx m0 L SP m m' HP SUB XP a Ha [HL NF]. apply XP; [exact Ha|]. split.
    - destruct HL as [HX|[(b & Hb & R)|(b & Hb & R)]].
      + right; left. pose proof (alo_libx_proof a HX) as W. unfold alibx_ok, aimg_client in *. lia.
      + right; right; left. exists b. split; [apply SUB; exact Hb| exact R].
      + right; right; right; left. exists b. split; [apply SUB; exact Hb| exact R].
    - unfold memflag_foot. cbn. intros [K|K]; [apply NF; exact K| exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma fs_scratch_apart_app : forall LF m iv A n,
    as_RFS H LF m -> fs_scratch H LF iv -> aapp A n -> 0 <= n -> (A + n <= as_FSB H \/ as_FSB H + AFS_SIZE <= A) ->
    A + n <= fst iv \/ snd iv <= A.
  Proof.
    intros LF m iv A n R SC AP Hn HF. destruct (proj1 (ah_RFS_range H HH _ _ R)) as (F1 & F2 & F3 & F4). acb.
    pose proof (aapp_not_shadowland _ _ AP) as NS. assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
    destruct SC as [->|(k & ff & fp & FF & E)]; cbn [fst snd].
    - unfold AFS_FLAGS, AFS_SIZE in *. lia.
    - pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      pose proof (fsz_pos k ltac:(lia)) as FP. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *.
      destruct E as [-> |[-> | ->]]; cbn [fst snd]; [lia| lia|].
      pose proof (sh_aapp_range ff (fsz k) ltac:(eapply aapp_sub; [exact P9| lia| lia]) ltac:(lia)) as (S1 & S2 & S3).
      rewrite fshn_nsh by lia. unfold ALOWSH_LO, AHI_LO in *. lia.
  Qed.
  Lemma fs_scratch_apart_blocksh : forall LF m iv A n,
    as_RFS H LF m -> fs_scratch H LF iv -> ablock_range H A n -> n mod 8 = 0 ->
    sh A + nsh n <= fst iv \/ snd iv <= sh A.
  Proof.
    intros LF m iv A n R SC BR N8. destruct (proj1 (ah_RFS_range H HH _ _ R)) as (F1 & F2 & F3 & F4). acb.
    pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof (aapp_not_shadowland _ _ B7) as NS.
    pose proof (sh_aapp_range A n B7 B3) as (SA1 & SA2 & SA3). assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
    pose proof (aapp_not_shadowland _ _ F4) as NSF.
    assert (SHN : sh A + nsh n = sh (A + n)) by (unfold nsh, sh; Z.div_mod_to_equations; lia).
    destruct SC as [->|(k & ff & fp & FF & E)]; cbn [fst snd].
    - unfold AFS_FLAGS, AFS_SIZE, ALOWSH_LO, AHI_LO in *. lia.
    - pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      pose proof (fsz_pos k ltac:(lia)) as FP. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *.
      destruct E as [-> |[-> | ->]]; cbn [fst snd]; [unfold ALOWSH_LO, AHI_LO in *; lia| unfold ALOWSH_LO, AHI_LO in *; lia|].
      rewrite fshn_nsh by lia. replace (sh ff + nsh (fsz k)) with (sh (ff + fsz k)) by (unfold fsz, nsh, sh; Z.div_mod_to_equations; nia || lia).
      rewrite SHN. destruct B6 as [B6|B6].
      + left. apply sh_mono. unfold AFS_HDR in *. lia.
      + right. apply sh_mono. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma addressable_xpres_gen : forall LB2 m m' SP X p A n,
    In (p, A, n) LB2 -> A + n <= AAPP_HI -> addressable m A n -> xpres H LB2 SP X m m' ->
    (forall a, sh A <= a < sh A + nsh n -> ~ rin_ivs X a) -> addressable m' A n.
  Proof.
    intros LB2 m m' SP X p A n IN Htop (Hn & A0 & A8 & (B0 & B1 & BA) & (W0 & W1 & WA)) XP NX. acb.
    assert (CL : forall i, 0 <= i < nsh n -> m' (wa (sh A + i)) = m (wa (sh A + i)) /\ (wview asegs m (wa (sh A + i)) <> None -> wview asegs m' (wa (sh A + i)) <> None)).
    { intros i Hi. apply XP.
      - unfold nsh in Hi. unfold sh, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
      - split; [| apply NX; lia]. right; right; right; left. exists (p, A, n). split; [exact IN|]. cbn [blk_addr blk_size fst snd]. lia. }
    split; [exact Hn|]. split; [exact A0|]. split; [exact A8|]. split.
    - split; [exact B0|]. split; [exact B1|].
      intros i Hi. rewrite <- (BA i Hi). unfold mrd. destruct (CL (Z.of_nat i) ltac:(pose proof (shadow_of_length n Hn); lia)) as [E _]. rewrite E. reflexivity.
    - split; [exact W0|]. split; [exact W1|].
      intros i Hi. destruct (CL i ltac:(pose proof (shadow_of_length n Hn); lia)) as [_ Wp]. apply Wp. apply WA. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma CTX_X_range : Forall (fun iv : Z * Z => 0x5ea000 <= fst iv /\ snd iv <= AIMG_TOP) CTX_X.
  Proof.
    unfold CTX_X, A_destructor_key, A_defctx_inited, A_defctx, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret,
      A_base_inited, A_in_init_config_key, A_base_once, A_base_ret, A_optsdone_lock, A_init_lock, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, AIMG_TOP.
    repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
  Qed.
  Lemma ctxph_foot_range : forall ph, Forall (fun iv : Z * Z => 0x5ea000 <= fst iv /\ snd iv <= AIMG_TOP) (ctxph_foot ph).
  Proof. intros ph. apply ctxph_foot_rangeX. Qed.

  (* [comment removed for export] *)
  Lemma RFS_across_wins : forall LF m m' W,
    as_RFS H LF m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => aceil <= fst iv \/ (AIMG_TOP <= fst iv /\ (snd iv <= as_FSB H \/ as_FSB H + AFS_SIZE <= fst iv))) W ->
    as_RFS H LF m'.
  Proof.
    intros LF m m' W R MU WM FW. destruct (proj1 (ah_RFS_range H HH _ _ R)) as (F1 & F2 & F3 & F4). acb.
    eapply (ah_RFS_frame H HH); [exact R| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros [lo hi] K. unfold afs_write_ok. cbn [fst snd] in *. left.
    unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *. lia.
  Qed.
End K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section K2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Lemma aclient_cases : forall s LB m0 SP a,
    as_RHEAP H s LB m0 -> aclient_addr H LB SP a -> 0 <= a < 2^64 -> SP <= a \/ a < aceil.
  Proof.
    intros s LB m0 SP a RH Hc Ha. unfold aclient_addr in Hc. destruct Hc as [Hc|Hc]; [left; exact Hc| right].
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3). acb.
    destruct Hc as [Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]].
    - unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP in *. lia.
    - pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (_ & _ & _ & _ & R & _). lia.
    - pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (_ & _ & R0 & R1 & R & _).
      pose proof (sh_below_aceil (blk_addr b + blk_size b + 8) ltac:(unfold AIMG_TOP, AAPP_HI in *; lia)).
      unfold nsh, sh in *. rewrite ASHADOW_BASE_val in *. Z.div_mod_to_equations. lia.
    - lia.
    - pose proof (sh_below_aceil (as_FSB H + AFS_SIZE) ltac:(unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; lia)). unfold AFS_SIZE in *. lia.
    - unfold AHI_LO in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_drop_fresh : forall s' LB m0 p A n SP SP' wlo whi X m m',
    as_RHEAP H s' ((p, A, n) :: LB) m0 -> aceil <= SP -> SP <= SP' -> A <= wlo -> whi <= A + n ->
    xpres H ((p, A, n) :: LB) SP ((wlo, whi) :: X) m m' -> xpres H LB SP' X m m'.
  Proof.
    intros s' LB m0 p A n SP SP' wlo whi X m m' RH CE LE W1 W2 XP a Ha [HC HX]. apply XP; [exact Ha|]. split.
    - eapply aclient_addr_weaken; [exact HC| exact LE| intros b Hb; right; exact Hb].
    - cbn. intros [K|K]; [| exact (HX K)].
      eapply (afresh_outside H HH); [exact RH| exact CE| eapply aclient_addr_weaken; [exact HC| exact LE| auto]| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma ADL_across : forall s LBx m0 L W m m',
    as_RHEAP H s LBx m0 -> (forall b, In b L -> In b LBx) ->
    Forall (fun b => addressable m (blk_addr b) (blk_size b)) L -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) W ->
    Forall (fun b => addressable m' (blk_addr b) (blk_size b)) L.
  Proof.
    intros s LBx m0 L W m m' HP SUB AD MU WM NSW. apply Forall_forall. intros b Hb.
    pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & _ & _ & _ & _ & B7).
    eapply addressable_across2; [exact (proj1 (Forall_forall _ _) AD b Hb)| exact B7| exact MU| exact WM| exact NSW].
  Qed.
  Lemma ADL_xpres_mf : forall s LBx m0 L SP m m',
    as_RHEAP H s LBx m0 -> (forall b, In b L -> In b LBx) ->
    Forall (fun b => addressable m (blk_addr b) (blk_size b)) L -> xpres H LBx SP memflag_foot m m' ->
    Forall (fun b => addressable m' (blk_addr b) (blk_size b)) L.
  Proof.
    intros s LBx m0 L SP m m' HP SUB AD XP. apply Forall_forall. intros b Hb.
    pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & B3 & B4 & _ & _ & B7).
    pose proof (aapp_bounds _ _ B7 B3) as (_ & _ & AB3 & _). destruct b as [[q a0] n0]. cbn [blk_addr blk_size fst snd] in *.
    eapply addressable_xpres_gen; [apply SUB; exact Hb| lia| exact (proj1 (Forall_forall _ _) AD _ Hb)| exact XP|].
    intros a Ha. unfold memflag_foot, A_mem_inited. cbn. unfold AIMG_TOP in *. assert (ASHADOW_BASE <= sh a0) by (unfold sh; Z.div_mod_to_equations; lia).
    rewrite ASHADOW_BASE_val in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ACONST_frame_win : forall W m m', ACONST m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => aceil <= fst iv \/ exists A n, aapp A n /\ A <= fst iv /\ snd iv <= A + n) W -> ACONST m'.
  Proof.
    intros W m m' AC MU WM FW. eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros [lo hi] K. cbn [fst snd] in K. destruct K as [K|(A & n & AP & K1 & K2)].
    - apply aconst_ok_high; cbn [fst snd]; acb; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
    - eapply aconst_ok_aapp; [exact AP| cbn; lia| cbn; lia].
  Qed.
End K2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  (* [comment removed for export] *)
  Hypothesis CNX : cnewex_stmt H.

  Definition anm_R (buf len Abb Abm Arp : Z) (i1 i2 i3 i4 : bptr) : membio :=
    mkMB buf len 0 (BIO_FLAGS_MEM_RDONLY + BIO_FLAGS_MEM_LEGACY_EOF) 0 0 0 0 Abb Abm Arp i1 i2 i3 i4.

  Lemma rin_Forall : forall (P : Z * Z -> Prop) X a, Forall P X -> rin_ivs X a -> exists iv, In iv X /\ P iv /\ fst iv <= a < snd iv.
  Proof.
    intros P X a FA R. induction X as [|iv X IH]; [destruct R|]. cbn in R. destruct R as [R|R].
    - exists iv. split; [left; reflexivity|]. split; [exact (Forall_inv FA)| exact R].
    - destruct (IH (Forall_inv_tail FA) R) as (iv' & I1 & I2 & I3). exists iv'. split; [right; exact I1|]. split; assumption.
  Qed.
  (* [comment removed for export] *)
  Lemma X4_low : forall LF m XS ph A a, as_RFS H LF m -> Forall (fs_scratch H LF) XS -> A + 128 <= aceil ->
    rin_ivs ((A + 112, A + 112 + 16) :: ctxph_foot ph ++ XS) a -> a < aceil.
  Proof.
    intros LF m XS ph A a R FX ACE K. cbn [rin_ivs fst snd] in K. destruct K as [K|K]; [lia|]. apply rin_ivs_app in K. destruct K as [K|K].
    - destruct (rin_Forall _ _ _ (ctxph_foot_range ph) K) as (iv & _ & [P1 P2] & P3). acb. unfold AIMG_TOP in *. lia.
    - destruct (rin_Forall _ _ _ FX K) as (iv & _ & P & P3). pose proof (fs_scratch_below_ceil H HH _ _ _ R P). lia.
  Qed.
  Lemma X4_apart_hi : forall LF m XS ph T n, as_RFS H LF m -> Forall (fs_scratch H LF) XS -> aceil <= T ->
    Forall (fun iv : Z * Z => T + n <= fst iv \/ snd iv <= T) (ctxph_foot ph ++ XS).
  Proof.
    intros LF m XS ph T n R FX CE. apply Forall_app. split.
    - eapply Forall_impl; [| exact (ctxph_foot_range ph)]. intros iv [P1 P2]. acb. unfold AIMG_TOP in *. lia.
    - eapply Forall_impl; [| exact FX]. intros iv P. pose proof (fs_scratch_below_ceil H HH _ _ _ R P). lia.
  Qed.
  Lemma X4_apart_blk : forall LF m XS ph A n k, as_RFS H LF m -> Forall (fs_scratch H LF) XS -> ablock_range H A n -> 0 <= k <= n ->
    Forall (fun iv : Z * Z => A + k <= fst iv \/ snd iv <= A) (ctxph_foot ph ++ XS).
  Proof.
    intros LF m XS ph A n k R FX BR HK. pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7). apply Forall_app. split.
    - eapply Forall_impl; [| exact (ctxph_foot_range ph)]. intros iv [P1 P2]. lia.
    - eapply Forall_impl; [| exact FX]. intros iv P.
      destruct (fs_scratch_apart_app H HH _ _ _ A k R P ltac:(eapply aapp_sub; [exact B7| lia| lia]) ltac:(lia) ltac:(lia)); lia.
  Qed.
  Lemma X4_apart_shA : forall LF m XS ph A, as_RFS H LF m -> Forall (fs_scratch H LF) XS -> ablock_range H A 128 ->
    forall a, sh A <= a < sh A + nsh 128 -> ~ rin_ivs ((A + 112, A + 112 + 16) :: ctxph_foot ph ++ XS) a.
  Proof.
    intros LF m XS ph A R FX BR a Ha K. pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7). change (nsh 128) with 16 in Ha.
    pose proof (aapp_not_shadowland _ _ B7) as NS. pose proof (sh_aapp_range A 128 B7 ltac:(lia)) as (S1 & S2 & S3).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
    cbn [rin_ivs fst snd] in K. destruct K as [K|K].
    - unfold sh, ALOWSH_LO, AHI_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *. Z.div_mod_to_equations. lia.
    - apply rin_ivs_app in K. destruct K as [K|K].
      + destruct (rin_Forall _ _ _ (ctxph_foot_range ph) K) as (iv & _ & [P1 P2] & P3). unfold AIMG_TOP in *. lia.
      + destruct (rin_Forall _ _ _ FX K) as (iv & _ & P & P3).
        destruct (fs_scratch_apart_blocksh H HH _ _ _ A 128 R P BR ltac:(reflexivity)); change (nsh 128) with 16 in *; lia.
  Qed.

  Local Ltac mpacc MPA0 MP := let T := fresh "MPX" in pose proof (ah_mpres_trans H HH _ _ _ MPA0 MP) as T; clear MPA0 MP; rename T into MPA0.
  Local Ltac hlia := first [lia | unfold hidden in *; lia].
  Local Ltac fw := repeat (apply Forall_cons; [try unfold win_lib_ok; cbn [fst snd]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, ATLS_PRIV_LO, ATP, memflag_foot, A_mem_inited; rewrite ?ASHADOW_BASE_val|]); try apply Forall_nil.

  Lemma anewmembuf_spec : newmembuf_stmt H.
  Proof.
    unfold newmembuf_stmt. intros until CH.
    intros VIS A0 A1 BP BH LR HP KREL BUD BUDC AUX SPB SPA ST CEIL LO SH0 ERR MI TP AC MF IM GM METH RL CPH RFS LFB CHN CHS PF PCL HAL RAE.
    pose proof (ctxph_nonneg H HH ph) as (PHB & PHC & PHS & PHK). set (XST := CNEWEX_STACK ph) in *.
    unfold NEWMEMBUF_STACK, BIONEW_STACK, MEMINIT_STACK, BUFNEW_STACK, CZALLOC_STACK, CMALLOC_STACK, AMALLOC_STACK, AINTRIN_STACK, FR_BIO_new_mem_buf, FR_BIO_new_ex,
      FR_mem_init, FR_BUF_MEM_new, FR_CRYPTO_zalloc, FR_CRYPTO_malloc in LO.
    unfold MEMBIO_BYTES, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in BUD.
    pose proof (ah_costs H HH) as (CM0 & _ & CF0 & _). unfold NEWMEMBUF_COST, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in HAL.
    pose proof (CM0 16 ltac:(lia)) as CM16. pose proof (CM0 32 ltac:(lia)) as CM32. pose proof (CM0 128 ltac:(lia)) as CM128. pose proof (CF0 0 ltac:(lia)) as CF00.
    acb. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply anm_seg1 with (lo := lo); [exact A0| exact A1| exact BP| exact BH| exact LR| exact AC| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MPA (m1 & j1 & VIS1 & MU1 & WM1 & MI1 & ST1 & F01 & F21).
    assert (CW1 : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -112, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW1]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW1]).
    assert (AC1 : ACONST m1) by (eapply ACONST_stack_frame; [exact AC| exact MU1| exact WM1| lia]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (MF1 : MEMFLAG m1 1) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (RL1 : arelro_lib m1) by (eapply arelro_across7; [exact RL| exact MU1| fw; hlia]).
    assert (RFS1 : as_RFS H LF m1) by (eapply (RFS_across_wins H HH); [exact RFS| exact MU1| exact WM1| fw; left; hlia]).
    assert (SH01 : ctxph_sh0 ph m1 lo sp).
    { destruct ph; [| exact I]. cbn in SH0 |- *. eapply stack0_transport; [exact SH0| exact MU1| exact WM1| constructor; [apply stack0_ok_app; cbn; unfold AHI_LO; lia| constructor]]. }
    assert (CPH1 : CTXPH LB m1 ph).
    { eapply CTXPH_frame; [exact CPH|]. eapply (magree_lib_munch H HH); [exact HP| auto| exact MU1| exact WM1| fw; left; hlia]. }
    assert (XP1 : forall X, xpres H LB (bv_unsigned sp) X m m1).
    { intros X. eapply (xpres_of_munch H s LB _ X _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    (* [comment removed for export] *)
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. constructor; [left; cbn; lia| constructor]. }
    set (CH1 := (bv_unsigned sp, bv_unsigned ra) :: CH). set (CH2 := (bv_unsigned sp + -48, ANMB_RET) :: CH1).
    assert (CHN1 : as_chain H m1 (bv_unsigned sp) CH1).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SPA| lia| lia|].
      pose proof F01 as FR. change ([C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [_ FR].
      lazymatch type of FR with rw_cells _ _ ?adr _ => replace adr with (bv_unsigned sp - 16) in FR by (cbn; lia) end. rewrite !Z_to_bv_bv_unsigned. exact FR. }
    assert (CHN2 : as_chain H m1 (bv_unsigned sp + -48) CH2).
    { eapply (ah_chain_cons H HH); [exact CHN1| lia| unfold ANMB_RET; lia| replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity| lia| lia|].
      pose proof F21 as FR.
      change ([CB 8 j1; C8 s5; C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 len); C8 s1; C8 sp; C8 (Z_to_bv 64 ANMB_RET)])
        with ([CB 8 j1; C8 s5; C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 len); C8 s1] ++ [C8 sp; C8 (Z_to_bv 64 ANMB_RET)]) in FR.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [_ FR].
      lazymatch type of FR with rw_cells _ _ ?adr _ => replace adr with (bv_unsigned sp + -48 - 16) in FR by (cbn; lia) end. rewrite Z_to_bv_bv_unsigned. exact FR. }
    assert (CHS2 : forall fp' ra', In (fp', ra') CH2 -> bv_unsigned sp + -112 + 16 <= fp').
    { intros fp' ra' [E|[E|Hin]]; [injection E as <- <-; lia| injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]. }
    assert (PF1 : pf_ok (as_TR H) (PF_bionewex ph) ANMB_RET CH1).
    { eapply pf_ok_call; [exact PF|]. unfold PF_newmembuf, R_BIO_new_mem_buf_BIO_new, ANMB_RET. intros q Hq; exact Hq. }
    (* [comment removed for export] *)
    pose proof (aczalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (ah_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB) (s := s) (v := 1) (num := 128) (size := 1) (CH := CH2);
        [exact VIS1| reflexivity| reflexivity| ..]; rewrite ?Z.mul_1_r; rewrite ?unsigned_lit by (unfold ANEX_RA1; clear - SPR LO LO0 PHS; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- as_rauxv_ok _ _ _ => exact AUX1
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => exact ERR1
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- ACONST _ => exact AC1
           | |- as_chain _ _ _ _ => exact CHN2
           | |- forall fp' ra', In _ _ -> _ => exact CHS2
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF1|]; unfold PF_bionewex, R_BIO_new_ex_CRYPTO_zalloc, ANEX_RA1; intros q Hq; apply in_or_app; left; exact Hq
           | |- _ <= as_AL _ _ => clear - HAL CM16 CM32 CM128 CF00 PHK; lia
           | |- MEMFLAG _ _ => exact MF1
           | |- IMPL_mem _ => exact IM1
           | |- GOT_mem _ => exact GM1
           | |- lb_bytes _ + _ <= _ => clear - BUD PHB; lia
           | |- Z.of_nat (length _) + _ <= _ => clear - BUDC PHC; lia
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 PHS CEIL; unfold CZALLOC_STACK, CMALLOC_STACK, AMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc; lia]
           end | idtac "CZ1-FAIL:" G; fail ] end. }
    clear CZ. intros [msF2 mo2] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO. rewrite ?Z.mul_1_r in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p1 & s2' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & BR1 & HEAP2 & BLK2 & ADDR2 & MF2 & IM2 & GM2 & AL2). mpacc MPA MP2.
    rewrite (unsigned_lit (bv_unsigned sp + -112)) in ST2, XP2 by lia. rewrite unsigned_lit in ERR2 by (unfold ATP; lia).
    pose proof BR1 as (AP & AAL & _ & AH & ACE & AFS & AAP). unfold AIMG_TOP in AH.
    pose proof (aapp_bounds A 128 AAP ltac:(lia)) as (_ & _ & ATOP & _ & _). unfold AAPP_HI in ATOP.
    pose proof (aapp_not_shadowland _ _ AAP) as NSA. unfold ALOWSH_LO, AHI_LO in NSA. hide NSA. hide AFS.
    set (LB1 := (p1, A, 128) :: LB) in *.
    assert (SUB01 : forall b, In b LB -> In b LB1) by (intros b Hb; right; exact Hb).
    assert (AIN1 : In (p1, A, 128) LB1) by (left; reflexivity).
    assert (F02 : rw_cells asegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact F01| left; cbn; lia| fw; hlia]. }
    assert (F22 : rw_cells asegs m2 (bv_unsigned sp + -112) [CB 8 j1; C8 s5; C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 len); C8 s1; C8 sp; C8 (Z_to_bv 64 ANMB_RET)]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact F21| left; cbn; lia| fw; hlia]. }
    assert (RL2 : arelro_lib m2) by (eapply (arelro_xpres H); [exact RL1| exact XP2| fw; hlia]).
    assert (RFS2 : as_RFS H LF m2) by (eapply (RFS_via_xpres H HH); [exact RFS1| exact XP2| fw; hlia]).
    assert (SH02 : ctxph_sh0 ph m2 lo sp).
    { destruct ph; [| exact I]. cbn in SH01 |- *. eapply (stack0_xpres H); [exact XP2| exact SH01|]. unfold memflag_foot, A_mem_inited. constructor; [right; cbn; acb; unfold sh; rewrite ASHADOW_BASE_val; lia| constructor]. }
    assert (CPH2 : CTXPH LB m2 ph) by (eapply CTXPH_frame_mf; [exact CPH1| eapply (magree_mf_of_xpres H); [exact HP1| auto| exact XP2]]).
    assert (CHN3 : as_chain H m2 (bv_unsigned sp + -48) CH2) by (eapply (chain_via_xpres H HH); [exact CHN2| exact XP2| exact CHS2| apply rin_memflag_low]).
    apply bio_zero_recut in BLK2.
    assert (ACC2 : accessible m2 A 128) by (eapply addressable_accessible; [exact ADDR2| lia| lia| unfold AAPP_HI; lia]).
    clear VIS1 KREL1 HP1 AUX1 AC1 ERR1 MF1 IM1 GM1 RL1 RFS1 CPH1 CH0 CHN1 CHN2 MI1 ST1 F01 F21.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply anm_seg2; [exact AP| exact AAL| exact ACE| exact AAP| exact BLK2| exact ACC2| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 (m3 & VIS3 & MU3 & WM3 & MI3 & BA3). unfold BIO_SIZE in MU3. mpacc MPA MP3.
    assert (CW3 : Forall (aclient_write_ok H LB1) [(A, A + 128)]).
    { constructor; [| constructor]. right; right; left. exists (p1, A, 128). split; [exact AIN1| cbn; hlia]. }
    assert (NSWA : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(A, A + 128)]) by (fw; hlia).
    apply (stk_transport_disjoint asegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| cbn; hlia].
    apply (rw_cells_transport asegs _ m2 m3 _ _ F02) in MU3 as F03; [| exact WM3| cbn; hlia].
    apply (rw_cells_transport asegs _ m2 m3 _ _ F22) in MU3 as F23; [| exact WM3| cbn; hlia].
    assert (ERR3 : rw_cells asegs m3 (ATP + -164) [C4 errv2]) by (eapply errno_across; [exact ERR2| exact MU3| exact WM3| unfold ATP; cbn; lia]).
    assert (AUX3 : as_rauxv_ok H m3 B) by (eapply (ah_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3| exact CW3]).
    assert (HEAP3 : as_RHEAP H s2' LB1 m3) by (eapply (ah_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3| exact CW3]).
    assert (AC3 : ACONST m3) by (eapply ACONST_frame; [exact AC2| exact MU3| exact WM3| constructor; [eapply aconst_ok_aapp; [exact AAP| cbn; lia| cbn; lia]| constructor]]).
    assert (MF3 : MEMFLAG m3 1) by (eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]).
    assert (IM3 : IMPL_mem m3) by (eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]).
    assert (GM3 : GOT_mem m3) by (eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2]).
    assert (RL3 : arelro_lib m3) by (eapply arelro_across7; [exact RL2| exact MU3| fw; hlia]).
    assert (RFS3 : as_RFS H LF m3) by (eapply (RFS_across_wins H HH); [exact RFS2| exact MU3| exact WM3| fw; right; hlia]).
    assert (SH03 : ctxph_sh0 ph m3 lo sp).
    { destruct ph; [| exact I]. cbn in SH02 |- *. eapply stack0_transport; [exact SH02| exact MU3| exact WM3| constructor; [eapply stack0_ok_aapp; [exact AAP| lia| lia]| constructor]]. }
    assert (CPH3 : CTXPH LB1 m3 ph).
    { apply (CTXPH_mono LB LB1 SUB01). eapply CTXPH_frame; [exact CPH2|]. eapply (magree_lib_munch H HH); [exact HEAP2| exact SUB01| exact MU3| exact WM3|].
      fw. right. split; [hlia|]. split; [hlia|]. intros a (b & Hb & R).
      destruct (Z.lt_ge_cases a A) as [K|K]; [left; exact K|]. destruct (Z.le_gt_cases (A + 128) a) as [K2|K2]; [right; exact K2|].
      exfalso. eapply (afresh_outside H HH); [exact HEAP2| exact CEIL| right; right; left; exists b; split; [exact Hb| exact R]| lia]. }
    assert (ADDR3 : addressable m3 A 128) by (eapply addressable_across2; [exact ADDR2| exact AAP| exact MU3| exact WM3| exact NSWA]).
    assert (CHN4 : as_chain H m3 (bv_unsigned sp + -48) CH2).
    { eapply (chain_via_munch H HH); [exact CHN3| exact MU3|]. intros fp' ra' Hin. pose proof (CHS2 _ _ Hin). cbn. split; [lia| exact I]. }
    assert (XP3 : xpres H LB (bv_unsigned sp) (memflag_foot ++ ctxph_foot ph) m2 m3).
    { eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU3| exact WM3|]. constructor; [right; left; cbn; lia| constructor]. }
    destruct (bio_cells_split_ex _ _ _ BA3) as [BA3a EXD3].
    assert (ACC3x : accessible m3 (A + 112) 16) by (eapply accessible_sub; [eapply accessible_across2; [exact ACC2| exact MU3| exact NSWA]| lia| lia| lia]).
    clear VIS2 KREL2 MI2 AC2 ST2 ERR2 AUX2 MF2 IM2 GM2 RL2 RFS2 CPH2 CHN3 ACC2 BLK2 F02 F22 BA3.
    (* [comment removed for export] *)
    pose proof CNX as CN. unfold cnewex_stmt in CN.
    eapply (ah_seq H HH).
    { eapply CN with (lo := lo) (B := B) (LB := LB1) (s := s2') (ph := ph) (obj := A) (ad := A + O_BIO_EXDATA) (c0 := 0) (k0 := 0) (LF := LF) (CH := CH2);
        [exact VIS3| ..]; unfold O_BIO_EXDATA; rewrite ?unsigned_lit by (unfold ANEX_RA2; clear - SPR LO LO0 PHS ACE AH; lia); try reflexivity.
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- rw_cells _ _ (_ + 112) _ => exact EXD3
           | |- xclient_range _ _ _ _ _ _ => eapply (ashobj_xclient_range H); [left; exists (p1, A, 128); split; [exact AIN1| cbn; lia]|];
                                            eapply Forall_impl; [| exact CTX_X_range]; intros iv K; cbn beta in K; unfold AIMG_TOP in K; lia
           | |- ainblk _ _ _ => exists (p1, A, 128); split; [exact AIN1| cbn; lia]
           | |- ctxph_sh0 _ _ _ _ => destruct ph; [| exact I]; cbn in SH03 |- *; rewrite unsigned_lit by lia; eapply stack0_sub; [exact SH03| clear; lia| clear - SPR SPB LO LO0 PHS CEIL ACE AH; lia| clear - SPA SPR; Z.div_mod_to_equations; lia]
           | |- ctxph_closed_ok _ _ => exact PCL
           | |- accessible _ _ _ => exact ACC3x
           | |- forall x0, _ = CtxReady x0 -> _ =>
               intros x Hph; pose proof CPH3 as C; rewrite Hph in C; cbn [CTXPH] in C; destruct C as [_ [[BIN [BSZ _]] _]];
               destruct BIN as [EQ|BIN]; [rewrite <- EQ in BSZ; cbn in BSZ; unfold MUTEX_SIZE in BSZ; lia|]; 
               destruct (cx_exlock x) as [[q ea] en]; cbn [blk_addr blk_size fst snd] in *; 
               pose proof (afresh_apart H HH _ _ _ _ _ _ lo ea MUTEX_SIZE HEAP2 CEIL
                  ltac:(eapply aclient_range_block; [exact BIN| lia| rewrite BSZ; lia])
                  ltac:(unfold MUTEX_SIZE; lia) ltac:(lia)) as D;
               unfold MUTEX_SIZE in *; lia
           | |- as_RHEAP _ _ _ _ => exact HEAP3
           | |- as_AKREL _ _ _ => exact KREL3
           | |- lb_bytes _ + _ <= _ => unfold LB1; rewrite lb_bytes_cons; cbn [blk_size snd]; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold LB1; cbn [length]; lia
           | |- as_rauxv_ok _ _ _ => exact AUX3
           | |- stk _ _ _ _ => exact ST3
           | |- rw_cells _ _ _ [C4 _] => exact ERR3
           | |- mem_inv _ _ => exact MI3
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- _ mod 8 = 0 => clear - AAL; replace (A + 112) with (A + 8 * 14) by lia; rewrite Z.add_mod, Z.mul_comm, Z.mod_mul by lia; Z.div_mod_to_equations; lia
           | |- ACONST _ => exact AC3
           | |- MEMFLAG _ _ => exact MF3
           | |- IMPL_mem _ => exact IM3
           | |- GOT_mem _ => exact GM3
           | |- arelro_lib _ => exact RL3
           | |- CTXPH _ _ _ => exact CPH3
           | |- as_RFS _ _ _ => exact RFS3
           | |- (_ <= AFS_MAXLIVE)%nat => exact LFB
           | |- as_chain _ _ _ _ => exact CHN4
           | |- forall fp' ra', In _ _ -> _ => exact CHS2
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF1|]; unfold PF_bionewex, R_BIO_new_ex_CRYPTO_new_ex_data, ANEX_RA2; intros q Hq;
                                 apply in_or_app; right; apply in_or_app; left; exact Hq
           | |- _ <= as_AL _ _ => clear - AL2 HAL CM16 CM32 CM128 CF00 PHK; lia
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 PHS CEIL ACE AH; lia]
           end | idtac "CNX-FAIL:" G; fail ] end. }
    clear CN. intros [msF4 mo4] PO. unfold cnewex_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & errv4 & s4' & LBN & x & XS &
                    VIS4 & MP4 & (KREL4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & HEAP4 & MF4 & IM4 & GM4 & RL4) & DELTA & ADN4 & CPH4 & KEYS4 & EXD4 & FXS & RFS4 & XP4 & AL4). mpacc MPA MP4.
    unfold O_BIO_EXDATA in XP4, EXD4. rewrite (unsigned_lit (bv_unsigned sp + -112)) in ST4, XP4 by lia. rewrite unsigned_lit in ERR4 by (unfold ATP; lia).
    pose proof (ctxph_delta_bounds _ _ _ DELTA) as (NB1 & NB2).
    set (LB2 := LBN ++ LB1) in *. set (L := LBN ++ LB).
    assert (SUB12 : forall b, In b LB1 -> In b LB2) by (intros b Hb; unfold LB2; apply in_or_app; right; exact Hb).
    assert (SUBL2 : forall b, In b L -> In b LB2) by (intros b Hb; unfold LB2, LB1; apply in_app_mid; exact Hb).
    assert (SUB0L : forall b, In b LB -> In b L) by (intros b Hb; unfold L; apply in_or_app; right; exact Hb).
    assert (AIN2 : In (p1, A, 128) LB2) by (apply SUB12; exact AIN1).
    pose proof (fun a => X4_low LF m4 XS ph A a RFS4 FXS ACE) as X4L.  (* [comment removed for export] *)
    assert (F04 : rw_cells asegs m4 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4); [exact F03| left; cbn; lia|]. constructor; [cbn; lia| eapply (X4_apart_hi _ _ _ ph); [exact RFS4| exact FXS| cbn; lia]]. }
    assert (F24 : rw_cells asegs m4 (bv_unsigned sp + -112) [CB 8 j1; C8 s5; C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 len); C8 s1; C8 sp; C8 (Z_to_bv 64 ANMB_RET)]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4); [exact F23| left; cbn; lia|]. constructor; [cbn; lia| eapply (X4_apart_hi _ _ _ ph); [exact RFS4| exact FXS| cbn; lia]]. }
    assert (BA4a : rw_cells asegs m4 A (firstn 18 (bio_cells (bio_hdr1 A_mem_buf_method)))).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4); [exact BA3a| eapply aclient_range_block; [exact AIN1| lia| cbn; lia]|].
      constructor; [cbn; lia| eapply (X4_apart_blk _ _ _ ph A 128); [exact RFS4| exact FXS| exact BR1| cbn; lia]]. }
    pose proof (bio_cells_join_ex _ _ _ BA4a EXD4) as BA4. clear BA4a EXD4.
    assert (ADDR4 : addressable m4 A 128).
    { eapply (addressable_xpres_gen H); [exact AIN1| unfold AAPP_HI; lia| exact ADDR3| exact XP4| eapply X4_apart_shA; [exact RFS4| exact FXS| exact BR1]]. }
    assert (ADL4 : Forall (fun b => addressable m4 (blk_addr b) (blk_size b)) ((p1, A, 128) :: LBN)) by (constructor; [exact ADDR4| exact ADN4]).
    assert (SUBA : forall b, In b ((p1, A, 128) :: LBN) -> In b LB2) by (intros b [<-|Hb]; [exact AIN2| unfold LB2; apply in_or_app; left; exact Hb]).
    assert (CHN5 : as_chain H m4 (bv_unsigned sp + -48) CH2) by (eapply (chain_via_xpres H HH); [exact CHN4| exact XP4| exact CHS2| exact X4L]).
    (* [comment removed for export] *)
    assert (CPHx : CTXPH L m4 (CtxReady x)).
    { cbn [CTXPH] in CPH4 |- *. destruct CPH4 as [CS [[BIN [BSZ [BRR BMX]]] (po & pi & O1 & O2)]].
      assert (DROP : forall q a n, In (q, a, n) LB2 -> n <> 128 -> In (q, a, n) L).
      { intros q a n Hin Hn. unfold LB2, LB1 in Hin. apply in_app_or in Hin. unfold L. apply in_or_app. destruct Hin as [Hin|[Hin|Hin]]; [left; exact Hin| | right; exact Hin].
        exfalso. injection Hin. lia. }
      split; [exact CS|]. split.
      - split; [| split; [exact BSZ| split; [exact BRR| exact BMX]]]. destruct (cx_exlock x) as [[q a] n]. cbn [blk_size snd] in BSZ. apply DROP; [exact BIN| unfold MUTEX_SIZE in BSZ; lia].
      - exists po, pi. split; apply DROP; try assumption; lia. }
    clear CPH4.
    (* [comment removed for export] *)
    assert (OUT_A : forall a, in_block L a -> a < A \/ A + 128 <= a).
    { intros a (b & Hb & R). unfold L in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      - assert (NE : blk_id b <> blk_id (p1, A, 128)).
        { eapply (nodup_ids_app_ne7 LBN LB1); [exact (ah_nodup H HH _ _ _ HEAP4)| exact Hb| exact AIN1]. }
        pose proof (ah_disj H HH _ _ _ _ _ HEAP4 ltac:(unfold LB2; apply in_or_app; left; exact Hb) AIN2 NE) as D. cbn [blk_addr blk_size fst snd] in D. lia.
      - destruct (Z.lt_ge_cases a A) as [K|K]; [left; exact K|]. destruct (Z.le_gt_cases (A + 128) a) as [K2|K2]; [right; exact K2|].
        exfalso. eapply (afresh_outside H HH); [exact HEAP2| exact CEIL| right; right; left; exists b; split; [exact Hb| exact R]| lia]. }
    assert (BY2 : lb_bytes LB2 = lb_bytes LBN + 128 + lb_bytes LB) by (unfold LB2, LB1; rewrite lb_bytes_app7, lb_bytes_cons; cbn [blk_size snd]; lia).
    assert (CN2 : Z.of_nat (length LB2) = Z.of_nat (length LBN) + 1 + Z.of_nat (length LB)) by (unfold LB2, LB1; rewrite length_app; cbn [length]; lia).
    assert (PF3 : pf_ok (as_TR H) PF_meminit ANEX_RA3 CH2).
    { eapply pf_ok_call; [exact PF1|]. unfold PF_bionewex, R_BIO_new_ex_create, ANEX_RA3. intros q Hq. apply in_or_app; right; apply in_or_app; right; exact Hq. }
    clear VIS3 KREL3 MI3 ST3 ERR3 AUX3 HEAP3 AC3 MF3 IM3 GM3 RL3 RFS3 CPH3 ADDR3 CHN4 ACC3x EXD3 BA3a F03 F23.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply anm_seg3 with (lo := lo) (A := A);
      [exact AC4| exact (METH_of_relro _ RL4)| rewrite unsigned_lit by lia; exact ST4| exact CEIL| rewrite unsigned_lit by lia; lia| exact MI4]|].
    intros msF5 mo5 KREL5 MP5 (m5 & VIS5 & MU5 & WM5 & MI5 & ST5 & F35). mpacc MPA MP5.
    rewrite (unsigned_lit (bv_unsigned sp + -112)) in MU5, ST5, F35, VIS5 by lia.
    replace (bv_unsigned sp + -112 + -48) with (bv_unsigned sp + -160) in MU5 by lia. replace (bv_unsigned sp + -112 + -48) with (bv_unsigned sp + -160) in ST5 by lia.
    replace (bv_unsigned sp + -112 + -48) with (bv_unsigned sp + -160) in F35 by lia. replace (bv_unsigned sp + -112 + -48) with (bv_unsigned sp + -160) in VIS5 by lia.
    assert (CW5 : Forall (aclient_write_ok H LB2) [(lo, bv_unsigned sp + -112)]) by (constructor; [left; cbn; lia| constructor]).
    assert (NSW5 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp + -112)]) by (fw; hlia).
    apply (rw_cells_transport asegs _ m4 m5 _ _ F04) in MU5 as F05; [| exact WM5| cbn; hlia].
    apply (rw_cells_transport asegs _ m4 m5 _ _ F24) in MU5 as F25; [| exact WM5| cbn; hlia].
    apply (rw_cells_transport asegs _ m4 m5 _ _ BA4) in MU5 as BA5; [| exact WM5| cbn; hlia].
    assert (ERR5 : rw_cells asegs m5 (ATP + -164) [C4 errv4]) by (eapply errno_across; [exact ERR4| exact MU5| exact WM5| unfold ATP; cbn; lia]).
    assert (AUX5 : as_rauxv_ok H m5 B) by (eapply (ah_rauxv_frame H HH); [exact AUX4| exact MU5| exact WM5| exact CW5]).
    assert (HEAP5 : as_RHEAP H s4' LB2 m5) by (eapply (ah_RHEAP_frame H HH); [exact HEAP4| exact MU5| exact WM5| exact CW5]).
    assert (AC5 : ACONST m5) by (eapply ACONST_stack_frame; [exact AC4| exact MU5| exact WM5| exact CEIL]).
    assert (MF5 : MEMFLAG m5 1) by (eapply MEMFLAG_across; [exact MU5| exact WM5| unfold A_mem_inited; cbn; lia| exact MF4]).
    assert (IM5 : IMPL_mem m5) by (eapply IMPL_across; [exact MU5| exact WM5| unfold A_malloc_impl; cbn; lia| exact IM4]).
    assert (GM5 : GOT_mem m5) by (eapply GOT_across; [exact MU5| exact WM5| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM4]).
    assert (RL5 : arelro_lib m5) by (eapply arelro_across7; [exact RL4| exact MU5| fw; hlia]).
    assert (RFS5 : as_RFS H LF m5) by (eapply (RFS_across_wins H HH); [exact RFS4| exact MU5| exact WM5| fw; left; hlia]).
    assert (CPH5 : CTXPH L m5 (CtxReady x)).
    { eapply CTXPH_frame; [exact CPHx|]. eapply (magree_lib_munch H HH); [exact HEAP4| exact SUBL2| exact MU5| exact WM5| fw; left; hlia]. }
    assert (KEYS5 : ph = CtxFresh -> CTX_keys m5).
    { intros E. eapply (CTX_keys_frame []); [exact (KEYS4 E)|]. eapply (magree_lib_munch H HH) with (L := []); [exact HEAP4| intros b []| exact MU5| exact WM5| fw; left; hlia]. }
    assert (ADL5 : Forall (fun b => addressable m5 (blk_addr b) (blk_size b)) ((p1, A, 128) :: LBN)).
    { eapply (ADL_across H HH); [exact HEAP4| exact SUBA| exact ADL4| exact MU5| exact WM5| exact NSW5]. }
    set (CH3 := (bv_unsigned sp + -112, ANEX_RA3) :: CH2).
    assert (CHN5b : as_chain H m5 (bv_unsigned sp + -48) CH2).
    { eapply (achain_below H HH m4 m5); [exact CHN5| exact CHS2| exact MU5|]. constructor; [right; intros fp' ra' Hin; pose proof (CHS2 _ _ Hin); cbn; lia| constructor]. }
    assert (CHN6 : as_chain H m5 (bv_unsigned sp + -112) CH3).
    { eapply (ah_chain_cons H HH); [exact CHN5b| lia| unfold ANEX_RA3; lia| replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity| lia| lia|].
      pose proof F35 as FR.
      change ([C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 (A + 112)); C8 (Z_to_bv 64 (A_mem_buf_method + 72)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 ANEX_RA3)])
        with ([C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 (A + 112)); C8 (Z_to_bv 64 (A_mem_buf_method + 72)); C8 (Z_to_bv 64 A)] ++ [C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 ANEX_RA3)]) in FR.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [_ FR].
      lazymatch type of FR with rw_cells _ _ ?adr _ => replace adr with (bv_unsigned sp + -112 - 16) in FR by (cbn; lia) end. exact FR. }
    assert (CHS3 : forall fp' ra', In (fp', ra') CH3 -> bv_unsigned sp + -160 + 16 <= fp').
    { intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS2 _ _ Hin); lia]. }
    clear VIS4 KREL4 MI4 AC4 ST4 ERR4 AUX4 MF4 IM4 GM4 RL4 RFS4 CPHx ADL4 CHN5 CHN5b F04 F24 BA4 ADDR4.
    (* [comment removed for export] *)
    pose proof (aczalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (ah_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB2) (s := s4') (v := 1) (num := 16) (size := 1) (CH := CH3);
        [exact VIS5| reflexivity| reflexivity| ..]; rewrite ?Z.mul_1_r; rewrite ?unsigned_lit by (unfold AMI_RA1; clear - SPR LO LO0 PHS; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HEAP5
           | |- as_AKREL _ _ _ => exact KREL5
           | |- as_rauxv_ok _ _ _ => exact AUX5
           | |- stk _ _ _ _ => exact ST5
           | |- rw_cells _ _ _ [C4 _] => exact ERR5
           | |- mem_inv _ _ => exact MI5
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -160) with (bv_unsigned sp - 160) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- ACONST _ => exact AC5
           | |- as_chain _ _ _ _ => exact CHN6
           | |- forall fp' ra', In _ _ -> _ => exact CHS3
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF3|]; unfold PF_meminit, R_mem_init_CRYPTO_zalloc, AMI_RA1; intros q Hq; apply in_or_app; left; exact Hq
           | |- _ <= as_AL _ _ => clear - AL4 AL2 HAL CM16 CM32 CM128 CF00 PHK; lia
           | |- MEMFLAG _ _ => exact MF5
           | |- IMPL_mem _ => exact IM5
           | |- GOT_mem _ => exact GM5
           | |- lb_bytes _ + _ <= _ => rewrite BY2; lia
           | |- Z.of_nat (length _) + _ <= _ => rewrite CN2; lia
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 PHS CEIL; unfold CZALLOC_STACK, CMALLOC_STACK, AMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc; lia]
           end | idtac "CZ2-FAIL:" G; fail ] end. }
    clear CZ. intros [msF6 mo6] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO. rewrite ?Z.mul_1_r in PO.
    destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m6 & errv6 & BB & p2 & s6' &
                    VIS6 & KREL6 & MP6 & MI6 & AC6 & ST6 & ERR6 & AUX6 & XP6 & BR2 & HEAP6 & BB6 & ADDRB6 & MF6 & IM6 & GM6 & AL6). mpacc MPA MP6.
    rewrite (unsigned_lit (bv_unsigned sp + -160)) in ST6, XP6 by lia. rewrite unsigned_lit in ERR6 by (unfold ATP; lia).
    pose proof BR2 as (BBP & BBAL & _ & BBH & BBCE & BBFS & BBAP). unfold AIMG_TOP in BBH.
    pose proof (aapp_bounds BB 16 BBAP ltac:(lia)) as (_ & _ & BBTOP & _ & _). unfold AAPP_HI in BBTOP.
    pose proof (aapp_not_shadowland _ _ BBAP) as NSB. unfold ALOWSH_LO, AHI_LO in NSB. hide NSB. hide BBFS.
    set (LB3 := (p2, BB, 16) :: LB2) in *.
    assert (SUB23 : forall b, In b LB2 -> In b LB3) by (intros b Hb; right; exact Hb).
    assert (BIN3 : In (p2, BB, 16) LB3) by (left; reflexivity).
    assert (F36 : rw_cells asegs m6 (bv_unsigned sp + -160) [C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 (A + 112)); C8 (Z_to_bv 64 (A_mem_buf_method + 72)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 ANEX_RA3)]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact F35| left; cbn; lia| fw; hlia]. }
    assert (F26 : rw_cells asegs m6 (bv_unsigned sp + -112) [CB 8 j1; C8 s5; C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 len); C8 s1; C8 sp; C8 (Z_to_bv 64 ANMB_RET)]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact F25| left; cbn; lia| fw; hlia]. }
    assert (F06 : rw_cells asegs m6 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact F05| left; cbn; lia| fw; hlia]. }
    assert (BA6 : rw_cells asegs m6 A (bio_cells (bio_hdr1 A_mem_buf_method))).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact BA5| eapply aclient_range_block; [exact AIN2| lia| cbn; lia]| fw; hlia]. }
    assert (RL6 : arelro_lib m6) by (eapply (arelro_xpres H); [exact RL5| exact XP6| fw; hlia]).
    assert (RFS6 : as_RFS H LF m6) by (eapply (RFS_via_xpres H HH); [exact RFS5| exact XP6| fw; hlia]).
    assert (CPH6 : CTXPH L m6 (CtxReady x)) by (eapply CTXPH_frame_mf; [exact CPH5| eapply (magree_mf_of_xpres H); [exact HEAP5| exact SUBL2| exact XP6]]).
    assert (KEYS6 : ph = CtxFresh -> CTX_keys m6).
    { intros E. eapply (CTX_keys_frame_mf []); [exact (KEYS5 E)|]. eapply (magree_mf_of_xpres H) with (L := []); [exact HEAP5| intros b []| exact XP6]. }
    assert (ADL6 : Forall (fun b => addressable m6 (blk_addr b) (blk_size b)) ((p2, BB, 16) :: (p1, A, 128) :: LBN)).
    { constructor; [exact ADDRB6|]. eapply (ADL_xpres_mf H HH); [exact HEAP5| exact SUBA| exact ADL5| exact XP6]. }
    assert (SUBB : forall b, In b ((p2, BB, 16) :: (p1, A, 128) :: LBN) -> In b LB3) by (intros b [<-|Hb]; [exact BIN3| right; apply SUBA; exact Hb]).
    assert (SUBL3 : forall b, In b L -> In b LB3) by (intros b Hb; right; apply SUBL2; exact Hb).
    assert (CHN7 : as_chain H m6 (bv_unsigned sp + -112) CH3) by (eapply (chain_via_xpres H HH); [exact CHN6| exact XP6| exact CHS3| apply rin_memflag_low]).
    assert (OUT_BB : forall a, in_block L a -> a < BB \/ BB + 16 <= a).
    { intros a (b & Hb & R). destruct (Z.lt_ge_cases a BB) as [K|K]; [left; exact K|]. destruct (Z.le_gt_cases (BB + 16) a) as [K2|K2]; [right; exact K2|].
      exfalso. eapply (afresh_outside H HH); [exact HEAP6| exact CEIL| right; right; left; exists b; split; [apply SUBL2; exact Hb| exact R]| lia]. }
    pose proof (afresh_apart H HH _ _ _ _ _ _ lo A 128 HEAP6 CEIL ltac:(eapply aclient_range_block; [exact AIN2| lia| lia]) ltac:(lia) ltac:(lia)) as DJ_A_BB. hide DJ_A_BB.
    apply bb_zero_recut in BB6.
    clear VIS5 KREL5 MI5 AC5 ST5 ERR5 AUX5 MF5 IM5 GM5 RL5 RFS5 CPH5 ADL5 CHN6 F05 F25 F35 BA5.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply anm_seg4; [lia| exact MI6]|].
    intros msF7 mo7 KREL7 MP7 VIS7. mpacc MPA MP7.
    (* [comment removed for export] *)
    pose proof (abufnew_spec H HH) as BN. unfold bufnew_stmt in BN.
    eapply (ah_seq H HH).
    { eapply BN with (lo := lo) (B := B) (LB := LB3) (s := s6') (v := 1) (CH := CH3); [exact VIS7| reflexivity| ..]; rewrite ?unsigned_lit by (unfold AMI_RA2; clear - SPR LO LO0 PHS; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HEAP6
           | |- as_AKREL _ _ _ => exact KREL7
           | |- as_rauxv_ok _ _ _ => exact AUX6
           | |- stk _ _ _ _ => exact ST6
           | |- rw_cells _ _ _ [C4 _] => exact ERR6
           | |- mem_inv _ _ => exact MI6
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -160) with (bv_unsigned sp - 160) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- ACONST _ => exact AC6
           | |- as_chain _ _ _ _ => exact CHN7
           | |- forall fp' ra', In _ _ -> _ => exact CHS3
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF3|]; unfold PF_meminit, R_mem_init_BUF_MEM_new, AMI_RA2; intros q Hq;
                                 apply in_or_app; right; apply in_or_app; left; exact Hq
           | |- _ <= as_AL _ _ => unfold BUFMEM_SIZE; clear - AL6 AL4 AL2 HAL CM16 CM32 CM128 CF00 PHK; lia
           | |- MEMFLAG _ _ => exact MF6
           | |- IMPL_mem _ => exact IM6
           | |- GOT_mem _ => exact GM6
           | |- lb_bytes _ + _ <= _ => unfold LB3, BUFMEM_SIZE; rewrite lb_bytes_cons, BY2; cbn [blk_size snd]; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold LB3; cbn [length]; rewrite Nat2Z.inj_succ, CN2; lia
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 PHS CEIL; unfold BUFNEW_STACK, FR_BUF_MEM_new, CZALLOC_STACK, CMALLOC_STACK, AMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc; lia]
           end | idtac "BN-FAIL:" G; fail ] end. }
    clear BN. intros [msF8 mo8] PO. unfold bufnew_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (x0 & x1 & x2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m8 & errv8 & BM & p3 & s8' &
                    VIS8 & KREL8 & MP8 & MI8 & AC8 & ST8 & ERR8 & AUX8 & XP8 & BR3 & HEAP8 & BM8 & ADDRM8 & MF8 & IM8 & GM8 & AL8). mpacc MPA MP8.
    rewrite (unsigned_lit (bv_unsigned sp + -160)) in ST8, XP8 by lia. rewrite unsigned_lit in ERR8 by (unfold ATP; lia). unfold BUFMEM_SIZE in BR3, HEAP8, ADDRM8, AL8.
    pose proof BR3 as (BMP & BMAL & _ & BMH & BMCE & BMFS & BMAP). unfold AIMG_TOP in BMH.
    pose proof (aapp_bounds BM 32 BMAP ltac:(lia)) as (_ & _ & BMTOP & _ & _). unfold AAPP_HI in BMTOP.
    pose proof (aapp_not_shadowland _ _ BMAP) as NSM. unfold ALOWSH_LO, AHI_LO in NSM. hide NSM. hide BMFS.
    set (LB4 := (p3, BM, 32) :: LB3) in *.
    assert (NSWM : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(BM, BM + 32)]) by (unhide NSM; fw; lia).
    assert (SUB34 : forall b, In b LB3 -> In b LB4) by (intros b Hb; right; exact Hb).
    assert (MIN4 : In (p3, BM, 32) LB4) by (left; reflexivity).
    assert (F38 : rw_cells asegs m8 (bv_unsigned sp + -160) [C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 (A + 112)); C8 (Z_to_bv 64 (A_mem_buf_method + 72)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 ANEX_RA3)]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP8); [exact F36| left; cbn; lia| fw; hlia]. }
    assert (F28 : rw_cells asegs m8 (bv_unsigned sp + -112) [CB 8 j1; C8 s5; C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 len); C8 s1; C8 sp; C8 (Z_to_bv 64 ANMB_RET)]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP8); [exact F26| left; cbn; lia| fw; hlia]. }
    assert (F08 : rw_cells asegs m8 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP8); [exact F06| left; cbn; lia| fw; hlia]. }
    assert (BA8 : rw_cells asegs m8 A (bio_cells (bio_hdr1 A_mem_buf_method))).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP8); [exact BA6| eapply aclient_range_block; [apply SUB23; exact AIN2| lia| cbn; lia]| fw; hlia]. }
    assert (BB8 : rw_cells asegs m8 BB [C8 (wz 0); C8 (wz 0)]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP8); [exact BB6| eapply aclient_range_block; [exact BIN3| lia| cbn; lia]| fw; hlia]. }
    assert (RL8 : arelro_lib m8) by (eapply (arelro_xpres H); [exact RL6| exact XP8| fw; hlia]).
    assert (RFS8 : as_RFS H LF m8) by (eapply (RFS_via_xpres H HH); [exact RFS6| exact XP8| fw; hlia]).
    assert (CPH8 : CTXPH L m8 (CtxReady x)) by (eapply CTXPH_frame_mf; [exact CPH6| eapply (magree_mf_of_xpres H); [exact HEAP6| exact SUBL3| exact XP8]]).
    assert (KEYS8 : ph = CtxFresh -> CTX_keys m8).
    { intros E. eapply (CTX_keys_frame_mf []); [exact (KEYS6 E)|]. eapply (magree_mf_of_xpres H) with (L := []); [exact HEAP6| intros b []| exact XP8]. }
    assert (ADL8 : Forall (fun b => addressable m8 (blk_addr b) (blk_size b)) ((p3, BM, 32) :: (p2, BB, 16) :: (p1, A, 128) :: LBN)).
    { constructor; [exact ADDRM8|]. eapply (ADL_xpres_mf H HH); [exact HEAP6| exact SUBB| exact ADL6| exact XP8]. }
    assert (SUBM : forall b, In b ((p3, BM, 32) :: (p2, BB, 16) :: (p1, A, 128) :: LBN) -> In b LB4) by (intros b [<-|Hb]; [exact MIN4| right; apply SUBB; exact Hb]).
    assert (SUBL4 : forall b, In b L -> In b LB4) by (intros b Hb; right; apply SUBL3; exact Hb).
    assert (CHN9 : as_chain H m8 (bv_unsigned sp + -112) CH3) by (eapply (chain_via_xpres H HH); [exact CHN7| exact XP8| exact CHS3| apply rin_memflag_low]).
    assert (OUT_BM : forall a, in_block L a -> a < BM \/ BM + 32 <= a).
    { intros a (b & Hb & R). destruct (Z.lt_ge_cases a BM) as [K|K]; [left; exact K|]. destruct (Z.le_gt_cases (BM + 32) a) as [K2|K2]; [right; exact K2|].
      exfalso. eapply (afresh_outside H HH); [exact HEAP8| exact CEIL| right; right; left; exists b; split; [apply SUBL3; exact Hb| exact R]| lia]. }
    pose proof (afresh_apart H HH _ _ _ _ _ _ lo A 128 HEAP8 CEIL ltac:(eapply aclient_range_block; [apply SUB23; exact AIN2| lia| lia]) ltac:(lia) ltac:(lia)) as DJ_A_BM. hide DJ_A_BM.
    pose proof (afresh_apart H HH _ _ _ _ _ _ lo BB 16 HEAP8 CEIL ltac:(eapply aclient_range_block; [exact BIN3| lia| lia]) ltac:(lia) ltac:(lia)) as DJ_BB_BM. hide DJ_BB_BM.
    clear VIS6 KREL6 MI6 AC6 ST6 ERR6 AUX6 MF6 IM6 GM6 RL6 RFS6 CPH6 ADL6 CHN7 F06 F26 F36 BA6 BB6 VIS7 KREL7.
    (* [comment removed for export] *)
    pose proof (Forall_inv (Forall_inv_tail ADL8)) as ADB8. cbn [blk_addr blk_size fst snd] in ADB8.
    assert (ACCB8 : accessible m8 BB 16) by (eapply addressable_accessible; [exact ADB8| lia| lia| unfold AAPP_HI; lia]).
    eapply (ahh_evt_then H HH); [exact KREL8| exact VIS8| eapply anm_seg5; [lia| exact BBAL| exact BBAP| exact BB8| exact ACCB8| exact MI8]|].
    intros msF9 mo9 KREL9 MP9 (m9 & VIS9 & MU9 & WM9 & MI9 & BB9). unfold BIOBUFMEM_SIZE in MU9. mpacc MPA MP9.
    assert (CW9 : Forall (aclient_write_ok H LB4) [(BB, BB + 16)]).
    { constructor; [| constructor]. right; right; left. exists (p2, BB, 16). split; [apply SUB34; exact BIN3| cbn; hlia]. }
    assert (NSWB : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(BB, BB + 16)]) by (fw; hlia).
    apply (stk_transport_disjoint asegs _ m8 m9 _ _ ST8) in MU9 as ST9; [| exact WM9| cbn; hlia].
    apply (rw_cells_transport asegs _ m8 m9 _ _ F38) in MU9 as F39; [| exact WM9| cbn; hlia].
    apply (rw_cells_transport asegs _ m8 m9 _ _ F28) in MU9 as F29; [| exact WM9| cbn; hlia].
    apply (rw_cells_transport asegs _ m8 m9 _ _ F08) in MU9 as F09; [| exact WM9| cbn; hlia].
    apply (rw_cells_transport asegs _ m8 m9 _ _ BA8) in MU9 as BA9; [| exact WM9| cbn; hlia].
    apply (rw_cells_transport asegs _ m8 m9 _ _ BM8) in MU9 as BM9; [| exact WM9| cbn; hlia].
    assert (ERR9 : rw_cells asegs m9 (ATP + -164) [C4 errv8]) by (eapply errno_across; [exact ERR8| exact MU9| exact WM9| unfold ATP; cbn; lia]).
    assert (AUX9 : as_rauxv_ok H m9 B) by (eapply (ah_rauxv_frame H HH); [exact AUX8| exact MU9| exact WM9| exact CW9]).
    assert (HEAP9 : as_RHEAP H s8' LB4 m9) by (eapply (ah_RHEAP_frame H HH); [exact HEAP8| exact MU9| exact WM9| exact CW9]).
    assert (AC9 : ACONST m9) by (eapply ACONST_frame; [exact AC8| exact MU9| exact WM9| constructor; [eapply aconst_ok_aapp; [exact BBAP| cbn; lia| cbn; lia]| constructor]]).
    assert (MF9 : MEMFLAG m9 1) by (eapply MEMFLAG_across; [exact MU9| exact WM9| unfold A_mem_inited; cbn; lia| exact MF8]).
    assert (IM9 : IMPL_mem m9) by (eapply IMPL_across; [exact MU9| exact WM9| unfold A_malloc_impl; cbn; lia| exact IM8]).
    assert (GM9 : GOT_mem m9) by (eapply GOT_across; [exact MU9| exact WM9| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM8]).
    assert (RL9 : arelro_lib m9) by (eapply arelro_across7; [exact RL8| exact MU9| fw; hlia]).
    assert (RFS9 : as_RFS H LF m9) by (eapply (RFS_across_wins H HH); [exact RFS8| exact MU9| exact WM9| fw; right; hlia]).
    assert (CPH9 : CTXPH L m9 (CtxReady x)).
    { eapply CTXPH_frame; [exact CPH8|]. eapply (magree_lib_munch H HH); [exact HEAP8| exact SUBL4| exact MU9| exact WM9| fw; right; split; [hlia| split; [hlia| exact OUT_BB]]]. }
    assert (KEYS9 : ph = CtxFresh -> CTX_keys m9).
    { intros E. eapply (CTX_keys_frame []); [exact (KEYS8 E)|]. eapply (magree_lib_munch H HH) with (L := []); [exact HEAP8| intros b []| exact MU9| exact WM9| fw; right; split; [hlia| split; [hlia| intros a (b & [] & _)]]]. }
    assert (ADL9 : Forall (fun b => addressable m9 (blk_addr b) (blk_size b)) ((p3, BM, 32) :: (p2, BB, 16) :: (p1, A, 128) :: LBN)).
    { eapply (ADL_across H HH); [exact HEAP8| exact SUBM| exact ADL8| exact MU9| exact WM9| exact NSWB]. }
    assert (CHN10 : as_chain H m9 (bv_unsigned sp + -112) CH3).
    { eapply (chain_via_munch H HH); [exact CHN9| exact MU9|]. intros fp' ra' Hin. pose proof (CHS3 _ _ Hin). cbn. split; [lia| exact I]. }
    clear VIS8 KREL8 MI8 AC8 ST8 ERR8 AUX8 MF8 IM8 GM8 RL8 RFS8 CPH8 ADL8 CHN9 F08 F28 F38 BA8 BB8 BM8 ACCB8.
    (* [comment removed for export] *)
    pose proof (aczalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (ah_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB4) (s := s8') (v := 1) (num := 32) (size := 1) (CH := CH3);
        [exact VIS9| reflexivity| reflexivity| ..]; rewrite ?Z.mul_1_r; rewrite ?unsigned_lit by (unfold AMI_RA3; clear - SPR LO LO0 PHS; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HEAP9
           | |- as_AKREL _ _ _ => exact KREL9
           | |- as_rauxv_ok _ _ _ => exact AUX9
           | |- stk _ _ _ _ => exact ST9
           | |- rw_cells _ _ _ [C4 _] => exact ERR9
           | |- mem_inv _ _ => exact MI9
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -160) with (bv_unsigned sp - 160) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- ACONST _ => exact AC9
           | |- as_chain _ _ _ _ => exact CHN10
           | |- forall fp' ra', In _ _ -> _ => exact CHS3
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF3|]; unfold PF_meminit, R_mem_init_CRYPTO_zalloc_2, AMI_RA3; intros q Hq;
                                 apply in_or_app; right; apply in_or_app; right; exact Hq
           | |- _ <= as_AL _ _ => clear - AL8 AL6 AL4 AL2 HAL CM16 CM32 CM128 CF00 PHK; lia
           | |- MEMFLAG _ _ => exact MF9
           | |- IMPL_mem _ => exact IM9
           | |- GOT_mem _ => exact GM9
           | |- lb_bytes _ + _ <= _ => unfold LB4, LB3; rewrite !lb_bytes_cons, BY2; cbn [blk_size snd]; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold LB4, LB3; cbn [length]; rewrite !Nat2Z.inj_succ, CN2; lia
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 PHS CEIL; unfold CZALLOC_STACK, CMALLOC_STACK, AMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc; lia]
           end | idtac "CZ3-FAIL:" G; fail ] end. }
    clear CZ. intros [msF10 mo10] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO. rewrite ?Z.mul_1_r in PO.
    destruct PO as (y0 & y1 & y2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m10 & errv10 & RP & p4 & s10' &
                    VIS10 & KREL10 & MP10 & MI10 & AC10 & ST10 & ERR10 & AUX10 & XP10 & BR4 & HEAP10 & RP10 & ADDRR10 & MF10 & IM10 & GM10 & AL10). mpacc MPA MP10.
    rewrite (unsigned_lit (bv_unsigned sp + -160)) in ST10, XP10 by lia. rewrite unsigned_lit in ERR10 by (unfold ATP; lia).
    pose proof BR4 as (RPP & RPAL & _ & RPH & RPCE & RPFS & RPAP). unfold AIMG_TOP in RPH.
    pose proof (aapp_bounds RP 32 RPAP ltac:(lia)) as (_ & _ & RPTOP & _ & _). unfold AAPP_HI in RPTOP.
    pose proof (aapp_not_shadowland _ _ RPAP) as NSR. unfold ALOWSH_LO, AHI_LO in NSR. hide NSR. hide RPFS.
    set (LB5 := (p4, RP, 32) :: LB4) in *.
    assert (NSWR : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(RP, RP + 32)]) by (unhide NSR; fw; lia).
    assert (SUB45 : forall b, In b LB4 -> In b LB5) by (intros b Hb; right; exact Hb).
    assert (RIN5 : In (p4, RP, 32) LB5) by (left; reflexivity).
    assert (F310 : rw_cells asegs m10 (bv_unsigned sp + -160) [C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 (A + 112)); C8 (Z_to_bv 64 (A_mem_buf_method + 72)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 ANEX_RA3)]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact F39| left; cbn; lia| fw; hlia]. }
    assert (F210 : rw_cells asegs m10 (bv_unsigned sp + -112) [CB 8 j1; C8 s5; C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 len); C8 s1; C8 sp; C8 (Z_to_bv 64 ANMB_RET)]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact F29| left; cbn; lia| fw; hlia]. }
    assert (F010 : rw_cells asegs m10 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact F09| left; cbn; lia| fw; hlia]. }
    assert (BA10 : rw_cells asegs m10 A (bio_cells (bio_hdr1 A_mem_buf_method))).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact BA9| eapply aclient_range_block; [apply SUB34, SUB23; exact AIN2| lia| cbn; lia]| fw; hlia]. }
    assert (BB10 : rw_cells asegs m10 BB [C8 (wz BM); C8 (wz 0)]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact BB9| eapply aclient_range_block; [apply SUB34; exact BIN3| lia| cbn; lia]| fw; hlia]. }
    assert (BM10 : rw_cells asegs m10 BM (buf_cells (mkBUF 0 0 0 0))).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact BM9| eapply aclient_range_block; [exact MIN4| lia| cbn; lia]| fw; hlia]. }
    assert (RL10 : arelro_lib m10) by (eapply (arelro_xpres H); [exact RL9| exact XP10| fw; hlia]).
    assert (RFS10 : as_RFS H LF m10) by (eapply (RFS_via_xpres H HH); [exact RFS9| exact XP10| fw; hlia]).
    assert (CPH10 : CTXPH L m10 (CtxReady x)) by (eapply CTXPH_frame_mf; [exact CPH9| eapply (magree_mf_of_xpres H); [exact HEAP9| exact SUBL4| exact XP10]]).
    assert (KEYS10 : ph = CtxFresh -> CTX_keys m10).
    { intros E. eapply (CTX_keys_frame_mf []); [exact (KEYS9 E)|]. eapply (magree_mf_of_xpres H) with (L := []); [exact HEAP9| intros b []| exact XP10]. }
    set (LQ := (p4, RP, 32) :: (p3, BM, 32) :: (p2, BB, 16) :: (p1, A, 128) :: LBN).
    assert (ADL10 : Forall (fun b => addressable m10 (blk_addr b) (blk_size b)) LQ).
    { constructor; [exact ADDRR10|]. eapply (ADL_xpres_mf H HH); [exact HEAP9| exact SUBM| exact ADL9| exact XP10]. }
    assert (SUBR : forall b, In b LQ -> In b LB5) by (intros b [<-|Hb]; [exact RIN5| right; apply SUBM; exact Hb]).
    assert (SUBL5 : forall b, In b L -> In b LB5) by (intros b Hb; right; apply SUBL4; exact Hb).
    assert (OUT_RP : forall a, in_block L a -> a < RP \/ RP + 32 <= a).
    { intros a (b & Hb & R). destruct (Z.lt_ge_cases a RP) as [K|K]; [left; exact K|]. destruct (Z.le_gt_cases (RP + 32) a) as [K2|K2]; [right; exact K2|].
      exfalso. eapply (afresh_outside H HH); [exact HEAP10| exact CEIL| right; right; left; exists b; split; [apply SUBL4; exact Hb| exact R]| lia]. }
    pose proof (afresh_apart H HH _ _ _ _ _ _ lo A 128 HEAP10 CEIL ltac:(eapply aclient_range_block; [apply SUB34, SUB23; exact AIN2| lia| lia]) ltac:(lia) ltac:(lia)) as DJ_A_RP. hide DJ_A_RP.
    pose proof (afresh_apart H HH _ _ _ _ _ _ lo BB 16 HEAP10 CEIL ltac:(eapply aclient_range_block; [apply SUB34; exact BIN3| lia| lia]) ltac:(lia) ltac:(lia)) as DJ_BB_RP. hide DJ_BB_RP.
    pose proof (afresh_apart H HH _ _ _ _ _ _ lo BM 32 HEAP10 CEIL ltac:(eapply aclient_range_block; [exact MIN4| lia| lia]) ltac:(lia) ltac:(lia)) as DJ_BM_RP. hide DJ_BM_RP.
    (* [comment removed for export] *)
    pose proof (Forall_inv ADL10) as ADR10. pose proof (Forall_inv (Forall_inv_tail ADL10)) as ADM10.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail ADL10))) as ADB10. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail ADL10)))) as ADA10.
    cbn [blk_addr blk_size fst snd] in ADR10, ADM10, ADB10, ADA10.
    assert (ACCR10 : accessible m10 RP 32) by (eapply addressable_accessible; [exact ADR10| lia| lia| unfold AAPP_HI; lia]).
    assert (ACCM10 : accessible m10 BM 32) by (eapply addressable_accessible; [exact ADM10| lia| lia| unfold AAPP_HI; lia]).
    assert (ACCB10 : accessible m10 BB 16) by (eapply addressable_accessible; [exact ADB10| lia| lia| unfold AAPP_HI; lia]).
    assert (ACCA10 : accessible m10 A 128) by (eapply addressable_accessible; [exact ADA10| lia| lia| unfold AAPP_HI; lia]).
    clear ADR10 ADM10 ADB10 ADA10 VIS9 KREL9 MI9 AC9 ST9 ERR9 AUX9 MF9 IM9 GM9 RL9 RFS9 CPH9 ADL9 CHN10 F09 F29 F39 BA9 BB9 BM9 HEAP9 KEYS9.
    (* [comment removed for export] *)
    set (WT := [(lo, bv_unsigned sp); (A, A + 112); (BB, BB + 16); (BM, BM + 32); (RP, RP + 32)]).
    assert (NSWT : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) WT).
    { unfold WT. constructor; [cbn [fst snd]; unfold AHI_LO; lia|]. constructor; [pose proof (Forall_inv NSWA) as K; cbn [fst snd] in K |- *; unfold AHI_LO in *; rewrite ?ASHADOW_BASE_val in *; lia|].
      constructor; [exact (Forall_inv NSWB)|]. constructor; [exact (Forall_inv NSWM)|]. constructor; [exact (Forall_inv NSWR)| constructor]. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL10| exact VIS10| eapply anm_seg6 with (BM := BM); [lia| lia| exact BBAP| exact BB10| exact ACCB10| exact MI10]|].
    intros msF11 mo11 KREL11 MP11 (m11 & VIS11 & MU11 & WM11 & MI11 & BB11). unfold BIOBUFMEM_SIZE in MU11. mpacc MPA MP11.
    assert (SUB11 : sub_fp [(BB, BB + 16)] WT) by (unfold WT; intros q Hq; cbn in Hq |- *; clear - Hq LO PHS; lia).
    apply (stk_transport_disjoint asegs _ m10 m11 _ _ ST10) in MU11 as ST11; [| exact WM11| cbn; lia].
    apply (rw_cells_transport asegs _ m10 m11 _ _ F310) in MU11 as F311; [| exact WM11| cbn; lia].
    apply (rw_cells_transport asegs _ m10 m11 _ _ F210) in MU11 as F211; [| exact WM11| cbn; lia].
    apply (rw_cells_transport asegs _ m10 m11 _ _ F010) in MU11 as F011; [| exact WM11| cbn; lia].
    apply (rw_cells_transport asegs _ m10 m11 _ _ BA10) in MU11 as BA11; [| exact WM11| unhide DJ_A_BB; cbn; lia].
    apply (rw_cells_transport asegs _ m10 m11 _ _ BM10) in MU11 as BM11; [| exact WM11| unhide DJ_BB_BM; cbn; lia].
    apply (rw_cells_transport asegs _ m10 m11 _ _ RP10) in MU11 as RP11; [| exact WM11| unhide DJ_BB_RP; cbn; lia].
    assert (HEAP11 : as_RHEAP H s10' LB5 m11).
    { eapply (ah_RHEAP_frame H HH); [exact HEAP10| exact MU11| exact WM11|]. constructor; [| constructor]. right; right; left. exists (p2, BB, 16). split; [apply SUB45, SUB34; exact BIN3| cbn; lia]. }
    assert (AC11 : ACONST m11) by (eapply ACONST_frame_win; [exact AC10| exact MU11| exact WM11| fw; right; exists BB, 16; split; [exact BBAP| lia]]).
    assert (ACCM11 : accessible m11 BM 32) by (eapply accessible_across2; [exact ACCM10| exact MU11| exact NSWB]).
    assert (ACCR11 : accessible m11 RP 32) by (eapply accessible_across2; [exact ACCR10| exact MU11| exact NSWB]).
    assert (ACCA11 : accessible m11 A 128) by (eapply accessible_across2; [exact ACCA10| exact MU11| exact NSWB]).
    assert (ACCB11 : accessible m11 BB 16) by (eapply accessible_across2; [exact ACCB10| exact MU11| exact NSWB]).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL11| exact VIS11|
      eapply (asan_memcpy_specZ H HH) with (lo := lo) (src := cells_bytes (buf_cells (mkBUF 0 0 0 0))) (junk := zeros (Z.to_nat 32));
      match goal with |- ?G => first [ lazymatch goal with
         | |- bytes_at _ _ _ _ => exact (rw_cells_bytes_at asegs _ _ _ BM11)
         | |- length _ = _ => reflexivity
         | |- rw_cells _ _ _ _ => exact RP11
         | |- accessible _ _ _ => first [exact ACCM11| exact ACCR11]
         | |- shvis _ _ _ => eapply (ah_blk_shvis H HH); [exact HEAP11| first [exact RIN5| apply SUB45; exact MIN4]]
         | |- in_app_mem _ _ => first [eapply (aapp_in_app_mem BM 32); [exact BMAP| lia| lia] | eapply (aapp_in_app_mem RP 32); [exact RPAP| lia| lia]]
         | |- aconst_ok _ => eapply aconst_ok_aapp; [exact RPAP| lia| lia]
         | |- stk _ _ _ _ => exact ST11
         | |- mem_inv _ _ => exact MI11
         | |- ACONST _ => exact AC11
         | |- _ => first [exact CEIL| unhide DJ_BM_RP; clear - DJ_BM_RP RPCE BMCE CEIL LO LO0 SPR PHS RPP BMP; lia]
        end | idtac "MC1-FAIL:" G; fail ] end |].
    intros msF12 mo12 KREL12 MP12 PO. unfold amove_post in PO.
    destruct PO as (g0 & g1 & g2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & g3 & g4 & g5 & g6 & m12 & VIS12 & MU12 & WM12 & MI12 & ST12 & RP12 & _ & AC12). mpacc MPA MP12.
    assert (SUB12w : sub_fp [(RP, RP + 32); (bv_unsigned sp + -160 - 4096, bv_unsigned sp + -160)] WT) by (unfold WT; intros q Hq; cbn in Hq |- *; clear - Hq LO PHS; lia).
    apply (rw_cells_transport asegs _ m11 m12 _ _ F311) in MU12 as F312; [| exact WM12| cbn; lia].
    apply (rw_cells_transport asegs _ m11 m12 _ _ F211) in MU12 as F212; [| exact WM12| cbn; lia].
    apply (rw_cells_transport asegs _ m11 m12 _ _ F011) in MU12 as F012; [| exact WM12| cbn; lia].
    apply (rw_cells_transport asegs _ m11 m12 _ _ BA11) in MU12 as BA12; [| exact WM12| unhide DJ_A_RP; cbn; lia].
    apply (rw_cells_transport asegs _ m11 m12 _ _ BB11) in MU12 as BB12; [| exact WM12| unhide DJ_BB_RP; cbn; lia].
    apply (rw_cells_transport asegs _ m11 m12 _ _ BM11) in MU12 as BM12; [| exact WM12| unhide DJ_BM_RP; cbn; lia].
    assert (HEAP12 : as_RHEAP H s10' LB5 m12).
    { eapply (ah_RHEAP_frame H HH); [exact HEAP11| exact MU12| exact WM12|]. constructor; [| constructor; [left; cbn; lia| constructor]].
      right; right; left. exists (p4, RP, 32). split; [exact RIN5| cbn; lia]. }
    assert (RL12 : arelro_lib m12). { eapply arelro_across7; [| exact MU12| fw; lia]. eapply arelro_across7; [exact RL10| exact MU11| fw; lia]. }
    assert (NSW12 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(RP, RP + 32); (bv_unsigned sp + -160 - 4096, bv_unsigned sp + -160)]) by (constructor; [exact (Forall_inv NSWR)| fw; lia]).
    assert (ACCA12 : accessible m12 A 128) by (eapply accessible_across2; [exact ACCA11| exact MU12| exact NSW12]).
    assert (ACCB12 : accessible m12 BB 16) by (eapply accessible_across2; [exact ACCB11| exact MU12| exact NSW12]).
    assert (ACCM12 : accessible m12 BM 32) by (eapply accessible_across2; [exact ACCM11| exact MU12| exact NSW12]).
    assert (ACCR12 : accessible m12 RP 32) by (eapply accessible_across2; [exact ACCR11| exact MU12| exact NSW12]).
    destruct (bio_cells_split_ex _ _ _ BA12) as [BA12a EXD12]. unfold O_BIO_EXDATA in EXD12.
    clear VIS10 KREL10 MI10 F010 F210 F310 BA10 BB10 BM10 VIS11 KREL11 MI11 ST11 F311 F211 F011 BA11 BM11 RP11 BB11 AC11 ACCM11 ACCR11 ACCA11 ACCB11 HEAP11.
    (* [comment removed for export] *)
    assert (E7 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
    replace (Z_to_bv 64 (bv_unsigned sp + -160) : word) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) + -48) : word) in VIS12 by (rewrite E7; f_equal; lia).
    eapply (ahh_evt_then H HH); [exact KREL12| exact VIS12| eapply anm_seg7 with (lo := lo);
      [exact AAP| exact AAL| exact BA12a| exact ACCA12| lia| exact AC12| exact (METH_of_relro _ RL12)| rewrite E7; replace (bv_unsigned sp + -112 + -48) with (bv_unsigned sp + -160) by lia; exact F312
      | rewrite E7; exact F212| rewrite E7; replace (bv_unsigned sp + -112 + -48) with (bv_unsigned sp + -160) by lia; exact ST12| exact CEIL| rewrite E7; lia| rewrite E7; lia| exact MI12]|].
    intros msF13 mo13 KREL13 MP13 (m13 & VIS13 & MU13 & WM13 & MI13 & ST13 & BA13a). mpacc MPA MP13.
    rewrite E7 in VIS13, MU13, ST13. replace (bv_unsigned sp + -112 + 64) with (bv_unsigned sp + -48) in VIS13 by lia.
    replace (bv_unsigned sp + -112 + 64) with (bv_unsigned sp + -48) in MU13 by lia. replace (bv_unsigned sp + -112 + 64) with (bv_unsigned sp + -48) in ST13 by lia.
    assert (SUB13 : sub_fp [(lo, bv_unsigned sp + -48); (A, A + 112)] WT) by (unfold WT; intros q Hq; cbn in Hq |- *; clear - Hq LO PHS; lia).
    apply (rw_cells_transport asegs _ m12 m13 _ _ F012) in MU13 as F013; [| exact WM13| cbn; lia].
    apply (rw_cells_transport asegs _ m12 m13 _ _ EXD12) in MU13 as EXD13; [| exact WM13| cbn; lia].
    apply (rw_cells_transport asegs _ m12 m13 _ _ BB12) in MU13 as BB13; [| exact WM13| unhide DJ_A_BB; cbn; lia].
    apply (rw_cells_transport asegs _ m12 m13 _ _ BM12) in MU13 as BM13; [| exact WM13| unhide DJ_A_BM; cbn; lia].
    apply (rw_cells_transport asegs _ m12 m13 _ _ RP12) in MU13 as RP13; [| exact WM13| unhide DJ_A_RP; cbn; lia].
    assert (HEAP13 : as_RHEAP H s10' LB5 m13).
    { eapply (ah_RHEAP_frame H HH); [exact HEAP12| exact MU13| exact WM13|]. constructor; [left; cbn; lia| constructor; [| constructor]].
      right; right; left. exists (p1, A, 128). split; [apply SUB45, SUB34, SUB23; exact AIN2| cbn; lia]. }
    assert (AC13 : ACONST m13) by (eapply ACONST_frame_win; [exact AC12| exact MU13| exact WM13| fw; [left; lia| right; exists A, 128; split; [exact AAP| lia]]]).
    assert (NSW13 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp + -48); (A, A + 112)]) by (fw; [lia| pose proof (Forall_inv NSWA) as K; cbn [fst snd] in K; unfold AHI_LO in K; rewrite ?ASHADOW_BASE_val in K; lia]).
    assert (ACCA13 : accessible m13 A 128) by (eapply accessible_across2; [exact ACCA12| exact MU13| exact NSW13]).
    assert (ACCB13 : accessible m13 BB 16) by (eapply accessible_across2; [exact ACCB12| exact MU13| exact NSW13]).
    assert (ACCM13 : accessible m13 BM 32) by (eapply accessible_across2; [exact ACCM12| exact MU13| exact NSW13]).
    assert (ACCR13 : accessible m13 RP 32) by (eapply accessible_across2; [exact ACCR12| exact MU13| exact NSW13]).
    clear VIS12 KREL12 MI12 ST12 F312 F212 F012 BA12 BA12a EXD12 BB12 BM12 RP12 AC12 ACCA12 ACCB12 ACCM12 ACCR12 HEAP12 E7.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL13| exact VIS13| eapply anm_seg8 with (BB := BB) (BM := BM) (RP := RP);
      [exact AAP| exact BBAP| exact BMAP| exact AAL| exact BBAL| exact BMAL| lia| lia| lia| exact BA13a| exact BB13| exact BM13| exact ACCA13| exact ACCB13| exact ACCM13| unhide DJ_A_BM; unfold BIO_SIZE, BUFMEM_SIZE; clear - DJ_A_BM; lia| unhide DJ_BB_BM; unfold BIOBUFMEM_SIZE, BUFMEM_SIZE; clear - DJ_BB_BM; lia| exact MI13]|].
    intros msF14 mo14 KREL14 MP14 (m14 & VIS14 & MU14 & WM14 & MI14 & BM14). unfold BUFMEM_SIZE in MU14. mpacc MPA MP14.
    assert (SUB14 : sub_fp [(BM, BM + 32)] WT) by (unfold WT; intros q Hq; cbn in Hq |- *; clear - Hq LO PHS; lia).
    apply (stk_transport_disjoint asegs _ m13 m14 _ _ ST13) in MU14 as ST14; [| exact WM14| cbn; lia].
    apply (rw_cells_transport asegs _ m13 m14 _ _ F013) in MU14 as F014; [| exact WM14| cbn; lia].
    apply (rw_cells_transport asegs _ m13 m14 _ _ BA13a) in MU14 as BA14a; [| exact WM14| unhide DJ_A_BM; cbn; lia].
    apply (rw_cells_transport asegs _ m13 m14 _ _ EXD13) in MU14 as EXD14; [| exact WM14| unhide DJ_A_BM; cbn; lia].
    apply (rw_cells_transport asegs _ m13 m14 _ _ BB13) in MU14 as BB14; [| exact WM14| unhide DJ_BB_BM; cbn; lia].
    apply (rw_cells_transport asegs _ m13 m14 _ _ RP13) in MU14 as RP14; [| exact WM14| unhide DJ_BM_RP; cbn; lia].
    assert (HEAP14 : as_RHEAP H s10' LB5 m14).
    { eapply (ah_RHEAP_frame H HH); [exact HEAP13| exact MU14| exact WM14|]. constructor; [| constructor].
      right; right; left. exists (p3, BM, 32). split; [apply SUB45; exact MIN4| cbn; lia]. }
    assert (AC14 : ACONST m14) by (eapply ACONST_frame_win; [exact AC13| exact MU14| exact WM14| fw; right; exists BM, 32; split; [exact BMAP| lia]]).
    assert (ACCM14 : accessible m14 BM 32) by (eapply accessible_across2; [exact ACCM13| exact MU14| exact NSWM]).
    assert (ACCR14 : accessible m14 RP 32) by (eapply accessible_across2; [exact ACCR13| exact MU14| exact NSWM]).
    assert (ACCA14 : accessible m14 A 128) by (eapply accessible_across2; [exact ACCA13| exact MU14| exact NSWM]).
    clear VIS13 KREL13 MI13 ST13 F013 BA13a EXD13 BB13 BM13 RP13 AC13 ACCA13 ACCB13 ACCM13 ACCR13 HEAP13.
    (* [comment removed for export] *)
    assert (SRCL : length (cells_bytes (buf_cells (mkBUF len buf len 0))) = Z.to_nat 32).
    { rewrite cells_bytes_length; [reflexivity|]. cbn. repeat split. }
    eapply (ahh_evt_then H HH); [exact KREL14| exact VIS14|
      eapply (asan_memcpy_specZ H HH) with (lo := lo) (src := cells_bytes (buf_cells (mkBUF len buf len 0))) (junk := cells_bytes (buf_cells (mkBUF 0 0 0 0))) (SP := bv_unsigned sp + -48);
      match goal with |- ?G => first [ lazymatch goal with
         | |- bytes_at _ _ _ _ => exact (rw_cells_bytes_at asegs _ _ _ BM14)
         | |- length _ = _ => exact SRCL
         | |- rw_cells _ _ _ _ => exact RP14
         | |- accessible _ _ _ => first [exact ACCM14| exact ACCR14]
         | |- shvis _ _ _ => eapply (ah_blk_shvis H HH); [exact HEAP14| first [exact RIN5| apply SUB45; exact MIN4]]
         | |- in_app_mem _ _ => first [eapply (aapp_in_app_mem BM 32); [exact BMAP| lia| lia] | eapply (aapp_in_app_mem RP 32); [exact RPAP| lia| lia]]
         | |- aconst_ok _ => eapply aconst_ok_aapp; [exact RPAP| lia| lia]
         | |- stk _ _ _ _ => exact ST14
         | |- mem_inv _ _ => exact MI14
         | |- ACONST _ => exact AC14
         | |- _ => first [exact CEIL| unhide DJ_BM_RP; clear - DJ_BM_RP RPCE BMCE CEIL LO LO0 SPR PHS RPP BMP; lia]
        end | idtac "MC2-FAIL:" G; fail ] end |].
    intros msF15 mo15 KREL15 MP15 PO. unfold amove_post in PO.
    destruct PO as (z0 & z1 & z2 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & z3 & z4 & z5 & z6 & m15 & VIS15 & MU15 & WM15 & MI15 & ST15 & RP15 & _ & AC15). mpacc MPA MP15.
    assert (SUB15 : sub_fp [(RP, RP + 32); (bv_unsigned sp + -48 - 4096, bv_unsigned sp + -48)] WT) by (unfold WT; intros q Hq; cbn in Hq |- *; clear - Hq LO PHS; lia).
    assert (NSW15 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(RP, RP + 32); (bv_unsigned sp + -48 - 4096, bv_unsigned sp + -48)]) by (constructor; [exact (Forall_inv NSWR)| fw; lia]).
    apply (rw_cells_transport asegs _ m14 m15 _ _ F014) in MU15 as F015; [| exact WM15| cbn; lia].
    apply (rw_cells_transport asegs _ m14 m15 _ _ BA14a) in MU15 as BA15a; [| exact WM15| unhide DJ_A_RP; cbn; lia].
    apply (rw_cells_transport asegs _ m14 m15 _ _ EXD14) in MU15 as EXD15; [| exact WM15| unhide DJ_A_RP; cbn; lia].
    apply (rw_cells_transport asegs _ m14 m15 _ _ BB14) in MU15 as BB15; [| exact WM15| unhide DJ_BB_RP; cbn; lia].
    apply (rw_cells_transport asegs _ m14 m15 _ _ BM14) in MU15 as BM15; [| exact WM15| unhide DJ_BM_RP; cbn; lia].
    assert (ACCA15 : accessible m15 A 128) by (eapply accessible_across2; [exact ACCA14| exact MU15| exact NSW15]).
    clear VIS14 KREL14 MI14 ST14 F014 BA14a EXD14 BB14 BM14 RP14 AC14 ACCA14 ACCM14 ACCR14 HEAP14.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL15| exact VIS15| eapply anm_seg9 with (lo := lo);
      [exact AAP| exact BA15a| exact ACCA15| exact F015| exact ST15| exact CEIL| lia| exact MI15]|].
    intros msF16 mo16 KREL16 MP16 (a1f & m16 & VIS16 & MU16 & WM16 & MI16 & ST16 & BA16a). mpacc MPA MP16.
    assert (SUB16 : sub_fp [(lo, bv_unsigned sp); (A, A + 112)] WT) by (unfold WT; intros q Hq; cbn in Hq |- *; clear - Hq LO PHS; lia).
    apply (rw_cells_transport asegs _ m15 m16 _ _ EXD15) in MU16 as EXD16; [| exact WM16| cbn; lia].
    apply (rw_cells_transport asegs _ m15 m16 _ _ BB15) in MU16 as BB16; [| exact WM16| unhide DJ_A_BB; cbn; lia].
    apply (rw_cells_transport asegs _ m15 m16 _ _ BM15) in MU16 as BM16; [| exact WM16| unhide DJ_A_BM; cbn; lia].
    apply (rw_cells_transport asegs _ m15 m16 _ _ RP15) in MU16 as RP16; [| exact WM16| unhide DJ_A_RP; cbn; lia].
    pose proof (bio_cells_join_ex _ _ _ BA16a EXD16) as BA16.
    (* [comment removed for export] *)
    assert (MUT : munch WT m10 m16).
    { eapply munch_trans; [eapply munch_weaken; [exact SUB11| exact MU11]|]. eapply munch_trans; [eapply munch_weaken; [exact SUB12w| exact MU12]|].
      eapply munch_trans; [eapply munch_weaken; [exact SUB13| exact MU13]|]. eapply munch_trans; [eapply munch_weaken; [exact SUB14| exact MU14]|].
      eapply munch_trans; [eapply munch_weaken; [exact SUB15| exact MU15]|]. eapply munch_weaken; [exact SUB16| exact MU16]. }
    assert (WMT : wmono asegs m10 m16).
    { eapply wmono_trans; [exact WM11|]. eapply wmono_trans; [exact WM12|]. eapply wmono_trans; [exact WM13|]. eapply wmono_trans; [exact WM14|]. eapply wmono_trans; [exact WM15| exact WM16]. }
    assert (CWT : Forall (aclient_write_ok H LB5) WT).
    { unfold WT. constructor; [left; cbn; lia|].
      constructor; [right; right; left; exists (p1, A, 128); split; [apply SUB45, SUB34, SUB23; exact AIN2| cbn; lia]|].
      constructor; [right; right; left; exists (p2, BB, 16); split; [apply SUB45, SUB34; exact BIN3| cbn; lia]|].
      constructor; [right; right; left; exists (p3, BM, 32); split; [apply SUB45; exact MIN4| cbn; lia]|].
      constructor; [right; right; left; exists (p4, RP, 32); split; [exact RIN5| cbn; lia]| constructor]. }
    assert (LWT : Forall (win_lib_ok L) WT).
    { unfold WT. unhide NSA. unhide NSB. unhide NSM. unhide NSR. fw; [left; lia| right..]; (split; [lia| split; [lia|]]); [intros q Hq; destruct (OUT_A q Hq); lia| exact OUT_BB| exact OUT_BM| exact OUT_RP]. }
    assert (ERR16 : rw_cells asegs m16 (ATP + -164) [C4 errv10]) by (eapply errno_across; [exact ERR10| exact MUT| exact WMT| unfold ATP; cbn; lia]).
    assert (AUX16 : as_rauxv_ok H m16 B) by (eapply (ah_rauxv_frame H HH); [exact AUX10| exact MUT| exact WMT| exact CWT]).
    assert (HEAP16 : as_RHEAP H s10' LB5 m16) by (eapply (ah_RHEAP_frame H HH); [exact HEAP10| exact MUT| exact WMT| exact CWT]).
    assert (AC16 : ACONST m16).
    { eapply ACONST_frame_win; [exact AC10| exact MUT| exact WMT|]. unfold WT.
      fw; [left; lia| right; exists A, 128; split; [exact AAP| lia]| right; exists BB, 16; split; [exact BBAP| lia]| right; exists BM, 32; split; [exact BMAP| lia]| right; exists RP, 32; split; [exact RPAP| lia]]. }
    assert (MF16 : MEMFLAG m16 1) by (eapply MEMFLAG_across; [exact MUT| exact WMT| unfold WT, A_mem_inited; cbn; lia| exact MF10]).
    assert (IM16 : IMPL_mem m16) by (eapply IMPL_across; [exact MUT| exact WMT| unfold WT, A_malloc_impl; cbn; lia| exact IM10]).
    assert (GM16 : GOT_mem m16) by (eapply GOT_across; [exact MUT| exact WMT| unfold WT, A_got_CRYPTO_malloc; cbn; lia| exact GM10]).
    assert (RL16 : arelro_lib m16) by (eapply arelro_across7; [exact RL10| exact MUT| unfold WT; fw; lia]).
    assert (RFS16 : as_RFS H LF m16).
    { eapply (RFS_across_wins H HH); [exact RFS10| exact MUT| exact WMT|]. unfold WT. unhide AFS. unhide BBFS. unhide BMFS. unhide RPFS. fw; [left; lia| right; lia..]. }
    assert (CPH16 : CTXPH L m16 (CtxReady x)).
    { eapply CTXPH_frame; [exact CPH10|]. eapply (magree_lib_munch H HH); [exact HEAP10| exact SUBL5| exact MUT| exact WMT| exact LWT]. }
    assert (KEYS16 : ph = CtxFresh -> CTX_keys m16).
    { intros E. eapply (CTX_keys_frame []); [exact (KEYS10 E)|]. eapply (magree_lib_munch H HH) with (L := []); [exact HEAP10| intros b []| exact MUT| exact WMT|].
      eapply Forall_impl; [| exact LWT]. intros iv [K|(K1 & K2 & K3)]; [left; exact K| right]. split; [exact K1|]. split; [exact K2|]. intros a (b & [] & _). }
    assert (ADL16 : Forall (fun b => addressable m16 (blk_addr b) (blk_size b)) LQ).
    { eapply (ADL_across H HH); [exact HEAP10| exact SUBR| exact ADL10| exact MUT| exact WMT| exact NSWT]. }
    (* [comment removed for export] *)
    assert (XPT : xpres H LB (bv_unsigned sp) (memflag_foot ++ ctxph_foot ph ++ XS) m10 m16).
    { eapply (xpres_of_munch_gen H); [exact MUT| exact WMT|]. intros a Ha [HC _]. unfold WT. cbn.
      destruct (aclient_cases H HH _ _ _ _ a HP HC Ha) as [K|K].
      - acb. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact I].
      - split; [lia|].
        split; [intros R; eapply (afresh_outside H HH); [exact HEAP2| exact CEIL| eapply aclient_addr_weaken; [exact HC| lia| auto]| lia]|].
        split; [intros R; eapply (afresh_outside H HH); [exact HEAP6| exact CEIL| eapply aclient_addr_weaken; [exact HC| lia| intros b Hb; apply SUBL2, SUB0L; exact Hb]| lia]|].
        split; [intros R; eapply (afresh_outside H HH); [exact HEAP8| exact CEIL| eapply aclient_addr_weaken; [exact HC| lia| intros b Hb; apply SUBL3, SUB0L; exact Hb]| lia]|].
        split; [intros R; eapply (afresh_outside H HH); [exact HEAP10| exact CEIL| eapply aclient_addr_weaken; [exact HC| lia| intros b Hb; apply SUBL4, SUB0L; exact Hb]| lia]| exact I]. }
    assert (RPc : rw_cells asegs m16 RP (buf_cells (mkBUF len buf len 0))).
    { eapply arw_cells_recut; [exact RP16| cbn; repeat split| cbn [cells_bytes cbytes app]; rewrite app_nil_r; reflexivity]. }
    pose proof (Forall_inv ADL16) as ADR16. pose proof (Forall_inv (Forall_inv_tail ADL16)) as ADM16.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail ADL16))) as ADB16. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail ADL16)))) as ADA16.
    pose proof (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail ADL16)))) as ADN16.
    cbn [blk_addr blk_size fst snd] in ADR16, ADM16, ADB16, ADA16.
    (* [comment removed for export] *)
    apply (ah_done H HH). unfold newmembuf_post. cbn [cfg_ms cfg_model].
    do 14 eexists. exists m16, errv10, s10', LBN, LB5, x, A, (anm_R buf len BB BM RP p1 p2 p3 p4), XS.
    split; [exact VIS16|].
    split.
    { unfold LB5, LB4, LB3, LB2, LB1, blocks_MEMBIO, anm_R, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. cbn [mb_id mb_bb mb_bm mb_rp mb_bbid mb_bmid mb_rpid app].
      apply (Permutation_trans (l' := (p4, RP, 32) :: (p3, BM, 32) :: (p2, BB, 16) :: (p1, A, 128) :: LBN ++ LB)).
      - do 3 apply perm_skip. apply Permutation_sym. apply Permutation_middle.
      - change (Permutation (rev [(p1, A, 128); (p2, BB, 16); (p3, BM, 32); (p4, RP, 32)] ++ (LBN ++ LB)) ([(p1, A, 128); (p2, BB, 16); (p3, BM, 32); (p4, RP, 32)] ++ (LBN ++ LB))).
        apply Permutation_app_tail. apply Permutation_sym. apply Permutation_rev. }
    split; [exact MPA|].
    split. { unfold c3_frame. rewrite unsigned_lit by (unfold ATP; lia).
             split; [exact KREL16|]. split; [exact MI16|]. split; [exact AC16|]. split; [exact ST16|]. split; [exact ERR16|]. split; [exact AUX16|].
             split; [exact HEAP16|]. split; [exact MF16|]. split; [exact IM16|]. split; [exact GM16| exact RL16]. }
    split; [exact (METH_of_relro _ RL16)|].
    split; [exact DELTA|].
    split; [exact ADN16|].
    split; [exact (CTXPH_mono L LB5 SUBL5 _ _ CPH16)|].
    split; [exact KEYS16|].
    split.
    { unfold MEMBIO, anm_R, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
      cbn [mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid membio_bio].
      rewrite ?Z.sub_0_r, ?Z.add_0_r.
      split. { unfold bio_hdr3 in BA16. replace (BIO_FLAGS_MEM_RDONLY + BIO_FLAGS_MEM_LEGACY_EOF) with 4608 by reflexivity. exact BA16. }
      split; [exact BB16|]. split; [exact BM16|]. split; [exact RPc|].
      split; [apply SUB45, SUB34, SUB23; exact AIN2|]. split; [apply SUB45, SUB34; exact BIN3|]. split; [apply SUB45; exact MIN4|]. split; [exact RIN5|].
      split; [exact BR1|]. split; [exact BR2|]. split; [exact BR3|]. split; [exact BR4|].
      unfold BIO_FLAGS_MEM_RDONLY, BIO_FLAGS_MEM_LEGACY_EOF. repeat split; try reflexivity; clear - LR BP BH; lia. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact AP|].
    split. { unfold MEMBIO_apart, anm_R, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. cbn [mb_bb mb_bm mb_rp].
             unhide DJ_A_BB. unhide DJ_A_BM. unhide DJ_A_RP. unhide DJ_BB_BM. unhide DJ_BB_RP. unhide DJ_BM_RP.
             clear - DJ_A_BB DJ_A_BM DJ_A_RP DJ_BB_BM DJ_BB_RP DJ_BM_RP. lia. }
    split. { unfold MEMBIO_shad, anm_R, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. cbn [mb_bb mb_bm mb_rp].
             split; [exact ADA16|]. split; [exact ADB16|]. split; [exact ADM16| exact ADR16]. }
    split; [exact FXS|]. split; [exact RFS16|].
    split.
    { (* [comment removed for export] *)
      eapply xpres_trans; [exact (XP1 _)|].
      eapply xpres_trans; [eapply (xpres_weaken H); [exact XP2| lia| auto| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
      eapply xpres_trans.
      { eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU3| exact WM3|]. constructor; [right; left; cbn; lia| constructor]. }
      eapply xpres_trans.
      { eapply (xpres_X_mono H); [eapply (xpres_drop_fresh H HH) with (SP := bv_unsigned sp + -112); [exact HEAP2| lia| lia| | | exact XP4]; cbn; lia|].
        intros q Hq. apply rin_ivs_app. right. exact Hq. }
      eapply xpres_trans.
      { eapply (xpres_of_munch H s LB _ _ _ m m4 m5); [exact HH| exact HP| exact MU5| exact WM5|]. constructor; [left; cbn; lia| constructor]. }
      eapply xpres_trans; [eapply (xpres_weaken H); [exact XP6| lia| intros b Hb; apply SUBL2, SUB0L; exact Hb| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
      eapply xpres_trans; [eapply (xpres_weaken H); [exact XP8| lia| intros b Hb; apply SUBL3, SUB0L; exact Hb| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
      eapply xpres_trans.
      { eapply (xpres_weaken H); [eapply (xpres_of_munch_fresh H HH) with (SP := bv_unsigned sp) (X := memflag_foot ++ ctxph_foot ph ++ XS); [exact HEAP6| lia| exact MU9| exact WM9|]| lia| intros b Hb; apply SUBL2, SUB0L; exact Hb| auto].
        constructor; [right; left; cbn; lia| constructor]. }
      eapply xpres_trans; [eapply (xpres_weaken H); [exact XP10| lia| intros b Hb; apply SUBL4, SUB0L; exact Hb| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
      exact XPT. }
    unfold NEWMEMBUF_COST, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. clear - AL2 AL4 AL6 AL8 AL10. lia.
  Qed.
End W.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AKit ECH_AKitS
  ECH_AStmt_C1 ECH_AStmt_C2 ECH_APF_C4 ECH_AStmt_C4 ECH_AC4_rep.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition AC4W (LBx : list block) (m : mem) (ph : errphase) (x : ctxinfo) : Prop :=
  MEMFLAG m 1 /\ IMPL_mem m /\ GOT_mem m /\ arelro_lib m /\ ERRPH LBx m ph /\ CTXPH LBx m (CtxReady x).

(* [comment removed for export] *)
Definition ARELRO_LO : Z := 0x571000.
Definition ARELRO_HI : Z := 0x5ea000.
Definition ac4_addr (LBx : list block) (a : Z) : Prop := lib_addr LBx a \/ (ARELRO_LO <= a < ARELRO_HI).

(* [comment removed for export] *)
Lemma libx_of_sub : forall lo hi a, sub_iv_b lo hi LIBX = true -> lo <= a < hi -> rin_ivs LIBX a.
Proof. intros lo hi a SB Ha. eapply sub_iv_b_sound; [exact SB| exact Ha]. Qed.
Local Ltac in_libx lo hi :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; left; left; apply (libx_of_sub lo hi); [vm_compute; reflexivity|];
  unfold in_range in Ha; cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in Ha;
  unfold A_mem_inited, A_malloc_impl, A_realloc_impl, A_free_impl in Ha |- *; lia.

Lemma AC4W_agree : forall LBx m m' ph x, magree (ac4_addr LBx) m m' -> AC4W LBx m ph x -> AC4W LBx m' ph x.
Proof.
  intros LBx m m' ph x AG ((fb & MF & MV) & (I1 & I2 & I3) & GM & RL & EP & CP).
  assert (AGL : magree (lib_addr LBx) m m') by (eapply magree_mono; [exact AG| intros a Ha; left; exact Ha]).
  split; [exists fb; split; [eapply rw_cells_agree; [exact AG| exact MF| in_libx A_mem_inited (A_mem_inited + 1)]| exact MV]|].
  split.
  { unfold IMPL_mem. split; [| split];
      [ eapply rw_cells_agree; [exact AG| exact I1| in_libx A_malloc_impl (A_malloc_impl + 8)]
      | eapply rw_cells_agree; [exact AG| exact I2| in_libx A_realloc_impl (A_realloc_impl + 8)]
      | eapply rw_cells_agree; [exact AG| exact I3| in_libx A_free_impl (A_free_impl + 8)] ]. }
  split.
  { unfold GOT_mem in *. eapply rw_cells_agree; [exact AG| exact GM|]. intros a Ha. right. unfold in_range in Ha.
    cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. unfold A_got_CRYPTO_malloc, ARELRO_LO, ARELRO_HI in *. lia. }
  split.
  { intros a Ha. eapply none_agree; [exact AG| unfold ARELRO_LO, ARELRO_HI in *; lia| right; unfold ARELRO_LO, ARELRO_HI; lia| apply RL; exact Ha]. }
  split; [eapply ERRPH_frame; [exact EP| exact AGL]| eapply CTXPH_frame; [exact CP| exact AGL]].
Qed.

(* [comment removed for export] *)
Lemma ac4_static_client : forall (H : asr) LB SP a, rin_ivs LIBX a \/ (ARELRO_LO <= a < ARELRO_HI) -> aclient_addr H LB SP a.
Proof.
  intros H LB SP a HA. right; left. unfold aimg_client, ARELRO_LO, ARELRO_HI in *.
  destruct HA as [HX|HR]; [| lia]. revert HX. unfold LIBX, LIBX0, LIBXW. cbn [rin_ivs fst snd app]. lia.
Qed.

Lemma AC4W_xpres : forall (H : asr) LBx Lall SP m m' ph x,
  AC4W LBx m ph x -> xpres H Lall SP [] m m' -> (forall b, In b LBx -> In b Lall) -> AC4W LBx m' ph x.
Proof.
  intros H LBx Lall SP m m' ph x W XP SUB. eapply AC4W_agree; [| exact W].
  intros a Ha HA. apply XP; [exact Ha|]. split; [| intros K; exact K].
  destruct HA as [[HX|[(b & Hb & Hr)|(b & Hb & Hr)]]|HR].
  - apply ac4_static_client. left. exact HX.
  - right; right; left. exists b. split; [apply SUB; exact Hb| exact Hr].
  - right; right; right; left. exists b. split; [apply SUB; exact Hb| exact Hr].
  - apply ac4_static_client. right. exact HR.
Qed.

Lemma abyte_eq_of_unsigned : forall (b : byte) z, bv_unsigned b = z -> b = Z_to_bv 8 z.
Proof. intros b z E. subst z. symmetry. apply (bitvector.definitions.Z_to_bv_bv_unsigned 8). Qed.
(* [comment removed for export] *)
Lemma amemflag_same : forall m m', MEMFLAG m 1 -> MEMFLAG m' 1 ->
  m' (wa A_mem_inited) = m (wa A_mem_inited) /\ (wview asegs m (wa A_mem_inited) <> None -> wview asegs m' (wa A_mem_inited) <> None).
Proof.
  intros m m' (fb & [[_ (_ & _ & B1)] _] & V1 & _) (fb' & [[_ (_ & _ & B2)] (_ & _ & W2)] & V2 & _).
  cbn [cells_bytes cbytes app length cells_size csize Nat.add] in *.
  specialize (B1 0%nat ltac:(lia)). specialize (B2 0%nat ltac:(lia)). cbn [nth_error] in B1, B2. change (Z.of_nat 0) with 0 in B1, B2.
  replace (A_mem_inited + 0) with A_mem_inited in B1, B2 by lia.
  assert (ROM : seg_rom asegs (wa A_mem_inited) = Some (b8 0)) by (vm_compute; reflexivity).
  assert (E : fb = fb') by (rewrite (abyte_eq_of_unsigned fb 1 V1), (abyte_eq_of_unsigned fb' 1 V2); reflexivity). subst fb'.
  unfold mrd in B1, B2. split.
  - destruct (m (wa A_mem_inited)) as [x1|] eqn:E1, (m' (wa A_mem_inited)) as [x2|] eqn:E2; try congruence;
      exfalso; rewrite ROM in *; assert (EF : fb = b8 0) by congruence; rewrite EF in V1; vm_compute in V1; discriminate.
  - intros _. specialize (W2 0 ltac:(change (Z.of_nat 1) with 1; lia)). replace (A_mem_inited + 0) with A_mem_inited in W2 by lia. exact W2.
Qed.

Lemma AC4W_xpres_mf : forall (H : asr) LBx Lall SP m m' ph x,
  AC4W LBx m ph x -> xpres H Lall SP memflag_foot m m' -> MEMFLAG m' 1 -> (forall b, In b LBx -> In b Lall) -> AC4W LBx m' ph x.
Proof.
  intros H LBx Lall SP m m' ph x W XP MF' SUB. pose proof W as (MF & _). eapply AC4W_agree; [| exact W].
  intros a Ha HA. destruct (Z.eq_dec a A_mem_inited) as [->|NE]; [apply amemflag_same; assumption|].
  apply XP; [exact Ha|]. split; [| unfold memflag_foot; cbn; lia].
  destruct HA as [[HX|[(b & Hb & Hr)|(b & Hb & Hr)]]|HR].
  - apply ac4_static_client. left. exact HX.
  - right; right; left. exists b. split; [apply SUB; exact Hb| exact Hr].
  - right; right; right; left. exists b. split; [apply SUB; exact Hb| exact Hr].
  - apply ac4_static_client. right. exact HR.
Qed.

(* [comment removed for export] *)
Lemma magree_lib_xpres : forall (H : asr) L SP m m', xpres H L SP [] m m' -> magree (lib_addr L) m m'.
Proof.
  intros H L SP m m' XP a Ha HA. apply XP; [exact Ha|]. split; [| intros K; exact K].
  destruct HA as [HX|[(b & Hb & Hr)|(b & Hb & Hr)]].
  - apply ac4_static_client. left. exact HX.
  - right; right; left. exists b. split; [exact Hb| exact Hr].
  - right; right; right; left. exists b. split; [exact Hb| exact Hr].
Qed.
Lemma magree_lib_xpres_mf : forall (H : asr) L SP m m', xpres H L SP memflag_foot m m' -> MEMFLAG m 1 -> MEMFLAG m' 1 -> magree (lib_addr L) m m'.
Proof.
  intros H L SP m m' XP MF MF' a Ha HA. destruct (Z.eq_dec a A_mem_inited) as [->|NE]; [apply amemflag_same; assumption|].
  apply XP; [exact Ha|]. split; [| unfold memflag_foot; cbn; lia].
  destruct HA as [HX|[(b & Hb & Hr)|(b & Hb & Hr)]].
  - apply ac4_static_client. left. exact HX.
  - right; right; left. exists b. split; [exact Hb| exact Hr].
  - right; right; right; left. exists b. split; [exact Hb| exact Hr].
Qed.
(* [comment removed for export] *)
Lemma estrs_agree : forall Lx m m' E,
  (forall b, In b (blocks_ERRST E) -> In b Lx) -> (forall b, In b (blocks_ERRST E) -> 0 <= blk_size b) ->
  magree (lib_addr Lx) m m' -> lib_shad (blocks_ERRST E) m -> estrs_cells m E -> lib_shad (blocks_ERRST E) m' /\ estrs_cells m' E.
Proof.
  intros Lx m m' E SUB POS AG ESH ESC. split.
  - eapply lib_shad_frame; [exact ESH|]. eapply magree_mono; [exact AG|]. intros a Ha. eapply lib_addr_mono; [exact SUB| exact Ha].
  - unfold estrs_cells in *. apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) ESC _ Hb) as [bs BC]. exists bs.
    eapply rw_cells_agree; [exact AG| exact BC|]. intros a Ha. right; left. exists b. split; [apply SUB; exact Hb|].
    unfold in_range in Ha. pose proof (POS b Hb). revert Ha. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. intros Ha. lia.
Qed.

(* [comment removed for export] *)
Lemma nodup_map_app_excl : forall {X Y} (f : X -> Y) l1 l2 b, List.NoDup (map f (l1 ++ l2)) -> In b l1 -> In b l2 -> False.
Proof.
  intros X Y f l1. induction l1 as [|y l1 IH]; cbn; intros l2 b ND I1 I2; [contradiction|].
  inversion ND as [|z l NI ND']; subst. destruct I1 as [->|I1]; [apply NI; apply in_map; apply in_or_app; right; exact I2| eapply IH; eauto].
Qed.
Lemma perm_keep : forall (Fr L' L : list block) b, Permutation (Fr ++ L') L -> In b L -> ~ In b Fr -> In b L'.
Proof.
  intros Fr L' L b PM IB NF. apply Permutation_sym in PM. pose proof (Permutation_in _ PM IB) as K.
  apply in_app_or in K. destruct K as [K|K]; [contradiction| exact K].
Qed.
Lemma nodup_mid_excl : forall {X Y} (f : X -> Y) A Fr G C b, List.NoDup (map f (A ++ (Fr ++ G) ++ C)) -> In b Fr -> In b G -> False.
Proof.
  intros X Y f A Fr G C b ND IF IG. rewrite map_app in ND. apply NoDup_app_remove_l in ND. rewrite <- app_assoc in ND.
  eapply (nodup_map_app_excl f Fr (G ++ C) b); [exact ND| exact IF| apply in_or_app; left; exact IG].
Qed.
(* [comment removed for export] *)
Lemma disjoint_from_inside : forall W lo' hi' A n,
  Forall (fun iv : Z * Z => lo' <= fst iv /\ snd iv <= hi') W -> (A + n <= lo' \/ hi' <= A) -> disjoint_from W A n.
Proof.
  induction W as [|[wl wh] W IH]; intros lo' hi' A n FW HD; [exact I|]. cbn. split; [| eapply IH; [exact (Forall_inv_tail FW)| exact HD]].
  pose proof (Forall_inv FW) as K. cbn in K. lia.
Qed.

(* [comment removed for export] *)
Lemma EXLOCK_munch : forall LIB W m m' b,
  EXLOCK LIB m b -> munch W m m' -> wmono asegs m m' -> disjoint_from W (blk_addr b) 12 -> EXLOCK LIB m' b.
Proof.
  intros LIB W m m' b (I1 & Z1 & R1 & C1) MU WM DJ. split; [exact I1|]. split; [exact Z1|]. split; [exact R1|].
  unfold MUTEX in *. eapply rw_cells_transport; [exact C1| exact MU| exact WM| exact DJ].
Qed.

Section HH.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Lemma ablocks_apart_by_size : forall s L m b1 b2,
    as_RHEAP H s L m -> In b1 L -> In b2 L -> blk_size b1 <> blk_size b2 ->
    blk_addr b1 + blk_size b1 + 16 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 + 16 <= blk_addr b1.
  Proof.
    intros s L m b1 b2 HP I1 I2 NE. eapply (ah_disj H HH); [exact HP| exact I1| exact I2|].
    intros E. apply NE. rewrite (nodup_id_inj L b1 b2 (ah_nodup H HH _ _ _ HP) I1 I2 E). reflexivity.
  Qed.

  Lemma chain_sep_of_RHEAP : forall s L m0 LBx m c,
    as_RHEAP H s L m0 -> (forall b, In b LBx -> In b L) -> ERR_chain LBx m c -> chain_sep c.
  Proof.
    intros s L m0 LBx m c HP SUB (I2 & Z2 & _ & I3 & Z3 & _ & I4 & Z4 & _ & I5 & Z5 & _).
    unfold chain_sep. cbv zeta.
    pose proof (ablocks_apart_by_size _ _ _ _ _ HP (SUB _ I2) (SUB _ I5) ltac:(rewrite Z2, Z5; unfold ERRST_SIZE; lia)) as D2.
    pose proof (ablocks_apart_by_size _ _ _ _ _ HP (SUB _ I3) (SUB _ I5) ltac:(rewrite Z3, Z5; unfold ERRST_SIZE; lia)) as D3.
    pose proof (ablocks_apart_by_size _ _ _ _ _ HP (SUB _ I4) (SUB _ I5) ltac:(rewrite Z4, Z5; unfold ERRST_SIZE; lia)) as D4.
    rewrite Z2, Z3, Z4, Z5 in *. lia.
  Qed.

  (* [comment removed for export] *)
  Definition lowr_ok (iv : Z * Z) : Prop := low_ok iv /\ (snd iv <= ARELRO_LO \/ ARELRO_HI <= fst iv).
  Lemma errno_lowr : Forall lowr_ok ERRNO_X.
  Proof.
    apply Forall_cons; [| apply Forall_nil]. split; [apply errno_low_ok| cbn [fst snd]; unfold ARERRNO, ATP, ARELRO_LO, ARELRO_HI; lia].
  Qed.
  Lemma AC4W_foot : forall LF m0 s L m1 LBx lo hi XS LIT m m' ph x,
    as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> Forall lowr_ok LIT -> aceil <= lo ->
    as_RHEAP H s L m1 -> (forall b, In b LBx -> In b L) ->
    munch ((lo, hi) :: XS ++ LIT) m m' -> wmono asegs m m' -> AC4W LBx m ph x -> AC4W LBx m' ph x.
  Proof.
    intros LF m0 s L m1 LBx lo hi XS LIT m m' ph x R FXS FL CE HP SUB MU WM W. acb.
    assert (PL : Forall (fun b => ablock_range H (blk_addr b) (blk_size b)) LBx).
    { apply Forall_forall. intros b Hb. eapply (ah_blocks H HH); [exact HP| apply SUB; exact Hb]. }
    eapply AC4W_agree; [| exact W]. intros a Ha HA. destruct HA as [HA|HR].
    - eapply (lib_magree_scratch H HH); [exact R| exact PL| exact MU| exact WM| exact CE| | exact Ha| exact HA].
      apply Forall_app. split; [apply scr_ok_of_scratch; exact FXS| eapply Forall_impl; [| exact FL]; intros iv [K _]; right; exact K].
    - split; [| intros K; apply WM; exact K]. unfold wa. apply MU. rewrite unsigned_lit by lia. clear MU WM W.
      cbn. split; [unfold ARELRO_HI in HR; lia|].
      induction XS as [|iv XS IH]; cbn.
      + induction LIT as [|[u v] LIT IH2]; [exact I|]. cbn. pose proof (Forall_inv FL) as [[L1 _] L2]. cbn [fst snd] in L1, L2.
        split; [lia| exact (IH2 (Forall_inv_tail FL))].
      + destruct iv as [u v]. cbn. pose proof (fs_scratch_range H HH _ _ _ R (Forall_inv FXS)) as K. cbn [fst snd] in K.
        split; [unfold AIMG_TOP, ARELRO_HI in *; lia| exact (IH (Forall_inv_tail FXS))].
  Qed.

  (* [comment removed for export] *)
  Lemma AC4W_es : forall LBx L s m0 W m m' c x,
    AC4W LBx m (ErrReady c) x -> as_RHEAP H s L m0 -> (forall b, In b LBx -> In b L) ->
    munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => blk_addr (ec_es c) <= fst iv /\ snd iv <= blk_addr (ec_es c) + ERRST_SIZE) W ->
    AC4W LBx m' (ErrReady c) x.
  Proof.
    intros LBx L s m0 W m m' c x ((fb & MF & MV) & (IM1 & IM2 & IM3) & GM & RL & [ES EC] & [CS [EX OL]]) HP SUB MU WM FW. acb.
    pose proof EC as EC0. destruct EC as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
    pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ I5)) as BR. rewrite Z5 in BR. destruct BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7). unfold ERRST_SIZE in *.
    assert (OFFI : forall A n, A + n <= AIMG_TOP -> disjoint_from W A n).
    { intros A n H1. eapply disjoint_from_inside; [exact FW|]. cbn [fst snd]. lia. }
    pose proof (chain_sep_of_RHEAP _ _ _ _ m _ HP SUB EC0) as CSEP. unfold chain_sep in CSEP. cbv zeta in CSEP. unfold ERRST_SIZE in CSEP.
    assert (AGX : magree (lib_addr []) m m').
    { eapply magree_of_munch; [exact MU| exact WM|]. intros a [HX|[(b & Hb & _)|(b & Hb & _)]]; [| destruct Hb| destruct Hb].
      pose proof (LIBX_below _ HX). clear - FW H0 B4. induction W as [|[wl wh] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as K. cbn in K. split; [lia| exact (IH (Forall_inv_tail FW))]. }
    unfold AC4W, IMPL_mem, GOT_mem in *. unfold A_mem_inited, A_malloc_impl, A_realloc_impl, A_free_impl, A_got_CRYPTO_malloc, AIMG_TOP in *.
    split. { exists fb. split; [| exact MV]. eapply rw_cells_transport; [exact MF| exact MU| exact WM|]. apply OFFI. unfold A_mem_inited. cbn. lia. }
    split; [split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| apply OFFI; unfold A_malloc_impl, A_realloc_impl, A_free_impl; cbn; lia])|].
    split; [eapply rw_cells_transport; [exact GM| exact MU| exact WM| apply OFFI; unfold A_got_CRYPTO_malloc; cbn; lia]|].
    split.
    { intros a Ha. unfold wa. rewrite MU; [apply RL; exact Ha|]. rewrite unsigned_lit by lia.
      eapply disjoint_outside; [apply (OFFI a 1); lia| lia]. }
    split.
    - split; [eapply (ERR_statics_frame []); [exact ES| exact AGX]|].
      unfold ERR_chain, sa_cells. repeat match goal with |- _ /\ _ => split end; try assumption.
      + eapply rw_cells_transport; [exact K2| exact MU| exact WM|]. eapply disjoint_from_inside; [exact FW|]. unfold O_MKEY_ERR. cbn. lia.
      + eapply rw_cells_transport; [exact K3| exact MU| exact WM|]. eapply disjoint_from_inside; [exact FW|]. cbn. lia.
      + eapply rw_cells_transport; [exact K4| exact MU| exact WM|]. eapply disjoint_from_inside; [exact FW|]. cbn. lia.
    - split; [eapply (CTX_statics_frame []); [exact CS| exact AGX]|]. split; [| exact OL].
      pose proof EX as (XI & XZ & _ & _).
      pose proof (ablocks_apart_by_size _ _ _ _ _ HP (SUB _ XI) (SUB _ I5) ltac:(rewrite XZ, Z5; unfold MUTEX_SIZE; lia)) as DX.
      rewrite XZ, Z5 in DX. unfold MUTEX_SIZE in DX.
      eapply EXLOCK_munch; [exact EX| exact MU| exact WM|]. eapply disjoint_from_inside; [exact FW|]. cbn [fst snd]. unfold MUTEX_SIZE. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma aes_world : forall s L LBx m m' c x lo spx B (errv : word) A cs,
    as_RHEAP H s L m -> (forall b, In b LBx -> In b L) -> AC4W LBx m (ErrReady c) x ->
    as_rauxv_ok H m B -> rw_cells asegs m ARERRNO [C4 errv] -> stk asegs m lo spx -> rw_cells asegs m A cs ->
    ACONST m -> lib_shad (chain_blocks c) m ->
    aceil <= lo -> lo <= A -> lo <= B ->
    munch [(blk_addr (ec_es c), blk_addr (ec_es c) + 904)] m m' -> wmono asegs m m' ->
    as_RHEAP H s L m' /\ AC4W LBx m' (ErrReady c) x /\ as_rauxv_ok H m' B /\ rw_cells asegs m' ARERRNO [C4 errv]
    /\ stk asegs m' lo spx /\ rw_cells asegs m' A cs /\ ACONST m' /\ lib_shad (chain_blocks c) m'.
  Proof.
    intros s L LBx m m' c x lo spx B errv A cs HP SUB CW AUX ERR ST FR AC LS CEIL LA LB0 MU WM. acb.
    pose proof CW as (_ & _ & _ & _ & [_ EC] & _). cbn [ERRPH] in EC. pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _ & _ & RR).
    pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ I5)) as BR. rewrite Z5 in BR. pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7). unfold ERRST_SIZE in *.
    unfold AIMG_TOP, ARERRNO, ATP in *.
    split. { eapply (ah_RHEAP_frame H HH); [exact HP| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil].
             right; right; left. exists (ec_es c). split; [apply SUB; exact I5|]. rewrite Z5. cbn. lia. }
    split. { eapply AC4W_es; [exact CW| exact HP| exact SUB| exact MU| exact WM|]. apply Forall_cons; [unfold ERRST_SIZE; cbn; lia| apply Forall_nil]. }
    split. { eapply (ah_rauxv_frame H HH); [exact AUX| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil].
             right; right; left. exists (ec_es c). split; [apply SUB; exact I5|]. rewrite Z5. cbn. lia. }
    split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. cbn. lia. }
    split. { eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. cbn. lia. }
    split. { pose proof (rw_cells_bound _ _ _ _ FR) as FB. eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn. lia. }
    split. { eapply ACONST_frame; [exact AC| exact MU| exact WM|]. apply Forall_cons; [eapply aconst_ok_aapp; [exact B7| cbn; lia| cbn; lia]| apply Forall_nil]. }
    unfold lib_shad in *. apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) LS _ Hb) as AD.
    pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ (chain_blocks_in _ _ _ _ EC Hb))) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
    pose proof (aapp_bounds _ _ Q7 Q3) as (_ & _ & T1 & _).
    eapply addressable_transport; [exact AD| exact MU| exact WM|]. cbn. split; [| exact I].
    pose proof (aapp_disjoint_sh (blk_addr (ec_es c)) 904 (blk_addr b) (blk_size b) B7 ltac:(lia) ltac:(lia) Q3). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ERRXR_agree : forall L m m' c E,
    ERRXR m c E -> In (ec_es c) L -> blk_size (ec_es c) = ERRST_SIZE -> (forall b, In b (blocks_ERRST E) -> In b L) ->
    (forall b, In b (blocks_ERRST E) -> 0 <= blk_size b) -> magree (lib_addr L) m m' -> ERRXR m' c E.
  Proof.
    intros L m m' c E (EST & ESZ & ESH & ESC) I5 Z5 SUB POS AG. split; [| split; [exact ESZ| split]].
    - eapply ERRST_agree; [exact AG| exact EST|]. intros a Ha. right; left. exists (ec_es c). split; [exact I5|]. unfold in_range in Ha. rewrite Z5. lia.
    - eapply lib_shad_frame; [exact ESH|]. eapply magree_mono; [exact AG|]. intros a Ha. eapply lib_addr_mono; [exact SUB| exact Ha].
    - unfold estrs_cells in *. apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) ESC _ Hb) as [bs BC]. exists bs.
      eapply rw_cells_agree; [exact AG| exact BC|]. intros a Ha. right; left. exists b. split; [apply SUB; exact Hb|].
      unfold in_range in Ha. pose proof (POS b Hb). revert Ha. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. intros Ha. lia.
  Qed.
  Lemma estrs_pos : forall E b, estrs_ok E -> In b (blocks_ERRST E) -> 0 <= blk_size b <= 32.
  Proof.
    intros E b OK Hb. unfold blocks_ERRST in Hb. apply in_concat in Hb. destruct Hb as (l & Hl & Hbl). apply in_map_iff in Hl. destruct Hl as (sl & <- & Hsl).
    pose proof (proj1 (Forall_forall _ _) OK _ Hsl) as [K1 K2]. unfold blocks_slot, blocks_of in Hbl.
    destruct (sl_file_o sl) as [[i1 n1]|], (sl_func_o sl) as [[i2 n2]|]; cbn [oszb app] in *;
      repeat (destruct Hbl as [<-|Hbl]; [cbn; lia|]); destruct Hbl.
  Qed.

  (* [comment removed for export] *)
  Lemma afree_world : forall LBx L' m m' c x spx A cs E,
    AC4W LBx m (ErrReady c) x -> xpres H L' spx [] m m' -> (forall b, In b LBx -> In b L') ->
    rw_cells asegs m A cs -> spx <= A -> ERRSTm m (blk_addr (ec_es c)) E -> 0 <= blk_addr (ec_es c) -> blk_addr (ec_es c) + ERRST_SIZE <= 2^64 ->
    lib_shad (chain_blocks c) m ->
    AC4W LBx m' (ErrReady c) x /\ rw_cells asegs m' A cs /\ ERRSTm m' (blk_addr (ec_es c)) E /\ lib_shad (chain_blocks c) m'.
  Proof.
    intros LBx L' m m' c x spx A cs E CW XP SUB FR SA EM E0 E1 LS.
    pose proof CW as (_ & _ & _ & _ & [_ EC] & _). cbn [ERRPH] in EC. pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    split; [eapply AC4W_xpres; eassumption|].
    split; [eapply xpres_rw_cells'; [exact XP| exact FR| left; lia| constructor]|].
    split.
    { eapply ERRSTm_xpres; [exact EM| exact XP| | exact E0| exact E1].
      intros a Ha. split; [| intros K; exact K]. right; right; left. exists (ec_es c). split; [apply SUB; exact I5| rewrite Z5; exact Ha]. }
    unfold lib_shad in *. apply Forall_forall. intros b Hb.
    eapply (addressable_agree (chain_blocks c)); [| exact Hb| exact (proj1 (Forall_forall _ _) LS _ Hb)].
    intros a Ha HA. apply XP; [exact Ha|]. split; [| intros K; exact K].
    destruct HA as [HX|[(b' & Hb' & Hr)|(b' & Hb' & Hr)]].
    - apply ac4_static_client. left. exact HX.
    - right; right; left. exists b'. split; [apply SUB; eapply chain_blocks_in; [exact EC| exact Hb']| exact Hr].
    - right; right; right; left. exists b'. split; [apply SUB; eapply chain_blocks_in; [exact EC| exact Hb']| exact Hr].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ablocks_apart_notin : forall s L m Lx b1 b2,
    as_RHEAP H s L m -> In b1 L -> ~ In b1 Lx -> In b2 Lx -> (forall b, In b Lx -> In b L) ->
    blk_addr b1 + blk_size b1 + 16 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 + 16 <= blk_addr b1.
  Proof.
    intros s L m Lx b1 b2 HP I1 N1 I2 SUB. eapply (ah_disj H HH); [exact HP| exact I1| apply SUB; exact I2|].
    intros E. apply N1. rewrite (nodup_id_inj L b1 b2 (ah_nodup H HH _ _ _ HP) I1 (SUB _ I2) E). exact I2.
  Qed.
  (* [comment removed for export] *)
  Definition esw_ok (LBx : list block) (iv : Z * Z) : Prop :=
    AIMG_TOP <= fst iv /\
    forall b, In b LBx -> blk_size b <> ERRST_SIZE -> snd iv <= blk_addr b \/ blk_addr b + blk_size b <= fst iv.
  Lemma disjoint_from_esw : forall LBx W b A n,
    Forall (esw_ok LBx) W -> In b LBx -> blk_size b <> ERRST_SIZE -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b ->
    disjoint_from W A n.
  Proof.
    intros LBx W b A n FW Hb NE LA HA. induction W as [|[wl wh] W IH]; [exact I|]. cbn.
    pose proof (Forall_inv FW) as [K1 K3]. cbn [fst snd] in K1, K3. pose proof (K3 _ Hb NE) as K4.
    split; [lia| exact (IH (Forall_inv_tail FW))].
  Qed.
  (* [comment removed for export] *)
  Lemma AC4W_esw : forall LBx L s m0 W m m' c x,
    AC4W LBx m (ErrReady c) x -> as_RHEAP H s L m0 -> (forall b, In b LBx -> In b L) ->
    munch W m m' -> wmono asegs m m' -> Forall (esw_ok LBx) W ->
    AC4W LBx m' (ErrReady c) x.
  Proof.
    intros LBx L s m0 W m m' c x ((fb & MF & MV) & (IM1 & IM2 & IM3) & GM & RL & [ES EC] & [CS [EX OL]]) HP SUB MU WM FW. acb.
    pose proof EC as EC0. destruct EC as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
    assert (OFFI : forall A n, A + n <= AIMG_TOP -> disjoint_from W A n).
    { intros A n H1. clear - FW H1. induction W as [|[wl wh] W IH]; [exact I|]. cbn. pose proof (Forall_inv FW) as [K1 _]. cbn [fst] in K1.
      split; [lia| exact (IH (Forall_inv_tail FW))]. }
    assert (AGX : magree (lib_addr []) m m').
    { eapply magree_of_munch; [exact MU| exact WM|]. intros a [HX|[(b & Hb & _)|(b & Hb & _)]]; [| destruct Hb| destruct Hb].
      pose proof (LIBX_below _ HX). clear - FW H0. induction W as [|[wl wh] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as [K _]. cbn in K. split; [lia| exact (IH (Forall_inv_tail FW))]. }
    assert (DK2 : disjoint_from W (blk_addr (ec_mkey c) + O_MKEY_ERR) 8).
    { eapply disjoint_from_esw; [exact FW| exact I2| rewrite Z2; unfold ERRST_SIZE; lia| unfold O_MKEY_ERR; lia| rewrite Z2; unfold O_MKEY_ERR; lia]. }
    assert (DK3 : disjoint_from W (blk_addr (ec_sa c)) 32).
    { eapply disjoint_from_esw; [exact FW| exact I3| rewrite Z3; unfold ERRST_SIZE; lia| lia| rewrite Z3; lia]. }
    assert (DK4 : disjoint_from W (blk_addr (ec_nodes c)) 8).
    { eapply disjoint_from_esw; [exact FW| exact I4| rewrite Z4; unfold ERRST_SIZE; lia| lia| rewrite Z4; lia]. }
    pose proof EX as (XI & XZ & _ & _).
    assert (DKX : disjoint_from W (blk_addr (cx_exlock x)) 12).
    { eapply disjoint_from_esw; [exact FW| exact XI| rewrite XZ; unfold MUTEX_SIZE, ERRST_SIZE; lia| lia| rewrite XZ; unfold MUTEX_SIZE; lia]. }
    clear FW.
    unfold AC4W, IMPL_mem, GOT_mem in *. unfold A_mem_inited, A_malloc_impl, A_realloc_impl, A_free_impl, A_got_CRYPTO_malloc, AIMG_TOP in *.
    split. { exists fb. split; [| exact MV]. eapply rw_cells_transport; [exact MF| exact MU| exact WM|]. apply OFFI. unfold A_mem_inited. cbn. lia. }
    split; [split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| apply OFFI; unfold A_malloc_impl, A_realloc_impl, A_free_impl; cbn; lia])|].
    split; [eapply rw_cells_transport; [exact GM| exact MU| exact WM| apply OFFI; unfold A_got_CRYPTO_malloc; cbn; lia]|].
    split.
    { intros a Ha. unfold wa. rewrite MU; [apply RL; exact Ha|]. rewrite unsigned_lit by lia.
      eapply disjoint_outside; [apply (OFFI a 1); lia| lia]. }
    split.
    - split; [eapply (ERR_statics_frame []); [exact ES| exact AGX]|].
      unfold ERR_chain, sa_cells. repeat match goal with |- _ /\ _ => split end; try assumption.
      + eapply rw_cells_transport; [exact K2| exact MU| exact WM| exact DK2].
      + eapply rw_cells_transport; [exact K3| exact MU| exact WM| exact DK3].
      + eapply rw_cells_transport; [exact K4| exact MU| exact WM| exact DK4].
    - split; [eapply (CTX_statics_frame []); [exact CS| exact AGX]|]. split; [| exact OL].
      eapply EXLOCK_munch; [exact EX| exact MU| exact WM| exact DKX].
  Qed.
  (* [comment removed for export] *)
  Lemma addressable_acrossW : forall W m m' A n, addressable m A n -> aapp A n ->
    munch W m m' -> wmono asegs m m' -> Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W -> addressable m' A n.
  Proof.
    intros W m m' A n AD AP MU WM HW. eapply addressable_transport; [exact AD| exact MU| exact WM|].
    pose proof (sh_aapp_range A n AP ltac:(destruct AD; lia)) as (S1 & S2 & S3).
    pose proof (aapp_bounds A n AP ltac:(destruct AD; lia)) as (B1 & _ & _ & B4 & _).
    assert (S0 : ASHADOW_BASE <= sh A) by (unfold sh; Z.div_mod_to_equations; lia). rewrite ASHADOW_BASE_val in S0.
    clear - HW S0 S2 S3. induction W as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv HW) as K1. cbn in K1.
    split; [unfold ALOWSH_LO, AHI_LO in *; lia| exact (IH (Forall_inv_tail HW))].
  Qed.
  (* [comment removed for export] *)
  Lemma aheapw_world : forall s L LBx m m' c x lo slo shi B (errv : word) A cs bk,
    as_RHEAP H s L m -> (forall b, In b LBx -> In b L) -> In bk L -> ~ In bk LBx -> AC4W LBx m (ErrReady c) x ->
    as_rauxv_ok H m B -> rw_cells asegs m ARERRNO [C4 errv] -> rw_cells asegs m A cs -> lib_shad (chain_blocks c) m ->
    aceil <= lo -> lo <= slo -> slo <= shi -> shi <= A ->
    munch [(blk_addr (ec_es c), blk_addr (ec_es c) + 904); (blk_addr bk, blk_addr bk + blk_size bk); (slo, shi)] m m' ->
    wmono asegs m m' ->
    as_RHEAP H s L m' /\ AC4W LBx m' (ErrReady c) x /\ as_rauxv_ok H m' B /\ rw_cells asegs m' ARERRNO [C4 errv]
    /\ rw_cells asegs m' A cs /\ lib_shad (chain_blocks c) m'.
  Proof.
    intros s L LBx m m' c x lo slo shi B errv A cs bk HP SUB IBK NBK CW AUX ERR FR LS CEIL LS0 LS1 SA MU WM. acb.
    pose proof CW as (_ & _ & _ & _ & [_ EC] & _). cbn [ERRPH] in EC. pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _ & _ & RR).
    pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ I5)) as BR. rewrite Z5 in BR. pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (ah_blocks H HH _ _ _ _ HP IBK) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). unfold ERRST_SIZE in *.
    assert (FW : Forall (esw_ok LBx) [(blk_addr (ec_es c), blk_addr (ec_es c) + 904); (blk_addr bk, blk_addr bk + blk_size bk); (slo, shi)]).
    { apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]];
        (split; [cbn [fst]; lia| cbn [fst snd]; intros b Hb NE]).
      - pose proof (ablocks_apart_by_size _ _ _ _ _ HP (SUB _ Hb) (SUB _ I5) ltac:(rewrite Z5; exact NE)) as K. rewrite Z5 in K. lia.
      - pose proof (ablocks_apart_notin _ _ _ _ _ _ HP IBK NBK Hb SUB). lia.
      - pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & _ & _ & K5 & _). lia. }
    unfold AIMG_TOP, ARERRNO, ATP in *.
    split. { eapply (ah_RHEAP_frame H HH); [exact HP| exact MU| exact WM|].
             apply Forall_cons; [right; right; left; exists (ec_es c); split; [apply SUB; exact I5| rewrite Z5; cbn; lia]|].
             apply Forall_cons; [right; right; left; exists bk; split; [exact IBK| cbn; lia]|].
             apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    split. { eapply AC4W_esw; [exact CW| exact HP| exact SUB| exact MU| exact WM| exact FW]. }
    split. { eapply (ah_rauxv_frame H HH) with (LB := L); [exact AUX| exact MU| exact WM|].
             apply Forall_cons; [right; right; left; exists (ec_es c); split; [apply SUB; exact I5| rewrite Z5; cbn; lia]|].
             apply Forall_cons; [right; right; left; exists bk; split; [exact IBK| cbn; lia]|].
             apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. cbn. lia. }
    split. { pose proof (rw_cells_bound _ _ _ _ FR) as FB. eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn. lia. }
    unfold lib_shad in *. apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) LS _ Hb) as AD.
    pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ (chain_blocks_in _ _ _ _ EC Hb))) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
    eapply addressable_acrossW; [exact AD| exact R7| exact MU| exact WM|].
    apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ B7)|].
    apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ Q7)|].
    apply Forall_cons; [cbn [fst snd]; right; unfold AHI_LO; lia| apply Forall_nil].
  Qed.
  (* [comment removed for export] *)
  Lemma lib_magree_esw : forall s L m0 Lx W m m',
    as_RHEAP H s L m0 -> (forall b, In b Lx -> In b L) -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv /\ (snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) /\
                              forall b, In b Lx -> snd iv <= blk_addr b \/ blk_addr b + blk_size b <= fst iv) W ->
    magree (lib_addr Lx) m m'.
  Proof.
    intros s L m0 Lx W m m' HP SUB MU WM FW. acb. eapply magree_of_munch; [exact MU| exact WM|].
    intros a Ha. clear MU WM. induction W as [|[wl wh] W IH]; [exact I|]. cbn. split; [| exact (IH (Forall_inv_tail FW))].
    pose proof (Forall_inv FW) as (K1 & K2 & K3). cbn [fst snd] in K1, K2, K3.
    destruct Ha as [HX|[(b & Hb & Hr)|(b & Hb & Hr)]].
    - pose proof (LIBX_below _ HX). lia.
    - pose proof (K3 _ Hb). lia.
    - pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (B1 & _ & B3 & _ & _ & _ & B7).
      pose proof (sh_aapp_range _ _ B7 B3) as (S1 & S2 & S3).
      assert (S0 : ASHADOW_BASE <= sh (blk_addr b)) by (unfold sh; Z.div_mod_to_equations; lia). rewrite ASHADOW_BASE_val in S0.
      unfold ALOWSH_LO, AHI_LO in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma lib_magree_dbg : forall s L LBx Lx m m' es bk slo shi,
    as_RHEAP H s L m -> (forall b, In b LBx -> In b L) -> (forall b, In b Lx -> In b LBx) ->
    In es L -> blk_size es = 904 -> (forall b, In b Lx -> 0 <= blk_size b <= 32) ->
    In bk L -> ~ In bk LBx -> aceil <= slo ->
    munch [(blk_addr es, blk_addr es + 904); (blk_addr bk, blk_addr bk + blk_size bk); (slo, shi)] m m' -> wmono asegs m m' ->
    magree (lib_addr Lx) m m'.
  Proof.
    intros s L LBx Lx m m' es bk slo shi HP SUB SUBx IES ZES SMALL IBK NBK CE MU WM. acb.
    pose proof (ah_blocks H HH _ _ _ _ HP IES) as BR. rewrite ZES in BR. destruct BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (ah_blocks H HH _ _ _ _ HP IBK) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
    eapply lib_magree_esw with (L := L); [exact HP| intros b Hb; apply SUB; apply SUBx; exact Hb| exact MU| exact WM|].
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd].
    - split; [lia|]. split; [exact (aapp_not_shadowland _ _ B7)|]. intros b Hb.
      pose proof (ablocks_apart_by_size _ _ _ _ _ HP (SUB _ (SUBx _ Hb)) IES ltac:(rewrite ZES; pose proof (SMALL _ Hb); lia)) as K.
      rewrite ZES in K. lia.
    - split; [lia|]. split; [exact (aapp_not_shadowland _ _ Q7)|]. intros b Hb.
      pose proof (ablocks_apart_notin _ _ _ _ _ _ HP IBK NBK (SUBx _ Hb) SUB). lia.
    - split; [unfold AIMG_TOP; lia|]. split; [right; unfold AHI_LO; lia|]. intros b Hb.
      pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ (SUBx _ Hb))) as (_ & _ & _ & _ & K5 & _). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma RFS_dbg : forall LF s L m m' es bk slo shi,
    as_RFS H LF m -> as_RHEAP H s L m -> In es L -> blk_size es = 904 -> In bk L -> aceil <= slo ->
    munch [(blk_addr es, blk_addr es + 904); (blk_addr bk, blk_addr bk + blk_size bk); (slo, shi)] m m' -> wmono asegs m m' ->
    as_RFS H LF m'.
  Proof.
    intros LF s L m m' es bk slo shi R HP IES ZES IBK CE MU WM. acb. pose proof (RFS_fsb H HH _ _ R) as (F1 & F2 & F3 & F4).
    pose proof (ah_blocks H HH _ _ _ _ HP IES) as BR. rewrite ZES in BR. destruct BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (ah_blocks H HH _ _ _ _ HP IBK) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
    eapply (ah_RFS_frame H HH); [exact R| exact MU| exact WM|].
    repeat (apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, AIMG_TOP in *; lia|]). apply Forall_nil.
  Qed.
  (* [comment removed for export] *)
  Lemma xpres_dbgw : forall s L LB SP X m es bk slo shi m1 m2,
    as_RHEAP H s L m -> (forall b, In b LB -> In b L) -> In bk L -> ~ In bk LB ->
    (forall a, blk_addr es <= a < blk_addr es + 904 -> rin_ivs X a) -> aceil <= slo -> slo <= shi -> shi <= SP ->
    munch [(blk_addr es, blk_addr es + 904); (blk_addr bk, blk_addr bk + blk_size bk); (slo, shi)] m1 m2 -> wmono asegs m1 m2 ->
    xpres H LB SP X m1 m2.
  Proof.
    intros s L LB SP X m es bk slo shi m1 m2 HP SUB IBK NBK XE CE SS SSP MU WM a Ha [Hc Hx]. acb.
    pose proof (ah_blocks H HH _ _ _ _ HP IBK) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
    pose proof (ah_fsb H HH _ _ _ HP) as (F1 & F2 & F3 & F4).
    pose proof (sh_aapp_range _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (G1 & G2 & G3).
    assert (G0 : ASHADOW_BASE <= sh (as_FSB H)) by (unfold sh; Z.div_mod_to_equations; unfold AIMG_TOP in F1; lia). rewrite ASHADOW_BASE_val in G0.
    assert (G4 : sh (as_FSB H + AFS_SIZE) <= sh (as_FSB H) + nsh AFS_SIZE) by (unfold sh, nsh, AFS_SIZE; Z.div_mod_to_equations; lia).
    assert (SC1 : sh aceil < aceil) by (apply sh_below_aceil; unfold AAPP_HI; lia).
    assert (SC0 : ALOWSH_LO <= sh aceil) by (unfold sh, ALOWSH_LO; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    pose proof (aapp_not_shadowland _ _ Q7) as QS.
    split; [| intros Hw; apply WM; exact Hw].
    unfold wa. apply MU. rewrite unsigned_lit by lia. cbn. split; [| split; [| split; [| exact I]]].
    - assert (K : ~ (blk_addr es <= a < blk_addr es + 904)) by (intros K; exact (Hx (XE _ K))). lia.
    - assert (NIN : ~ (blk_addr bk <= a < blk_addr bk + blk_size bk)); [intros K| lia].
      unfold aclient_addr in Hc.
      destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]]].
      + lia.
      + unfold aimg_client, AIMG_TOP in *. lia.
      + pose proof (ablocks_apart_notin _ _ _ _ _ _ HP IBK NBK Hb SUB). lia.
      + pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (R1 & _ & R3 & _ & _ & _ & R7).
        pose proof (sh_aapp_range _ _ R7 R3) as (S1 & S2 & S3).
        assert (S0 : ASHADOW_BASE <= sh (blk_addr b)) by (unfold sh; Z.div_mod_to_equations; lia). rewrite ASHADOW_BASE_val in S0.
        unfold ALOWSH_LO, AHI_LO in *. lia.
      + unfold AFS_SIZE in *. lia.
      + unfold ALOWSH_LO, AHI_LO in *. lia.
      + unfold ALOWSH_LO, AHI_LO in *. lia.
    - unfold aclient_addr in Hc.
      destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]]].
      + lia.
      + unfold aimg_client, AIMG_TOP in *. lia.
      + pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & _ & _ & R5 & _). lia.
      + pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (R1 & _ & R3 & _ & _ & _ & R7).
        pose proof (sh_aapp_range _ _ R7 R3) as (S1 & S2 & S3). lia.
      + lia.
      + lia.
      + unfold AHI_LO in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma amalloc_world : forall s LBx Lall m m' c x spx A cs E,
    as_RHEAP H s Lall m -> (forall b, In b LBx -> In b Lall) -> aceil <= spx ->
    AC4W LBx m (ErrReady c) x -> xpres H Lall spx memflag_foot m m' -> MEMFLAG m' 1 ->
    rw_cells asegs m A cs -> spx <= A -> ERRSTm m (blk_addr (ec_es c)) E -> lib_shad (chain_blocks c) m ->
    AC4W LBx m' (ErrReady c) x /\ rw_cells asegs m' A cs /\ ERRSTm m' (blk_addr (ec_es c)) E /\ lib_shad (chain_blocks c) m'.
  Proof.
    intros s LBx Lall m m' c x spx A cs E HP SUB CE CW XP MF' FR SA EM LS. acb.
    pose proof CW as (_ & _ & _ & _ & [_ EC] & _). cbn [ERRPH] in EC. pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ I5)) as BR. rewrite Z5 in BR. pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7). unfold ERRST_SIZE in *.
    split; [eapply AC4W_xpres_mf; eassumption|].
    split. { pose proof (rw_cells_bound _ _ _ _ FR) as FB. eapply xpres_rw_cells'; [exact XP| exact FR| left; lia|].
             unfold memflag_foot, A_mem_inited. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    split.
    { eapply ERRSTm_xpres; [exact EM| exact XP| | lia| unfold ERRST_SIZE, AIMG_TOP in *; lia].
      intros a Ha. split; [right; right; left; exists (ec_es c); split; [apply SUB; exact I5| rewrite Z5; unfold ERRST_SIZE in Ha; exact Ha]|].
      unfold memflag_foot, A_mem_inited, ERRST_SIZE, AIMG_TOP in *. cbn. lia. }
    unfold lib_shad in *. apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) LS _ Hb) as AD.
    pose proof (SUB _ (chain_blocks_in _ _ _ _ EC Hb)) as HbL.
    pose proof (ah_blocks H HH _ _ _ _ HP HbL) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
    pose proof (aapp_bounds _ _ R7 R3) as (_ & _ & T1 & _).
    eapply (ashobj_addressable_xpres H HH); [exact HP| intros b' K; exact K| exact CE| | lia| exact AD| exact XP|].
    - left. exists b. split; [exact HbL| lia].
    - unfold memflag_foot, A_mem_inited, ALOWSH_LO. apply Forall_cons; [cbn; lia| apply Forall_nil].
  Qed.
End HH.
End HCW.

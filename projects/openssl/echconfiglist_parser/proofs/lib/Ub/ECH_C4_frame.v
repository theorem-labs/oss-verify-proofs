(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C1_stmt ECH_C2_stmt ECH_LibFrame ECH_C4_stmt ECH_C4_rep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition C4W (LBx : list block) (m : mem) (ph : errphase) (x : ctxinfo) : Prop :=
  MEMFLAG m 1 /\ IMPL_mem m /\ GOT_mem m /\ relro_lib m /\ ERRPH LBx m ph /\ CTXPH LBx m (CtxReady x).

(* [comment removed for export] *)
Definition c4_addr (LBx : list block) (a : Z) : Prop :=
  lib_addr LBx a \/ (RELRO_LO <= a < RELRO_HI /\ ~ (RGOT_SSP <= a < RGOT_SSP + 8)).

Local Ltac in_libx :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; left; left; unfold in_range in Ha;
  cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in Ha;
  unfold LIBX, LIBX0, A_malloc_impl, A_destructor_key, A_vdso_func, A_mem_inited, A_err_string_once, A_master_once_ret,
    A_defctx_inited, A_defctx_exlock, A_defctx_exmeth_bio, A_tevent_once, A_stopped, A_base_inited, A_base_once, A_optsdone,
    A_optsdone_lock, A_in_init_config_key, A_load_strings_once, A_td_tsd, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key,
    A_key_lock, A_tsd_main in *;
  cbn [rin_ivs fst snd]; lia.

Lemma ERR_fresh_agree : forall LBx m m', magree (c4_addr LBx) m m' -> ERR_fresh m -> ERR_fresh m'.
Proof.
  intros LBx m m' AG [(N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9) (K1 & K2 & K3)].
  unfold ERR_fresh, ERR_fresh_core, CTX_keys. split; [| split; [| split]].
  - repeat match goal with |- _ /\ _ => split end;
      (eapply none_on_agree; [exact AG| eassumption| in_libx| |]);
      unfold A_err_string_once, A_defctx_inited, A_tevent_once, A_load_strings_once, A_optsdone, A_td_tsd_used, A_keys, A_key_lock, A_tsd_main; lia.
  - eapply rw_cells_agree; [exact AG| exact K1| in_libx].
  - eapply rw_cells_agree; [exact AG| exact K2| in_libx].
  - eapply rw_cells_agree; [exact AG| exact K3| in_libx].
Qed.

Lemma C4W_agree : forall LBx m m' ph x, magree (c4_addr LBx) m m' -> C4W LBx m ph x -> C4W LBx m' ph x.
Proof.
  intros LBx m m' ph x AG ((fb & MF & MV) & IM & GM & RL & EP & CP).
  assert (AGL : magree (lib_addr LBx) m m') by (eapply magree_mono; [exact AG| intros a Ha; left; exact Ha]).
  split; [exists fb; split; [eapply rw_cells_agree; [exact AG| exact MF| in_libx]| exact MV]|].
  split; [unfold IMPL_mem in *; eapply rw_cells_agree; [exact AG| exact IM| in_libx]|].
  split.
  { unfold GOT_mem in *. eapply rw_cells_agree; [exact AG| exact GM|]. intros a Ha. right. unfold in_range in Ha.
    cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. unfold A_got_CRYPTO_malloc, RELRO_LO, RELRO_HI, RGOT_SSP in *. lia. }
  split.
  { intros a Ha NS. eapply none_agree; [exact AG| unfold RELRO_LO, RELRO_HI in Ha; lia| right; split; assumption| apply RL; assumption]. }
  split.
  - destruct ph as [|c]; cbn [ERRPH] in *; [eapply ERR_fresh_agree; eassumption|].
    destruct EP as [ES EC]. split; [eapply ERR_statics_frame; eassumption| eapply ERR_chain_frame; eassumption].
  - cbn [CTXPH] in *. destruct CP as [CS CB]. split; [eapply CTX_statics_frame; eassumption| eapply CTX_blocks_frame; eassumption].
Qed.

(* [comment removed for export] *)
Lemma c4_static_client : forall LB SP a,
  rin_ivs LIBX a \/ (RELRO_LO <= a < RELRO_HI /\ ~ (RGOT_SSP <= a < RGOT_SSP + 8)) -> rclient_addr LB SP a.
Proof.
  intros LB SP a HA. right; left. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK, RELRO_LO, RELRO_HI in *.
  destruct HA as [HX|HR]; [unfold LIBX, LIBX0 in HX; cbn [rin_ivs fst snd] in HX; lia| lia].
Qed.

Lemma C4W_xpres : forall LBx Lall SP m m' ph x,
  C4W LBx m ph x -> xpres Lall SP [] m m' -> (forall b, In b LBx -> In b Lall) -> C4W LBx m' ph x.
Proof.
  intros LBx Lall SP m m' ph x W XP SUB. eapply C4W_agree; [| exact W].
  intros a Ha HA. apply XP; [exact Ha|]. split; [| intros K; exact K].
  destruct HA as [[HX|(b & Hb & Hr)]|HR].
  - apply c4_static_client. left. exact HX.
  - right; right. exists b. split; [apply SUB; exact Hb| exact Hr].
  - apply c4_static_client. right. exact HR.
Qed.

(* [comment removed for export] *)
Lemma memflag_same : forall m m', MEMFLAG m 1 -> MEMFLAG m' 1 ->
  m' (wa A_mem_inited) = m (wa A_mem_inited) /\ (wview usegs m (wa A_mem_inited) <> None -> wview usegs m' (wa A_mem_inited) <> None).
Proof.
  intros m m' (fb & [[_ (_ & _ & B1)] _] & V1 & _) (fb' & [[_ (_ & _ & B2)] (_ & _ & W2)] & V2 & _).
  cbn [cells_bytes cbytes app length cells_size csize Nat.add] in *.
  specialize (B1 0%nat ltac:(lia)). specialize (B2 0%nat ltac:(lia)). cbn [nth_error Z.of_nat] in B1, B2.
  replace (A_mem_inited + 0) with A_mem_inited in B1, B2 by lia.
  assert (ROM : seg_rom usegs (wa A_mem_inited) = Some (b8 0)) by (vm_compute; reflexivity).
  assert (E : fb = fb') by (rewrite (byte_eq_of_unsigned fb 1 V1), (byte_eq_of_unsigned fb' 1 V2); reflexivity). subst fb'.
  unfold mrd in B1, B2. split.
  - destruct (m (wa A_mem_inited)) as [x1|] eqn:E1, (m' (wa A_mem_inited)) as [x2|] eqn:E2; try congruence;
      exfalso; rewrite ROM in *; assert (EF : fb = b8 0) by congruence; rewrite EF in V1; vm_compute in V1; discriminate.
  - intros _. specialize (W2 0 ltac:(lia)). replace (A_mem_inited + 0) with A_mem_inited in W2 by lia. exact W2.
Qed.

Lemma C4W_xpres_mf : forall LBx Lall SP m m' ph x,
  C4W LBx m ph x -> xpres Lall SP memflag_foot m m' -> MEMFLAG m' 1 -> (forall b, In b LBx -> In b Lall) -> C4W LBx m' ph x.
Proof.
  intros LBx Lall SP m m' ph x W XP MF' SUB. pose proof W as (MF & _). eapply C4W_agree; [| exact W].
  intros a Ha HA. destruct (Z.eq_dec a A_mem_inited) as [->|NE]; [apply memflag_same; assumption|].
  apply XP; [exact Ha|]. split; [| unfold memflag_foot; cbn; lia].
  destruct HA as [[HX|(b & Hb & Hr)]|HR].
  - apply c4_static_client. left. exact HX.
  - right; right. exists b. split; [apply SUB; exact Hb| exact Hr].
  - apply c4_static_client. right. exact HR.
Qed.

(* [comment removed for export] *)
Definition stack_or_errno (iv : Z * Z) : Prop := hceil <= fst iv \/ (RERRNO <= fst iv /\ snd iv <= RERRNO + 4).
Lemma C4W_stack : forall LBx W m m' ph x,
  C4W LBx m ph x -> munch W m m' -> wmono usegs m m' -> Forall stack_or_errno W ->
  (forall b, In b LBx -> rblock_range (blk_addr b) (blk_size b)) -> C4W LBx m' ph x.
Proof.
  intros LBx W m m' ph x CW MU WM FW HB. eapply C4W_agree; [| exact CW].
  eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha HA. hcb.
  assert (AB : a < hceil /\ ~ (RERRNO <= a < RERRNO + 4)).
  { unfold RERRNO. destruct HA as [[HX|(b & Hb & Hr)]|HR].
    - unfold LIBX, LIBX0 in HX; cbn [rin_ivs fst snd] in HX; lia.
    - pose proof (HB b Hb) as RB. unfold rblock_range in RB. lia.
    - unfold RELRO_LO, RELRO_HI in HR. lia. }
  clear - FW AB. induction W as [|[wl wh] W IH]; [exact I|]. cbn. split; [| apply IH; exact (Forall_inv_tail FW)].
  pose proof (Forall_inv FW) as K. unfold stack_or_errno in K. cbn in K. lia.
Qed.

(* [comment removed for export] *)
Lemma nodup_map_app_excl : forall {X Y} (f : X -> Y) l1 l2 b, List.NoDup (map f (l1 ++ l2)) -> In b l1 -> In b l2 -> False.
Proof.
  intros X Y f l1. induction l1 as [|y l1 IH]; cbn; intros l2 b ND I1 I2; [contradiction|].
  inversion ND as [|z l NI ND']; subst. destruct I1 as [->|I1]; [apply NI; apply in_map; apply in_or_app; right; exact I2| eapply IH; eauto].
Qed.
Lemma perm_keep : forall (Fr L' L : list block) b, Permutation.Permutation (Fr ++ L') L -> In b L -> ~ In b Fr -> In b L'.
Proof.
  intros Fr L' L b PM IB NF. apply Permutation.Permutation_sym in PM. pose proof (Permutation.Permutation_in _ PM IB) as K.
  apply in_app_or in K. destruct K as [K|K]; [contradiction| exact K].
Qed.
Lemma nodup_mid_excl : forall {X Y} (f : X -> Y) A Fr G C b, List.NoDup (map f (A ++ (Fr ++ G) ++ C)) -> In b Fr -> In b G -> False.
Proof.
  intros X Y f A Fr G C b ND IF IG. rewrite map_app in ND. apply NoDup_app_remove_l in ND. rewrite <- app_assoc in ND.
  eapply (nodup_map_app_excl f Fr (G ++ C) b); [exact ND| exact IF| apply in_or_app; left; exact IG].
Qed.
Lemma mod16_sub64 : forall x, x mod 16 = 0 -> (x + -64) mod 16 = 0.
Proof. intros x Hx. replace (x + -64) with (x + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hx. Qed.
Lemma mod16_sub32 : forall x, x mod 16 = 0 -> (x + -32) mod 16 = 0.
Proof. intros x Hx. replace (x + -32) with (x + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact Hx. Qed.

(* [comment removed for export] *)
Lemma disjoint_from_inside : forall W lo' hi' A n,
  Forall (fun iv : Z * Z => lo' <= fst iv /\ snd iv <= hi') W -> (A + n <= lo' \/ hi' <= A) -> disjoint_from W A n.
Proof.
  induction W as [|[wl wh] W IH]; intros lo' hi' A n FW HD; [exact I|]. cbn. split; [| eapply IH; [exact (Forall_inv_tail FW)| exact HD]].
  pose proof (Forall_inv FW) as K. cbn in K. lia.
Qed.

Section HH.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  (* [comment removed for export] *)
  Lemma blocks_apart_by_size : forall s L m b1 b2,
    hs_RHEAP H s L m -> In b1 L -> In b2 L -> blk_size b1 <> blk_size b2 ->
    blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
  Proof.
    intros s L m b1 b2 HP I1 I2 NE. eapply (HH_RHEAP_blocks_disjoint H HH); [exact HP| exact I1| exact I2|].
    intros E. apply NE. rewrite (nodup_id_inj L b1 b2 (HH_RHEAP_blocks_nodup H HH _ _ _ HP) I1 I2 E). reflexivity.
  Qed.

  Lemma chain_sep_of_RHEAP : forall s L m0 LBx m c,
    hs_RHEAP H s L m0 -> (forall b, In b LBx -> In b L) -> ERR_chain LBx m c -> chain_sep c.
  Proof.
    intros s L m0 LBx m c HP SUB (I2 & Z2 & _ & I3 & Z3 & _ & I4 & Z4 & _ & I5 & Z5 & _).
    unfold chain_sep. cbv zeta.
    pose proof (blocks_apart_by_size _ _ _ _ _ HP (SUB _ I2) (SUB _ I5) ltac:(rewrite Z2, Z5; unfold ERRST_SIZE; lia)) as D2.
    pose proof (blocks_apart_by_size _ _ _ _ _ HP (SUB _ I3) (SUB _ I5) ltac:(rewrite Z3, Z5; unfold ERRST_SIZE; lia)) as D3.
    pose proof (blocks_apart_by_size _ _ _ _ _ HP (SUB _ I4) (SUB _ I5) ltac:(rewrite Z4, Z5; unfold ERRST_SIZE; lia)) as D4.
    rewrite Z2, Z3, Z4, Z5 in *. lia.
  Qed.

  Lemma C4W_es : forall LBx L s m0 W m m' c x,
    C4W LBx m (ErrReady c) x -> hs_RHEAP H s L m0 -> (forall b, In b LBx -> In b L) ->
    munch W m m' -> wmono usegs m m' ->
    Forall (fun iv : Z * Z => blk_addr (ec_es c) <= fst iv /\ snd iv <= blk_addr (ec_es c) + ERRST_SIZE) W ->
    C4W LBx m' (ErrReady c) x.
  Proof.
    intros LBx L s m0 W m m' c x ((fb & MF & MV) & IM & GM & RL & [ES EC] & [CS [EX OL]]) HP SUB MU WM FW.
    pose proof EC as EC0. destruct EC as (I2 & Z2 & _ & I3 & Z3 & _ & I4 & Z4 & _ & I5 & Z5 & _).
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUB _ I5)) as RB. unfold rblock_range in RB. rewrite Z5 in RB. unfold ERRST_SIZE in *.
    assert (OFFI : forall A n, 65536 <= A -> A + n <= 3506176 -> disjoint_from W A n).
    { intros A n H1 H2. eapply disjoint_from_inside; [exact FW|]. lia. }
    assert (FX : Forall off_libx W).
    { clear - FW RB. induction W as [|[wl wh] W IH]; [constructor|]. constructor; [| apply IH; exact (Forall_inv_tail FW)].
      pose proof (Forall_inv FW) as K. cbn in K. unfold off_libx, IMG_LO, IMG_HI. cbn [fst snd]. lia. }
    pose proof (chain_sep_of_RHEAP _ _ _ _ _ _ HP SUB EC0) as CSEP.
    assert (CBL : chain_below c hceil).
    { unfold chain_below. destruct EC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I6 & Z6 & RR).
      pose proof (Forall_inv RR) as R2. pose proof (Forall_inv (Forall_inv_tail RR)) as R3.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RR))) as R4.
      unfold rblock_range in R2, R3, R4. rewrite Z2 in R2. rewrite Z3 in R3. rewrite Z4 in R4. unfold ERRST_SIZE. lia. }
    split; [exists fb; split; [eapply rw_cells_transport; [exact MF| exact MU| exact WM| apply OFFI; unfold A_mem_inited; cbn; lia]| exact MV]|].
    split; [unfold IMPL_mem in *; eapply rw_cells_transport; [exact IM| exact MU| exact WM| apply OFFI; unfold A_malloc_impl; cbn; lia]|].
    split; [unfold GOT_mem in *; eapply rw_cells_transport; [exact GM| exact MU| exact WM| apply OFFI; unfold A_got_CRYPTO_malloc; cbn; lia]|].
    split.
    { intros a Ha NS. unfold wa. rewrite MU; [apply RL; assumption|]. rewrite unsigned_lit by (unfold RELRO_LO, RELRO_HI in Ha; lia).
      eapply disjoint_outside; [apply (OFFI a 1); unfold RELRO_LO, RELRO_HI in Ha; lia| lia]. }
    split.
    - split; [eapply ERR_statics_munch; eassumption|].
      eapply ERR_chain_munch; [exact EC0| exact CBL| exact MU| exact WM|].
      clear - FW CSEP. induction W as [|[wl wh] W IH]; [constructor|]. constructor; [| apply IH; exact (Forall_inv_tail FW)].
      pose proof (Forall_inv FW) as K. cbn in K. unfold chain_free. cbn [fst snd]. right; right. split; [exact CSEP| exact K].
    - split; [eapply CTX_statics_munch; eassumption|]. split; [| exact OL].
      pose proof EX as (XI & XZ & _ & _).
      pose proof (blocks_apart_by_size _ _ _ _ _ HP (SUB _ XI) (SUB _ I5) ltac:(rewrite XZ, Z5; unfold MUTEX_SIZE, ERRST_SIZE; lia)) as DX.
      rewrite XZ, Z5 in DX. unfold MUTEX_SIZE, ERRST_SIZE in DX.
      eapply EXLOCK_munch; [exact EX| exact MU| exact WM|]. eapply disjoint_from_inside; [exact FW|]. lia.
  Qed.
  (* [comment removed for export] *)
  Definition heapw (c : errchain) (lo spx : Z) (b0 : block) (iv : Z * Z) : Prop :=
       (lo <= fst iv /\ snd iv <= spx)
    \/ (blk_addr (ec_es c) <= fst iv /\ snd iv <= blk_addr (ec_es c) + ERRST_SIZE)
    \/ (blk_addr b0 <= fst iv /\ snd iv <= blk_addr b0 + blk_size b0).

  Lemma C4W_heapw : forall LBx L s m0 W m m' c x lo spx b0,
    C4W LBx m (ErrReady c) x -> hs_RHEAP H s L m0 -> (forall b, In b LBx -> In b L) ->
    In b0 L -> ~ In b0 LBx -> hceil <= lo ->
    munch W m m' -> wmono usegs m m' -> Forall (heapw c lo spx b0) W ->
    C4W LBx m' (ErrReady c) x.
  Proof.
    intros LBx L s m0 W m m' c x lo spx b0 ((fb & MF & MV) & IM & GM & RL & [ES EC] & [CS [EX OL]]) HP SUB IB0 NB0 CEIL MU WM FW. hcb.
    pose proof EC as EC0. destruct EC as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUB _ I5)) as RB5. unfold rblock_range in RB5. rewrite Z5 in RB5.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP IB0) as RB0. unfold rblock_range in RB0. unfold ERRST_SIZE in *.
    (* [comment removed for export] *)
    assert (APART : forall d, In d LBx -> blk_size d <> 904 -> 0 <= blk_size d -> blk_addr d + blk_size d <= hceil ->
                    forall A n, blk_addr d <= A -> A + n <= blk_addr d + blk_size d -> disjoint_from W A n).
    { intros d Hd SZ SZ0 DH A n HA1 HA2.
      pose proof (blocks_apart_by_size _ _ _ _ _ HP (SUB _ Hd) (SUB _ I5) ltac:(rewrite Z5; exact SZ)) as D5. rewrite Z5 in D5.
      assert (D0 : blk_addr d + blk_size d <= blk_addr b0 \/ blk_addr b0 + blk_size b0 <= blk_addr d).
      { eapply (HH_RHEAP_blocks_disjoint H HH); [exact HP| apply SUB; exact Hd| exact IB0|]. intros EQ. apply NB0.
        rewrite <- (nodup_id_inj L d b0 (HH_RHEAP_blocks_nodup H HH _ _ _ HP) (SUB _ Hd) IB0 EQ). exact Hd. }
      clear - FW D5 D0 HA1 HA2 CEIL DH. induction W as [|[wl wh] W IH]; [exact I|]. cbn. split; [| apply IH; exact (Forall_inv_tail FW)].
      pose proof (Forall_inv FW) as K. unfold heapw, ERRST_SIZE in K. cbn [fst snd] in K. lia. }
    assert (OFFI : forall A n, 65536 <= A -> A + n <= 3506176 -> disjoint_from W A n).
    { intros A n H1 H2. clear - FW RB5 RB0 H1 H2 CEIL HCEILB. induction W as [|[wl wh] W IH]; [exact I|]. cbn. split; [| apply IH; exact (Forall_inv_tail FW)].
      pose proof (Forall_inv FW) as K. unfold heapw, ERRST_SIZE in K. cbn [fst snd] in K. lia. }
    assert (FX : Forall off_libx W).
    { clear - FW RB5 RB0 CEIL HCEILB. induction W as [|[wl wh] W IH]; [constructor|]. constructor; [| apply IH; exact (Forall_inv_tail FW)].
      pose proof (Forall_inv FW) as K. unfold heapw, ERRST_SIZE in K. cbn [fst snd] in K. unfold off_libx, IMG_LO, IMG_HI. cbn [fst snd]. lia. }
    pose proof (Forall_inv RR) as R2. pose proof (Forall_inv (Forall_inv_tail RR)) as R3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RR))) as R4. unfold rblock_range in R2, R3, R4.
    split; [exists fb; split; [eapply rw_cells_transport; [exact MF| exact MU| exact WM| apply OFFI; unfold A_mem_inited; cbn; lia]| exact MV]|].
    split; [unfold IMPL_mem in *; eapply rw_cells_transport; [exact IM| exact MU| exact WM| apply OFFI; unfold A_malloc_impl; cbn; lia]|].
    split; [unfold GOT_mem in *; eapply rw_cells_transport; [exact GM| exact MU| exact WM| apply OFFI; unfold A_got_CRYPTO_malloc; cbn; lia]|].
    split.
    { intros a Ha NS. unfold wa. rewrite MU; [apply RL; assumption|]. rewrite unsigned_lit by (unfold RELRO_LO, RELRO_HI in Ha; lia).
      eapply disjoint_outside; [apply (OFFI a 1); unfold RELRO_LO, RELRO_HI in Ha; lia| lia]. }
    split.
    - split; [eapply ERR_statics_munch; eassumption|].
      unfold ERR_chain, sa_cells. repeat match goal with |- _ /\ _ => split end; try assumption.
      + eapply rw_cells_transport; [exact K2| exact MU| exact WM|]. apply (APART _ I2); unfold O_MKEY_ERR; cbn; lia.
      + eapply rw_cells_transport; [exact K3| exact MU| exact WM|]. apply (APART _ I3); cbn; lia.
      + eapply rw_cells_transport; [exact K4| exact MU| exact WM|]. apply (APART _ I4); cbn; lia.
    - split; [eapply CTX_statics_munch; eassumption|]. split; [| exact OL].
      pose proof EX as (XI & XZ & XR & _). unfold rblock_range, MUTEX_SIZE in *.
      eapply EXLOCK_munch; [exact EX| exact MU| exact WM|]. apply (APART _ XI); lia.
  Qed.
  (* [comment removed for export] *)
  Lemma heapw_world : forall s L LBx m m' c x lo spx B (errv : word) b0 W,
    hs_RHEAP H s L m -> (forall b, In b LBx -> In b L) -> In b0 L -> ~ In b0 LBx -> C4W LBx m (ErrReady c) x ->
    hs_rauxv_ok H m B -> rw_cells usegs m RERRNO [C4 errv] ->
    hceil <= lo -> lo <= spx -> spx <= B ->
    munch W m m' -> wmono usegs m m' -> Forall (heapw c lo spx b0) W ->
    hs_RHEAP H s L m' /\ C4W LBx m' (ErrReady c) x /\ hs_rauxv_ok H m' B /\ rw_cells usegs m' RERRNO [C4 errv]
    /\ (forall A cs, rw_cells usegs m A cs -> spx <= A -> rw_cells usegs m' A cs).
  Proof.
    intros s L LBx m m' c x lo spx B errv b0 W HP SUB IB0 NB0 CW AUX ERR CEIL LS SB MU WM FW. hcb.
    pose proof CW as (_ & _ & _ & _ & [_ EC] & _). destruct EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUB _ I5)) as RB5. unfold rblock_range in RB5. rewrite Z5 in RB5.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP IB0) as RB0. unfold rblock_range in RB0. unfold ERRST_SIZE in *.
    split.
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU| exact WM|].
      clear - FW CEIL I5 Z5 SUB IB0. induction W as [|[wl wh] W IH]; [constructor|]. constructor; [| apply IH; exact (Forall_inv_tail FW)].
      pose proof (Forall_inv FW) as K. unfold heapw, ERRST_SIZE in K. cbn [fst snd] in K. destruct K as [K|[K|K]].
      - left. cbn. lia.
      - right; right. exists (ec_es c). split; [apply SUB; exact I5|]. rewrite Z5. unfold ERRST_SIZE. cbn. lia.
      - right; right. exists b0. split; [exact IB0|]. cbn. lia. }
    split; [eapply C4W_heapw; eassumption|].
    split.
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL.
      clear - FW CEIL LS SB RB5 RB0 HCEILB. induction W as [|[wl wh] W IH]; [constructor|]. constructor; [| apply IH; exact (Forall_inv_tail FW)].
      pose proof (Forall_inv FW) as K. unfold heapw, ERRST_SIZE in K. cbn [fst snd] in K |- *. lia. }
    split.
    { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. unfold RERRNO.
      clear - FW CEIL RB5 RB0 HCEILB. induction W as [|[wl wh] W IH]; [exact I|]. cbn. split; [| apply IH; exact (Forall_inv_tail FW)].
      pose proof (Forall_inv FW) as K. unfold heapw, ERRST_SIZE in K. cbn [fst snd] in K. lia. }
    intros A cs FR SA. pose proof (rw_cells_bound _ _ _ _ FR) as FB.
    eapply rw_cells_transport; [exact FR| exact MU| exact WM|].
    clear - FW CEIL LS SA RB5 RB0 FB. induction W as [|[wl wh] W IH]; [exact I|]. cbn. split; [| apply IH; exact (Forall_inv_tail FW)].
    pose proof (Forall_inv FW) as K. unfold heapw, ERRST_SIZE in K. cbn [fst snd] in K. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_heapw : forall s L LBx m0 m m' c lo spx SP X b0 W,
    hs_RHEAP H s L m0 -> (forall b, In b LBx -> In b L) -> In b0 L -> ~ In b0 LBx ->
    hceil <= lo -> spx <= SP -> hceil <= SP ->
    (forall a, blk_addr (ec_es c) <= a < blk_addr (ec_es c) + ERRST_SIZE -> rin_ivs X a) ->
    munch W m m' -> wmono usegs m m' -> Forall (heapw c lo spx b0) W ->
    xpres LBx SP X m m'.
  Proof.
    intros s L LBx m0 m m' c lo spx SP X b0 W HP SUB IB0 NB0 CEIL SS HSP XE MU WM FW. hcb.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP IB0) as RB0. unfold rblock_range in RB0.
    eapply xpres_of_munch_gen; [exact MU| exact WM|]. intros a Ha [HC HXn].
    clear MU WM. induction W as [|[wl wh] W IH]; [exact I|]. cbn. split; [| apply IH; exact (Forall_inv_tail FW)].
    pose proof (Forall_inv FW) as K. unfold heapw in K. cbn [fst snd] in K. intros Hr.
    destruct K as [K|[K|K]].
    - destruct HC as [HC|[[HC _]|(b & Hb & Hrb)]]; [lia| lia|].
      pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUB _ Hb)) as RB. unfold rblock_range in RB. lia.
    - apply HXn. apply XE. lia.
    - destruct HC as [HC|[[HC _]|(b & Hb & Hrb)]]; [lia| lia|].
      assert (NE : blk_id b <> blk_id b0).
      { intros EQ. apply NB0. rewrite <- (nodup_id_inj L b b0 (HH_RHEAP_blocks_nodup H HH _ _ _ HP) (SUB _ Hb) IB0 EQ). exact Hb. }
      pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP (SUB _ Hb) IB0 NE) as DJ. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma es_world : forall s L LBx m m' c x lo spx B (errv : word) A cs,
    hs_RHEAP H s L m -> (forall b, In b LBx -> In b L) -> C4W LBx m (ErrReady c) x ->
    hs_rauxv_ok H m B -> rw_cells usegs m RERRNO [C4 errv] -> stk usegs m lo spx -> rw_cells usegs m A cs ->
    hceil <= lo -> lo <= A -> lo <= B ->
    munch [(blk_addr (ec_es c), blk_addr (ec_es c) + 904)] m m' -> wmono usegs m m' ->
    hs_RHEAP H s L m' /\ C4W LBx m' (ErrReady c) x /\ hs_rauxv_ok H m' B /\ rw_cells usegs m' RERRNO [C4 errv]
    /\ stk usegs m' lo spx /\ rw_cells usegs m' A cs.
  Proof.
    intros s L LBx m m' c x lo spx B errv A cs HP SUB CW AUX ERR ST FR CEIL LA LB0 MU WM. hcb.
    pose proof CW as (_ & _ & _ & _ & [_ EC] & _). cbn [ERRPH] in EC. destruct EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUB _ I5)) as RB5. unfold rblock_range in RB5. rewrite Z5 in RB5. unfold ERRST_SIZE in RB5.
    split. { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil].
             right; right. exists (ec_es c). split; [apply SUB; exact I5|]. rewrite Z5. unfold ERRST_SIZE. cbn. lia. }
    split. { eapply C4W_es; [exact CW| exact HP| exact SUB| exact MU| exact WM|]. apply Forall_cons; [unfold ERRST_SIZE; cbn; lia| apply Forall_nil]. }
    split. { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. unfold RERRNO. cbn. lia. }
    split. { eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. cbn. lia. }
    pose proof (rw_cells_bound _ _ _ _ FR) as FB. eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn. lia.
  Qed.

End HH.

  (* [comment removed for export] *)
Lemma free_world : forall LBx L' m m' c x spx A cs E,
  C4W LBx m (ErrReady c) x -> xpres L' spx [] m m' -> (forall b, In b LBx -> In b L') ->
  rw_cells usegs m A cs -> spx <= A -> ERRSTm m (blk_addr (ec_es c)) E -> 0 <= blk_addr (ec_es c) -> blk_addr (ec_es c) + ERRST_SIZE <= 2^64 ->
  C4W LBx m' (ErrReady c) x /\ rw_cells usegs m' A cs /\ ERRSTm m' (blk_addr (ec_es c)) E.
Proof.
  intros LBx L' m m' c x spx A cs E CW XP SUB FR SA EM E0 E1.
  pose proof CW as (_ & _ & _ & _ & [_ EC] & _). cbn [ERRPH] in EC. destruct EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
  split; [eapply C4W_xpres; eassumption|].
  split; [eapply xpres_rw_cells'; [exact XP| exact FR| left; lia| constructor]|].
  eapply ERRSTm_xpres; [exact EM| exact XP| | exact E0| exact E1].
  intros a Ha. split; [| intros K; exact K]. right; right. exists (ec_es c). split; [apply SUB; exact I5| rewrite Z5; exact Ha].
Qed.

End HCW.

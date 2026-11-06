(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val Mem State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Ops Seal SealX.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp UO.
Open Scope Z_scope.
Unset Lia Cache.

Module UOT.
Section WithSegs.
Variable segs : list Segment.
Variable XW : client_world.

Local Abbreviation cwh := (cw_unp_holds segs XW).

Lemma chunk_al8 : forall g c, pure_ok g -> In c (z_chunks (u_zone g)) -> fst c mod 8 = 0.
Proof.
  intros g c (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ZV) Hc. destruct ZV as (_ & _ & V3 & _).
  destruct (V3 c Hc) as (_ & A16 & _). rewrite (Z.div_mod (fst c) 16) by lia. rewrite A16.
  replace (16 * (fst c / 16) + 0) with ((2 * (fst c / 16)) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Lemma owned_not_kblock : forall md g ws b n, pure_ok g -> wins_ok md g ws -> In (Win b n K_BLOCK) ws -> 0 < n ->
  forall ob, In ob (owned g) -> fst ob <> b.
Proof.
  intros md g ws b n P Wk Hin POS ob Hob E.
  pose proof (owned_pos g P ob Hob) as PO.
  destruct (proj1 (Forall_forall _ _) Wk _ Hin ltac:(cbn [w_kind]; unfold K_BLOCK, K_STACK; lia)) as [[_ D]|[NB _]].
  - apply (D ob Hob b); unfold in_iv, w_iv; cbn [fst snd w_lo w_len]; lia.
  - apply NB. reflexivity.
Qed.

Hypothesis XW_twin_grow : forall md ca LB ws m b0 n0 n, cw_holds XW md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (Seal.shadZ b0, n) a -> ~ in_user LB a) ->
  cw_holds XW md ca ((Seal.shadZ b0, n) :: LB) (ws ++ [Win (Seal.shadZ b0) n Seal.K_TWIN]) m.

Lemma cw_unp_twin_grow : forall md ca LB ws m b0 n0 n, cwh md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (Seal.shadZ b0, n) a -> ~ in_user LB a) ->
  cwh md ca ((Seal.shadZ b0, n) :: LB) (ws ++ [Win (Seal.shadZ b0) n Seal.K_TWIN]) m.
Proof.
  intros md ca LB ws m b0 n0 n H Hin POS AL FR. unfold cw_unp_holds in *.
  destruct (md =? CM_NONE); [apply Forall_app; split; [exact H| constructor; [unfold no_sub; cbn [w_kind]; unfold K_SUB, Seal.K_TWIN, K_GHOST; lia| constructor]]|].
  destruct ((md =? CM_UNP) || (md =? CM_CONS)); [| exact (XW_twin_grow md ca LB ws m b0 n0 n H Hin POS AL FR)].
  destruct (decode_uc ca) as [u|]; [|exact H].
  assert (NP : forall w, In w (ws ++ [Win (Seal.shadZ b0) n Seal.K_TWIN]) -> pot_win w -> In w ws).
  { apply pot_app_heap. intros w [<-|[]]. cbn [w_kind]. unfold Seal.K_TWIN, K_STACK. lia. }
  destruct H as (g & L & P & O & Wk & M & CS & AX & SE). exists g.
  split; [exact L|]. split; [exact P|]. split; [apply own_ok_grow; exact O|].
  split; [| split; [exact M| split; [exact (cons_ok_ws _ _ _ _ _ _ CS NP)| split; [exact (acct_pot_ws _ _ _ _ _ AX NP)|]]]].
  -
    destruct O as [O1 _]. unfold wins_ok in *. apply Forall_app. split; [exact Wk|]. constructor; [|constructor].
    intros _. left. split; [right; cbn [w_kind]; unfold K_GHOST, Seal.K_TWIN; lia|].
    intros ob Hob a Ha Hb. apply (FR a Ha). unfold in_user. apply in_ivs_In. exists ob. split; [exact (O1 ob Hob)| exact Hb].
  - apply SealX.seal_ok_twin_window; [exact SE| exact AL|]. intros c Hc. split; [exact (chunk_al8 g c P Hc)|].
    exact (owned_not_kblock md g ws b0 n0 P Wk Hin POS (chunk_block c) (owned_chunk g c Hc)).
Qed.

Lemma cw_unp_grow_twin : forall md ca LB ws m b n, cwh md ca LB ws m ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) -> b mod 8 = 0 -> 0 < n ->
  (forall a, in_iv (Seal.shadZ b, (n + 7) / 8) a -> ~ in_user ((b, n) :: LB) a) ->
  cwh md ca ((Seal.shadZ b, (n + 7) / 8) :: (b, n) :: LB) ((ws ++ [Win b n K_BLOCK]) ++ [Win (Seal.shadZ b) ((n + 7) / 8) Seal.K_TWIN]) m.
Proof.
  intros md ca LB ws m b n H FR AL POS FR2.
  apply (cw_unp_twin_grow md ca ((b, n) :: LB) (ws ++ [Win b n K_BLOCK]) m b n ((n + 7) / 8)); [| | exact POS| exact AL| exact FR2].
  - exact (cw_unp_grow segs XW md ca LB ws m b n H FR).
  - apply in_or_app. right. left. reflexivity.
Qed.

Hypothesis XW_ghost_grow : forall md ca LB ws m b n kd, cw_holds XW md ca LB ws m -> 7 <= kd -> kd <> Seal.K_TWIN ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) -> cw_holds XW md ca ((b, n) :: LB) (ws ++ [Win b n kd]) m.

Lemma cw_unp_ghost_grow : forall md ca LB ws m b n kd, cwh md ca LB ws m -> 7 <= kd -> kd <> Seal.K_TWIN ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) -> cwh md ca ((b, n) :: LB) (ws ++ [Win b n kd]) m.
Proof.
  intros md ca LB ws m b n kd H K7 NT FR. unfold cw_unp_holds in *.
  destruct (md =? CM_NONE); [apply Forall_app; split; [exact H| constructor; [unfold no_sub; cbn [w_kind]; unfold K_SUB, K_GHOST; lia| constructor]]|].
  destruct ((md =? CM_UNP) || (md =? CM_CONS)); [| exact (XW_ghost_grow md ca LB ws m b n kd H K7 NT FR)].
  destruct (decode_uc ca) as [u|]; [|exact H].
  assert (NP : forall w, In w (ws ++ [Win b n kd]) -> pot_win w -> In w ws).
  { apply pot_app_heap. intros w [<-|[]]. cbn [w_kind]. unfold K_STACK. lia. }
  destruct H as (g & L & P & O & Wk & M & CS & AX & SE). exists g.
  split; [exact L|]. split; [exact P|]. split; [apply own_ok_grow; exact O|].
  split; [| split; [exact M| split; [exact (cons_ok_ws _ _ _ _ _ _ CS NP)| split; [exact (acct_pot_ws _ _ _ _ _ AX NP)|]]]].
  - destruct O as [O1 _]. unfold wins_ok in *. apply Forall_app. split; [exact Wk|]. constructor; [|constructor].
    intros _. left. split; [right; cbn [w_kind]; unfold K_GHOST; lia|].
    intros ob Hob a Ha Hb. apply (FR a Ha). unfold in_user. apply in_ivs_In. exists ob. split; [exact (O1 ob Hob)| exact Hb].
  - apply SealX.seal_ok_app_other; [exact SE|]. intros w [<-|[]]. cbn [w_kind]. exact NT.
Qed.

Hypothesis XW_ghost_free : forall md ca LB ws m b n kd ws', cw_holds XW md ca LB ws m -> 7 <= kd -> In (Win b n kd) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n kd) -> cw_holds XW md ca (remove iv_eq_dec (b, n) LB) ws' m.

Lemma cw_unp_ghost_free : forall md ca LB ws m b n kd ws', cwh md ca LB ws m -> 7 <= kd -> In (Win b n kd) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n kd) -> cwh md ca (remove iv_eq_dec (b, n) LB) ws' m.
Proof.
  intros md ca LB ws m b n kd ws' H K7 Hin Hws'. unfold cw_unp_holds in *.
  destruct (md =? CM_NONE); [apply Forall_forall; intros w Hw; apply Hws' in Hw as [Hw _]; exact (proj1 (Forall_forall _ _) H w Hw)|].
  destruct ((md =? CM_UNP) || (md =? CM_CONS)); [| exact (XW_ghost_free md ca LB ws m b n kd ws' H K7 Hin Hws')].
  destruct (decode_uc ca) as [u|]; [|exact H].
  assert (NP : forall w, In w ws' -> pot_win w -> In w ws) by (intros w Hw _; apply Hws' in Hw as [Hw _]; exact Hw).
  destruct H as (g & L & P & O & Wk & M & CS & AX & SE). exists g.
  split; [exact L|]. split; [exact P|]. split; [| split; [| split; [exact M| split; [exact (cons_ok_ws _ _ _ _ _ _ CS NP)| split; [exact (acct_pot_ws _ _ _ _ _ AX NP)|]]]]].
  -
    destruct O as [O1 O2]. split; [| exact O2]. intros x Hx. apply in_in_remove; [| exact (O1 x Hx)]. intros E. subst x.
    pose proof (owned_pos g P _ Hx) as POS. cbn [snd] in POS.
    destruct (proj1 (Forall_forall _ _) Wk _ Hin ltac:(cbn [w_kind]; unfold K_STACK; lia)) as [[_ D]|[_ SO]].
    + apply (D (b, n) Hx b); unfold in_iv, w_iv; cbn [fst snd w_lo w_len]; lia.
    + unfold sub_ok in SO. cbn [w_kind] in SO. unfold K_CTOP, K_VTOP, K_SLOT, K_ZONE in SO.
      destruct SO as [(K & _)|[(K & _)|[(K & _)|(K & _)]]]; lia.
  - unfold wins_ok in *. apply Forall_forall. intros w Hw. apply Hws' in Hw as [Hw _]. exact (proj1 (Forall_forall _ _) Wk w Hw).
  - apply (Seal.seal_ok_ws ws _ ws' SE). intros w Hw _. apply Hws' in Hw as [Hw _]. exact Hw.
Qed.
Lemma cw_unp_twin_free : forall md ca LB ws m b n ws', cwh md ca LB ws m -> In (Win b n Seal.K_TWIN) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n Seal.K_TWIN) -> cwh md ca (remove iv_eq_dec (b, n) LB) ws' m.
Proof. intros md ca LB ws m b n ws' H. apply (cw_unp_ghost_free md ca LB ws m b n Seal.K_TWIN ws' H). unfold Seal.K_TWIN. lia. Qed.

Lemma cw_unp_vec_unowned : forall md ca LB ws m i a, cwh md ca LB ws m -> (md = CM_UNP \/ md = CM_CONS) -> (i = 1 \/ i = 4)%nat ->
  nth_error ca i = Some a -> forall w, In w ws -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned a.
Proof.
  intros md ca LB ws m i a H MD I NA w Hw K POS. unfold cw_unp_holds in H.
  assert (M0 : (md =? CM_NONE) = false) by (apply Z.eqb_neq; unfold CM_NONE, CM_UNP, CM_CONS in *; lia). rewrite M0 in H.
  assert (M1 : ((md =? CM_UNP) || (md =? CM_CONS)) = true) by (apply orb_true_iff; destruct MD as [->| ->]; [left| right]; apply Z.eqb_refl). rewrite M1 in H.
  destruct (decode_uc ca) as [u|] eqn:DU; [| contradiction].
  destruct H as (g & L & P & O & Wk & _).
  destruct w as [b n k]. cbn [w_kind w_len w_lo] in *. subst k.
  unfold decode_uc in DU.
  destruct ca as [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 [|a7 [|a8 [|a9 [|a10 [|a11 [|a12 [|a13 [|a14 [|a15 [|zh [|? ?]]]]]]]]]]]]]]]]]]; try discriminate DU.
  injection DU as <-. destruct L as (_ & LCB & _ & _ & LVB & _). cbn [c_cb c_vb] in LCB, LVB.
  destruct I as [-> | ->]; cbn [nth_error] in NA; injection NA as <-.
  - rewrite <- LCB. intros E. exact (owned_not_kblock md g ws b n P Wk Hw POS (cstk_block g) (or_introl eq_refl) (eq_sym E)).
  - rewrite <- LVB. intros E. exact (owned_not_kblock md g ws b n P Wk Hw POS (vstk_block g) (or_intror (or_introl eq_refl)) (eq_sym E)).
Qed.

Lemma pow2_not_c24 : forall k, 0 <= k -> ~ (5881 <= 256 * 2 ^ k <= 7936).
Proof.
  intros k Hk [L U]. destruct (Z.le_gt_cases k 4) as [K4|K5].
  - assert (2 ^ k <= 2 ^ 4) by (apply Z.pow_le_mono_r; lia). change (2 ^ 4) with 16 in *. lia.
  - assert (2 ^ 5 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). change (2 ^ 5) with 32 in *. lia.
Qed.
Lemma cap32_bytes : forall c, cap32_b c = true -> exists k, 0 <= k /\ 8 * c = 256 * 2 ^ k.
Proof.
  intros c H. unfold cap32_b in H. apply andb_prop in H as [H P2]. apply andb_prop in H as [_ M]. apply Z.eqb_eq in M.
  apply pow2_b_spec in P2 as (k & Hk & E). exists k. split; [lia|].
  unfold EMBED_STACK in *. rewrite (Z.div_mod c 32) by lia. rewrite M, E. lia.
Qed.
Lemma unp_owned_not_c24 : forall g, pure_ok g -> forall ob, In ob (owned g) -> ~ (5881 <= snd ob <= 7936).
Proof.
  intros g (VC & EC & SC & CC & VV & EV & SV & CV & LV & DL & LA & ZV) ob Hob.
  unfold owned in Hob. cbn [In] in Hob. destruct Hob as [<-|[<-|Hob]].
  - cbn [snd cstk_block]. unfold v_bytes. rewrite EC. destruct (cap32_bytes _ CC) as (k & Hk & ->). exact (pow2_not_c24 k Hk).
  - cbn [snd vstk_block]. unfold v_bytes. rewrite EV. destruct (cap32_bytes _ CV) as (k & Hk & ->). exact (pow2_not_c24 k Hk).
  - apply in_map_iff in Hob as (c & <- & Hc). cbn [snd chunk_block].
    destruct ZV as (_ & _ & V3 & _). destruct (V3 c Hc) as (_ & _ & S). unfold CHUNK_HDR, CHUNK_SIZE0 in *. lia.
Qed.

Definition unp_cgl_sec : client_ghost_laws (unp_cw segs XW) Seal.shadZ Seal.K_TWIN :=
  CGL (unp_cw segs XW) Seal.shadZ Seal.K_TWIN cw_unp_twin_grow cw_unp_ghost_grow cw_unp_ghost_free.

End WithSegs.

Definition unp_cgl (segs : list Segment) (XW : client_world) (X : client_ghost_laws XW Seal.shadZ Seal.K_TWIN)
  : client_ghost_laws (unp_cw segs XW) Seal.shadZ Seal.K_TWIN :=
  unp_cgl_sec segs XW (cg_twin_grow _ _ _ X) (cg_ghost_grow _ _ _ X) (cg_ghost_free _ _ _ X).

End UOT.

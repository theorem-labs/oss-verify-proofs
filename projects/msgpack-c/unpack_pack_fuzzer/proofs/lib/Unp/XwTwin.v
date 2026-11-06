(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem State MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv OpsBridge Seal SealX TdOps PkOps ClientX.
Import ListNotations.
Import W64 Val Mem St MemP HeapOp UB.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module XWT.

Lemma al16_al8 : forall a, a mod 16 = 0 -> a mod 8 = 0.
Proof. intros a A. apply Z.mod_divide in A; [|lia]. destruct A as [q Hq]. apply Z.mod_divide; [lia|]. exists (2 * q). lia. Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma pk_grow_gen : forall ca LB ws m b n kd, PK.cw_pk_holds segs ca LB ws m -> kd = K_BLOCK \/ K_GHOST <= kd ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) ->
  (forall g ls, PK.pure_pk g ls -> PK.wins_pk g ws -> Seal.seal_ok ws (z_chunks (PK.k_zone g)) ->
                Seal.seal_ok (ws ++ [Win b n kd]) (z_chunks (PK.k_zone g))) ->
  PK.cw_pk_holds segs ca ((b, n) :: LB) (ws ++ [Win b n kd]) m.
Proof.
  intros ca LB ws m b n kd H KDk FR HSEAL. unfold PK.cw_pk_holds in *. destruct (PK.decode_pk ca) as [u|]; [|exact H].
  destruct H as (g & ls & L & P & O & Wk & M & [SE EP] & CO). exists g, ls.
  split; [exact L|]. split; [exact P|]. split; [apply PK.own_pk_grow; exact O|]. split; [| split; [exact M| split; [split|]]].
  4: { apply PK.cost_pk_app; [exact CO|]. constructor; [|constructor]. left. cbn [w_kind]. destruct KDk as [->|K7]; [unfold K_BLOCK; lia| unfold K_GHOST in K7; lia]. }
  - unfold PK.wins_pk in *. apply Forall_app. split; [exact Wk|]. constructor; [|constructor].
    intros _. left. split; [exact KDk|]. intros ob Hob a Ha Hb. apply (FR a Ha). unfold in_user. apply in_ivs_In. exists ob. split; [exact (proj1 O ob Hob)| exact Hb].
  - exact (HSEAL g ls P Wk SE).
  - intros VB. destruct (EP VB) as (w & Hw & EW). exists w. split; [apply in_app_iff; left; exact Hw| exact EW].
Qed.

Lemma pk_twin_grow : forall ca LB ws m b0 n0 n, PK.cw_pk_holds segs ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (Seal.shadZ b0, n) a -> ~ in_user LB a) ->
  PK.cw_pk_holds segs ca ((Seal.shadZ b0, n) :: LB) (ws ++ [Win (Seal.shadZ b0) n Seal.K_TWIN]) m.
Proof.
  intros ca LB ws m b0 n0 n H HB N0 A8 FR. apply (pk_grow_gen ca LB ws m (Seal.shadZ b0) n Seal.K_TWIN H ltac:(right; unfold Seal.K_TWIN, K_GHOST; lia) FR).
  intros g ls P Wk SE. apply SealX.seal_ok_twin_window; [exact SE| exact A8|].
  intros c Hc. destruct P as (_ & _ & _ & _ & _ & ((_ & _ & V3 & _) & _)). destruct (V3 c Hc) as (_ & A16 & S0).
  split; [exact (al16_al8 _ A16)|]. intros E.
  assert (OWc : In (chunk_block c) (PK.owned g)) by (unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc).
  destruct (proj1 (Forall_forall _ _) Wk _ HB ltac:(cbn [w_kind]; unfold K_BLOCK, K_STACK; lia)) as [[_ D]|[NB _]]; [| apply NB; reflexivity].
  apply (D (chunk_block c) OWc b0); unfold in_iv, w_iv, chunk_block; cbn [fst snd w_lo w_len]; unfold CHUNK_HDR, CHUNK_SIZE0 in *; lia.
Qed.

Lemma pk_ghost_grow : forall ca LB ws m b n kd, PK.cw_pk_holds segs ca LB ws m -> 7 <= kd -> kd <> Seal.K_TWIN ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) -> PK.cw_pk_holds segs ca ((b, n) :: LB) (ws ++ [Win b n kd]) m.
Proof.
  intros ca LB ws m b n kd H K7 K9 FR. apply (pk_grow_gen ca LB ws m b n kd H ltac:(right; unfold K_GHOST; lia) FR).
  intros g ls _ _ SE. apply SealX.seal_ok_app_other; [exact SE|]. intros w [<-|[]]. exact K9.
Qed.

Lemma pk_ghost_free : forall ca LB ws m b n kd ws', PK.cw_pk_holds segs ca LB ws m -> 7 <= kd -> In (Win b n kd) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n kd) -> PK.cw_pk_holds segs ca (remove iv_eq_dec (b, n) LB) ws' m.
Proof.
  intros ca LB ws m b n kd ws' H K7 Hin Hws'. unfold PK.cw_pk_holds in *. destruct (PK.decode_pk ca) as [u|]; [|exact H].
  destruct H as (g & ls & L & P & O & Wk & M & [SE EP] & CO). exists g, ls.
  split; [exact L|]. split; [exact P|]. split; [| split; [| split; [exact M| split; [split|]]]].
  5: { apply (PK.cost_pk_sub u g ls ws); [exact CO|]. intros w Hw. exact (proj1 (proj1 (Hws' w) Hw)). }
  - destruct O as [O1 O2]. split; [| exact O2]. intros x Hx. apply in_in_remove; [| exact (O1 x Hx)]. intros E. subst x.
    pose proof (PK.owned_pos g ls P _ Hx) as POS. cbn [snd] in POS.
    destruct (proj1 (Forall_forall _ _) Wk _ Hin ltac:(cbn [w_kind]; unfold K_STACK; lia)) as [[_ D]|[_ ET]].
    + apply (D (b, n) Hx b); unfold in_iv, w_iv; cbn [fst snd w_lo w_len]; lia.
    + destruct ET as (K6 & _). cbn [w_kind] in K6. unfold PK.K_ETOP in K6. lia.
  - unfold PK.wins_pk in *. apply Forall_forall. intros w Hw. apply Hws' in Hw as [Hw _]. exact (proj1 (Forall_forall _ _) Wk w Hw).
  - apply (Seal.seal_ok_ws ws); [exact SE|]. intros w Hw _. exact (proj1 (proj1 (Hws' w) Hw)).
  - intros VB. destruct (EP VB) as (w & Hw & EW). exists w. split; [| exact EW]. apply Hws'. split; [exact Hw|].
    intros X. subst w. destruct EW as ((K6 & _) & _). cbn [w_kind] in K6. unfold PK.K_ETOP in K6. lia.
Qed.

Lemma pk_vec_unowned : forall ca LB ws m a, PK.cw_pk_holds segs ca LB ws m -> nth_error ca 6 = Some a -> bv_unsigned a <> 0 ->
  forall w, In w ws -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned a.
Proof.
  intros ca LB ws m a H NTH A0 w Hw KB LEN E. unfold PK.cw_pk_holds in H.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    cbn [PK.decode_pk] in H; try contradiction.
  cbn [nth_error] in NTH. injection NTH as <-.
  destruct H as (g & ls & L & P & O & Wk & M & GH & CO). destruct L as (_ & _ & _ & _ & Leb & _). cbn [PK.a_eb] in Leb.
  assert (VB : v_begin (PK.k_evec g) <> 0) by (rewrite Leb; exact A0).
  assert (OW : In (v_begin (PK.k_evec g), v_bytes (PK.k_evec g)) (PK.owned g)).
  { unfold PK.owned, PK.evec_blocks. destruct (v_begin (PK.k_evec g) =? 0) eqn:Z0; [apply Z.eqb_eq in Z0; contradiction| left; reflexivity]. }
  pose proof (PK.owned_pos g ls P _ OW) as POS. cbn [snd] in POS.
  destruct (proj1 (Forall_forall _ _) Wk w Hw ltac:(rewrite KB; unfold K_BLOCK, K_STACK; lia)) as [[_ D]|[NB _]]; [| exact (NB KB)].
  apply (D _ OW (w_lo w)); unfold in_iv, w_iv; cbn [fst snd]; [lia| rewrite E, <- Leb; lia].
Qed.

Lemma pk_owned_c24 : forall ca LB ws m, PK.cw_pk_holds segs ca LB ws m ->
  match PK.decode_pk ca with
  | Some u => exists g ls, PK.pure_pk g ls /\ PK.own_pk g LB /\
      forall ob, In ob (PK.owned g) -> 5881 <= snd ob <= 7936 ->
        exists w, In w ws /\ w_kind w = PK.K_ETOP /\ 0 < w_len w /\ in_iv ob (w_lo w)
  | None => False
  end.
Proof.
  intros ca LB ws m H. unfold PK.cw_pk_holds in H. destruct (PK.decode_pk ca) as [u|]; [| exact H].
  destruct H as (g & ls & L & P & O & Wk & M & [SE EP] & CO). exists g, ls. split; [exact P|]. split; [exact O|].
  intros ob Hob C24. unfold PK.owned in Hob. apply in_app_iff in Hob as [Hob|Hob].
  - unfold PK.evec_blocks in Hob. destruct (v_begin (PK.k_evec g) =? 0) eqn:Z0; [contradiction|]. destruct Hob as [<-|[]].
    apply Z.eqb_neq in Z0. destruct (EP Z0) as (w & Hw & (K6 & _ & E1 & _ & E3) & LEN).
    exists w. split; [exact Hw|]. split; [exact K6|]. split; [exact LEN|].
    unfold in_iv, v_capend, v_bytes in *. cbn [fst snd]. lia.
  - exfalso. apply in_map_iff in Hob as (c & <- & Hc). destruct P as (_ & _ & _ & _ & _ & ((_ & _ & V3 & _) & _)).
    destruct (V3 c Hc) as (_ & _ & S0). unfold chunk_block, CHUNK_HDR, CHUNK_SIZE0 in *. cbn [snd] in C24. lia.
Qed.

Lemma td_grow_gen : forall ca LB ws m b n kd, TD.td_client segs ca LB ws m -> (kd < K_SUB \/ K_GHOST <= kd) ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) ->
  (forall cs, Forall TD.tchunk_ok cs ->
              Forall (fun w => w_kind w <> K_STACK -> forall c, In c cs -> forall a, in_iv (w_iv w) a -> ~ in_iv (chunk_block c) a) ws ->
              Seal.seal_ok ws cs -> Seal.seal_ok (ws ++ [Win b n kd]) cs) ->
  TD.td_client segs ca ((b, n) :: LB) (ws ++ [Win b n kd]) m.
Proof.
  intros ca LB ws m b n kd H KD FR HSEAL. destruct H as [H NS]. split; [| apply TD.nosub_app; [exact NS| apply TD.nosub_one; exact KD]].
  unfold TD.td_client0 in *. destruct (TD.decode_td ca) as [[cur cnt]|]; [|exact H].
  destruct H as (cs & Hcur & Hcnt & Hok & Hdisj & Hlb & Hws & Hat & SE). exists cs.
  split; [exact Hcur|]. split; [exact Hcnt|]. split; [exact Hok|]. split; [exact Hdisj|]. split; [| split; [| split; [exact Hat|]]].
  - intros c Hc. right. exact (Hlb c Hc).
  - apply Forall_app. split; [exact Hws|]. constructor; [|constructor]. intros _ c Hc a Ha Hb.
    apply (FR a Ha). unfold in_user. apply in_ivs_In. exists (chunk_block c). split; [exact (Hlb c Hc)| exact Hb].
  - exact (HSEAL cs Hok Hws SE).
Qed.

Lemma td_twin_grow : forall ca LB ws m b0 n0 n, TD.td_client segs ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (Seal.shadZ b0, n) a -> ~ in_user LB a) ->
  TD.td_client segs ca ((Seal.shadZ b0, n) :: LB) (ws ++ [Win (Seal.shadZ b0) n Seal.K_TWIN]) m.
Proof.
  intros ca LB ws m b0 n0 n H HB N0 A8 FR. apply (td_grow_gen ca LB ws m _ _ Seal.K_TWIN H ltac:(right; unfold K_GHOST, Seal.K_TWIN; lia) FR).
  intros cs Hok Hws SE. apply SealX.seal_ok_twin_window; [exact SE| exact A8|].
  intros c Hc. destruct (proj1 (Forall_forall _ _) Hok c Hc) as (_ & A16 & S0). split; [exact (al16_al8 _ A16)|]. intros E.
  apply (proj1 (Forall_forall _ _) Hws _ HB ltac:(cbn [w_kind]; unfold K_BLOCK, K_STACK; lia) c Hc b0);
    unfold in_iv, w_iv, chunk_block; cbn [fst snd w_lo w_len]; unfold CHUNK_HDR, CHUNK_SIZE0 in *; lia.
Qed.

Lemma td_ghost_grow : forall ca LB ws m b n kd, TD.td_client segs ca LB ws m -> 7 <= kd -> kd <> Seal.K_TWIN ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) -> TD.td_client segs ca ((b, n) :: LB) (ws ++ [Win b n kd]) m.
Proof.
  intros ca LB ws m b n kd H K7 K9 FR. apply (td_grow_gen ca LB ws m _ _ kd H ltac:(right; unfold K_GHOST; lia) FR).
  intros cs _ _ SE. apply SealX.seal_ok_app_other; [exact SE|]. intros w [<-|[]]. exact K9.
Qed.

Lemma td_ghost_free : forall ca LB ws m b n kd ws', TD.td_client segs ca LB ws m -> 7 <= kd -> In (Win b n kd) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n kd) -> TD.td_client segs ca (remove iv_eq_dec (b, n) LB) ws' m.
Proof.
  intros ca LB ws m b n kd ws' H K7 Hin Hws'. destruct H as [H NS]. split; [| apply (TD.nosub_sub ws); [exact NS| intros w Hw; exact (proj1 (proj1 (Hws' w) Hw))]].
  unfold TD.td_client0 in *. destruct (TD.decode_td ca) as [[cur cnt]|]; [|exact H].
  destruct H as (cs & Hcur & Hcnt & Hok & Hdisj & Hlb & Hws & Hat & SE). exists cs.
  split; [exact Hcur|]. split; [exact Hcnt|]. split; [exact Hok|]. split; [exact Hdisj|]. split; [| split; [| split; [exact Hat|]]].
  - intros c Hc. apply in_in_remove; [| exact (Hlb c Hc)]. intros E.
    pose proof (TD.chunk_block_pos c (proj1 (Forall_forall _ _) Hok c Hc)) as POS.
    pose proof (proj1 (Forall_forall _ _) Hws _ Hin ltac:(cbn [w_kind]; unfold K_STACK; lia) c Hc b) as D.
    rewrite E in D, POS. cbn [snd] in POS. apply D; unfold in_iv, w_iv; cbn [fst snd w_lo w_len]; lia.
  - apply Forall_forall. intros w Hw. apply Hws' in Hw as [Hw _]. exact (proj1 (Forall_forall _ _) Hws w Hw).
  - apply (Seal.seal_ok_ws ws); [exact SE|]. intros w Hw _. exact (proj1 (proj1 (Hws' w) Hw)).
Qed.

Theorem XW_twin_grow : forall md ca LB ws m b0 n0 n, cw_holds (CX.XTP segs) md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (Seal.shadZ b0, n) a -> ~ in_user LB a) ->
  cw_holds (CX.XTP segs) md ca ((Seal.shadZ b0, n) :: LB) (ws ++ [Win (Seal.shadZ b0) n Seal.K_TWIN]) m.
Proof.
  intros md ca LB ws m b0 n0 n H HB N0 A8 FR. cbn [cw_holds CX.XTP] in *. unfold CX.x_holds in *.
  destruct (md =? TD.CM_TD); [exact (td_twin_grow ca LB ws m b0 n0 n H HB N0 A8 FR)|].
  destruct (md =? PK.CM_PK); [exact (pk_twin_grow ca LB ws m b0 n0 n H HB N0 A8 FR)| exact H].
Qed.
Theorem XW_ghost_grow : forall md ca LB ws m b n kd, cw_holds (CX.XTP segs) md ca LB ws m -> 7 <= kd -> kd <> Seal.K_TWIN ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) -> cw_holds (CX.XTP segs) md ca ((b, n) :: LB) (ws ++ [Win b n kd]) m.
Proof.
  intros md ca LB ws m b n kd H K7 K9 FR. cbn [cw_holds CX.XTP] in *. unfold CX.x_holds in *.
  destruct (md =? TD.CM_TD); [exact (td_ghost_grow ca LB ws m b n kd H K7 K9 FR)|].
  destruct (md =? PK.CM_PK); [exact (pk_ghost_grow ca LB ws m b n kd H K7 K9 FR)| exact H].
Qed.
Theorem XW_ghost_free : forall md ca LB ws m b n kd ws', cw_holds (CX.XTP segs) md ca LB ws m -> 7 <= kd -> In (Win b n kd) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n kd) -> cw_holds (CX.XTP segs) md ca (remove iv_eq_dec (b, n) LB) ws' m.
Proof.
  intros md ca LB ws m b n kd ws' H K7 Hin Hws'. cbn [cw_holds CX.XTP] in *. unfold CX.x_holds in *.
  destruct (md =? TD.CM_TD); [exact (td_ghost_free ca LB ws m b n kd ws' H K7 Hin Hws')|].
  destruct (md =? PK.CM_PK); [exact (pk_ghost_free ca LB ws m b n kd ws' H K7 Hin Hws')| exact H].
Qed.

Lemma pk_sub_ghost : forall ca LB ws m w g a, PK.cw_pk_holds segs ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Proof.
  intros ca LB ws m w g a H Hw Hg KW KG Ia Ig. unfold PK.cw_pk_holds in H. destruct (PK.decode_pk ca) as [u|]; [| exact H].
  destruct H as (gg & ls & _ & _ & _ & Wk & _). unfold PK.wins_pk in Wk.
  destruct (proj1 (Forall_forall _ _) Wk w Hw ltac:(unfold K_STACK, K_SUB in *; lia)) as [[[KB|KGw] _]|[_ EO]]; [unfold K_BLOCK, K_SUB in *; lia| lia|].
  destruct EO as (_ & VB & LO1 & _ & HI1).
  destruct (proj1 (Forall_forall _ _) Wk g Hg ltac:(unfold K_STACK, K_GHOST in *; lia)) as [[_ DJ]|[_ (K6 & _)]]; [| unfold PK.K_ETOP, K_GHOST in *; lia].
  apply (DJ (v_begin (PK.k_evec gg), v_bytes (PK.k_evec gg))) with (a := a); [| exact Ig|].
  - unfold PK.owned. apply in_or_app. left. unfold PK.evec_blocks. destruct (Z.eqb_spec (v_begin (PK.k_evec gg)) 0) as [E0|_]; [contradiction| left; reflexivity].
  - unfold in_iv, w_iv, v_capend, v_bytes in *. cbn [fst snd] in *. lia.
Qed.
Lemma td_sub_ghost : forall ca LB ws m w g a, TD.td_client segs ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Proof. intros ca LB ws m w g a [_ NS] Hw _ KW _ _ _. exact (proj1 (Forall_forall _ _) NS w Hw KW). Qed.
Theorem XW_sub_ghost : forall md ca LB ws m w g a, cw_holds (CX.XTP segs) md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Proof.
  intros md ca LB ws m w g a H. cbn [cw_holds CX.XTP] in H. unfold CX.x_holds in H.
  destruct (md =? TD.CM_TD); [exact (td_sub_ghost ca LB ws m w g a H)|].
  destruct (md =? PK.CM_PK); [exact (pk_sub_ghost ca LB ws m w g a H)| destruct H].
Qed.

Lemma td_nosub : forall ca LB ws m, TD.td_client segs ca LB ws m -> TD.nosub ws.
Proof. intros ca LB ws m [_ NS]. exact NS. Qed.

Lemma pk_zc : forall ca LB ws ws' m z z', PK.cw_pk_holds segs ca LB ws m -> z' < 2 ^ 48 ->
  (forall w, In w ws' <-> (In w ws /\ w <> Win z 0 K_STACK) \/ w = Win z' 0 K_STACK) -> PK.cw_pk_holds segs ca LB ws' m.
Proof.
  intros ca LB ws ws' m z z' H Z48 Hws'. unfold PK.cw_pk_holds in *. destruct (PK.decode_pk ca) as [u|]; [| exact H].
  destruct H as (g & ls & LK & PU & OW & Wk & ME & [SE EP] & CO). exists g, ls.
  assert (OLD : forall w, In w ws' -> w_kind w <> K_STACK -> In w ws).
  { intros w Hw NK. apply Hws' in Hw as [[Hw _]|Q]; [exact Hw| exfalso; apply NK; rewrite Q; reflexivity]. }
  split; [exact LK|]. split; [exact PU|]. split; [exact OW|]. split; [| split; [exact ME| split; [split|]]].
  - unfold PK.wins_pk in *. apply Forall_forall. intros w Hw NK. exact (proj1 (Forall_forall _ _) Wk w (OLD w Hw NK) NK).
  - apply (Seal.seal_ok_ws ws); [exact SE|]. intros w Hw K9. apply OLD; [exact Hw| rewrite K9; unfold Seal.K_TWIN, K_STACK; lia].
  - intros VB. destruct (EP VB) as (w & Hw & EW & LW). exists w. split; [| split; [exact EW| exact LW]]. apply Hws'. left. split; [exact Hw|].
    intros Q. destruct EW as (K6 & _). rewrite Q in K6. cbn [w_kind] in K6. unfold PK.K_ETOP, K_STACK in K6. lia.
  - apply (PK.cost_pk_ws u g ls ws); [exact CO|]. intros w Hw NV. apply Hws' in Hw as [[Hw _]|Q]; [exact Hw|]. exfalso. apply NV. rewrite Q.
    unfold PK.pku_val. cbn [w_kind w_len w_lo]. unfold K_STACK. cbn [Z.eqb andb].
    assert (P62 : 2 ^ 48 < PK.PKU_BASE) by (vm_compute; reflexivity).
    destruct (Z.leb_spec PK.PKU_BASE z') as [L|_]; [lia|]. cbn [andb].
    destruct (Z.leb_spec (PK.PKU_BASE + PK.PKU_ST) z') as [L|_]; [assert (0 <= PK.PKU_ST) by (vm_compute; discriminate); lia| reflexivity].
Qed.
Lemma td_zc : forall ca LB ws ws' m z z', TD.td_client segs ca LB ws m ->
  (forall w, In w ws' <-> (In w ws /\ w <> Win z 0 K_STACK) \/ w = Win z' 0 K_STACK) -> TD.td_client segs ca LB ws' m.
Proof.
  intros ca LB ws ws' m z z' [H NS] Hws'.
  assert (OLD : forall w, In w ws' -> w_kind w <> K_STACK -> In w ws).
  { intros w Hw NK. apply Hws' in Hw as [[Hw _]|Q]; [exact Hw| exfalso; apply NK; rewrite Q; reflexivity]. }
  split.
  - unfold TD.td_client0 in *. destruct (TD.decode_td ca) as [[cur cnt]|]; [| exact H].
    destruct H as (cs & Hcur & Hcnt & Hok & Hdisj & Hlb & Hws & Hat & SE). exists cs.
    split; [exact Hcur|]. split; [exact Hcnt|]. split; [exact Hok|]. split; [exact Hdisj|]. split; [exact Hlb|]. split; [| split; [exact Hat|]].
    + apply Forall_forall. intros w Hw NK. exact (proj1 (Forall_forall _ _) Hws w (OLD w Hw NK) NK).
    + apply (Seal.seal_ok_ws ws); [exact SE|]. intros w Hw K9. apply OLD; [exact Hw| rewrite K9; unfold Seal.K_TWIN, K_STACK; lia].
  - apply Forall_forall. intros w Hw KW. apply (proj1 (Forall_forall _ _) NS w); [| exact KW]. apply OLD; [exact Hw| unfold K_STACK, K_SUB in *; lia].
Qed.
Theorem XW_zc : forall md ca LB ws ws' m z z', cw_holds (CX.XTP segs) md ca LB ws m -> z' < 2 ^ 48 ->
  (forall w, In w ws' <-> (In w ws /\ w <> Win z 0 K_STACK) \/ w = Win z' 0 K_STACK) -> cw_holds (CX.XTP segs) md ca LB ws' m.
Proof.
  intros md ca LB ws ws' m z z' H Z48 Hws'. cbn [cw_holds CX.XTP] in *. unfold CX.x_holds in *.
  destruct (md =? TD.CM_TD); [exact (td_zc ca LB ws ws' m z z' H Hws')|].
  destruct (md =? PK.CM_PK); [exact (pk_zc ca LB ws ws' m z z' H Z48 Hws')| exact H].
Qed.

Lemma pk_k0_del : forall ca LB ws ws' m w0, PK.cw_pk_holds segs ca LB ws m -> w_kind w0 = K_STACK ->
  (forall w, In w ws' <-> In w ws /\ w <> w0) -> PK.cw_pk_holds segs ca LB ws' m.
Proof.
  intros ca LB ws ws' m w0 H K0 Hws'. unfold PK.cw_pk_holds in *. destruct (PK.decode_pk ca) as [u|]; [| exact H].
  destruct H as (g & ls & LK & PU & OW & Wk & ME & [SE EP] & CO). exists g, ls.
  assert (SUB : forall w, In w ws' -> In w ws) by (intros w Hw; exact (proj1 (proj1 (Hws' w) Hw))).
  split; [exact LK|]. split; [exact PU|]. split; [exact OW|]. split; [| split; [exact ME| split; [split|]]].
  - unfold PK.wins_pk in *. apply Forall_forall. intros w Hw. exact (proj1 (Forall_forall _ _) Wk w (SUB w Hw)).
  - apply (Seal.seal_ok_ws ws); [exact SE|]. intros w Hw _. exact (SUB w Hw).
  - intros VB. destruct (EP VB) as (w & Hw & EW & LW). exists w. split; [| split; [exact EW| exact LW]]. apply Hws'. split; [exact Hw|].
    intros Q. destruct EW as (K6 & _). rewrite Q, K0 in K6. unfold PK.K_ETOP, K_STACK in K6. lia.
  - apply (PK.cost_pk_sub u g ls ws); [exact CO| exact SUB].
Qed.
Lemma td_k0_del : forall ca LB ws ws' m w0, TD.td_client segs ca LB ws m ->
  (forall w, In w ws' <-> In w ws /\ w <> w0) -> TD.td_client segs ca LB ws' m.
Proof.
  intros ca LB ws ws' m w0 [H NS] Hws'.
  assert (SUB : forall w, In w ws' -> In w ws) by (intros w Hw; exact (proj1 (proj1 (Hws' w) Hw))).
  split; [| exact (TD.nosub_sub ws ws' NS SUB)].
  unfold TD.td_client0 in *. destruct (TD.decode_td ca) as [[cur cnt]|]; [| exact H].
  destruct H as (cs & Hcur & Hcnt & Hok & Hdisj & Hlb & Hws & Hat & SE). exists cs.
  split; [exact Hcur|]. split; [exact Hcnt|]. split; [exact Hok|]. split; [exact Hdisj|]. split; [exact Hlb|]. split; [| split; [exact Hat|]].
  - apply Forall_forall. intros w Hw. exact (proj1 (Forall_forall _ _) Hws w (SUB w Hw)).
  - apply (Seal.seal_ok_ws ws); [exact SE|]. intros w Hw _. exact (SUB w Hw).
Qed.
Theorem XW_k0_del : forall md ca LB ws ws' m w0, cw_holds (CX.XTP segs) md ca LB ws m -> w_kind w0 = K_STACK ->
  (forall w, In w ws' <-> In w ws /\ w <> w0) -> cw_holds (CX.XTP segs) md ca LB ws' m.
Proof.
  intros md ca LB ws ws' m w0 H K0 Hws'. cbn [cw_holds CX.XTP] in *. unfold CX.x_holds in *.
  destruct (md =? TD.CM_TD); [exact (td_k0_del ca LB ws ws' m w0 H Hws')|].
  destruct (md =? PK.CM_PK); [exact (pk_k0_del ca LB ws ws' m w0 H K0 Hws')| exact H].
Qed.

End WithSegs.
End XWT.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import LedgerCfg AllocCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxRn FxImage FxHandoff FxHoBuild FxSys FxDrive.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import HoBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint chain_cover (l : list (Z * Z)) (lo hi : Z) : bool :=
  match l with
  | [] => hi <=? lo
  | (b, s) :: r => (b <=? lo) && chain_cover r (Z.max lo (b + s)) hi
  end.

Lemma chain_cover_sound : forall l lo hi, chain_cover l lo hi = true ->
  forall x, lo <= x < hi -> exists b s, In (b, s) l /\ b <= x < b + s.
Proof.
  induction l as [|[b s] r IH]; intros lo hi H x Hx; cbn [chain_cover] in H.
  - apply Z.leb_le in H. lia.
  - apply andb_true_iff in H as [Hb Hr]. apply Z.leb_le in Hb.
    destruct (Z_lt_le_dec x (b + s)) as [Hlt | Hge].
    + exists b, s. split; [left; reflexivity | lia].
    + assert (Hx2 : Z.max lo (b + s) <= x < hi) by lia.
      destruct (IH _ _ Hr x Hx2) as (b' & s' & Hin & Hx'). exists b', s'. split; [right; exact Hin | exact Hx'].
Qed.

Definition res_pairs (R : list (word * word)) : list (Z * Z) := map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) R.

Lemma res_cover : forall R lo hi, chain_cover (res_pairs R) lo hi = true ->
  forall x, lo <= x < hi -> exists p, In p R /\ e_lo p <= x < e_hi p.
Proof.
  intros R lo hi H x Hx. destruct (chain_cover_sound _ _ _ H x Hx) as (b & s & Hin & Hb).
  unfold res_pairs in Hin. apply in_map_iff in Hin as (p & E & Hp). injection E as <- <-.
  exists p. split; [exact Hp | unfold e_hi, e_lo, e_sz; lia].
Qed.

(* [comment removed for export] *)
Section Built.
  Variable IM : fimage.
  Variable facts : list hfact.

  Lemma region_desc_shape : forall t lo len al d,
    let r := region_desc IM facts (t, lo, len, al, d) in
    rd_tag r = t /\ rd_lo r = lo /\ rd_len r = len /\ rd_align r = al /\ rd_dflt r = d.
  Proof. intros t lo len al d. unfold region_desc. destruct (t =? 0)%uint63; cbn; repeat split; reflexivity. Qed.

  Definition shape_tag (s : int * int * int * int * option pkind) : int := let '(t, _, _, _, _) := s in t.
  Definition shape_lo (s : int * int * int * int * option pkind) : int := let '(_, lo, _, _, _) := s in lo.
  Definition shape_len (s : int * int * int * int * option pkind) : int := let '(_, _, len, _, _) := s in len.

  Lemma built_region_inv : forall pc shapes t rg,
    iget t (f_mem (state_of (ho_build IM facts pc shapes))) = Some rg ->
    exists s, In s shapes /\ shape_tag s = t /\ rg_lo rg = shape_lo s /\ rg_len rg = shape_len s.
  Proof.
    intros pc shapes t rg H. unfold state_of, ho_build in H. cbn [f_mem sd_mem] in H.
    apply (iget_iof_list_map_In rd_tag region_of) in H as (r & Hr & Ht & ->).
    apply in_map_iff in Hr as (s & <- & Hs). exists s. split; [exact Hs|].
    destruct s as [[[[t' lo] len] al] d]. destruct (region_desc_shape t' lo len al d) as (E1 & E2 & E3 & _).
    cbn [shape_tag shape_lo shape_len]. rewrite <- Ht, E1. unfold region_of. cbn [rg_lo rg_len]. rewrite E2, E3. auto.
  Qed.

  (* [comment removed for export] *)
  Definition shapes4 (lo0 top nb : int) (d1 : option pkind) : list (int * int * int * int * option pkind) :=
    [ (0%uint63, lo0, top, 0%uint63, None); (1%uint63, 0%uint63, 8388608%uint63, 4%uint63, d1);
      (2%uint63, 0%uint63, 8192%uint63, 12%uint63, None); (3%uint63, 0%uint63, nb, 12%uint63, None) ].

  Lemma built_region_get : forall pc lo0 top nb d1 (t : int),
    (t = 0 \/ t = 1 \/ t = 2 \/ t = 3)%uint63 ->
    exists rg, iget t (f_mem (state_of (ho_build IM facts pc (shapes4 lo0 top nb d1)))) = Some rg.
  Proof.
    intros pc lo0 top nb d1 t Ht. unfold state_of, ho_build. cbn [f_mem sd_mem]. rewrite iget_iof_list.
    unfold shapes4. cbn [map rev app].
    destruct (region_desc_shape 0%uint63 lo0 top 0%uint63 None) as (E0 & _).
    destruct (region_desc_shape 1%uint63 0%uint63 8388608%uint63 4%uint63 d1) as (E1 & _).
    destruct (region_desc_shape 2%uint63 0%uint63 8192%uint63 12%uint63 None) as (E2 & _).
    destruct (region_desc_shape 3%uint63 0%uint63 nb 12%uint63 None) as (E3 & _).
    cbn [find fst]. rewrite E0, E1, E2, E3.
    destruct Ht as [-> | [-> | [-> | ->]]]; cbn; eexists; reflexivity.
  Qed.
End Built.

(* [comment removed for export] *)
Section Root.
  Variable cfg : SpuriousCfg.
  Variable segs : list Segment.
  Variable IM : fimage.
  Variable R0 : list (word * word).
  Variable Lim : Z.
  Variable mem0 : word -> option byte.
  Variable XI : (int -> word) -> Model -> Prop.
  Variable xtags : list int.

  Lemma bv_add_0 : forall w : word, bv_add w (Z_to_bv 64 0) = w.
  Proof. intros w. rewrite bv_add_word_Z, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

  Definition ledger4 (nbi : int) (nb : Z) : fledger :=
    FL [(3%uint63, 0%uint63, nbi); (2%uint63, 0%uint63, 8192%uint63)] [(2%uint63, 0%uint63, 4096%uint63)] 2%uint63 2 (nb + 8192).

  Lemma dinv_root : forall facts pc (lo0 top nbi : int) d1 (n : int) rho ms m (sp0 mb B : word) (nb : Z),
    let F := state_of (ho_build IM facts pc (shapes4 lo0 top nbi d1)) in
    Rn segs IM n rho F ms ->
    rho 0%uint63 = Z_to_bv 64 0 -> rho 1%uint63 = Z_to_bv 64 (bv_unsigned sp0 - 8388608) -> rho 2%uint63 = mb -> rho 3%uint63 = B ->
    to_Z nbi = nb -> to_Z lo0 < to_Z top -> 0 < nb < 2 ^ 62 ->
    8388608 <= bv_unsigned sp0 -> bv_unsigned mb + 8192 < 2 ^ 64 ->
    m_halted m = None -> model_nolazy m ->
    ledger_inv R0 Lim 2 (nb + 8192) (m_vmmaps m) ->
    vm_reserved (m_vmmaps m) = R0 -> vm_init_sp (m_vmmaps m) = sp0 ->
    vm_maps (m_vmmaps m) = [(B, Z_to_bv 64 nb); (mb, Z_to_bv 64 8192)] ->
    vm_noaccess (m_vmmaps m) = [(mb, Z_to_bv 64 4096)] ->
    vm_brk (m_vmmaps m) = Z_to_bv 64 (bv_unsigned mb + 8192) ->
    chain_cover (res_pairs R0) (to_Z lo0) (to_Z top) = true ->
    XI rho m -> (forall t, In t xtags -> to_Z t < to_Z n) ->
    DInv cfg segs IM R0 Lim RTgt [] mem0 XI xtags n rho F (ledger4 nbi nb) ms m.
  Proof.
    intros facts pc lo0 top nbi d1 n rho ms m sp0 mb B nb F HRn H0 H1 H2 H3 Hnb Hlt Hnbr Hsp Hmbr Hh Hnl Hli Vres Visp Vmaps Vna Vbrk Hcov HXI Hx.
    pose proof (u64_range sp0) as Us. pose proof (u64_range mb) as Um. pose proof (u64_range B) as Ub.
    assert (Un : bv_unsigned (Z_to_bv 64 nb) = nb) by (apply u64z; lia).
    assert (U8 : bv_unsigned (Z_to_bv 64 8192) = 8192) by (apply u64z; lia).
    assert (Hshape : forall t rg, iget t (f_mem F) = Some rg ->
              (t = 0%uint63 /\ rg_lo rg = lo0 /\ rg_len rg = top) \/ (t = 1%uint63 /\ rg_lo rg = 0%uint63 /\ rg_len rg = 8388608%uint63)
              \/ (t = 2%uint63 /\ rg_lo rg = 0%uint63 /\ rg_len rg = 8192%uint63) \/ (t = 3%uint63 /\ rg_lo rg = 0%uint63 /\ rg_len rg = nbi)).
    { intros t rg H. destruct (built_region_inv IM facts pc _ t rg H) as (s & Hin & Ht & Elo & Elen).
      unfold shapes4 in Hin. cbn [In] in Hin.
      destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [shape_tag shape_lo shape_len] in Ht, Elo, Elen; subst t; tauto. }
    unfold DInv. split; [exact HRn|]. split; [exact H0|]. split; [exact Hh|]. split; [exact Hnl|]. split; [exact Hli|].
    split; [|split; [|split; [exact I|split; [exact HXI|split; [exact Hx|]]]]].
    - (* [comment removed for export] *)
      intros t rg H. destruct (Hshape t rg H) as [(-> & El & Ee) | [(-> & El & Ee) | [(-> & El & Ee) | (-> & El & Ee)]]];
        unfold in_ival; rewrite El, Ee.
      + split; [exact Hlt|]. intros x Hxx. rewrite H0 in Hxx. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hxx.
        left. destruct (res_cover R0 _ _ Hcov x ltac:(lia)) as (p & Hp & Hpx). exists p. split; [|exact Hpx].
        rewrite Vres. apply in_or_app. left. exact Hp.
      + split; [reflexivity|]. intros x Hxx. rewrite H1, u64z in Hxx by lia. right. unfold alloc_top, stack_max_size. rewrite Visp.
        change (to_Z 0) with 0 in Hxx. lia.
      + split; [reflexivity|]. intros x Hxx. rewrite H2 in Hxx. left. exists (mb, Z_to_bv 64 8192). split.
        * rewrite Vmaps. apply in_or_app. right. right. left. reflexivity.
        * unfold e_hi, e_lo, e_sz. cbn [fst snd]. rewrite U8. change (to_Z 0) with 0 in Hxx. change (to_Z 8192) with 8192 in Hxx. lia.
      + split; [change (to_Z 0) with 0; lia|]. intros x Hxx. rewrite H3 in Hxx. left. exists (B, Z_to_bv 64 nb). split.
        * rewrite Vmaps. apply in_or_app. right. left. reflexivity.
        * unfold e_hi, e_lo, e_sz. cbn [fst snd]. rewrite Un. change (to_Z 0) with 0 in Hxx. lia.
    - (* [comment removed for export] *)
      unfold mirror, ledger4. cbn [fl_maps fl_na fl_brk]. split; [|split].
      + constructor; [|constructor; [|constructor]]; unfold ent_ok.
        * destruct (built_region_get IM facts pc lo0 top nbi d1 3%uint63 ltac:(tauto)) as (rg & Hrg). exists rg. split; [exact Hrg|].
          destruct (Hshape _ _ Hrg) as [(E & _) | [(E & _) | [(E & _) | (_ & El & Ee)]]]; try discriminate E.
          rewrite El, Ee. change (to_Z 0) with 0. split; [lia|]. split; [lia|].
          unfold adr. rewrite H3, bv_add_0, Hnb, Vmaps. left. reflexivity.
        * destruct (built_region_get IM facts pc lo0 top nbi d1 2%uint63 ltac:(tauto)) as (rg & Hrg). exists rg. split; [exact Hrg|].
          destruct (Hshape _ _ Hrg) as [(E & _) | [(E & _) | [(_ & El & Ee) | (E & _)]]]; try discriminate E.
          rewrite El, Ee. change (to_Z 0) with 0. change (to_Z 8192) with 8192. split; [lia|]. split; [lia|].
          unfold adr. rewrite H2, bv_add_0, Vmaps. right. left. reflexivity.
      + constructor; [|constructor]. unfold ent_ok.
        destruct (built_region_get IM facts pc lo0 top nbi d1 2%uint63 ltac:(tauto)) as (rg & Hrg). exists rg. split; [exact Hrg|].
        destruct (Hshape _ _ Hrg) as [(E & _) | [(E & _) | [(_ & El & Ee) | (E & _)]]]; try discriminate E.
        rewrite El, Ee. change (to_Z 0) with 0. change (to_Z 8192) with 8192. change (to_Z 4096) with 4096. split; [lia|]. split; [lia|].
        unfold adr. rewrite H2, bv_add_0, Vna. left. reflexivity.
      + destruct (built_region_get IM facts pc lo0 top nbi d1 2%uint63 ltac:(tauto)) as (rg & Hrg). exists rg. split; [exact Hrg|].
        destruct (Hshape _ _ Hrg) as [(E & _) | [(E & _) | [(_ & El & Ee) | (E & _)]]]; try discriminate E.
        rewrite Ee. change (to_Z 8192) with 8192. unfold adr. rewrite H2, bv_add_word_Z, Vbrk. reflexivity.
    - (* [comment removed for export] *) intros t [].
  Qed.
End Root.

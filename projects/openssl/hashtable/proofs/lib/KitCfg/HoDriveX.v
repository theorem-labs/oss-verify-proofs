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
From OSSVerify.Proofs.openssl.hashtable.lib Require Import HoBridge HoDrive.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition pristine_b (M : itrie region) (t : int) : bool :=
  negb (t =? 0)%uint63 &&
  match iget t M with
  | Some rg => match rg_dflt rg, rg_pages rg with None, IEmpty => true | _, _ => false end
  | None => false
  end.

Lemma pristine_b_sound : forall M t, pristine_b M t = true -> pristine M t.
Proof.
  intros M t H. unfold pristine_b in H. apply andb_true_iff in H as [Hn H].
  split.
  - intros ->. discriminate Hn.
  - destruct (iget t M) as [rg|]; [|discriminate H]. exists rg. split; [reflexivity|].
    destruct (rg_dflt rg); [discriminate H|]. split; [reflexivity|].
    destruct (rg_pages rg); try discriminate H. intros pn. apply (iget_iempty pn).
Qed.

Section RootX.
  Variable cfg : SpuriousCfg.
  Variable segs : list Segment.
  Variable IM : fimage.
  Variable R0 : list (word * word).
  Variable Lim : Z.
  Variable XI : (int -> word) -> Model -> Prop.
  Variable xtags : list int.

  (* [comment removed for export] *)
  Lemma dinv_keep : forall mem0 keep n rho F L ms m,
    DInv cfg segs IM R0 Lim RTgt [] mem0 XI xtags n rho F L ms m ->
    forallb (pristine_b (f_mem F)) keep = true ->
    DInv cfg segs IM R0 Lim RTgt keep (ms_mem ms) XI xtags n rho F L ms m.
  Proof.
    intros mem0 keep n rho F L ms m (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _) Hk.
    unfold DInv. repeat (split; [assumption|]).
    intros t Ht. split.
    - apply pristine_b_sound. exact (proj1 (forallb_forall _ _) Hk t Ht).
    - intros rg x _ _. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma dinvx_root : forall facts pc (lo0 top nbi : int) d1 (n : int) rho ms m (sp0 mb B : word) (nb : Z) keep,
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
    forallb (pristine_b (f_mem F)) keep = true ->
    to_Z top <= bv_unsigned sp0 -> bv_unsigned mb + 8192 <= bv_unsigned sp0 -> bv_unsigned B + nb <= bv_unsigned sp0 ->
    DInvX cfg segs IM R0 Lim RTgt keep (ms_mem ms) XI xtags (ms_fregs ms) (ms_fcsr ms) (ms_rom ms)
          (fun x => bv_unsigned sp0 <= bv_unsigned x) n rho F (ledger4 nbi nb) ms m.
  Proof.
    intros facts pc lo0 top nbi d1 n rho ms m sp0 mb B nb keep F HRn H0 H1 H2 H3 Hnb Hlt Hnbr Hsp Hmbr Hh Hnl Hli Vres Visp Vmaps Vna Vbrk
           Hcov HXI Hx Hkeep Htop Hmbtop HBtop.
    pose proof (u64_range sp0) as Us. pose proof (u64_range mb) as Um. pose proof (u64_range B) as Ub.
    pose proof (dinv_root cfg segs IM R0 Lim (ms_mem ms) XI xtags facts pc lo0 top nbi d1 n rho ms m sp0 mb B nb
                  HRn H0 H1 H2 H3 Hnb Hlt Hnbr Hsp Hmbr Hh Hnl Hli Vres Visp Vmaps Vna Vbrk Hcov HXI Hx) as HD.
    unfold DInvX. split; [exact (dinv_keep _ keep _ _ _ _ _ _ HD Hkeep)|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
    - intros x Hxhi. split; [|split; [|reflexivity]].
      + unfold alloc_top, stack_max_size. rewrite Visp. lia.
      + intros t rg Hg Hin. unfold in_ival in Hin.
        destruct (built_region_inv IM facts pc _ t rg Hg) as (s & Hs & Ht & Elo & Elen).
        unfold shapes4 in Hs. cbn [In] in Hs.
        destruct Hs as [<- | [<- | [<- | [<- | []]]]]; cbn [shape_tag shape_lo shape_len] in Ht, Elo, Elen; subst t; rewrite Elo, Elen in Hin.
        * rewrite H0 in Hin. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hin. lia.
        * rewrite H1, u64z in Hin by lia. change (to_Z 8388608) with 8388608 in Hin. lia.
        * rewrite H2 in Hin. change (to_Z 8192) with 8192 in Hin. lia.
        * rewrite H3, Hnb in Hin. lia.
    - unfold exact, ledger4. cbn [fl_maps fl_na map den]. unfold adr. change (to_Z 0) with 0.
      rewrite H2, H3, !bv_add_0, Hnb. change (to_Z 8192) with 8192. change (to_Z 4096) with 4096. split; [exact Vmaps | exact Vna].
  Qed.
End RootX.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Ledger Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm Bothny9 AsanInit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Back4sr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothny9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Section Minv.
  Variables (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (fs : Fs.Fs).
  Variable cs : acs.
  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
  Hypothesis CS : cs_ok BSEGS BOTH (@AsanInit.blim BL) SINV argH fs E cs R FULL model.

  Lemma entries_nowrap_of_ivs_wf : forall l, ivs_wf l -> Ledger.entries_nowrap l.
  Proof. intros l H e He. unfold Ledger.entry_nowrap, Ledger.hi. pose proof (H e He) as X. unfold iv_wf, B, S in X. exact X. Qed.

  Lemma nooverlap_of_seps : forall l, seps l -> Ledger.nooverlap l.
  Proof.
    intros l H. induction H as [|p l HF HS IH]; [exact I|]. cbn. split; [|exact IH].
    intros e' He'. pose proof (proj1 (Forall_forall _ _) HF e' He') as D. unfold iv_disjoint in D. unfold Ledger.hi, Ledger.lo. lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma lazy_free_of_lazyb : forall lo hi,
    (forall iv, In iv (m_vm_lazy model) ->
        bv_unsigned (fst iv) + bv_unsigned (snd iv) <= lo \/ hi <= bv_unsigned (fst iv)) ->
    Hull.lazy_free (m_vm_lazy model) lo hi.
  Proof.
    intros lo hi HX x Hx. destruct (Ledger.zcovb (m_vm_lazy model) x) eqn:EQ; [|reflexivity]. exfalso.
    apply Ledger.zcovb_true in EQ as (r & Hin & Hr). unfold Ledger.lo, Ledger.hi in Hr. pose proof (HX r Hin). lia.
  Qed.

  Lemma lazy_free_image : Hull.lazy_free (m_vm_lazy model) (img_lo BOTH) (img_hi BOTH).
  Proof.
    apply lazy_free_of_lazyb. intros iv Hin.
    pose proof (proj1 (Forall_forall _ _) (co_lazyb _ _ _ _ _ _ _ _ _ _ _ CS) iv Hin) as [L1 L2]. lia.
  Qed.

  Lemma lazy_free_above_top : forall lo hi, alloc_top (m_vmmaps model) <= lo -> Hull.lazy_free (m_vm_lazy model) lo hi.
  Proof.
    intros lo hi Hlo. apply lazy_free_of_lazyb. intros iv Hin.
    pose proof (proj1 (Forall_forall _ _) (co_lazyb _ _ _ _ _ _ _ _ _ _ _ CS) iv Hin) as [L1 L2]. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem minv_of_cs3 : forall (H HL : Hull.hull) (Ecap : Z),
    (forall lo hi q (e : word * word), In (lo, hi) (allowA BOTH E cs) -> lo <= q -> q + 4096 <= hi -> q mod 4096 = 0 ->
        In e (vm_maps (m_vmmaps model)) ->
        bv_unsigned (fst e) <= q -> q + 4096 <= bv_unsigned (fst e) + bv_unsigned (snd e) ->
        bv_unsigned (fst e) + bv_unsigned (snd e) <= alloc_top (m_vmmaps model) ->
        (bv_unsigned (fst e) + bv_unsigned (snd e) <= img_lo BOTH \/ img_hi BOTH <= bv_unsigned (fst e)) ->
        Hull.page_hullb HL q = true) ->
    Hull.hull_cover H HL (m_vm_lazy model) ->
    a_eager cs <= Ecap -> Ecap + Hull.hull_bytes HL <= (@AsanInit.blim BL) ->
    Hull.MInv H HL Ecap model.
  Proof.
    intros H HL Ecap SUB HC HE HB. destruct CS. destruct co_minv0 as [ND AL AW LZ BU].
    destruct co_wf0 as (W1 & W2 & W3 & _).   (* [comment removed for export] *)
    constructor.
    - exact ND.
    - exact AL.
    - intros p Hp. specialize (AW p Hp). unfold page_allowedb in AW. apply existsb_exists in AW as [[lo hi] [Hin Hb]].
      cbn [fst snd] in Hb. apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold page_size in H2.
      specialize (LZ p Hp). unfold page_in_ranges in LZ. apply existsb_exists in LZ as [[rb rs] [Hr Hrb]]. cbn [fst snd] in Hrb.
      apply andb_true_iff in Hrb as [R1 R2]. apply Z.leb_le in R1. apply Z.leb_le in R2. unfold page_size in R2.
      (* [comment removed for export] *)
      assert (LB : in_ivs (bv_unsigned p) (m_vm_lazy model) = true).
      { apply (proj2 (in_ivs_true _ _)). exists (rb, rs). split; [exact Hr|]. cbn [fst snd]. lia. }
      pose proof (co_lzsub0 _ LB) as MBt. apply (proj1 (in_ivs_true _ _)) in MBt as [e [He Re]].
      pose proof (proj1 (Forall_forall _ _) co_bounds0 e He) as (B1 & B2 & B3 & B4 & B5). cbn beta in B1, B2, B3, B4, B5.
      pose proof (AL p Hp) as ALp. unfold page_size in ALp.
      apply (SUB lo hi (bv_unsigned p) e Hin H1 H2 ALp He); [lia| | exact B5| exact B4].
      (* [comment removed for export] *)
      clear - Re B2 B3 ALp. Z.div_mod_to_equations. nia.
    - exact HC.
    - apply entries_nowrap_of_ivs_wf. exact W3.
    - apply entries_nowrap_of_ivs_wf. exact W1.
    - apply entries_nowrap_of_ivs_wf. exact W2.
    - apply nooverlap_of_seps. exact co_seps0.
    - change (Ledger.eager_used model) with (eager_used model). lia.
    - rewrite co_limit0. exact HB.
  Qed.

  (* [comment removed for export] *)
  Corollary minv_of_cs2 : forall (H : Hull.hull) (Ecap : Z),
    (forall lo hi q (e : word * word), In (lo, hi) (allowA BOTH E cs) -> lo <= q -> q + 4096 <= hi -> q mod 4096 = 0 ->
        In e (vm_maps (m_vmmaps model)) ->
        bv_unsigned (fst e) <= q -> q + 4096 <= bv_unsigned (fst e) + bv_unsigned (snd e) ->
        bv_unsigned (fst e) + bv_unsigned (snd e) <= alloc_top (m_vmmaps model) ->
        (bv_unsigned (fst e) + bv_unsigned (snd e) <= img_lo BOTH \/ img_hi BOTH <= bv_unsigned (fst e)) ->
        Hull.page_hullb H q = true) ->
    a_eager cs <= Ecap -> Ecap + Hull.hull_bytes H <= (@AsanInit.blim BL) ->
    Hull.MInv H H Ecap model.
  Proof. intros H Ecap SUB HE HB. apply (minv_of_cs3 H H Ecap SUB (Hull.hull_cover_self H _) HE HB). Qed.
End Minv.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRn FxHandoff FxDrive.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AsanAcct AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import CXI CxOpt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrEnv BrMem BrRev.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma maps_exact E : forall ms l,
  CxOpt.ledger_exact E ms -> APS.maps_match E ms l -> l = map (APS.amap_den E) ms.
Proof. exact (CxOpt.maps_exact_D1 E). Qed.

Section Ledger.
Variable E : AX2.env.
Variable TT : ttab_e.
Variable M : itrie region.
Hypothesis HTT : tt_wf TT = true.
Local Notation rho := (rho_of TT E).
Local Notation XT := (xt_of TT).
Hypothesis HM : forall t rg, iget t M = Some rg -> region_ok rho t rg.

(* [comment removed for export] *)
Definition ent_chk (m : APC.amap) (e : fent) : bool :=
  let '(t, off, len) := e in
  match APC.am_len m, aview [] M [] XT (AX2.SA (APC.am_base m) 0) with
  | AX2.ELit l, Some (t', o') => (t' =? t)%uint63 && (o' =? to_Z off) && (l =? to_Z len)
  | _, _ => false
  end.

Lemma ent_chk_den m e : ent_chk m e = true -> APS.amap_den E m = den rho e.
Proof.
  destruct e as [[t off] len]. unfold ent_chk.
  destruct (APC.am_len m) as [l| | | | | | |] eqn:El; try discriminate.
  destruct (aview [] M [] XT (AX2.SA (APC.am_base m) 0)) as [[t' o']|] eqn:Hav; [|discriminate].
  intros Hc. apply andb_prop in Hc as [Hc Hl]. apply andb_prop in Hc as [Ht Ho].
  apply Uint63.eqb_spec in Ht. apply Z.eqb_eq in Ho, Hl. subst t' o' l.
  pose proof (aview_sound rho (AX2.ev E) (AX2.eb E) [] M [] XT HM (rho_of_0 TT E) eq_refl (xt_of_ok TT E HTT) _ t (to_Z off) Hav) as Hs.
  rewrite env_eta in Hs. unfold AX2S.estart in Hs. cbn [AX2.a_base AX2.a_off] in Hs. rewrite Z.add_0_r in Hs.
  unfold APS.amap_den, den. rewrite El. cbn [AX2.edenot]. f_equal.
  apply bv_eq. rewrite Hs. unfold adr. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r.
  symmetry. apply Z.mod_small. rewrite <- Hs. apply bv_unsigned_in_range.
Qed.

Fixpoint ents_chk (ms : list APC.amap) (es : list fent) : bool :=
  match ms, es with
  | [], [] => true
  | m :: ms', e :: es' => ent_chk m e && ents_chk ms' es'
  | _, _ => false
  end.

Lemma ents_den : forall ms es, ents_chk ms es = true -> map (APS.amap_den E) ms = map (den rho) es.
Proof.
  induction ms as [|m ms IH]; intros [|e es] Hc; cbn [ents_chk] in Hc; try discriminate; [reflexivity|].
  apply andb_prop in Hc as [H1 H2]. cbn [map]. rewrite (ent_chk_den m e H1), (IH es H2). reflexivity.
Qed.
End Ledger.

(* [comment removed for export] *)
Section Facts.
Variable segs : list Segment.
Variable A : APC.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Variable E : AX2.env.
Variable CS : APC.acs.
Variable R : bvmap 5 word.
Variable FULL : word -> option byte.
Variable m : Model.
Hypothesis HCS : CXI.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m.
(* [comment removed for export] *)
Hypothesis RES_in_hull : Forall (fun p => APC.img_lo A <= e_lo p /\ e_hi p <= APC.img_hi A) (segments_reserved segs).

Local Notation V := (m_vmmaps m).

Lemma seps_pw_disj : forall l, APS.seps l -> pw_disj l.
Proof.
  induction 1 as [|p l Hp _ IH]; [exact I|]. cbn [pw_disj]. split; [|exact IH].
  eapply Forall_impl; [|exact Hp]. intros q Hq. exact Hq.
Qed.

Theorem cs_maps_facts :
  vm_reserved V = segments_reserved segs
  /\ Lim <= vm_limit V                                  (* [comment removed for export] *)
  /\ Forall (fun p => 0 < e_sz p) (vm_maps V)
  /\ Forall (fun p => e_lo p mod page_size = 0 /\ e_sz p mod page_size = 0) (vm_maps V)
  /\ Forall (fun p => e_hi p <= alloc_top V) (vm_maps V)
  /\ Forall (fun p => Forall (e_disj p) (segments_reserved segs)) (vm_maps V)
  /\ pw_disj (vm_maps V)
  /\ sp_window_lo <= bv_unsigned (vm_init_sp V) <= sp_window_hi
  /\ bv_unsigned (vm_start_brk V) <= bv_unsigned (vm_brk V).
Proof.
  pose proof (CXI.co_top _ _ _ _ _ _ _ _ _ _ _ _ HCS) as co_top'. pose proof (CXI.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [co_isp' _].
  destruct HCS as [HCS' _]. destruct HCS'. split; [exact co_res|]. split; [rewrite co_limit; apply Z.le_refl|].
  split; [eapply Forall_impl; [|exact co_bounds]; intros p Hp; cbv beta in Hp; destruct Hp as (H1 & H2 & H3 & H4 & H5); unfold e_sz; exact H1|].
  split; [eapply Forall_impl; [|exact co_bounds]; intros p Hp; cbv beta in Hp; destruct Hp as (H1 & H2 & H3 & H4 & H5); unfold e_lo, e_sz, page_size; split; assumption|].
  split; [eapply Forall_impl; [|exact co_bounds]; intros p Hp; cbv beta in Hp; destruct Hp as (H1 & H2 & H3 & H4 & H5); unfold e_hi, e_lo, e_sz; exact H5|].
  split.
  { eapply Forall_impl; [|exact co_bounds]. intros p Hp. cbv beta in Hp. destruct Hp as (_ & _ & _ & Hh & _).
    eapply Forall_impl; [|exact RES_in_hull]. intros q Hq. cbv beta in Hq. destruct Hq as [Hq1 Hq2].
    unfold e_disj, e_hi, e_lo, e_sz in *. lia. }
  split; [exact (seps_pw_disj _ co_seps)|].
  split; [|exact co_sbrk].
  unfold APS.TOP, alloc_top, stack_max_size, APC.CEIL, APC.CEILMAX, sp_window_lo, sp_window_hi in *. lia.
Qed.

End Facts.

(* [comment removed for export] *)
Theorem cs_exact_maps segs A Lim SINV argH ISP FS0 E CS R FULL m TT M ALL :
  CXI.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m ->
  tt_wf TT = true ->
  (forall t rg, iget t M = Some rg -> region_ok (rho_of TT E) t rg) ->
  CxOpt.ledger_exact E (APC.a_maps CS) ->
  ents_chk TT M (APC.a_maps CS) ALL = true ->
  vm_maps (m_vmmaps m) = map (den (rho_of TT E)) ALL.
Proof.
  intros HCS HTT HM Hnf Hc.
  rewrite (maps_exact E _ _ Hnf (CXI.co_maps _ _ _ _ _ _ _ _ _ _ _ _ HCS)).
  exact (ents_den E TT M HTT HM _ _ Hc).
Qed.

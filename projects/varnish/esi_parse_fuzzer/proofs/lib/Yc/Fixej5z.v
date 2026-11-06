(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec CatSim MmapSim ShapeAlg Nodes.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Ledger Hull Lazyiq4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Divembc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg.Lazy9wo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull.Lazylo0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Ledger OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Lazyiq4.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fixed_gate (m : Model) (addr : word) (nZ : Z) : Prop :=
  (bv_unsigned addr + nZ <= alloc_top (m_vmmaps m))%Z
  /\ (bv_unsigned addr mod page_size = 0)%Z
  /\ (0 < bv_unsigned addr)%Z.

Lemma fixed_gate_rewrites : forall m addr nZ,
  fixed_gate m addr nZ ->
  (two_pow_64 <=? bv_unsigned addr + nZ)%Z = false
  /\ (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z = true
  /\ (bv_unsigned addr mod page_size =? 0)%Z = true
  /\ (0 <? bv_unsigned addr)%Z = true.
Proof.
  (intros m addr nZ; (first [ intro dR_12; dand3 dR_12 as Hce Hal Hpos | intros (Hce & Hal & Hpos) ])).
  split; [|split; [|split]].
  - apply Z.leb_gt. pose proof (alloc_top_lt (m_vmmaps m)). lia.
  - apply Z.leb_le. exact Hce.
  - apply Z.eqb_eq. exact Hal.
  - apply Z.ltb_lt. exact Hpos.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_rw_contained_outcome : forall addr len prot flags fd off i m o,
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  fixed_gate m addr nZ ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  (mmap_err_out m o \/ mmap_fixed_destr_out m addr n o)   (* [comment removed for export] *)
  \/ (mmap_fixed_rw_budget_ok flags m addr n = true
      /\ o = Ok (mkEffect addr [] [(addr, n)])
               (with_mmap_replacement flags addr n
                  (with_vmmaps (mmap_fixed_rw_next h addr n) m)) []).
Proof.
  intros addr len prot flags fd off i m o Hlen Hmod Hna Hfna Hfrw. cbv zeta. intros Hg Hrf Hmc.
  (first [ pose proof ((fixed_gate_rewrites m addr _ Hg)) as dR_1; dand4 dR_1 as E1 E2 E3 E4 | destruct (fixed_gate_rewrites m addr _ Hg) as (E1 & E2 & E3 & E4) ]).
  destruct (mmap_shape_gates _ _ _ _ Hfrw eq_refl) as [G1 G2].   (* [comment removed for export] *)
  unfold mmap_spec. rewrite G1, G2, Hlen, Hmod, Hna, Hfna, Hfrw. cbv zeta.
  rewrite E1. cbn [negb]. rewrite bind_get_model. cbv beta.
  rewrite E2, E3, E4, Hrf, Hmc. cbn [negb andb]. unfold mmap_err_out, mmap_fixed_destr_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption|reflexivity].
    + (* [comment removed for export] *)
      left. right. eexists; split; [eassumption|reflexivity].
  - intros [[(e & He & ->) | (e & He & ->)] | (Hb & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. right. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
    + right. left. eexists _, _, _, _. split; [exists tt; split; [exact Hb|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_fixed_args (prot flags : word) (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = prot /\ ms_gpr ms 3 = flags
  /\ ms_gpr ms 4 = Z_to_bv 64 (-1) /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)
Definition fixed_rw_shape (flags : word) : Prop :=
  mmap_modeled_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.

Definition fixed_na_shape (flags : word) : Prop :=
  mmap_modeled_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true.

(* [comment removed for export] *)
Lemma fixed_rw_shape_plain : fixed_rw_shape (Z_to_bv 64 50).
Proof. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; vm_compute; reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fixed_contained (ms : machine_state) (model : Model) : Prop :=
  let addr := ms_gpr ms 0 in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true
  /\ map_contains (vm_maps (m_vmmaps model)) addr n = true.

Definition fixed_free (ms : machine_state) (model : Model) : Prop :=
  let addr := ms_gpr ms 0 in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) in
  region_free (vm_reserved (m_vmmaps model)) addr n && map_contains (vm_maps (m_vmmaps model)) addr n = false
  /\ region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma commit_model_halted : forall flags addr n na m,
  m_halted (commit_model flags addr n na m) = m_halted m.
Proof.
  intros flags addr n na m. unfold m_halted.
  (first [ pose proof ((commit_model_nonvm flags addr n na m)) as dR_4; dand5 dR_4 as _ _ _ Hp _ | destruct (commit_model_nonvm flags addr n na m) as (_ & _ & _ & Hp & _) ]). rewrite Hp. reflexivity.
Qed.

Lemma destroy_model_halted : forall addr n m,
  m_halted (destroy_model addr n m) = m_halted m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Lemma mmap_fixed_rw_contained_si_rel : forall ms x8 model flags,
  bv_unsigned x8 = 222%Z -> mmap_fixed_args (Z_to_bv 64 3) flags ms -> fixed_rw_shape flags ->
  let addr := ms_gpr ms 0 in
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  let n := Z_to_bv 64 nZ in
  fixed_gate model addr nZ -> fixed_contained ms model ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    ((exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
     \/ (exists e, In e mmap_errnos
                   /\ o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] []) (destroy_model addr n model) []))
    \/ (mmap_fixed_rw_budget_ok flags model addr n = true
        /\ o = Ok (mkEffect addr [] [(addr, n)]) (commit_model flags addr n false model) []).
Proof.
  (intros ms x8 model flags Hno; (first [ intro dR_13; dand5 dR_13 as H1 H2 H3 H4 H5 | intros (H1 & H2 & H3 & H4 & H5) ]); (first [ intro dR_14; dand4 dR_14 as S1 S2 S3 S4 | intros (S1 & S2 & S3 & S4) ]); intros addr nZ n Hg [Hrf Hmc] o).
  rewrite (syscall_spec_222 _ model o) by (rewrite in_sysno_si'; exact Hno).
  rewrite in_arg0_si', in_arg1_si', in_arg2_si', in_arg3_si', in_arg4_si', in_arg5_si'.
  rewrite H2, H3, H4, H5.
  rewrite <- mmap_fixed_rw_commit_model.
  exact (mmap_fixed_rw_contained_outcome (ms_gpr ms 0) (ms_gpr ms 1) (Z_to_bv 64 3) flags
           (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (sys_input segs ms x8) model o
           (w_is0_false_of_ne _ H1) S1 S2 S3 S4 Hg Hrf Hmc).
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_rw_contained_si : forall ms x8 model flags,
  bv_unsigned x8 = 222%Z -> m_halted model = None ->
  mmap_fixed_args (Z_to_bv 64 3) flags ms -> fixed_rw_shape flags ->
  let addr := ms_gpr ms 0 in
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  let n := Z_to_bv 64 nZ in
  fixed_gate model addr nZ -> fixed_contained ms model ->
  forall o, syscall_spec_acfg (sys_input segs ms x8) model o <->
    (exists e, In e (mmap_errnos_when (mmap_fixed_commit_refusable flags model addr n))
               /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
    \/ (mmap_fixed_rw_budget_ok flags model addr n = true
        /\ o = Ok (mkEffect addr [] [(addr, n)]) (commit_model flags addr n false model) [])
    \/ (exists e, In e (mmap_errnos_when (mmap_fixed_commit_refusable flags model addr n))
                  /\ o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] []) (destroy_model addr n model) []).
Proof.
  intros ms x8 model flags Hno Hh Hargs Hsh addr nZ n Hg Hc o.
  pose proof (mmap_fixed_rw_contained_si_rel ms x8 model flags Hno Hargs Hsh Hg Hc) as Hchar.
  assert (HR : forall o', ((exists e, In e mmap_errnos /\ o' = Ok (mkEffect (errno_ret e) [] []) model [])
                           \/ (exists e, In e mmap_errnos
                                         /\ o' = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
                                                    (destroy_model addr n model) [])) ->
             exists eff m' evs, o' = Ok eff m' evs /\ eff_ret eff = errno_ret ENOMEM /\ m_halted m' = None).
  { intros o' [(e & He & ->) | (e & He & ->)]; destruct He as [<-|[]];
      (eexists _, _, _; split; [reflexivity|]; split; [reflexivity|]).
    - exact Hh.
    - rewrite destroy_model_halted. exact Hh. }
  assert (HG : forall o', (mmap_fixed_rw_budget_ok flags model addr n = true
                           /\ o' = Ok (mkEffect addr [] [(addr, n)]) (commit_model flags addr n false model) []) ->
             exists eff m' evs, o' = Ok eff m' evs
                                /\ (bv_unsigned (eff_ret eff) mod page_size = 0)%Z /\ m_halted m' = None).
  { intros o' [_ ->]. eexists _, _, _. split; [reflexivity|]. split.
    - exact (proj1 (proj2 Hg)).
    - rewrite commit_model_halted. exact Hh. }
  assert (Hgf : forall o', (mmap_fixed_rw_budget_ok flags model addr n = true
                            /\ o' = Ok (mkEffect addr [] [(addr, n)]) (commit_model flags addr n false model) []) ->
             mmap_fixed_commit_refusable flags model addr n = false).
  { intros o' [Hb _]. unfold mmap_fixed_commit_refusable. rewrite Hb. reflexivity. }
  assert (Hfg : mmap_fixed_commit_refusable flags model addr n = false ->
             exists o', mmap_fixed_rw_budget_ok flags model addr n = true
                        /\ o' = Ok (mkEffect addr [] [(addr, n)]) (commit_model flags addr n false model) []).
  { intros Hf. exists (Ok (mkEffect addr [] [(addr, n)]) (commit_model flags addr n false model) []).
    split; [|reflexivity]. unfold mmap_fixed_commit_refusable in Hf. apply negb_false_iff in Hf. exact Hf. }
  rewrite (acfg_lift_enomem (sys_input segs ms x8) model
             (fun o' => (exists e, In e mmap_errnos /\ o' = Ok (mkEffect (errno_ret e) [] []) model [])
                        \/ (exists e, In e mmap_errnos
                                      /\ o' = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
                                                 (destroy_model addr n model) []))
             (fun o' => mmap_fixed_rw_budget_ok flags model addr n = true
                        /\ o' = Ok (mkEffect addr [] [(addr, n)]) (commit_model flags addr n false model) [])
             (mmap_fixed_commit_refusable flags model addr n) (or_introl Hno) Hchar HR HG Hgf Hfg o).
  split.
  - intros [[Hf [(e & He & ->) | (e & He & ->)]] | HGo].
    + left. exists e. split; [rewrite Hf; exact He | reflexivity].
    + right; right. exists e. split; [rewrite Hf; exact He | reflexivity].
    + right; left. exact HGo.
  - intros [(e & He & ->) | [HGo | (e & He & ->)]].
    + left. split; [exact (proj2 (mmap_errnos_when_In _ e He)) |].
      left. exists e. split; [exact (mmap_errnos_when_sub _ _ He) | reflexivity].
    + right. exact HGo.
    + left. split; [exact (proj2 (mmap_errnos_when_In _ e He)) |].
      right. exists e. split; [exact (mmap_errnos_when_sub _ _ He) | reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fixed_rw_cont_I (flags : word) (ms : machine_state) (model : Model) : Type :=
  ({e : Z | In e (mmap_errnos_when (mmap_fixed_commit_refusable flags model (ms_gpr ms 0)
                     (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))))}   (* [comment removed for export] *)
   + {u : unit | mmap_fixed_rw_budget_ok flags model (ms_gpr ms 0)
                   (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = true}
   + {e : Z | In e (mmap_errnos_when (mmap_fixed_commit_refusable flags model (ms_gpr ms 0)
                     (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))))})%type.

Definition fixed_rw_cont_nx (flags : word) (ms : machine_state) (model : Model)
    (i : fixed_rw_cont_I flags ms model) : config :=
  let addr := ms_gpr ms 0 in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) in
  match i with
  | inl (inl (exist _ e _)) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | inl (inr _) => mkCfg (advance_past_svc (apply_effect ms (mkEffect addr [] [(addr, n)])))
                   (commit_model flags addr n false model)
  | inr (exist _ e _) => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])))
                   (destroy_model addr n model)
  end.

Lemma node_mmap_fixed_rw_contained : forall ms model x8 flags,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_fixed_args (Z_to_bv 64 3) flags ms -> fixed_rw_shape flags ->
  fixed_gate model (ms_gpr ms 0) (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) ->
  fixed_contained ms model ->
  node_ok segs (mkCfg ms model) (fixed_rw_cont_I flags ms model) (fun _ => [])
          (fixed_rw_cont_nx flags ms model).
Proof.
  intros ms model x8 flags Hh Hsvc Hno Hargs Hsh Hg Hc.
  set (addr := ms_gpr ms 0). set (n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))).
  pose (effs := fun i : fixed_rw_cont_I flags ms model => match i with
          | inl (inl (exist _ e _)) => (mkEffect (errno_ret e) [] [] : SyscallEffect)
          | inl (inr _) => mkEffect addr [] [(addr, n)]
          | inr (exist _ e _) => mkEffectU (errno_ret e) [] [] [(addr, n)] [] [] end).
  pose (ms' := fun i : fixed_rw_cont_I flags ms model => match i with
          | inl (inl _) => model
          | inl (inr _) => commit_model flags addr n false model
          | inr _ => destroy_model addr n model end).
  assert (Enx : forall i, fixed_rw_cont_nx flags ms model i
                          = mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
  { intros [[[e He] | [u Hu]] | [e He]]; cbn [fixed_rw_cont_nx effs ms'];
      [rewrite apply_effect_no_write; reflexivity | reflexivity | reflexivity]. }
  pose proof (mmap_fixed_rw_contained_si ms x8 model flags Hno Hh Hargs Hsh Hg Hc) as HR.
  cbv zeta in HR. fold addr n in HR.
  pose proof (node_family_nil segs ms model x8 (fixed_rw_cont_I flags ms model) effs ms' (fun _ => []) _
                Hh Hsvc HR
                ltac:(intros [[[e He] | [u Hu]] | [e He]]; cbn [effs ms'];
                        [left; exists e; auto | right; left; auto | right; right; exists e; auto])
                ltac:(intros o [(e & He & ->) | [(Hb & ->) | (e & He & ->)]];
                        [exists (inl (inl (exist _ e He))) | exists (inl (inr (exist _ tt Hb)))
                        | exists (inr (exist _ e He))]; reflexivity)
                ltac:(intros [[[e He] | [u Hu]] | [e He]]; cbn [ms'];
                        [exact Hh | rewrite commit_model_halted; exact Hh | rewrite destroy_model_halted; exact Hh])
                ltac:(intros [[[e He] | [u Hu]] | [e He]]; reflexivity)) as Hnode.
  split.
  - intros i. rewrite Enx. apply (proj1 Hnode).
  - intros e st Hss. (first [ pose proof ((proj2 Hnode e st Hss)) as dR_8; dex1 dR_8 as i; destruct dR_8 as [-> ->] | pose proof ((proj2 Hnode e st Hss)) as dR_8; dand3 dR_8 as i -> -> | destruct (proj2 Hnode e st Hss) as (i & -> & ->) ]).
    exists i. rewrite Enx. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fixed_commit_not_refusable : forall flags model addr n,
  mmap_fixed_rw_budget_ok flags model addr n = true ->
  mmap_fixed_commit_refusable flags model addr n = false.
Proof. intros flags model addr n Hb. unfold mmap_fixed_commit_refusable. rewrite Hb. reflexivity. Qed.

Lemma fixed_commit_errno_forced : forall flags model addr n e,
  In e (mmap_errnos_when (mmap_fixed_commit_refusable flags model addr n)) ->
  e = ENOMEM /\ mmap_fixed_rw_budget_ok flags model addr n = false.
Proof.
  intros flags model addr n e H. destruct (mmap_errnos_when_In _ e H) as [-> Hc]. split; [reflexivity|].
  unfold mmap_fixed_commit_refusable in Hc. apply negb_true_iff in Hc. exact Hc.
Qed.

Lemma fixed_rw_cont_I_no_errno : forall flags ms model
    (s : {e : Z | In e (mmap_errnos_when (mmap_fixed_commit_refusable flags model (ms_gpr ms 0)
                          (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))))}),
  mmap_fixed_rw_budget_ok flags model (ms_gpr ms 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = true -> False.
Proof.
  intros flags ms model [e He] Hb. rewrite (fixed_commit_not_refusable _ _ _ _ Hb) in He. exact He.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_fixed_rw_contained_nf : forall ms model x8 flags B,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_fixed_args (Z_to_bv 64 3) flags ms -> fixed_rw_shape flags ->
  let addr := ms_gpr ms 0 in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) in
  fixed_gate model addr (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) ->
  fixed_contained ms model ->
  mmap_fixed_rw_budget_ok flags model addr n = true ->
  srealizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffect addr [] [(addr, n)])))
                        (commit_model flags addr n false model)) B ->
  srealizes segs (mkCfg ms model) B.
Proof.
  intros ms model x8 flags B Hh Hsvc Hno Hargs Hsh addr n Hg Hc Hb HB.
  apply (srz_node_spin_b segs (mkCfg ms model) (fixed_rw_cont_I flags ms model)
           (fixed_rw_cont_nx flags ms model)
           (fun i => match i with inl (inr _) => false | _ => true end) B
           (inl (inr (exist _ tt Hb)))).
  - apply (node_mmap_fixed_rw_contained ms model x8 flags); assumption.
  - reflexivity.
  - intros [[s0 | [u Hu]] | s0] Hp; try discriminate; exfalso; exact (fixed_rw_cont_I_no_errno flags ms model s0 Hb).
  - intros [[s0 | [u Hu]] | s0] Hp; try discriminate. cbn. exact HB.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_fixed_rw_contained : forall ms model x8 flags A B,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_fixed_args (Z_to_bv 64 3) flags ms -> fixed_rw_shape flags ->
  let addr := ms_gpr ms 0 in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) in
  fixed_gate model addr (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) ->
  fixed_contained ms model ->
  mmap_fixed_rw_budget_ok flags model addr n = true ->
  (forall tr, A tr -> B tr) ->
  srealizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffect addr [] [(addr, n)])))
                        (commit_model flags addr n false model)) B ->
  srealizes segs (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 flags A B Hh Hsvc Hno Hargs Hsh addr n Hg Hc Hb HAB HB.
  eapply srz_conseq.
  { apply (srz_mmap_fixed_rw_contained_nf ms model x8 flags B); eassumption. }
  intros tr. unfold t_alt2. split; [intros H; right; exact H | intros [H|H]; [exact (HAB tr H) | exact H]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fixed_rw_free_I (flags : word) (ms : machine_state) (model : Model) : Type :=
  ({e : Z | In e (mmap_errnos_when (mmap_fixed_fresh_refusable flags model
                     (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))))}   (* [comment removed for export] *)
   + {u : unit | mmap_noreserve_backed_ok flags model
                   (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true})%type.

Definition fixed_rw_free_nx (flags : word) (ms : machine_state) (model : Model)
    (i : fixed_rw_free_I flags ms model) : config :=
  let addr := ms_gpr ms 0 in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) in
  match i with
  | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | inr _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect addr [] [(addr, n)])))
                   (grant_model flags addr n false model)
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fixed_na_cont_I : Type :=   (* [comment removed for export] *)
  ({e : Z | In e (mmap_errnos_when false)} + unit + {e : Z | In e mmap_errnos /\ spec_destructive_fixed})%type.

Definition fixed_na_cont_nx (flags : word) (ms : machine_state) (model : Model)
    (i : fixed_na_cont_I) : config :=
  let addr := ms_gpr ms 0 in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) in
  match i with
  | inl (inl (exist _ e _)) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | inl (inr _) => mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [] [(addr, n)] [] [])))
                   (commit_model flags addr n true model)
  | inr (exist _ e _) => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])))
                   (destroy_model addr n model)
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fixed_na_free_I : Type := ({e : Z | In e (mmap_errnos_when false)} + unit)%type.   (* [comment removed for export] *)

Definition fixed_na_free_nx (flags : word) (ms : machine_state) (model : Model)
    (i : fixed_na_free_I) : config :=
  let addr := ms_gpr ms 0 in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) in
  match i with
  | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | inr _ => mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [] [(addr, n)] [] [])))
                   (grant_model flags addr n true model)
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

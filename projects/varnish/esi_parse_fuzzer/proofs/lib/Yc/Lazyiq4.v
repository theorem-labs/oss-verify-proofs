(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec CatSim MmapSim AllocSim ShapeAlg Nodes.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Ledger Hull.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Divembc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg.Lazy9wo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull.Lazylo0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Ledger OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sysno_si' : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
Lemma in_arg0_si' : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.
Lemma in_arg1_si' : forall segs ms x8, in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.
Lemma in_arg2_si' : forall segs ms x8, in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.
Lemma in_arg3_si' : forall segs ms x8, in_arg (sys_input segs ms x8) 3 = ms_gpr ms 3.
Proof. reflexivity. Qed.
Lemma in_arg4_si' : forall segs ms x8, in_arg (sys_input segs ms x8) 4 = ms_gpr ms 4.
Proof. reflexivity. Qed.
Lemma in_arg5_si' : forall segs ms x8, in_arg (sys_input segs ms x8) 5 = ms_gpr ms 5.
Proof. reflexivity. Qed.

Lemma u64_lit' : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz.
Qed.

Lemma w_is0_false_of_ne : forall w : word, w <> Z_to_bv 64 0 -> w_is0 w = false.
Proof. intros w H. unfold w_is0. apply bv_eqb_neq. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma sstep_of_spec_mat : forall ms model x8 eff m' m'' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec_acfg (sys_input segs ms x8) model (Ok eff m' evs) ->
  m_halted m' = None ->
  materialize_model_accesses m' (syscall_effect_accesses eff) = Some m'' ->
  sstep_cfg segs ACFG (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m'')).
Proof.
  intros ms model x8 eff m' m'' evs Hh Hsvc Hc Hh' Hmat.
  exact (sstep_cfg_syscall_acfg segs ms model x8 eff m' m'' evs Hh Hsvc Hc Hh' Hmat).
Qed.

(* [comment removed for export] *)
Lemma node_family_mat : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' ms'' : I -> Model) (evs : I -> list event)
    (R : outcome SyscallEffect -> Prop),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec_acfg (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) (evs i))) ->
  (forall o, R o -> exists i, o = Ok (effs i) (ms' i) (evs i)) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, materialize_model_accesses (ms' i) (syscall_effect_accesses (effs i)) = Some (ms'' i)) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms'' i)).
Proof.
  intros ms model x8 I effs ms' ms'' evs R Hh Hsvc HR Hin Hout Hh' Hmat. split.
  - intros i. apply (sstep_of_spec_mat ms model x8 _ (ms' i)); auto. apply HR. apply Hin.
  - intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m2 & Hh2 & -> & Hm & ->) | [(Hh2 & -> & Hm & ->) | (code & Hh2 & -> & ->)]])
         | (Hc & -> & ->)].
    + apply HR in Hc. destruct (Hout _ Hc) as (i & Hi). apply Ok_inj in Hi as (-> & -> & ->).
      rewrite (Hmat i) in Hm. injection Hm as <-. exists i. split; reflexivity.
    + apply HR in Hc. destruct (Hout _ Hc) as (i & Hi). apply Ok_inj in Hi as (-> & -> & ->).
      rewrite (Hmat i) in Hm. discriminate.
    + apply HR in Hc. destruct (Hout _ Hc) as (i & Hi). apply Ok_inj in Hi as (-> & -> & ->).
      rewrite Hh' in Hh2. discriminate.
    + exfalso. apply HR in Hc. destruct (Hout _ Hc) as (i & Hi). exact (Unmodeled_Ok _ _ _ Hi).
Qed.

(* [comment removed for export] *)
Lemma node_family_nil : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event)
    (R : outcome SyscallEffect -> Prop),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec_acfg (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) (evs i))) ->
  (forall o, R o -> exists i, o = Ok (effs i) (ms' i) (evs i)) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hout Hh' Hnil.
  apply (node_family_mat ms model x8 I effs ms' ms' evs R Hh Hsvc HR Hin Hout Hh').
  intros i. rewrite (Hnil i). apply materialize_model_accesses_nil.
Qed.

(* [comment removed for export] *)
Lemma node_family_hull : forall A AL E ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event)
    (R : outcome SyscallEffect -> Prop),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec_acfg (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) (evs i))) ->
  (forall o, R o -> exists i, o = Ok (effs i) (ms' i) (evs i)) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, MInv A AL E (ms' i)) ->
  (forall i, accs_in_hull A (syscall_effect_accesses (effs i))) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i)))
                          (model_after (ms' i) (syscall_effect_accesses (effs i))))
  /\ (forall i, MInv A AL E (model_after (ms' i) (syscall_effect_accesses (effs i)))).
Proof.
  intros A AL E ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hout Hh' HI Ha. split.
  - apply (node_family_mat ms model x8 I effs ms' _ evs R Hh Hsvc HR Hin Hout Hh').
    intros i. exact (proj1 (materialize_hull A AL E (ms' i) _ (HI i) (Ha i))).
  - intros i. exact (proj2 (materialize_hull A AL E (ms' i) _ (HI i) (Ha i))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_det_mat : forall ms model x8 eff0 m0 m0' evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok eff0 m0 evs0) ->
  m_halted m0 = None ->
  materialize_model_accesses m0 (syscall_effect_accesses eff0) = Some m0' ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0').
Proof.
  intros ms model x8 eff0 m0 m0' evs0 Hh Hsvc Hchk Hh0 Hmat.
  apply (node_family_mat ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => m0') (fun _ => evs0)
           (fun o => o = Ok eff0 m0 evs0) Hh Hsvc (syscall_spec_acfg_det _ _ _ _ _ Hchk)).
  - intros []. reflexivity.
  - intros o ->. exists tt. reflexivity.
  - intros []; exact Hh0.
  - intros []; exact Hmat.
Qed.

Lemma node_det_nil : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok eff0 m0 evs0) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hh0 Hnil.
  apply (node_det_mat ms model x8 eff0 m0 m0 evs0 Hh Hsvc Hchk Hh0).
  rewrite Hnil. apply materialize_model_accesses_nil.
Qed.

Lemma node_det_hull : forall A AL E ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok eff0 m0 evs0) ->
  m_halted m0 = None ->
  MInv A AL E m0 -> accs_in_hull A (syscall_effect_accesses eff0) ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0))
                          (model_after m0 (syscall_effect_accesses eff0)))
  /\ MInv A AL E (model_after m0 (syscall_effect_accesses eff0)).
Proof.
  intros A AL E ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hh0 HI Ha.
  destruct (materialize_hull A AL E m0 _ HI Ha) as [Hmat HI']. split; [|exact HI'].
  apply (node_det_mat ms model x8 eff0 m0 _ evs0 Hh Hsvc Hchk Hh0 Hmat).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_ret_only_nil : forall ms model x8 r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok (mkEffect r [] []) m' evs) ->
  m_halted m' = None ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 r m' evs Hh Hsvc Hchk Hh'.
  rewrite <- (apply_effect_no_write ms r).
  apply (node_det_nil ms model x8 (mkEffect r [] []) m' evs Hh Hsvc Hchk Hh' eq_refl).
Qed.

(* [comment removed for export] *)
Lemma syscall_effect_accesses_copyins : forall reads r,
  syscall_effect_accesses (with_copyins reads (mkEffect r [] [])) = reads.
Proof. intros reads r. unfold syscall_effect_accesses. cbn. apply app_nil_r. Qed.

Lemma node_ret_only_copyins_hull : forall A AL E ms model x8 reads r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o
             <-> o = Ok (with_copyins reads (mkEffect r [] [])) m' evs) ->
  m_halted m' = None ->
  MInv A AL E m' -> accs_in_hull A reads ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) (model_after m' reads))
  /\ MInv A AL E (model_after m' reads).
Proof.
  intros A AL E ms model x8 reads r m' evs Hh Hsvc Hchk Hh' HI Ha.
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  destruct (materialize_hull A AL E m' reads HI Ha) as [Hmat HI']. split; [|exact HI'].
  apply (node_det_mat ms model x8 (with_copyins reads (mkEffect r [] [])) m' _ evs Hh Hsvc Hchk Hh').
  rewrite syscall_effect_accesses_copyins. exact Hmat.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma srz_ret_only_silent_nil : forall ms model x8 r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok (mkEffect r [] []) m' []) ->
  m_halted m' = None ->
  srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 r m' T Hh Hsvc Hchk Hh' Hc.
  eapply srz_silent1; [eapply node_ret_only_nil; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma srz_det_hull : forall A AL E ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok eff0 m0 []) ->
  m_halted m0 = None ->
  MInv A AL E m0 -> accs_in_hull A (syscall_effect_accesses eff0) ->
  (MInv A AL E (model_after m0 (syscall_effect_accesses eff0)) ->
   srealizes segs (mkCfg (advance_past_svc (apply_effect ms eff0))
                         (model_after m0 (syscall_effect_accesses eff0))) T) ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros A AL E ms model x8 eff0 m0 T Hh Hsvc Hchk Hh0 HI Ha Hc.
  destruct (node_det_hull A AL E ms model x8 eff0 m0 [] Hh Hsvc Hchk Hh0 HI Ha) as [Hn HI'].
  eapply srz_silent1; [exact Hn | exact (Hc HI')].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)


End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition grant_okf (flags hint : word) (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
  && mmap_noreserve_backed_ok flags m n.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition grant_ok_nr (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_rw_args (flags : word) (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3 /\ ms_gpr ms 3 = flags
  /\ ms_gpr ms 4 = Z_to_bv 64 (-1) /\ ms_gpr ms 5 = Z_to_bv 64 0
  /\ mmap_modeled_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.   (* [comment removed for export] *)

Lemma mmap_modeled_b_plain :
  mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)

Lemma mmap_noreserve_b_plain : mmap_noreserve_b (Z_to_bv 64 34) = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mmap_args_ok_noreserve (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
  /\ ms_gpr ms 3 = Z_to_bv 64 16418 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_model_noreserve (a n : word) (m : Model) : Model :=
  vm_add_lazy a n (mmap_model a n m).

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma grant_okf_plain : forall hint m a n,
  grant_okf (Z_to_bv 64 34) hint m a n = grant_ok hint m a n.
Proof.
  intros hint m a n. unfold grant_okf, grant_ok, mmap_noreserve_backed_ok.
  rewrite mmap_noreserve_b_plain. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma grant_model_halted : forall flags a n na m,
  m_halted (grant_model flags a n na m) = m_halted m.
Proof.
  intros flags a n na m. unfold grant_model, with_mmap_backing.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs2.
Variable segs : list Segment.

Lemma mmap_rw_outcome_si_rel : forall ms x8 model flags,
  bv_unsigned x8 = 222%Z -> mmap_rw_args flags ms ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    (exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
    \/ (exists a, grant_okf flags (ms_gpr ms 0) model a nZ = true
         /\ o = Ok (mkEffect a [] [(a, Z_to_bv 64 nZ)])
                   (grant_model flags a (Z_to_bv 64 nZ) false model) []).
Proof.
  (intros ms x8 model flags Hno; (first [ intro dR_14; dand6 dR_14 as H1 H2 H3 H4 H5 Hmb | intros (H1 & H2 & H3 & H4 & H5 & Hmb) ]); intros nZ o).
  rewrite (syscall_spec_222 _ model o) by (rewrite in_sysno_si'; exact Hno).
  rewrite in_arg0_si', in_arg1_si', in_arg2_si', in_arg3_si', in_arg4_si', in_arg5_si'.
  rewrite H2, H3, H4, H5.
  rewrite (mmap_rw_outcome (ms_gpr ms 0) (ms_gpr ms 1) (Z_to_bv 64 3) flags
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (sys_input segs ms x8) model o
             (w_is0_false_of_ne _ H1) Hmb).
  unfold mmap_err_out, grant_okf, grant_model, grant_vmmaps. fold nZ. cbn [negb].
  split; (intros [H | (a & Hg & ->)]; [left; exact H | right; exists a; split; [|reflexivity]]).
  - (first [ dand5 Hg as G1 G2 G3 G4 G5 | destruct Hg as (G1 & G2 & G3 & G4 & G5) ]).   (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) G1), (proj2 (Z.ltb_lt _ _) G2), (proj2 (Z.leb_le _ _) G3), G4, G5.
    reflexivity.
  - rewrite !andb_true_iff in Hg. destruct Hg as [[[[G1 G2] G3] G4] G5].
    apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. auto 10.
Qed.

(* [comment removed for export] *)
Lemma mmap_rw_outcome_si : forall ms x8 model flags,
  bv_unsigned x8 = 222%Z -> m_halted model = None -> mmap_rw_args flags ms ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  forall o, syscall_spec_acfg (sys_input segs ms x8) model o <->
    (exists e, In e (mmap_errnos_when (mmap_grant_refusable flags model nZ))
               /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
    \/ (exists a, grant_okf flags (ms_gpr ms 0) model a nZ = true
         /\ o = Ok (mkEffect a [] [(a, Z_to_bv 64 nZ)])
                   (grant_model flags a (Z_to_bv 64 nZ) false model) []).
Proof.
  intros ms x8 model flags Hno Hh Hargs nZ.
  apply (acfg_lift_mmap_when (sys_input segs ms x8) model
           (fun o => exists a, grant_okf flags (ms_gpr ms 0) model a nZ = true
                       /\ o = Ok (mkEffect a [] [(a, Z_to_bv 64 nZ)])
                                 (grant_model flags a (Z_to_bv 64 nZ) false model) [])
           (mmap_grant_refusable flags model nZ) Hno Hh
           (mmap_rw_outcome_si_rel ms x8 model flags Hno Hargs)).
  - intros o (a & Hg & ->). eexists _, _, _. split; [reflexivity|]. split.
    + unfold grant_okf in Hg. rewrite !andb_true_iff in Hg. destruct Hg as [[[[G1 _] _] _] _].
      apply Z.eqb_eq in G1. exact G1.
    + rewrite grant_model_halted. exact Hh.
  - intros o (a & Hg & _). unfold grant_okf in Hg.
    rewrite !andb_true_iff in Hg. destruct Hg as [[[[G1 G2] G3] G4] G5].
    apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3.
    exact (mmap_grant_not_refusable flags model nZ a G1 G2 G3 G4 G5).
  - intros Hf. destruct (mmap_grant_refusable_false flags model nZ Hf) as (Hb & a & G1 & G2 & G3 & G4).
    exists (Ok (mkEffect a [] [(a, Z_to_bv 64 nZ)]) (grant_model flags a (Z_to_bv 64 nZ) false model) []).
    cbv beta. exists a. split; [|reflexivity]. unfold grant_okf.
    rewrite (proj2 (Z.eqb_eq _ _) G1), (proj2 (Z.ltb_lt _ _) G2), (proj2 (Z.leb_le _ _) G3), G4, Hb.
    reflexivity.
Qed.

(* [comment removed for export] *)
Definition mmap_rw_I (flags : word) (ms : machine_state) (model : Model) : Type :=
  ({e : Z | In e (mmap_errnos_when (mmap_grant_refusable flags model
                     (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))))}   (* [comment removed for export] *)
   + {a : word | grant_okf flags (ms_gpr ms 0) model a
                   (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true})%type.

Definition mmap_rw_nx (flags : word) (ms : machine_state) (model : Model)
    (i : mmap_rw_I flags ms model) : config :=
  match i with
  | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | inr (exist _ a _) =>
      mkCfg (advance_past_svc
               (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
            (grant_model flags a (page_round_up (ms_gpr ms 1)) false model)
  end.

(* [comment removed for export] *)
Lemma node_mmap_rw : forall ms model x8 flags,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_rw_args flags ms ->
  node_ok segs (mkCfg ms model) (mmap_rw_I flags ms model) (fun _ => [])
          (mmap_rw_nx flags ms model).
Proof.
  intros ms model x8 flags Hh Hsvc Hno Hargs.
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1))).
  pose (effs := fun i : mmap_rw_I flags ms model => match i with
          | inl (exist _ e _) => (mkEffect (errno_ret e) [] [] : SyscallEffect)
          | inr (exist _ a _) => mkEffect a [] [(a, Z_to_bv 64 nZ)] end).
  pose (ms' := fun i : mmap_rw_I flags ms model => match i with
          | inl _ => model
          | inr (exist _ a _) => grant_model flags a (Z_to_bv 64 nZ) false model end).
  assert (Enx : forall i, mmap_rw_nx flags ms model i
                          = mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
  { intros [[e He] | [a Ha]]; cbn [mmap_rw_nx effs ms'];
      [rewrite apply_effect_no_write; reflexivity | reflexivity]. }
  pose proof (mmap_rw_outcome_si ms x8 model flags Hno Hh Hargs) as HR. cbv zeta in HR. fold nZ in HR.
  pose proof (node_family_nil segs ms model x8 (mmap_rw_I flags ms model) effs ms' (fun _ => []) _
                Hh Hsvc HR
                ltac:(intros [[e He] | [a Ha]]; cbn [effs ms']; [left; exists e; auto | right; exists a; auto])
                ltac:(intros o [(e & He & ->) | (a & Ha & ->)];
                        [exists (inl (exist _ e He)) | exists (inr (exist _ a Ha))]; reflexivity)
                ltac:(intros [[e He] | [a Ha]]; cbn [ms']; [exact Hh | rewrite grant_model_halted; exact Hh])
                ltac:(intros [[e He] | [a Ha]]; reflexivity)) as Hnode.
  split.
  - intros i. rewrite Enx. apply (proj1 Hnode).
  - intros e st Hss. (first [ pose proof ((proj2 Hnode e st Hss)) as dR_2; dex1 dR_2 as i; destruct dR_2 as [-> ->] | pose proof ((proj2 Hnode e st Hss)) as dR_2; dand3 dR_2 as i -> -> | destruct (proj2 Hnode e st Hss) as (i & -> & ->) ]).
    exists i. rewrite Enx. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_rw_errno_forced : forall flags model nZ e,
  In e (mmap_errnos_when (mmap_grant_refusable flags model nZ)) ->
  e = ENOMEM /\ mmap_grant_refusable flags model nZ = true.
Proof. intros flags model nZ e H. exact (mmap_errnos_when_In _ e H). Qed.

(* [comment removed for export] *)
Lemma grant_okf_not_refusable : forall flags hint m a n,
  grant_okf flags hint m a n = true -> mmap_grant_refusable flags m n = false.
Proof.
  intros flags hint m a n Hg. unfold grant_okf in Hg.
  rewrite !andb_true_iff in Hg. destruct Hg as [[[[G1 G2] G3] G4] G5].
  apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3.
  exact (mmap_grant_not_refusable flags m n a G1 G2 G3 G4 G5).
Qed.

(* [comment removed for export] *)
Lemma grant_okf_of_not_refusable : forall flags hint m n,
  mmap_grant_refusable flags m n = false -> exists a, grant_okf flags hint m a n = true.
Proof.
  intros flags hint m n H. destruct (mmap_grant_refusable_false flags m n H) as (Hb & a & G1 & G2 & G3 & G4).
  exists a. unfold grant_okf.
  rewrite (proj2 (Z.eqb_eq _ _) G1), (proj2 (Z.ltb_lt _ _) G2), (proj2 (Z.leb_le _ _) G3), G4, Hb. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_ok_nr_not_refusable : forall hint m a n,
  grant_ok_nr hint m a n = true -> mmap_reserve_refusable m n = false.
Proof.
  intros hint m a n Hg. unfold grant_ok_nr in Hg.
  rewrite !andb_true_iff in Hg. destruct Hg as [[[G1 G2] G3] G4].
  apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3.
  exact (mmap_reserve_not_refusable m n a G1 G2 G3 G4).
Qed.

(* [comment removed for export] *)
Lemma mmap_rw_I_no_errno : forall flags ms model
    (s : {e : Z | In e (mmap_errnos_when (mmap_grant_refusable flags model
                          (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))))}),
  mmap_grant_refusable flags model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false -> False.
Proof. intros flags ms model [e He] Hnf. rewrite Hnf in He. exact He. Qed.

(* [comment removed for export] *)
Lemma srz_mmap_rw_nf : forall ms model x8 flags T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_rw_args flags ms ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  mmap_grant_refusable flags model nZ = false ->
  (forall a, grant_okf flags (ms_gpr ms 0) model a nZ = true ->
     srealizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, Z_to_bv 64 nZ)])))
                          (grant_model flags a (Z_to_bv 64 nZ) false model)) T) ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 flags T Hh Hsvc Hno Hargs nZ Hnf HB.
  destruct (grant_okf_of_not_refusable flags (ms_gpr ms 0) model nZ Hnf) as [a0 Ha0].
  apply (srz_node_spin_b segs (mkCfg ms model) (mmap_rw_I flags ms model)
           (mmap_rw_nx flags ms model)
           (fun i => match i with inr _ => false | _ => true end) T
           (inr (exist _ a0 Ha0))).
  - apply (node_mmap_rw ms model x8 flags); assumption.
  - reflexivity.
  - intros [s | [a Ha]] Hp; try discriminate. exfalso. exact (mmap_rw_I_no_errno flags ms model s Hnf).
  - intros [s | [a Ha]] Hp; try discriminate. cbn. apply HB. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_rw_nf_ex : forall ms model x8 flags T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_rw_args flags ms ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  (exists a, grant_okf flags (ms_gpr ms 0) model a nZ = true) ->
  (forall a, grant_okf flags (ms_gpr ms 0) model a nZ = true ->
     srealizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, Z_to_bv 64 nZ)])))
                          (grant_model flags a (Z_to_bv 64 nZ) false model)) T) ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 flags T Hh Hsvc Hno Hargs nZ [a0 Ha0] HB.
  apply (srz_mmap_rw_nf ms model x8 flags T Hh Hsvc Hno Hargs); [| exact HB].
  exact (grant_okf_not_refusable flags (ms_gpr ms 0) model a0 _ Ha0).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegs2.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mmap_na_args (flags : word) (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0 /\ ms_gpr ms 3 = flags
  /\ ms_gpr ms 4 = Z_to_bv 64 (-1) /\ ms_gpr ms 5 = Z_to_bv 64 0
  /\ mmap_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true.   (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section WithSegs3.
Variable segs : list Segment.

(* [comment removed for export] *)

Definition mmap_na_I (ms : machine_state) (model : Model) : Type :=
  ({e : Z | In e (mmap_errnos_when (mmap_reserve_refusable model
                     (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))))}   (* [comment removed for export] *)
   + {a : word | grant_ok_nr (ms_gpr ms 0) model a
                   (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true})%type.

Definition mmap_na_nx (flags : word) (ms : machine_state) (model : Model)
    (i : mmap_na_I ms model) : config :=
  match i with
  | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | inr (exist _ a _) =>
      mkCfg (advance_past_svc
               (apply_effect ms (mkEffectU a [] [] [(a, page_round_up (ms_gpr ms 1))] [] [])))
            (grant_model flags a (page_round_up (ms_gpr ms 1)) true model)
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs3.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma munmap_model_modelL : forall a n m, munmap_model a n m = munmap_modelL a n m.
Proof. reflexivity. Qed.

Section WithSegs4.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma node_munmap_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno Hargs.
  apply (node_det_nil segs ms model x8 (munmap_eff ms) _ [] Hh Hsvc).
  - intros o. apply (munmap_outcome_si segs ms x8 model o Hno Hargs).
  - rewrite munmap_model_halted. exact Hh.
  - reflexivity.
Qed.

Lemma srz_munmap_lazy : forall ms model x8 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  srealizes segs (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hsvc Hno Hargs Hc.
  eapply srz_silent1; [apply (node_munmap_lazy ms model x8); assumption | exact Hc].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegs4.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs5.
Variable segs : list Segment.

(* [comment removed for export] *)

Definition brk_I (ms : machine_state) (model : Model) : Type :=
  {r : word | brk_resolution_ok model (ms_gpr ms 0) r}.

Definition brk_eff (ms : machine_state) (model : Model) (r : word) : SyscallEffect :=
  mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
               (brk_unmaps r (vm_brk (m_vmmaps model))) [] [].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegs5.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mprotect_args_ok (ms : machine_state) (model : Model) : Prop :=
  let addr := ms_gpr ms 0 in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) in
  (bv_unsigned addr mod page_size = 0)%Z
  /\ ms_gpr ms 1 <> Z_to_bv 64 0
  /\ (bv_unsigned addr + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) < two_pow_64)%Z
  /\ ms_gpr ms 2 = Z_to_bv 64 3
  /\ map_contains (vm_noaccess (m_vmmaps model)) addr n = true
  /\ map_contains (vm_maps (m_vmmaps model)) addr n = true.

Section WithSegs6.
Variable segs : list Segment.

(* [comment removed for export] *)

Definition mprotect_I (ms : machine_state) (model : Model) : Type :=
  ({e : Z | In e (mprotect_errnos_when (mprotect_refusable model (ms_gpr ms 0)
                     (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))))}   (* [comment removed for export] *)
   + {u : unit | mprotect_budget_ok model (ms_gpr ms 0)
                   (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) = true})%type.

Definition mprotect_nx (ms : machine_state) (model : Model) (i : mprotect_I ms model) : config :=
  let addr := ms_gpr ms 0 in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) in
  match i with
  | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | inr _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect (Z_to_bv 64 0) [] [(addr, n)])))
                   (mprotect_model_next model addr n)
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs6.

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
Definition svc_pend (ms : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := Some (ms_reg ms 17);
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms; ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.

(* [comment removed for export] *)

(* [comment removed for export] *)

Section WithSegs7.
Variable segs : list Segment.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegs7.

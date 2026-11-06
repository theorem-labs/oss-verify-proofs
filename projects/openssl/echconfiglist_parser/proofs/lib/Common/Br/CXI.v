(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AsanAcct BackingAlgebra AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CXI.
Section S.
Variable segs : list Segment.
Variable A : atable.
Variable Lim : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Variable E : env.
Variable cs : acs.
Variable R : bvmap 5 word.
Variable FULL : word -> option byte.
Variable model : Model.

Definition cs_ok : Prop :=
  APS.cs_ok segs A Lim SINV argH FS0 E cs R FULL model /\ bv_unsigned (vm_init_sp (m_vmmaps model)) = ISP.

Lemma cs_ok_intro : APS.cs_ok segs A Lim SINV argH FS0 E cs R FULL model ->
  bv_unsigned (vm_init_sp (m_vmmaps model)) = ISP -> cs_ok.
Proof. intros H1 H2. exact (conj H1 H2). Qed.
Lemma cs_ok_aps : cs_ok -> APS.cs_ok segs A Lim SINV argH FS0 E cs R FULL model.
Proof. intros [H _]. exact H. Qed.
Lemma cs_ok_visp : cs_ok -> bv_unsigned (vm_init_sp (m_vmmaps model)) = ISP.
Proof. intros [_ H]. exact H. Qed.

Hypothesis HC : cs_ok.
Let H := proj1 HC.

Lemma co_regs : regs_ok E (s_regs (a_ss cs)) R.                                   Proof. exact (APS.co_regs _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_log : s_log (a_ss cs) = [].                                               Proof. exact (APS.co_log _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_know : know_ok segs E (Mr A argH E cs model FULL) (kn cs).                Proof. exact (APS.co_know _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_halt : m_halted model = None.                                             Proof. exact (APS.co_halt _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_fds : fds_ok E (a_fd cs) model.                                           Proof. exact (APS.co_fds _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_fs : m_fs model = FS0.                                                    Proof. exact (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_tid : a_tidset cs = false -> m_tid model = None.                          Proof. exact (APS.co_tid _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_res : vm_reserved (m_vmmaps model) = segments_reserved segs.              Proof. exact (APS.co_res _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_limit_eq : vm_limit (m_vmmaps model) = Lim.                               Proof. exact (APS.co_limit _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_limit : Lim <= vm_limit (m_vmmaps model).                                 Proof. rewrite co_limit_eq. apply Z.le_refl. Qed.
Lemma co_maps : maps_match E (a_maps cs) (vm_maps (m_vmmaps model)).               Proof. exact (APS.co_maps _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_holes : Forall (hole_ok E (a_ylo cs) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) (a_maps cs).
Proof. exact (APS.co_holes _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_seps : seps (vm_maps (m_vmmaps model)).                                   Proof. exact (APS.co_seps _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_wf : model_ivs_wf model.                                                  Proof. exact (APS.co_wf _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_bounds : Forall (fun iv => 0 < bv_unsigned (snd iv)
                                /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                                /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
                                /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= alloc_top (m_vmmaps model)) (vm_maps (m_vmmaps model)).
Proof. exact (APS.co_bounds _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_lazyb : Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
                               /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= alloc_top (m_vmmaps model)) (m_vm_lazy model).
Proof. exact (APS.co_lazyb _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_nasub : forall z, in_ivs z (vm_noaccess (m_vmmaps model)) = true -> in_ivs z (vm_maps (m_vmmaps model)) = true.
Proof. exact (APS.co_nasub _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_none : Forall (fun m => am_kind m = KNONE \/ am_kind m = KNONELAZY -> In (amap_den E m) (vm_noaccess (m_vmmaps model))) (a_maps cs).
Proof. exact (APS.co_none _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_kinds : Forall (fun m => am_kind m = KRWLAZY ->
               forall a : word, bv_unsigned (edenot E (am_base m)) <= bv_unsigned a < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
                 in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false
                 /\ page_in_ranges (page_base a) (m_vm_lazy model) = true) (a_maps cs).
Proof. exact (APS.co_kinds _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_totsz : sum_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= a_totsz cs.
Proof. exact (APS.co_totsz _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_split : True.                                                             Proof. exact I. Qed.
Lemma co_brk : vm_brk (m_vmmaps model) = edenot E (a_brk cs).                      Proof. exact (APS.co_brk _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_sbrk : bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned (vm_brk (m_vmmaps model)).
Proof. exact (APS.co_sbrk _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_eager : eager_used model <= a_eager cs.                                   Proof. exact (APS.co_eager _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_abytes : A_bytes (allowA A E cs) <= a_abytes cs.                           Proof. exact (APS.co_abytes _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_minv : MInv (allowA A E cs) model.                                        Proof. exact (APS.co_minv _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_zero : forall a : word, hid A argH E cs model a = true ->
               in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true ->
               in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false ->
               page_in_ranges (page_base a) (m_vm_lazy model) = true ->
               in_ghost E cs (bv_unsigned a) = false ->
               FULL a = Some (Z_to_bv 8 0).
Proof. exact (APS.co_zero _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_sinv : SINV E FULL.                                                       Proof. exact (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_vmx : vm_noaccess (m_vmmaps model) = fst (vm_replay E (a_vmops cs)) /\ m_vm_lazy model = snd (vm_replay E (a_vmops cs)).
Proof. exact (APS.co_vmx _ _ _ _ _ _ _ _ _ _ _ H). Qed.
Lemma co_top : CEIL <= alloc_top (m_vmmaps model) <= CEILMAX.
Proof. pose proof (APS.co_top _ _ _ _ _ _ _ _ _ _ _ H) as X. unfold TOP in X. exact X. Qed.
Lemma co_sp0 : alloc_top (m_vmmaps model) = bv_unsigned (edenot E e_sp0_early) - 8388608.
Proof. pose proof (APS.co_sp0 _ _ _ _ _ _ _ _ _ _ _ H) as X. unfold TOP in X. exact X. Qed.
(* [comment removed for export] *)
Lemma co_isp : bv_unsigned (vm_init_sp (m_vmmaps model)) = ISP /\ uE E e_sp0_early = ISP.
Proof.
  pose proof co_sp0 as X. pose proof (proj2 HC) as Y. unfold alloc_top, stack_max_size in X. unfold uE. split; [exact Y | lia].
Qed.
End S.

(* [comment removed for export] *)
Definition argH_high1 (argH : env -> word -> bool) (ISP : Z)
  (argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a) :
  forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a :=
  fun E a H => proj1 (argH_high E a H).
(* [comment removed for export] *)
Lemma cs_ok_agree (segs : list Segment) (A : atable) (nx0 : nat) (Lim : Z)
  (NX0_spw : expr_vars_lt nx0 e_sp0_early = true)
  (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (ISP : Z)
  (argH_agree : forall E E' (a : word), AxSymRun3.env_agree nx0 E E' -> argH E a = argH E' a)
  (SINV_agree : forall E E' M, AxSymRun3.env_agree nx0 E E' -> SINV E M -> SINV E' M)
  (FS0 : Fs.Fs) (E E' : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) :
  AxSymRun3.env_agree (nxt cs) E E' -> fresh_ok nx0 cs = true ->
  cs_ok segs A Lim SINV argH ISP FS0 E cs R FULL model -> cs_ok segs A Lim SINV argH ISP FS0 E' cs R FULL model.
Proof.
  intros Hag Hf [HC HI]. split; [|exact HI].
  exact (APS.cs_ok_agree segs A nx0 Lim SINV argH NX0_spw argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hf HC).
Qed.
End CXI.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import RelSpec RelSpecMremap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg EdDefs Bridge.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache.

Definition nstep (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  match node_input n with
  | Some i => evs = [] /\ syscall_spec i mo (Ok eff mo' evs) /\ ~ spurious_refusal_cfg fcfg i mo eff
  | None => False
  end.

Definition nexit (n : node) (mo : Model) (code : word) (mo' : Model) : Prop :=
  match n with
  | NExit c => code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) /\ mo' = with_halted code mo
  | _ => False
  end.

Definition minv (mo : Model) : Prop := m_vm_lazy mo = [].

Lemma minv_init : forall reserved brk mbase lim sp inp, minv (init_model reserved brk mbase lim sp inp).
Proof. intros; reflexivity. Qed.

Definition mmap_rw_shape (prot flags : word) : Prop :=
  mmap_modeled_b prot flags (Z_to_bv 64 0) = true.
Definition mmap_none_shape (prot flags : word) : Prop :=
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = true.
Definition mmap_fixed_shape (addr len prot flags : word) (h : VmMaps) : Prop :=
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b prot flags (Z_to_bv 64 0) = true
  /\ bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= alloc_top h
  /\ bv_unsigned addr mod page_size = 0
  /\ 0 < bv_unsigned addr
  /\ region_free (vm_reserved h) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
  /\ map_contains (vm_maps h) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true.

Definition nsafe (n : node) (mo : Model) : Prop :=
  let h := m_vmmaps mo in
  match n with
  | NBrk _ => True
  | NMmap addr len prot flags =>
      let A := Z_to_bv 64 addr in let L := Z_to_bv 64 len in let P := Z_to_bv 64 prot in let FL := Z_to_bv 64 flags in
      w_is0 L = false /\ mmap_noreserve_b FL = false /\ mmap_anon_b FL = true
      /\ (mmap_rw_shape P FL \/ mmap_none_shape P FL \/ mmap_fixed_shape A L P FL h)
  | NMunmap addr len =>
      let A := Z_to_bv 64 addr in let L := Z_to_bv 64 len in
      bv_unsigned A mod page_size = 0 /\ w_is0 L = false
      /\ bv_unsigned A + page_round_up_Z (bv_unsigned L) <= TASK_SIZE
      /\ map_has (vm_maps h) A (Z_to_bv 64 (page_round_up_Z (bv_unsigned L))) = true
  | NMprotect addr len prot =>
      let A := Z_to_bv 64 addr in let L := Z_to_bv 64 len in let P := Z_to_bv 64 prot in
      mprotect_grows_conflict_b P = false /\ bv_unsigned A mod page_size = 0 /\ w_is0 L = false
      /\ bv_unsigned A + page_round_up_Z (bv_unsigned L) < two_pow_64
      /\ mprotect_modeled_b P = true
      /\ map_contains (vm_noaccess h) A (Z_to_bv 64 (page_round_up_Z (bv_unsigned L))) = true
      /\ map_contains (vm_maps h) A (Z_to_bv 64 (page_round_up_Z (bv_unsigned L))) = true
  | NMremap old osz nsz =>
      let OLD := Z_to_bv 64 old in let OSZ := Z_to_bv 64 osz in let NSZ := Z_to_bv 64 nsz in
      let old_nZ := page_round_up_Z (bv_unsigned OSZ) in let old_n := Z_to_bv 64 old_nZ in
      bv_unsigned OLD mod page_size = 0 /\ page_align_is0_b NSZ = false /\ page_align_is0_b OSZ = false
      /\ mremap_source_b h OLD old_n old_nZ = true /\ mremap_backing_uniform_b mo OLD old_n = true
  | _ => False
  end.

Lemma abi_low32_small : forall z, 0 <= z < 2^32 -> abi_low32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold abi_low32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma w_is0_lit : forall z, 0 <= z < 2^64 -> w_is0 (Z_to_bv 64 z) = (z =? 0).
Proof. intros z Hz. unfold w_is0, bv_eqb. rewrite unsigned_lit by lia. reflexivity. Qed.

Definition vm_same_consts (h h' : VmMaps) : Prop :=
  vm_reserved h' = vm_reserved h /\ vm_start_brk h' = vm_start_brk h /\ vm_limit h' = vm_limit h
  /\ vm_mmap_base h' = vm_mmap_base h /\ vm_init_sp h' = vm_init_sp h.

Definition vm_only (m m' : Model) : Prop :=
  m' = mkModelOf (m_fd m) (m_vm m') (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m)
  /\ vm_same_consts (m_vmmaps m) (m_vmmaps m')
  /\ (m_vm_lazy m = [] -> m_vm_lazy m' = [])
  /\ (m_vm_materialized m = [] -> m_vm_materialized m' = []).

Lemma vm_same_consts_refl h : vm_same_consts h h. Proof. repeat split; reflexivity. Qed.
Lemma vm_same_consts_trans a b c : vm_same_consts a b -> vm_same_consts b c -> vm_same_consts a c.
Proof. intros (?&?&?&?&?) (?&?&?&?&?). unfold vm_same_consts. repeat split; congruence. Qed.

Lemma vm_only_fields m m' : vm_only m m' ->
  m_fds m' = m_fds m /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\ m_tid m' = m_tid m /\ m_stdin m' = m_stdin m.
Proof. intros (E & _ & _). rewrite E. repeat split; reflexivity. Qed.
Lemma vm_only_but_vm m m' : vm_only m m' ->
  m' = mkModelOf (m_fd m) (m_vm m') (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).
Proof. intros (E & _). exact E. Qed.
Lemma vm_only_consts m m' : vm_only m m' -> vm_same_consts (m_vmmaps m) (m_vmmaps m').
Proof. intros (_ & E & _). exact E. Qed.
Lemma vm_only_init_sp m m' : vm_only m m' -> vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
Proof. intros (_ & (_&_&_&_&E) & _). exact E. Qed.
Lemma vm_only_alloc_top m m' : vm_only m m' -> alloc_top (m_vmmaps m') = alloc_top (m_vmmaps m).
Proof. intros H. unfold alloc_top. rewrite (vm_only_init_sp _ _ H). reflexivity. Qed.
Lemma vm_only_lazy m m' : vm_only m m' -> m_vm_lazy m = [] -> m_vm_lazy m' = [].
Proof. intros (_ & _ & L & _). exact L. Qed.
Lemma vm_only_materialized m m' : vm_only m m' -> m_vm_materialized m = [] -> m_vm_materialized m' = [].
Proof. intros (_ & _ & _ & L). exact L. Qed.

Lemma vm_only_refl m : vm_only m m.
Proof. split; [destruct m; reflexivity|]. split; [apply vm_same_consts_refl|]. split; intros L; exact L. Qed.
Lemma vm_only_trans a b c : vm_only a b -> vm_only b c -> vm_only a c.
Proof.
  intros (E1 & S1 & L1 & M1) (E2 & S2 & L2 & M2). split; [| split; [eapply vm_same_consts_trans; eassumption| split; tauto]].
  rewrite E2 at 1. rewrite E1. reflexivity.
Qed.
Lemma vm_only_with_vmmaps m h : vm_same_consts (m_vmmaps m) h -> vm_only m (with_vmmaps h m).
Proof. intros E. split; [reflexivity|]. split; [exact E| split; intros L; exact L]. Qed.
Lemma vm_only_with_vm_backing m l mt :
  (m_vm_lazy m = [] -> l = []) -> (m_vm_materialized m = [] -> mt = []) -> vm_only m (with_vm_backing l mt m).
Proof. intros HL HM. split; [reflexivity|]. split; [apply vm_same_consts_refl| split; [exact HL| exact HM]]. Qed.
Lemma filter_nil_eq {A} (f : A -> bool) (l : list A) : l = [] -> List.filter f l = [].
Proof. intros ->. reflexivity. Qed.
Lemma vm_only_vm_forget_range m lo hi : vm_only m (vm_forget_range lo hi m).
Proof. apply vm_only_with_vm_backing; [intros E; rewrite E; reflexivity| apply filter_nil_eq]. Qed.
Lemma vm_only_forget_vm_ranges rs : forall m, vm_only m (forget_vm_ranges rs m).
Proof. induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]. apply vm_only_refl. eapply vm_only_trans; [apply vm_only_vm_forget_range| apply IH]. Qed.
Lemma vm_only_with_brk_next m req r : vm_only m (with_brk_next m req r).
Proof. unfold with_brk_next. eapply vm_only_trans; [| apply vm_only_forget_vm_ranges]. apply vm_only_with_vmmaps; repeat split; reflexivity. Qed.
Lemma with_mmap_backing_noreserve_false : forall flags a n mo,
  mmap_noreserve_b flags = false -> with_mmap_backing flags a n mo = mo.
Proof. intros flags a n mo H. unfold with_mmap_backing. rewrite H. reflexivity. Qed.
Lemma vm_only_with_mmap_backing m f a n : mmap_noreserve_b f = false -> vm_only m (with_mmap_backing f a n m).
Proof. intros Hf. unfold with_mmap_backing. rewrite Hf. apply vm_only_refl. Qed.
Lemma vm_only_with_mmap_replacement m f a n : mmap_noreserve_b f = false -> vm_only m (with_mmap_replacement f a n m).
Proof. intros Hf. unfold with_mmap_replacement. eapply vm_only_trans; [apply vm_only_vm_forget_range| apply vm_only_with_mmap_backing; exact Hf]. Qed.
Lemma vm_only_with_mmap_destroyed m a n h : vm_same_consts (m_vmmaps m) h -> vm_only m (with_mmap_destroyed a n h m).
Proof. intros E. unfold with_mmap_destroyed. eapply vm_only_trans; [apply vm_only_with_vmmaps; exact E| apply vm_only_vm_forget_range]. Qed.
Lemma vm_only_mprotect_model_next m a n : vm_only m (mprotect_model_next m a n).
Proof. apply vm_only_with_vmmaps. repeat split; reflexivity. Qed.

Lemma m_vmmaps_with_vmmaps h m : m_vmmaps (with_vmmaps h m) = h. Proof. reflexivity. Qed.
Lemma m_vmmaps_with_vm_backing l mt m : m_vmmaps (with_vm_backing l mt m) = m_vmmaps m. Proof. reflexivity. Qed.
Lemma m_vmmaps_vm_forget_range lo hi m : m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m. Proof. reflexivity. Qed.
Lemma m_vmmaps_forget_vm_ranges rs : forall m, m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m.
Proof. induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma m_vmmaps_with_brk_next m req r : m_vmmaps (with_brk_next m req r) = brk_model_next (m_vmmaps m) req r.
Proof. unfold with_brk_next. rewrite m_vmmaps_forget_vm_ranges. reflexivity. Qed.
Lemma m_vmmaps_vm_add_lazy a n m : m_vmmaps (vm_add_lazy a n m) = m_vmmaps m. Proof. reflexivity. Qed.
Lemma m_vmmaps_with_mmap_backing f a n m : m_vmmaps (with_mmap_backing f a n m) = m_vmmaps m.
Proof. unfold with_mmap_backing. destruct (mmap_noreserve_b f); reflexivity. Qed.
Lemma m_vmmaps_with_mmap_destroyed a n h m : m_vmmaps (with_mmap_destroyed a n h m) = h. Proof. reflexivity. Qed.
Lemma m_vmmaps_mprotect_model_next m a n : m_vmmaps (mprotect_model_next m a n) =
  mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
    (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof. reflexivity. Qed.

Lemma vmo_vmmaps m x h : vm_same_consts (m_vmmaps x) h -> vm_only m x -> vm_only m (with_vmmaps h x).
Proof. intros; eapply vm_only_trans; [eassumption| apply vm_only_with_vmmaps; assumption]. Qed.
Lemma vmo_forget m x lo hi : vm_only m x -> vm_only m (vm_forget_range lo hi x). Proof. intros; eapply vm_only_trans; [eassumption| apply vm_only_vm_forget_range]. Qed.
Lemma vmo_forgets m x rs : vm_only m x -> vm_only m (forget_vm_ranges rs x). Proof. intros; eapply vm_only_trans; [eassumption| apply vm_only_forget_vm_ranges]. Qed.
Lemma vmo_brk m x req r : vm_only m x -> vm_only m (with_brk_next x req r). Proof. intros; eapply vm_only_trans; [eassumption| apply vm_only_with_brk_next]. Qed.
Lemma vmo_mbacking m x f a n : mmap_noreserve_b f = false -> vm_only m x -> vm_only m (with_mmap_backing f a n x).
Proof. intros; eapply vm_only_trans; [eassumption| apply vm_only_with_mmap_backing; assumption]. Qed.
Lemma vmo_mrepl m x f a n : mmap_noreserve_b f = false -> vm_only m x -> vm_only m (with_mmap_replacement f a n x).
Proof. intros; eapply vm_only_trans; [eassumption| apply vm_only_with_mmap_replacement; assumption]. Qed.
Lemma vmo_mdestr m x a n h : vm_same_consts (m_vmmaps x) h -> vm_only m x -> vm_only m (with_mmap_destroyed a n h x).
Proof. intros; eapply vm_only_trans; [eassumption| apply vm_only_with_mmap_destroyed; assumption]. Qed.
Lemma vmo_mprot m x a n : vm_only m x -> vm_only m (mprotect_model_next x a n). Proof. intros; eapply vm_only_trans; [eassumption| apply vm_only_mprotect_model_next]. Qed.
Lemma vmo_resize m x sl o on d nn : (m_vm_lazy x = [] -> sl = false) -> vm_only m x -> vm_only m (vm_resize_backing sl o on d nn x).
Proof.
  intros Hsl H; eapply vm_only_trans; [eassumption|]. unfold vm_resize_backing. apply vm_only_with_vm_backing.
  - intros L. rewrite (Hsl L), L. reflexivity.
  - intros M. rewrite M. cbn [List.filter List.map]. destruct sl; reflexivity.
Qed.
Lemma vmo_mremap m x o on d nn : vm_only m x -> vm_only m (mremap_model_next x o on d nn).
Proof.
  intros H; eapply vm_only_trans; [eassumption|]. unfold mremap_model_next. apply vmo_resize.
  - intros L. unfold mremap_source_lazy_b. change (m_vm_lazy (with_vmmaps (mremap_maps_next (m_vmmaps x) o d nn) x)) with (m_vm_lazy x) in L.
    rewrite L. reflexivity.
  - apply vm_only_with_vmmaps. repeat split; reflexivity.
Qed.

Create HintDb vm_only.
#[global] Hint Resolve vm_only_refl vmo_vmmaps vmo_forget vmo_forgets vmo_brk vmo_mbacking vmo_mrepl
  vmo_mdestr vmo_mprot vmo_resize vmo_mremap : vm_only.
#[global] Hint Extern 1 (vm_same_consts _ _) => (repeat split; reflexivity) : vm_only.
#[global] Hint Extern 1 (mmap_noreserve_b _ = false) => first [assumption | reflexivity] : vm_only.
#[global] Hint Extern 1 (m_vm_lazy _ = [] -> _ = false) => (intros; first [assumption | reflexivity]) : vm_only.

Ltac vm_only_done := solve [ eauto 12 with vm_only ].

Lemma minv_vm_only : forall mo mo', vm_only mo mo' -> minv mo -> minv mo'.
Proof. intros mo mo' H L. exact (vm_only_lazy mo mo' H L). Qed.

Ltac open_nstep lem :=
  cbn [nstep node_input];
  match goal with |- context [syscall_spec ?i _ _] => rewrite (lem i _ _ eq_refl) end;
  cbn [in_arg in_args pure_input nth].
Ltac open_nstep_in lem H :=
  cbn [nstep node_input] in H;
  match type of H with context [syscall_spec ?i _ _] => rewrite (lem i _ _ eq_refl) in H end;
  cbn [in_arg in_args pure_input nth] in H.

Lemma nonspur_forced_iff : forall i m eff,
  In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   (refusal_b i m (eff_ret eff) = true ->
    forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true)).
Proof.
  intros i m eff Ha. split.
  - intros Hns Hr. exact (fcfg_nonspur_refusal_forced i m eff Ha Hr Hns).
  - intros H. destruct (refusal_b i m (eff_ret eff)) eqn:E.
    + apply fcfg_forced_nonspur. exact (H eq_refl).
    + apply fcfg_nonref_nonspur. exact E.
Qed.

Lemma refusal_b_enomem : forall i m r, In (bv_unsigned (in_sysno i)) [216; 222; 226] ->
  refusal_b i m r = bv_eqb r (errno_ret ENOMEM).
Proof.
  intros i m r Hin. unfold refusal_b. cbv zeta.
  destruct Hin as [E|[E|[E|[]]]]; rewrite <- E;
    change (bv_eqb r (errno_ret ENOMEM) || false = bv_eqb r (errno_ret ENOMEM)); apply orb_false_r.
Qed.

Lemma bv_eqb_enomem_small : forall (r : word), bv_unsigned r < two_pow_64 - 4095 ->
  bv_eqb r (errno_ret ENOMEM) = false.
Proof.
  intros r H. destruct (bv_eqb r (errno_ret ENOMEM)) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. subst r. rewrite errno_ret_unsigned in H by (unfold ENOMEM; lia). unfold ENOMEM in H. lia.
Qed.

Lemma enomem_refusal : forall i m, In (bv_unsigned (in_sysno i)) [216; 222; 226] ->
  refusal_b i m (errno_ret ENOMEM) = true.
Proof. intros i m Hin. rewrite (refusal_b_enomem i m _ Hin). apply bv_eqb_refl. Qed.

Lemma grant_not_refusal : forall i m (a : word) nZ, In (bv_unsigned (in_sysno i)) [216; 222; 226] ->
  0 <= nZ -> bv_unsigned a + nZ <= alloc_top (m_vmmaps m) -> refusal_b i m a = false.
Proof.
  intros i m a nZ Hin Hn Ha. rewrite (refusal_b_enomem i m a Hin). apply bv_eqb_enomem_small.
  pose proof (alloc_top_room (m_vmmaps m)) as Ht. unfold stack_max_size in Ht. lia.
Qed.

Lemma len_nZ_nonneg : forall len, 0 <= page_round_up_Z (bv_unsigned (Z_to_bv 64 len)).
Proof. intros len. apply page_round_up_Z_nonneg. pose proof (word_unsigned_range (Z_to_bv 64 len)). lia. Qed.

Lemma nstep_brk_inv : forall req mo eff mo' evs,
  nstep (NBrk req) mo eff mo' evs <->
  exists r, brk_r_ok mo (Z_to_bv 64 req) r = true
    /\ (brk_refusal_b mo (Z_to_bv 64 req) r = true ->
        forall r', brk_r_ok mo (Z_to_bv 64 req) r' = true -> brk_refusal_b mo (Z_to_bv 64 req) r' = true)
    /\ eff = mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk (m_vmmaps mo))) (brk_unmaps r (vm_brk (m_vmmaps mo))) [] []
    /\ mo' = with_brk_next mo (Z_to_bv 64 req) r /\ evs = [].
Proof.
  intros req mo eff mo' evs. cbn [nstep node_input].
  set (i := pure_input 214 [Z_to_bv 64 req]).
  assert (HS : forall o, syscall_spec i mo o <->
    exists r, brk_r_ok mo (Z_to_bv 64 req) r = true
      /\ o = Ok (mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk (m_vmmaps mo)))
                    (brk_unmaps r (vm_brk (m_vmmaps mo))) [] []) (with_brk_next mo (Z_to_bv 64 req) r) []).
  { intros o. rewrite (syscall_spec_214 i mo o eq_refl). apply brk_outcome. }
  rewrite (nonspur_forced_iff i mo eff (or_introl eq_refl)). split.
  - intros (-> & Hs & Hns). apply HS in Hs as (r & Hr & E). apply Ok_inj in E as (-> & -> & _).
    exists r. split; [exact Hr|]. split; [|repeat split].
    intros Hrr r' Hr'.
    refine (Hns Hrr (mkEffectU r' [] (brk_zeros (Z_to_bv 64 req) r' (vm_brk (m_vmmaps mo)))
                       (brk_unmaps r' (vm_brk (m_vmmaps mo))) [] []) (with_brk_next mo (Z_to_bv 64 req) r') [] _).
    apply HS. exists r'. split; [exact Hr' | reflexivity].
  - intros (r & Hr & Hf & -> & -> & ->). split; [reflexivity|]. split; [apply HS; exists r; split; [exact Hr | reflexivity]|].
    intros Hrr eff' m' evs' Hs. apply HS in Hs as (r' & Hr' & E). apply Ok_inj in E as (-> & _ & _).
    exact (Hf Hrr r' Hr').
Qed.

Lemma nstep_mmap_rw_inv : forall addr len mo eff mo' evs,
  w_is0 (Z_to_bv 64 len) = false ->
  let h := m_vmmaps mo in
  let nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) in let n := Z_to_bv 64 nZ in
  nstep (NMmap addr len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo eff mo' evs <->
  evs = [] /\
  ( (exists e, In e (mmap_errnos_when (mmap_grant_refusable (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) mo nZ)) /\ eff = mkEffect (errno_ret e) [] [] /\ mo' = mo)
  \/ exists a, ((bv_unsigned a mod page_size = 0) /\ (0 < bv_unsigned a) /\ (bv_unsigned a + nZ <= alloc_top h)
                /\ region_free (vm_reserved h ++ vm_maps h) a n = true
                /\ mmap_noreserve_backed_ok (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) mo nZ = true)
               /\ eff = mkEffect a [] [(a, n)]
               /\ mo' = with_mmap_backing (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) a n
                          (with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
                             (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo) ).
Proof.
  intros addr len mo eff mo' evs Hlen h nZ n. open_nstep syscall_spec_222.
  match goal with |- context [mmap_spec ?a ?l ?p ?f ?fd ?off ?i ?m ?o] => rewrite (mmap_rw_outcome a l p f fd off i m o eq_refl eq_refl Hlen eq_refl) end.
  match goal with |- context [spurious_refusal_cfg fcfg ?i _ _] => set (si := i) end.
  assert (H222 : In (bv_unsigned (in_sysno si)) [216; 222; 226]) by (right; left; reflexivity).
  rewrite (mmap_rw_nonspur si mo eff eq_refl eq_refl eq_refl Hlen eq_refl).
  unfold mmap_err_out. fold h. split.
  - intros (-> & [(e & He & E) | (a & Ha & E)] & Hns); apply Ok_inj in E as (-> & -> & _).
    + split; [reflexivity|]. left. exists e. split; [|split; reflexivity].
      destruct He as [<-|[]].
      assert (RF : mmap_grant_refusable (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) mo nZ = true)
        by exact (Hns (enomem_refusal si mo H222)).
      rewrite RF. left. reflexivity.
    + split; [reflexivity|]. right. exists a. split; [exact Ha | split; reflexivity].
  - intros (-> & [(e & He & -> & ->) | (a & Ha & -> & ->)]).
    + destruct (mmap_grant_refusable (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) mo nZ) eqn:RF; [|destruct He].
      split; [reflexivity|]. split; [left; exists e; split; [exact He | reflexivity]|].
      intros _. exact RF.
    + split; [reflexivity|]. split; [right; exists a; split; [exact Ha | reflexivity]|].
      intros Hr. exfalso. destruct Ha as (_ & _ & Ha3 & _).
      assert (G : refusal_b si mo (eff_ret (mkEffect a [] [(a, n)])) = false)
        by exact (grant_not_refusal si mo a nZ H222 (len_nZ_nonneg len) Ha3).
      congruence.
Qed.

Lemma nstep_mmap_none_inv : forall addr len mo eff mo' evs,
  w_is0 (Z_to_bv 64 len) = false ->
  let h := m_vmmaps mo in
  let nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) in let n := Z_to_bv 64 nZ in
  nstep (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo eff mo' evs <->
  evs = [] /\
  ( (exists e, In e (mmap_errnos_when (mmap_reserve_refusable mo nZ)) /\ eff = mkEffect (errno_ret e) [] [] /\ mo' = mo)
  \/ exists a, ((bv_unsigned a mod page_size = 0) /\ (0 < bv_unsigned a) /\ (bv_unsigned a + nZ <= alloc_top h)
                /\ region_free (vm_reserved h ++ vm_maps h) a n = true)
               /\ eff = mkEffectU a [] [] [(a, n)] [] []
               /\ mo' = with_mmap_backing (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) a n
                          (with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
                             ((a, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo) ).
Proof.
  intros addr len mo eff mo' evs Hlen h nZ n. open_nstep syscall_spec_222.
  match goal with |- context [mmap_spec ?a ?l ?p ?f ?fd ?off ?i ?m ?o] => rewrite (mmap_noaccess_outcome a l p f fd off i m o eq_refl eq_refl Hlen eq_refl eq_refl) end.
  match goal with |- context [spurious_refusal_cfg fcfg ?i _ _] => set (si := i) end.
  assert (H222 : In (bv_unsigned (in_sysno si)) [216; 222; 226]) by (right; left; reflexivity).
  rewrite (mmap_reserve_nonspur si mo eff eq_refl eq_refl eq_refl Hlen eq_refl eq_refl).
  unfold mmap_err_out. fold h. split.
  - intros (-> & [(e & He & E) | (a & Ha & E)] & Hns); apply Ok_inj in E as (-> & -> & _).
    + split; [reflexivity|]. left. exists e. split; [|split; reflexivity].
      destruct He as [<-|[]].
      assert (RF : mmap_reserve_refusable mo nZ = true) by exact (Hns (enomem_refusal si mo H222)).
      rewrite RF. left. reflexivity.
    + split; [reflexivity|]. right. exists a. split; [exact Ha | split; reflexivity].
  - intros (-> & [(e & He & -> & ->) | (a & Ha & -> & ->)]).
    + destruct (mmap_reserve_refusable mo nZ) eqn:RF; [|destruct He].
      split; [reflexivity|]. split; [left; exists e; split; [exact He | reflexivity]|].
      intros _. exact RF.
    + split; [reflexivity|]. split; [right; exists a; split; [exact Ha | reflexivity]|].
      intros Hr. exfalso. destruct Ha as (_ & _ & Ha3 & _).
      assert (G : refusal_b si mo (eff_ret (mkEffectU a [] [] [(a, n)] [] [])) = false)
        by exact (grant_not_refusal si mo a nZ H222 (len_nZ_nonneg len) Ha3).
      congruence.
Qed.

Lemma nstep_mmap_fixed_inv0 : forall addr len mo eff mo' evs,
  let A := Z_to_bv 64 addr in let h := m_vmmaps mo in
  let nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) in let n := Z_to_bv 64 nZ in
  w_is0 (Z_to_bv 64 len) = false ->
  bv_unsigned A + nZ <= alloc_top h -> bv_unsigned A mod page_size = 0 -> 0 < bv_unsigned A ->
  region_free (vm_reserved h) A n = true -> map_contains (vm_maps h) A n = true ->
  nstep (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)) mo eff mo' evs <->
  evs = [] /\
  ( (exists e, In e (mmap_errnos_when false) /\ eff = mkEffect (errno_ret e) [] [] /\ mo' = mo)
  \/ (eff = mkEffectU A [] [] [(A, n)] [] []
      /\ mo' = with_mmap_replacement (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)) A n
                (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
                   ((A, n) :: maps_subtract (vm_noaccess h) (bv_unsigned A) (bv_unsigned A + bv_unsigned n))
                   (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo))
  \/ (exists e, In e mmap_destructive_errnos /\ eff = mkEffectU (errno_ret e) [] [] [(A, n)] [] []
      /\ mo' = with_mmap_destroyed A n
                 (mkVmMapsFull (vm_reserved h)
                   (maps_subtract (vm_maps h) (bv_unsigned A) (bv_unsigned A + bv_unsigned n))
                   (maps_subtract (vm_noaccess h) (bv_unsigned A) (bv_unsigned A + bv_unsigned n))
                   (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo) ).
Proof.
  intros addr len mo eff mo' evs A h nZ n Hlen Hc Hal Hpos Hrf Hmc. open_nstep syscall_spec_222.
  fold A. match goal with |- context [mmap_spec ?a ?l ?p ?f ?fd ?off ?i ?m ?o] => rewrite (mmap_fixed_noaccess_outcome a l p f fd off i m o eq_refl eq_refl Hlen eq_refl eq_refl eq_refl Hc Hal Hpos Hrf Hmc) end.
  match goal with |- context [spurious_refusal_cfg fcfg ?i _ _] => set (si := i) end.
  assert (H222 : In (bv_unsigned (in_sysno si)) [216; 222; 226]) by (right; left; reflexivity).
  rewrite (mmap_fixed_noaccess_nonspur si mo eff eq_refl eq_refl eq_refl Hlen eq_refl eq_refl eq_refl Hc Hal Hpos Hrf Hmc).
  unfold mmap_err_out. fold h. split.
  - intros (-> & [(e & He & E) | [E | (e & He & E)]] & Hns); apply Ok_inj in E as (-> & -> & _).
    + exfalso. destruct He as [<-|[]]. cbn [eff_ret] in Hns.
      rewrite (enomem_refusal si mo H222) in Hns. discriminate Hns.
    + split; [reflexivity|]. right; left. split; reflexivity.
    + exfalso. destruct He as [<-|[]]. cbn [eff_ret] in Hns.
      rewrite (enomem_refusal si mo H222) in Hns. discriminate Hns.
  - intros (-> & [(e & He & -> & ->) | [(-> & ->) | (e & He & -> & ->)]]).
    + destruct He.
    + split; [reflexivity|]. split; [right; left; reflexivity|].
      exact (grant_not_refusal si mo A nZ H222 (len_nZ_nonneg len) Hc).
    + destruct He.
Qed.

Lemma nstep_munmap_inv : forall addr len mo eff mo' evs,
  let A := Z_to_bv 64 addr in let L := Z_to_bv 64 len in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned L)) in
  bv_unsigned A mod page_size = 0 -> w_is0 L = false -> bv_unsigned A + page_round_up_Z (bv_unsigned L) <= TASK_SIZE ->
  map_has (vm_maps (m_vmmaps mo)) A n = true ->
  nstep (NMunmap addr len) mo eff mo' evs <->
  evs = [] /\ eff = mkEffectU (Z_to_bv 64 0) [] [] [(A, n)] [] []
  /\ mo' = with_mmap_destroyed A n
             (mkVmMapsFull (vm_reserved (m_vmmaps mo)) (map_remove (vm_maps (m_vmmaps mo)) A)
                (maps_subtract (vm_noaccess (m_vmmaps mo)) (bv_unsigned A) (bv_unsigned A + bv_unsigned n))
                (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))) mo.
Proof.
  intros addr len mo eff mo' evs A L n Hal Hlen Hnw Hhas. open_nstep syscall_spec_215.
  fold A L. match goal with |- context [munmap_spec ?a ?l ?i ?m ?o] => rewrite (munmap_exact_outcome a l i m o Hal Hlen Hnw Hhas) end. split.
  - intros [-> [E _]]. apply Ok_inj in E as (-> & -> & _). auto.
  - intros (-> & -> & ->). split; [reflexivity|]. split; [reflexivity|].
    apply fcfg_nonalloc_nonspur, (nonalloc_lit 215); [lia | reflexivity].
Qed.

Lemma nstep_mprotect_inv : forall addr len prot mo eff mo' evs,
  let A := Z_to_bv 64 addr in let L := Z_to_bv 64 len in let P := Z_to_bv 64 prot in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned L)) in
  mprotect_grows_conflict_b P = false -> bv_unsigned A mod page_size = 0 -> w_is0 L = false ->
  bv_unsigned A + page_round_up_Z (bv_unsigned L) < two_pow_64 -> mprotect_modeled_b P = true ->
  map_contains (vm_noaccess (m_vmmaps mo)) A n = true -> map_contains (vm_maps (m_vmmaps mo)) A n = true ->
  nstep (NMprotect addr len prot) mo eff mo' evs <->
  evs = [] /\
  ( (exists e, In e (mprotect_errnos_when (mprotect_refusable mo A n)) /\ eff = mkEffect (errno_ret e) [] [] /\ mo' = mo)
  \/ (mprotect_budget_ok mo A n = true /\ eff = mkEffect (Z_to_bv 64 0) [] [(A, n)] /\ mo' = mprotect_model_next mo A n) ).
Proof.
  intros addr len prot mo eff mo' evs A L P n Hgc Hal Hlen Hnw Hmod Hna Hma. open_nstep syscall_spec_226.
  fold A L P. match goal with |- context [mprotect_spec ?a ?l ?pr ?i ?m ?o] => rewrite (mprotect_expose_outcome a l pr i m o Hgc Hal Hlen Hnw Hmod Hna Hma) end.
  match goal with |- context [spurious_refusal_cfg fcfg ?i _ _] => set (si := i) end.
  assert (H226 : In (bv_unsigned (in_sysno si)) [216; 222; 226]) by (right; right; left; reflexivity).
  rewrite (mprotect_expose_nonspur si mo eff eq_refl Hgc Hal Hlen Hnw Hmod Hna Hma). split.
  - intros (-> & [(e & He & E) | (Hb & E)] & Hns); apply Ok_inj in E as (-> & -> & _).
    + split; [reflexivity|]. left. exists e. split; [|split; reflexivity].
      destruct He as [<-|[]].
      assert (RF : mprotect_refusable mo A n = true) by exact (Hns (enomem_refusal si mo H226)).
      rewrite RF. left. reflexivity.
    + split; [reflexivity|]. right. split; [exact Hb | split; reflexivity].
  - intros (-> & [(e & He & -> & ->) | (Hb & -> & ->)]).
    + destruct (mprotect_refusable mo A n) eqn:RF; [|destruct He].
      split; [reflexivity|]. split; [left; exists e; split; [exact He | reflexivity]|].
      intros _. exact RF.
    + split; [reflexivity|]. split; [right; split; [exact Hb | reflexivity]|].
      intros Hr. exfalso. cbn [eff_ret] in Hr.
      rewrite (refusal_b_enomem si mo _ H226), bv_eqb_enomem_small in Hr; [discriminate Hr|].
      rewrite unsigned_lit by lia. unfold two_pow_64. lia.
Qed.

Lemma nstep_mremap_inv : forall old osz nsz mo eff mo' evs,
  let OLD := Z_to_bv 64 old in let OSZ := Z_to_bv 64 osz in let NSZ := Z_to_bv 64 nsz in
  let old_nZ := page_round_up_Z (bv_unsigned OSZ) in let old_n := Z_to_bv 64 old_nZ in
  bv_unsigned OLD mod page_size = 0 -> page_align_is0_b NSZ = false -> page_align_is0_b OSZ = false ->
  mremap_source_b (m_vmmaps mo) OLD old_n old_nZ = true -> mremap_backing_uniform_b mo OLD old_n = true ->
  nstep (NMremap old osz nsz) mo eff mo' evs <->
  evs = [] /\ mremap_out OLD OSZ NSZ mo (Ok eff mo' evs)
  /\ (bv_eqb (eff_ret eff) (errno_ret ENOMEM) = true ->
      forall eff' m' evs', mremap_out OLD OSZ NSZ mo (Ok eff' m' evs') -> bv_eqb (eff_ret eff') (errno_ret ENOMEM) = true).
Proof.
  intros old osz nsz mo eff mo' evs OLD OSZ NSZ old_nZ old_n Hal Hn Ho Hsrc Hbk. cbn [nstep node_input].
  set (i := pure_input 216 [Z_to_bv 64 old; Z_to_bv 64 osz; Z_to_bv 64 nsz; Z_to_bv 64 1; Z_to_bv 64 0]).
  assert (HS : forall o, syscall_spec i mo o <-> mremap_out OLD OSZ NSZ mo o).
  { intros o. rewrite (syscall_spec_216 i mo o eq_refl).
    exact (mremap_maymove_outcome OLD OSZ NSZ (Z_to_bv 64 1) i mo o eq_refl Hal Hn Ho Hsrc Hbk). }
  assert (HR : forall r, refusal_b i mo r = bv_eqb r (errno_ret ENOMEM))
    by (intros r; apply refusal_b_enomem; left; reflexivity).
  rewrite (nonspur_forced_iff i mo eff (or_intror (or_introl eq_refl))), HS, HR. split.
  - intros (Hevs & Hs & Hns). split; [exact Hevs|]. split; [exact Hs|].
    intros Hr eff' m' evs' Hs'. rewrite <- HR. apply (Hns Hr eff' m' evs'). apply HS. exact Hs'.
  - intros (Hevs & Hs & Hns). split; [exact Hevs|]. split; [exact Hs|].
    intros Hr eff' m' evs' Hs'. rewrite HR. apply (Hns Hr eff' m' evs'). apply HS. exact Hs'.
Qed.

Lemma nstep_nsafe_vm_only : forall n mo eff mo' evs,
  nsafe n mo -> nstep n mo eff mo' evs -> vm_only mo mo' /\ evs = [].
Proof.
  intros n mo eff mo' evs Hs H. destruct n; cbn [nsafe] in Hs; cbv zeta in Hs; try contradiction.
  - apply nstep_brk_inv in H as (r & _ & _ & _ & -> & ->). split; [vm_only_done| reflexivity].
  - cbv zeta in Hs. unfold mmap_rw_shape, mmap_none_shape, mmap_fixed_shape in Hs.
    destruct Hs as (Hl & Hnr & Han & [Hm|[[Hm Hn]|(Hm & Hn & Hf & Hc & Hal & Hp & Hrf & Hmc)]]);
      (destruct H as [-> [H _]]; open_nstep_in syscall_spec_222 H).
    + match type of H with context [mmap_spec ?a ?l ?p ?f ?fd ?off ?i ?m ?o] => rewrite (mmap_rw_outcome a l p f fd off i m o eq_refl Han Hl Hm) in H end. unfold mmap_err_out in H.
      destruct H as [(e & _ & E)|(a & _ & E)]; apply Ok_inj in E as (-> & -> & _); (split; [vm_only_done|reflexivity]).
    + match type of H with context [mmap_spec ?a ?l ?p ?f ?fd ?off ?i ?m ?o] => rewrite (mmap_noaccess_outcome a l p f fd off i m o eq_refl Han Hl Hm Hn) in H end. unfold mmap_err_out in H.
      destruct H as [(e & _ & E)|(a & _ & E)]; apply Ok_inj in E as (-> & -> & _); (split; [vm_only_done|reflexivity]).
    + match type of H with context [mmap_spec ?a ?l ?p ?f ?fd ?off ?i ?m ?o] => rewrite (mmap_fixed_noaccess_outcome a l p f fd off i m o eq_refl Han Hl Hm Hn Hf Hc Hal Hp Hrf Hmc) in H end. unfold mmap_err_out in H.
      destruct H as [(e & _ & E)|[E|(e & _ & E)]]; apply Ok_inj in E as (-> & -> & _); (split; [vm_only_done|reflexivity]).
  - cbv zeta in Hs. destruct Hs as (Hal & Hl & Hnw & Hhas). apply (nstep_munmap_inv _ _ _ _ _ _ Hal Hl Hnw Hhas) in H as (-> & _ & ->). split; [vm_only_done| reflexivity].
  - cbv zeta in Hs. destruct Hs as (Hgc & Hal & Hl & Hnw & Hmod & Hna & Hma). apply (nstep_mprotect_inv _ _ _ _ _ _ _ Hgc Hal Hl Hnw Hmod Hna Hma) in H as [-> [(e & _ & _ & ->)|(_ & _ & ->)]]; (split; [vm_only_done| reflexivity]).
  - cbv zeta in Hs. destruct Hs as (Hal & Hn & Ho & Hsrc & Hbk). apply (nstep_mremap_inv _ _ _ _ _ _ _ Hal Hn Ho Hsrc Hbk) in H as [-> [H _]].
    unfold mremap_out in H. cbv zeta in H.
    destruct H as [[_ E]|[_ [(e & _ & E)|[[_ E]|[(_ & _ & E)|(_ & dst & _ & E)]]]]]; apply Ok_inj in E as (-> & -> & _); (split; [vm_only_done| reflexivity]).
Qed.

Lemma nsafe_mmap_rw : forall addr len mo, 0 < len < 2^64 ->
  nsafe (NMmap addr len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof. intros addr len mo Hl. cbn [nsafe]. cbv zeta. split; [rewrite w_is0_lit by lia; apply Z.eqb_neq; lia|]. split; [reflexivity|]. split; [reflexivity|]. left. reflexivity. Qed.

Lemma nsafe_mmap_none : forall addr len mo, 0 < len < 2^64 ->
  nsafe (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof. intros addr len mo Hl. cbn [nsafe]. cbv zeta. split; [rewrite w_is0_lit by lia; apply Z.eqb_neq; lia|]. split; [reflexivity|]. split; [reflexivity|]. right; left. split; reflexivity. Qed.

Lemma minv_preserved : forall n mo eff mo' evs,
  nsafe n mo -> minv mo -> m_halted mo = None -> nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
  intros n mo eff mo' evs Hs Hmi Hh H. destruct (nstep_nsafe_vm_only n mo eff mo' evs Hs H) as [Hv _].
  split; [| exact (minv_vm_only _ _ Hv Hmi)]. destruct (vm_only_fields _ _ Hv) as (_ & _ & -> & _); exact Hh.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_auxv MallocInv_vm MallocInv_coh.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record EnvOK (sp0 : word) (argv envp : list (list byte)) (s : mstate) : Prop := {
  eo_statics : statics_ok (ms_mem s);
  eo_rodata : rodata_clear (ms_mem s);
  eo_pagesize : rdn ml_segs (ms_mem s) A_PAGE_SIZE 8 = Some (Z_to_le_bytes 8 4096);
  eo_aux : aux_env sp0 argv envp (ms_mem s);
  eo_lock : forall i, 0 <= i < 8 -> ms_mem s (Z_to_bv 64 (LOCKA + i)) = None;
  eo_sp0 : ms_hi s <= bv_unsigned sp0
}.

Lemma envok_statics : forall sp0 argv envp s, EnvOK sp0 argv envp s -> statics_ok (ms_mem s).
Proof. intros sp0 argv envp s [HS _ _ _ _ _]. exact HS. Qed.

Lemma envok_rodata : forall sp0 argv envp s, EnvOK sp0 argv envp s -> rodata_clear (ms_mem s).
Proof. intros sp0 argv envp s [_ HR _ _ _ _]. exact HR. Qed.

Lemma envok_pagesize : forall sp0 argv envp s, EnvOK sp0 argv envp s ->
  rdn ml_segs (ms_mem s) (Z_to_bv 64 PGA) 8 = Some (Z_to_le_bytes 8 4096).
Proof.
  intros sp0 argv envp s [_ _ HP _ _ _]. unfold PGA. rewrite Z_to_bv_bv_unsigned. exact HP.
Qed.

Lemma envok_needlocks : forall sp0 argv envp s, EnvOK sp0 argv envp s ->
  rdn ml_segs (ms_mem s) A_NEED_LOCKS 1 = Some [Z_to_bv 8 0].
Proof. intros sp0 argv envp s H. exact (so_nl _ (envok_statics _ _ _ _ H)). Qed.

(* [comment removed for export] *)
Definition mzone (x : Z) : Prop :=
  (0x1000 <= x < IMG_LO) \/ (IMG_HI <= x < alloc_ceiling) \/ (ERRNO <= x < ERRNO + 4) \/ (CTX <= x < CTX_END).

Lemma envok_frame : forall sp0 argv envp s m' h',
  EnvOK sp0 argv envp s -> WIN s ->
  (forall a : word, m' a = ms_mem s a \/ mzone (bv_unsigned a)) ->
  EnvOK sp0 argv envp (upd s m' h').
Proof.
  intros sp0 argv envp s m' h' [HS HRO HP HX HL Hsp] HWIN Hf.
  pose proof layout_statics as LS. pose proof layout_nums as LN.
  assert (OUT : forall a : word, ~ mzone (bv_unsigned a) -> m' a = ms_mem s a).
  { intros a Ha. destruct (Hf a) as [E | Z]; [exact E | exfalso; exact (Ha Z)]. }
  assert (RD : forall (a : word) n, bv_unsigned a + Z.of_nat n <= 2^64 ->
            (forall x, bv_unsigned a <= x < bv_unsigned a + Z.of_nat n -> ~ mzone x) ->
            rdn ml_segs m' a n = rdn ml_segs (ms_mem s) a n).
  { intros a n Hn Hz. apply rdn_ext; [exact Hn|]. intros x Hx. apply OUT. apply Hz. exact Hx. }
  constructor; cbn [ms_mem ms_hi upd].
  - apply (statics_frame (ms_mem s) m' HS). intros a Ha. apply OUT. unfold static_addr, mzone, CTX, CTX_END in *. lia.
  - intros a Ha. rewrite OUT; [apply HRO; exact Ha|]. unfold mzone, CTX, CTX_END. rewrite uZ by lia. lia.
  - rewrite RD; [exact HP | unfold PGA in LS; lia | intros x Hx; unfold mzone, CTX, CTX_END; unfold PGA in LS; lia].
  - apply (aux_env_frame sp0 argv envp (ms_mem s) m' HX). intros a Ha. apply OUT.
    destruct HWIN as (W1 & W2 & W3). unfold aux_addr, mzone, CTX, CTX_END in *.
    pose proof (mlo_order_libc (ML:=ML)). pose proof (mlo_order_ssp (ML:=ML)). unfold LOCKA, SSPA in *. lia.
  - intros i Hi. rewrite OUT; [apply HL; exact Hi|]. unfold mzone, CTX, CTX_END. rewrite uZ by lia. lia.
  - exact Hsp.
Qed.

(* [comment removed for export] *)
Lemma st_zone_mzone : forall (a : word) (n : Z) x, st_zone a n = true -> 0 < n ->
  bv_unsigned a + n <= alloc_ceiling -> 0x1000 <= bv_unsigned a ->
  bv_unsigned a <= x < bv_unsigned a + n -> mzone x.
Proof.
  intros a n x Hz Hn Hc Hlo Hx. apply (proj1 (st_zone_spec a n)) in Hz.
  unfold mzone, ERRNO, CTX, CTX_END. ceil. llia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition CovM (m : word -> option byte) (h : VmMaps) : Prop :=
  forall a : word, m a <> None -> 0x1000 <= bv_unsigned a < alloc_ceiling ->
    ~ (IMG_LO <= bv_unsigned a < IMG_HI) -> mcov (vm_maps h) (bv_unsigned a) 1.

Lemma covm_of_coh : forall A m h, Coh A m h -> CovM m h.
Proof. intros A m h [C _ _ _]. exact C. Qed.

(* [comment removed for export] *)
Lemma covm_write : forall m m' h, CovM m h ->
  (forall a : word, m' a <> None -> m a <> None \/ (IMG_LO <= bv_unsigned a < IMG_HI) \/ mcov (vm_maps h) (bv_unsigned a) 1) ->
  CovM m' h.
Proof.
  intros m m' h HC Hw a Ha Hr Hi. destruct (Hw a Ha) as [H | [H | H]]; [exact (HC a H Hr Hi) | exfalso; exact (Hi H) | exact H].
Qed.

Lemma covm_wbytes : forall m h (a : word) bs, CovM m h ->
  (forall k, 0 <= k < Z.of_nat (length bs) -> m (Z_to_bv 64 (bv_unsigned a + k)) <> None \/
     (IMG_LO <= bv_unsigned a + k < IMG_HI) \/ mcov (vm_maps h) (bv_unsigned a + k) 1) ->
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  CovM (wbytes m a bs) h.
Proof.
  intros m h a bs HC Hbs Hnw. apply (covm_write m _ h HC). intros x Hx.
  pose proof (u64_range x). pose proof (u64_range a).
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a)) as [Hlt | Hge].
  - left. rewrite wbytes_below in Hx by llia. exact Hx.
  - destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin | Hout].
    + destruct (Hbs (bv_unsigned x - bv_unsigned a) ltac:(llia)) as [H1 | [H2 | H3]].
      * left. replace (bv_unsigned a + (bv_unsigned x - bv_unsigned a)) with (bv_unsigned x) in H1 by llia.
        rewrite Z_to_bv_bv_unsigned in H1. exact H1.
      * right; left. llia.
      * right; right. replace (bv_unsigned a + (bv_unsigned x - bv_unsigned a)) with (bv_unsigned x) in H3 by llia. exact H3.
    + left. rewrite wbytes_above in Hx by llia. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record FR (A : astate) (s : mstate) (A' : astate) (s' : mstate) : Prop := {
  fr_lo : ms_lo s' = ms_lo s;
  fr_hi : ms_hi s' = ms_hi s;
  fr_owned : forall x, owned_of A x -> owned_of A' x;
  fr_mem : forall a : word, ~ owned_of A' (bv_unsigned a) -> ~ (ERRNO <= bv_unsigned a < ERRNO + 4) ->
           ms_mem s' a = ms_mem s a;
  fr_live : forall p n, a_live A p = Some n -> a_live A' p = Some n;
  fr_livemem : forall p n (a : word), a_live A p = Some n -> p <= bv_unsigned a < p + n ->
               ms_mem s' a = ms_mem s a;
  fr_mapped : forall a : word, ms_mem s a <> None -> ms_mem s' a <> None;
  fr_limit : vm_limit (ms_vm s') = vm_limit (ms_vm s)
}.

Lemma FR_refl : forall A s, FR A s A s.
Proof. intros A s. constructor; auto. Qed.

Lemma FR_trans : forall A s A' s' A'' s'', FR A s A' s' -> FR A' s' A'' s'' -> FR A s A'' s''.
Proof.
  intros A s A' s' A'' s'' [L1 H1 O1 M1 V1 P1 Q1 T1] [L2 H2 O2 M2 V2 P2 Q2 T2]. constructor.
  - rewrite L2. exact L1.
  - rewrite H2. exact H1.
  - intros x Hx. apply O2. apply O1. exact Hx.
  - intros a Ho He. rewrite M2 by assumption. apply M1; [| exact He]. intros Ho'. apply Ho. apply O2. exact Ho'.
  - intros p n Hp. apply V2. apply V1. exact Hp.
  - intros p n a Hp Hi. rewrite (P2 p n a (V1 p n Hp) Hi). exact (P1 p n a Hp Hi).
  - intros a Ha. apply Q2. apply Q1. exact Ha.
  - rewrite T2. exact T1.
Qed.

(* [comment removed for export] *)
Lemma FR_mem : forall A s m' ,
  (forall a : word, m' a = ms_mem s a \/
     ((owned_of A (bv_unsigned a) \/ (ERRNO <= bv_unsigned a < ERRNO + 4)) /\
      (forall p n, a_live A p = Some n -> ~ (p <= bv_unsigned a < p + n)) /\
      (ms_mem s a <> None -> m' a <> None))) ->
  FR A s A (upd s m' (ms_vm s)).
Proof.
  intros A s m' Hm. constructor; cbn; auto.
  - intros a Ho He. destruct (Hm a) as [E | (H1 & _ & _)]; [exact E | exfalso; tauto].
  - intros p n a Hp Hi. destruct (Hm a) as [E | (_ & H2 & _)]; [exact E | exfalso]. exact (H2 p n Hp Hi).
  - intros a Ha. destruct (Hm a) as [E | (_ & _ & H3)]; [rewrite E; exact Ha | exact (H3 Ha)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition errno_mem (m : word -> option byte) (e : Z) : word -> option byte :=
  wbytes m A_ERRNO (word_to_le_bytes 4 (Z_to_bv 64 e)).

(* [comment removed for export] *)

(* [comment removed for export] *)

Section SysSteps.
  Context {R : Type}.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop).

  Lemma ts_set_errno : forall e s (k : unit -> M R) P, WIN s ->
    tsafe (k tt (upd s (errno_mem (ms_mem s) e) (ms_vm s))) P ->
    tsafe ((x <- set_errno e ;; k x) s) P.
  Proof.
    intros e s k P HWn Hk. unfold set_errno, m_sw, errno_mem. rewrite A_ERRNO_eq. pose proof layout_nums.
    eapply ts_st.
    - apply acc_ok_heap; [exact HWn | lia | lia | lia].
    - rewrite <- A_ERRNO_eq. exact st_zone_errno.
    - apply store_ok_rwseg; cbn; lia.
    - rewrite <- A_ERRNO_eq. exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_sys_mmap : forall mk (len : word) s (K : word -> M R) P,
    WIN s -> 0 < bv_unsigned len < 2^62 ->
    tsafe (K MAP_FAILED (upd s (errno_mem (ms_mem s) ENOMEM) (ms_vm s))) P ->
    (forall a : word, mmap_grant_ok mk (ms_vm s) a (page_round_up_Z (bv_unsigned len)) = true ->
       tsafe (K a (match mk with
                   | MMrw => upd s (zfill a (page_round_up len) (ms_mem s)) (vm_mmap a (page_round_up len) (ms_vm s))
                   | MMnone => upd s (unfill a (page_round_up len) (ms_mem s)) (vm_noacc a (page_round_up len) (ms_vm s))
                   end)) P) ->
    tsafe ((x <- sys_mmap mk len ;; K x) s) P.
  Proof.
    intros mk len s K P HWn Hlen Hf Hok. unfold mbind, sys_mmap.
    rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned len))) by llia. rewrite (proj2 (Z.ltb_lt (bv_unsigned len) (2^62))) by llia. cbn [andb tbind tsafe].
    split.
    - intros _ (* [comment removed for export] *).
      apply (proj1 (tsafe_tbind_assoc _ _ _ _)). cbn [tbind].
      pose proof (ts_set_errno ENOMEM s (fun _ s' => K MAP_FAILED s') P HWn) as X. unfold mbind in X. apply X. exact Hf.
    - intros a Hg. specialize (Hok a Hg). destruct mk; exact Hok.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_sys_munmap : forall (addr len : word) s (K : word -> M R) P,
    bv_unsigned addr mod 4096 = 0 -> 0 < bv_unsigned len ->
    bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= alloc_top (ms_vm s) ->
    map_has (vm_maps (ms_vm s)) addr (page_round_up len) = true ->
    tsafe (K (Z_to_bv 64 0) (upd s (unfill addr (page_round_up len) (ms_mem s)) (vm_munmap addr (page_round_up len) (ms_vm s)))) P ->
    tsafe ((x <- sys_munmap addr len ;; K x) s) P.
  Proof.
    intros addr len s K P Hal Hlen Hce Hhas Hk. unfold mbind, sys_munmap. unfold page_size.
    rewrite Hal, (proj2 (Z.ltb_lt 0 _)) by llia. rewrite (proj2 (Z.leb_le _ _)) by exact Hce. rewrite Hhas. cbn [andb Z.eqb tbind]. exact Hk.
  Qed.

  Lemma ts_sys_brk_query : forall s (K : word -> M R) P,
    tsafe (K (vm_brk (ms_vm s)) s) P -> tsafe ((x <- sys_brk_query ;; K x) s) P.
  Proof. intros s K P Hk. exact Hk. Qed.

  Lemma ts_sys_brk_grow : forall (req : word) s (K : word -> M R) P,
    0 < bv_unsigned (vm_brk (ms_vm s)) -> bv_unsigned (vm_start_brk (ms_vm s)) <= bv_unsigned req ->
    bv_unsigned (vm_brk (ms_vm s)) < bv_unsigned req ->
    tsafe (K (vm_brk (ms_vm s)) s) P ->
    (brk_grow_ok_vm (ms_vm s) req req = true ->
       tsafe (K req (upd s (apply_zeros (ms_mem s) (brk_zeros req req (vm_brk (ms_vm s)))) (vm_brk_grow req (ms_vm s)))) P) ->
    tsafe ((x <- sys_brk_grow req ;; K x) s) P.
  Proof.
    intros req s K P H1 H2 H3 Hf Hok. unfold mbind, sys_brk_grow.
    rewrite (proj2 (Z.ltb_lt 0 _)) by exact H1. rewrite (proj2 (Z.leb_le _ _)) by exact H2. rewrite (proj2 (Z.ltb_lt _ _)) by exact H3.
    cbn [andb tbind tsafe]. split; [intros _; exact Hf | exact Hok].
  Qed.

  Lemma ts_sys_mmap_fixed_none : forall (addr len : word) s (K : word -> M R) P,
    WIN s -> 0 < bv_unsigned len < 2^62 ->
    bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= alloc_top (ms_vm s) ->
    bv_unsigned addr mod 4096 = 0 -> 0 < bv_unsigned addr ->
    region_free (vm_reserved (ms_vm s)) addr (page_round_up len) = true ->
    map_contains (vm_maps (ms_vm s)) addr (page_round_up len) = true ->
    tsafe (K MAP_FAILED (upd s (errno_mem (ms_mem s) ENOMEM) (ms_vm s))) P ->
    tsafe (K addr (upd s (unfill addr (page_round_up len) (ms_mem s)) (vm_fixed_ok addr (page_round_up len) (ms_vm s)))) P ->
    tsafe (K MAP_FAILED (upd s (errno_mem (unfill addr (page_round_up len) (ms_mem s)) ENOMEM)
                               (vm_fixed_destroy addr (page_round_up len) (ms_vm s)))) P ->
    tsafe ((x <- sys_mmap_fixed_none addr len ;; K x) s) P.
  Proof.
    intros addr len s K P HWn Hlen Hce Hal Ha0 Hrf Hmc Hkeep Hok Hdes. unfold mbind, sys_mmap_fixed_none. unfold page_size.
    rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned len))) by llia. rewrite (proj2 (Z.ltb_lt (bv_unsigned len) (2^62))) by llia.
    rewrite (proj2 (Z.leb_le _ _)) by exact Hce. rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned addr))) by exact Ha0.
    rewrite Hal, Hrf, Hmc. cbn [andb Z.eqb tbind tsafe].
    (* [comment removed for export] *)
    exact Hok.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_sys_mprotect_none : forall (addr len : word) s (K : word -> M R) P,
    WIN s -> 0 < bv_unsigned len -> bv_unsigned addr mod 4096 = 0 ->
    bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= alloc_top (ms_vm s) ->
    map_contains (vm_maps (ms_vm s)) addr (page_round_up len) = true ->
    map_contains (vm_noaccess (ms_vm s)) addr (page_round_up len) = true ->
    tsafe (K MAP_FAILED (upd s (errno_mem (ms_mem s) ENOMEM) (ms_vm s))) P ->
    (mprot_ok_vm (ms_vm s) addr (page_round_up len) = true ->
     tsafe (K (Z_to_bv 64 0) (upd s (zfill addr (page_round_up len) (ms_mem s)) (vm_unprotect addr (page_round_up len) (ms_vm s)))) P) ->
    tsafe ((x <- sys_mprotect_rw addr len ;; K x) s) P.
  Proof.
    intros addr len s K P HWn Hlen Hal Hce Hmc Hna Hf Hok. unfold mbind, sys_mprotect_rw. unfold page_size.
    rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned len))) by llia. rewrite Hal. rewrite (proj2 (Z.leb_le _ _)) by exact Hce.
    rewrite Hmc, Hna. cbn [andb Z.eqb tbind tsafe]. split; [| exact Hok].
    intros _ (* [comment removed for export] *).
    apply (proj1 (tsafe_tbind_assoc _ _ _ _)). cbn [tbind].
    pose proof (ts_set_errno ENOMEM s (fun _ s' => K MAP_FAILED s') P HWn) as X. unfold mbind in X. apply X. exact Hf.
  Qed.
End SysSteps.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CtxReads.
  Context {R : Type}.
  Variable A : astate.
  Hypothesis HW : WF A.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop).

  Lemma ts_ld_ctx_m : forall s ck (k : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> cvalid ck -> clen ck = 8 ->
    tsafe (k (Z_to_bv 64 (a_ctx A ck mod 2^64)) s) P ->
    tsafe ((x <- m_ld (Z_to_bv 64 (caddr ck)) ;; k x) s) P.
  Proof.
    intros s ck k P HR HWn Hk Hlen Hk'.
    pose proof (wf_ctx_nonneg A HW ck) as Hv.
    destruct (rep_read_ctx A (ms_mem s) ck HR Hk Hv) as (bs & Hrd & Hl & Hval).
    rewrite Hlen in *. change (Z.to_nat 8) with 8%nat in *.
    pose proof (ctx_slot_range ck Hk) as (C1 & C2 & C3). unfold LOCKA, CTX_END in *.
    eapply ts_ld; [apply acc_ok_heap; [exact HWn | llia | llia | ceil; llia] | exact Hrd |].
    rewrite (le_val_Z bs (a_ctx A ck mod 2^64)); [exact Hk'|]. rewrite Hval. reflexivity.
  Qed.

  Lemma ts_lw_ctx_m : forall s ck (k : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> cvalid ck -> clen ck = 4 ->
    tsafe (k (Z_to_bv 64 (bv_swrap 32 (a_ctx A ck mod 2^32))) s) P ->
    tsafe ((x <- m_lw (Z_to_bv 64 (caddr ck)) ;; k x) s) P.
  Proof.
    intros s ck k P HR HWn Hk Hlen Hk'.
    pose proof (wf_ctx_nonneg A HW ck) as Hv.
    destruct (rep_read_ctx A (ms_mem s) ck HR Hk Hv) as (bs & Hrd & Hl & Hval).
    rewrite Hlen in *. change (Z.to_nat 4) with 4%nat in *.
    pose proof (ctx_slot_range ck Hk) as (C1 & C2 & C3). unfold LOCKA, CTX_END in *.
    eapply ts_lw; [apply acc_ok_heap; [exact HWn | llia | llia | ceil; llia] | exact Hrd |].
    rewrite (le_val_Z bs (a_ctx A ck mod 2^32)); [| rewrite Hval; reflexivity].
    pose proof (Z.mod_pos_bound (a_ctx A ck) (2^32) ltac:(llia)).
    rewrite v_lw_Z by llia. exact Hk'.
  Qed.

  Lemma ts_lbu_ctx_m : forall s ck (k : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> cvalid ck -> clen ck = 1 ->
    tsafe (k (Z_to_bv 64 (a_ctx A ck mod 256)) s) P ->
    tsafe ((x <- m_lbu (Z_to_bv 64 (caddr ck)) ;; k x) s) P.
  Proof.
    intros s ck k P HR HWn Hk Hlen Hk'.
    pose proof (wf_ctx_nonneg A HW ck) as Hv.
    destruct (rep_read_ctx A (ms_mem s) ck HR Hk Hv) as (bs & Hrd & Hl & Hval).
    rewrite Hlen in *. change (Z.to_nat 1) with 1%nat in *.
    pose proof (ctx_slot_range ck Hk) as (C1 & C2 & C3). unfold LOCKA, CTX_END in *.
    destruct bs as [|b [|]]; try (cbn in Hl; llia).
    eapply ts_lbu; [apply acc_ok_heap; [exact HWn | llia | llia | ceil; llia] | exact Hrd |].
    rewrite bytes_le_single in Hval. rewrite Hval. change (2^(8*1)) with 256. exact Hk'.
  Qed.
End CtxReads.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition GRD (cb : list byte) (m : word -> option byte) : Prop :=
  rdn ml_segs m A_SSP 8 = Some cb.

Lemma grd_frame : forall cb m m', GRD cb m -> (forall a : word, m' a = m a \/ mzone (bv_unsigned a)) -> GRD cb m'.
Proof.
  intros cb m m' HG Hf. unfold GRD in *. rewrite <- HG. pose proof layout_statics. unfold SSPA in *.
  apply rdn_ext; [cbn; lia|].
  intros x Hx. cbn in Hx. destruct (Hf x) as [E | Z]; [exact E | exfalso].
  unfold mzone, CTX, CTX_END in Z. lia.
Qed.

(* [comment removed for export] *)
Record IS (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (A : astate) (s : mstate) : Prop := {
  is_wf : WF A;
  is_rep : Rep A (ms_mem s);
  is_cov : CovM (ms_mem s) (ms_vm s);
  is_win : WIN s;
  is_env : EnvOK sp0 argv envp s;
  is_grd : GRD cb (ms_mem s)
}.

(* [comment removed for export] *)
Lemma IS_mem : forall sp0 argv envp cb A A' s m',
  IS sp0 argv envp cb A s -> WF A' -> Rep A' m' ->
  (forall a : word, m' a = ms_mem s a \/ mzone (bv_unsigned a)) ->
  (forall a : word, m' a <> None -> ms_mem s a <> None \/ (IMG_LO <= bv_unsigned a < IMG_HI) \/ mcov (vm_maps (ms_vm s)) (bv_unsigned a) 1) ->
  IS sp0 argv envp cb A' (upd s m' (ms_vm s)).
Proof.
  intros sp0 argv envp cb A A' s m' [W R C Wn E G] HW' HR' Hz Hm. constructor; cbn.
  - exact HW'.
  - exact HR'.
  - apply (covm_write (ms_mem s)); [exact C | exact Hm].
  - exact Wn.
  - apply (envok_frame sp0 argv envp s m' (ms_vm s) E Wn Hz).
  - apply (grd_frame cb (ms_mem s) m' G Hz).
Qed.

(* [comment removed for export] *)
Lemma IS_wbytes : forall sp0 argv envp cb A A' s (a : Z) bs,
  IS sp0 argv envp cb A s -> WF A' -> Rep A' (wbytes (ms_mem s) (Z_to_bv 64 a) bs) ->
  0 <= a < 2^64 -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mzone x) ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> ms_mem s (Z_to_bv 64 x) <> None \/ (IMG_LO <= x < IMG_HI)) ->
  IS sp0 argv envp cb A' (upd s (wbytes (ms_mem s) (Z_to_bv 64 a) bs) (ms_vm s)).
Proof.
  intros sp0 argv envp cb A A' s a bs HI HW' HR' Ha Hnw Hz Hm.
  apply (IS_mem sp0 argv envp cb A A' s _ HI HW' HR').
  - intros x. pose proof (u64_range x).
    destruct (Z.lt_ge_cases (bv_unsigned x) a) as [Hl | Hl]; [left; apply wbytes_below; rewrite ?uZ by llia; llia|].
    destruct (Z.lt_ge_cases (bv_unsigned x) (a + Z.of_nat (length bs))) as [Hi | Hi]; [right; apply Hz; llia|].
    left. apply wbytes_above; rewrite ?uZ by llia; llia.
  - intros x Hx. pose proof (u64_range x).
    destruct (Z.lt_ge_cases (bv_unsigned x) a) as [Hl | Hl]; [left; rewrite wbytes_below in Hx by (rewrite ?uZ by llia; llia); exact Hx|].
    destruct (Z.lt_ge_cases (bv_unsigned x) (a + Z.of_nat (length bs))) as [Hi | Hi].
    + destruct (Hm (bv_unsigned x) ltac:(llia)) as [H1 | H2]; [left; rewrite Z_to_bv_bv_unsigned in H1; exact H1 | right; left; exact H2].
    + left. rewrite wbytes_above in Hx by (rewrite ?uZ by llia; llia). exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_heap : forall A p n, WF A -> a_live A p = Some n ->
  0 <= n /\ 0x1000 <= p /\ p + round16 n <= alloc_ceiling /\ (p + round16 n <= IMG_LO \/ IMG_HI <= p) /\
  (forall x, p <= x < p + round16 n -> dom A x).
Proof.
  intros A p n HW Hl. apply (proj1 (wf_live_map A HW _ _)) in Hl.
  destruct Hl as (ma & mt & aib & slots & i & off & Hma & Hr & Hi0 & Hi & Ep).
  destruct (live_geom A HW ma mt aib slots i off n Hma Hr Hi0 Hi) as (q & Hq & Hn & Ho & Hfit & Hal & Hpal & G1 & G2 & G3 & G4 & G5 & G6 & G7).
  rewrite <- Ep in *. pose proof (round16_ge n).
  split; [exact Hn|]. split; [llia|]. split; [llia|]. split; [llia|].
  intros x Hx. apply (grp_dom A ma mt aib slots x HW Hma Hr). llia.
Qed.

(* [comment removed for export] *)
Lemma FR_memA : forall A A' s m', WF A ->
  (forall x, dom A' x <-> dom A x) -> a_live A' = a_live A ->
  (forall a : word, m' a = ms_mem s a \/
     ((LOCKA <= bv_unsigned a < CTX_END) \/ (ERRNO <= bv_unsigned a < ERRNO + 4) \/
      (dom A (bv_unsigned a) /\ forall p n, a_live A p = Some n -> ~ (p <= bv_unsigned a < p + n)))) ->
  (forall a : word, ms_mem s a <> None -> m' a <> None) ->
  FR A s A' (upd s m' (ms_vm s)).
Proof.
  intros A A' s m' HW Hd Hl Hm Hk. constructor; cbn; auto.
  - intros x [Hc | Hx]; [left; exact Hc | right; apply (proj2 (Hd x)); exact Hx].
  - intros a Ho He. destruct (Hm a) as [E | [Hc | [Herr | [Hdm _]]]]; [exact E | | |]; exfalso.
    + apply Ho. left. exact Hc.
    + exact (He Herr).
    + apply Ho. right. apply (proj2 (Hd _)). exact Hdm.
  - intros p n. rewrite Hl. exact (fun H => H).
  - intros p n a Hp Ha. destruct (Hm a) as [E | [Hc | [Herr | [_ Hnl]]]]; [exact E | | |]; exfalso.
    + destruct (live_heap A p n HW Hp) as (Hn & H1 & H2 & H3 & _). pose proof (round16_ge n).
      unfold LOCKA, CTX_END in Hc. ceil. llia.
    + destruct (live_heap A p n HW Hp) as (Hn & H1 & H2 & H3 & _). pose proof (round16_ge n).
      unfold ERRNO in Herr. ceil. llia.
    + exact (Hnl p n Hp Ha).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition gkeep (k : cslot) : Prop :=
  match k with KActive _ | KUsage _ | KCtr | KSeq | KUseq _ | KBounce _ => True | _ => False end.

Record gsame (A A' : astate) : Prop := {
  gs_grp : forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl -> a_meta A' x = Some mt;
  gs_grp_back : forall x mt aib sl, a_meta A' x = Some mt -> mt_role mt = RGroup aib sl -> a_meta A x = Some mt;
  gs_dead : forall x mt, a_meta A x = Some mt -> mt_role mt = RDead -> a_meta A' x = Some mt;
  gs_active : forall sc, a_active A' sc = a_active A sc;
  gs_live : a_live A' = a_live A;
  gs_ctx : forall k, gkeep k -> cvalid k -> a_ctx A' k = a_ctx A k
}.

Lemma gsame_refl : forall A, gsame A A.
Proof. intros A. constructor; auto. Qed.

Lemma gsame_trans : forall A B C, gsame A B -> gsame B C -> gsame A C.
Proof.
  intros A B C [G1 G2 G3 G4 G5 G6] [H1 H2 H3 H4 H5 H6]. constructor; eauto.
  - intros sc. rewrite H4. apply G4.
  - rewrite H5. exact G5.
  - intros k Hk Hv. rewrite (H6 k Hk Hv). apply G6; assumption.
Qed.

(* [comment removed for export] *)
Definition deads (A : astate) (D : list Z) : Prop :=
  forall x, (exists mt, a_meta A x = Some mt /\ mt_role mt = RDead) <-> In x D.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma repw_commit : forall A A' m0 ws m,
  RepW A m0 ws m ->
  (forall x b, facts A' x b -> facts A x b \/ wlook ws x <> None) ->
  (forall x b, facts A' x b -> wlook ws x <> None -> wlook ws x = Some b) ->
  (forall x, dom A' x -> dom A x) ->
  Rep A' m.
Proof.
  intros A A' m0 ws m HR H1 H2 Hd. apply (repw_final A A' m0 ws m HR); [| exact Hd].
  intros x b Hf. destruct (wlook ws x) as [b'|] eqn:E.
  - left. rewrite <- E. apply H2; [exact Hf | rewrite E; discriminate].
  - right. split; [reflexivity|]. destruct (H1 x b Hf) as [H | H]; [exact H | exfalso; apply H; exact E].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Locate.
  Variable A : astate.
  Hypothesis HW : WF A.

  Lemma fact_at_ctx : forall f k x, has A f -> cvalid k ->
    f_a f <= x < f_a f + f_n f -> caddr k <= x < caddr k + clen k ->
    f = FCT (caddr k) (clen k) (a_ctx A k).
  Proof.
    intros f k x Hf Hk Hx Hkx. destruct Hf as [(k' & Hk' & ->) | Hrest].
    - destruct (cslot_eq_dec k' k) as [-> | Hne]; [reflexivity|]. exfalso.
      destruct (ctx_slot_disj k' k Hk' Hk Hne); cbn in Hx; llia.
    - exfalso. destruct (nonctx_fact_avoids_ctx A HW f Hrest k Hk); llia.
  Qed.

  Lemma fact_at_meta : forall f ma mt fl x, has A f -> a_meta A ma = Some mt ->
    f_a f <= x < f_a f + f_n f -> ma + moff fl <= x < ma + moff fl + mlen fl ->
    f = FCT (ma + moff fl) (mlen fl) (mt_f mt fl).
  Proof.
    intros f ma mt fl x Hf Hma Hx Hflx. pose proof (mfield_range fl) as Hfl.
    destruct Hf as [Hc | [Har | [Hm | Hg]]].
    - exfalso. destruct (nonmeta_avoid_meta A HW ma mt Hma f (or_introl Hc)); llia.
    - exfalso. destruct (nonmeta_avoid_meta A HW ma mt Hma f (or_intror (or_introl Har))); llia.
    - destruct Hm as (ma' & mt' & fl' & Hma' & ->). cbn in Hx. pose proof (mfield_range fl') as Hfl'.
      destruct (Z.eq_dec ma' ma) as [-> | Hne].
      + rewrite Hma in Hma'. injection Hma' as <-.
        destruct (mfield_eq_dec fl' fl) as [-> | Hnf]; [reflexivity|]. exfalso.
        destruct (mfield_disj fl' fl Hnf); llia.
      + exfalso. destruct (other_meta_avoid_meta A HW ma mt Hma ma' mt' fl' Hma' Hne); llia.
    - exfalso. destruct (nonmeta_avoid_meta A HW ma mt Hma f (or_intror (or_intror Hg))); llia.
  Qed.

  (* [comment removed for export] *)
  Lemma fact_at_area_hdr : forall f pg x, has A f -> In pg (a_areas A) ->
    f_a f <= x < f_a f + f_n f -> pg <= x < pg + 24 ->
    f = FCT pg 8 (a_ctx A KSecret) /\ x < pg + 8.
  Proof.
    intros f pg x Hf Hpg Hx Hpx. destruct (wf_areas_al A HW pg Hpg) as [Hal Hh].
    destruct Hf as [Hc | [Har | [Hm | Hg]]].
    - exfalso. destruct Hc as (k & Hk & ->). cbn in Hx. destruct (heap_avoids_ctx pg (pg + 4096) Hh k Hk); llia.
    - destruct Har as (pg' & Hpg' & ->). cbn in Hx |- *. destruct (Z.eq_dec pg' pg) as [-> | Hne]; [split; [reflexivity | llia]|].
      exfalso. destruct (wf_areas_al A HW pg' Hpg') as [Hal' _]. destruct (pages_disj pg pg' Hal Hal' ltac:(congruence)); llia.
    - exfalso. destruct Hm as (ma & mt & fl & Hma & ->). cbn in Hx. pose proof (mfield_range fl).
      destruct (proj1 (wf_meta_dom A HW ma) ltac:(rewrite Hma; discriminate)) as (pg' & k & Hpg' & Hk & ->).
      pose proof (meta_addr_range pg' k Hk). destruct (Z.eq_dec pg' pg) as [-> | Hne]; [llia|].
      destruct (wf_areas_al A HW pg' Hpg') as [Hal' _]. destruct (pages_disj pg pg' Hal Hal' ltac:(congruence)); llia.
    - exfalso. pose proof (has_grp_where A HW f Hg) as ((mg & mtg & aib & slots & Hmg & Hrg & Hlo & Hhi) & Hn).
      destruct (wf_grp_root A HW mg mtg aib slots Hmg Hrg) as (mr & mtr & aibr & slr & Hmr' & Hrr & Hml & Hrlo & Hrhi & _).
      destruct (wf_disj_area_grp A HW pg mr mtr aibr slr Hpg Hmr' Hrr Hml); llia.
  Qed.
End Locate.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_free_image : forall (a n : word),
  region_free (segments_reserved ml_segs) a n = true -> 0 < bv_unsigned n ->
  bv_unsigned a + bv_unsigned n <= IMG_LO \/ IMG_HI <= bv_unsigned a.
Proof.
  intros a n Hf Hn. pose proof (proj1 (region_free_spec _ a n) Hf) as H.
  pose proof layout_nums.
  destruct (Z.le_gt_cases (bv_unsigned a + bv_unsigned n) IMG_LO) as [H1 | H1]; [left; exact H1|].
  destruct (Z.le_gt_cases IMG_HI (bv_unsigned a)) as [H2 | H2]; [right; exact H2|].
  exfalso.
  (* [comment removed for export] *)
  set (x := Z.max (bv_unsigned a) IMG_LO).
  assert (Hx : IMG_LO <= x < IMG_HI /\ bv_unsigned a <= x < bv_unsigned a + bv_unsigned n) by (subst x; lia).
  destruct (mlo_reserved_cover x (proj1 Hx)) as (b & sz & Hin & Hb). destruct (H b sz Hin); lia.
Qed.

(* [comment removed for export] *)
Definition AvOK (A : astate) : Prop :=
  forall ma mt, a_meta A ma = Some mt -> mt_role mt = RAvail ->
    exists k, 101 - a_ctx A KAmc <= k < 101 /\ ma = meta_addr (last (a_areas A) 0) k.

(* [comment removed for export] *)
Record got_meta (A : astate) (D : list Z) (A' : astate) (m : Z) : Prop := {
  gm_meta : exists md, a_meta A' m = Some md /\ mt_role md = RDead /\ forall fl, mt_f md fl = 0;
  gm_lo : 0x1000 <= m;
  gm_hi : m + 40 <= alloc_ceiling;
  gm_dom : forall j, 0 <= j < 40 -> dom A' (m + j);
  gm_deads : deads A' (m :: D);
  gm_fresh : ~ In m D;
  gm_gsame : gsame A A';
  gm_av : AvOK A'
}.

Lemma byte_of_zero : forall k, byte_of 0 k = 0.
Proof. intros k. unfold byte_of. rewrite Zdiv_0_l. reflexivity. Qed.

(* [comment removed for export] *)
Lemma area_not_live : forall A pg (a : Z) p n, WF A -> In pg (a_areas A) -> pg <= a < pg + 4096 ->
  a_live A p = Some n -> ~ (p <= a < p + n).
Proof.
  intros A pg a p n HW Hpg Ha Hl Hin. apply (proj1 (wf_live_map A HW _ _)) in Hl.
  destruct Hl as (ma & mt & aib & slots & i & off & Hma & Hr & Hi0 & Hi & Ep).
  destruct (live_geom A HW ma mt aib slots i off n Hma Hr Hi0 Hi) as (q & Hq & Hn & Ho & Hfit & Hal & Hpal & G1 & G2 & G3 & G4 & G5 & G6 & G7).
  rewrite <- Ep in *. pose proof (round16_ge n).
  destruct (wf_grp_root A HW ma mt aib slots Hma Hr) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hlo & Hhi & _).
  destruct (wf_disj_area_grp A HW pg mr mtr aibr slr Hpg Hmr Hrr Hml); llia.
Qed.

(* [comment removed for export] *)
Lemma page_not_live : forall A pg (a : Z) p n, WF A -> In pg (a_pages A) -> pg <= a < pg + 4096 ->
  a_live A p = Some n -> ~ (p <= a < p + n).
Proof.
  intros A pg a p n HW Hpg Ha Hl Hin. apply (proj1 (wf_live_map A HW _ _)) in Hl.
  destruct Hl as (ma & mt & aib & slots & i & off & Hma & Hr & Hi0 & Hi & Ep).
  destruct (live_geom A HW ma mt aib slots i off n Hma Hr Hi0 Hi) as (q & Hq & Hn & Ho & Hfit & Hal & Hpal & G1 & G2 & G3 & G4 & G5 & G6 & G7).
  rewrite <- Ep in *. pose proof (round16_ge n).
  destruct (wf_grp_root A HW ma mt aib slots Hma Hr) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hlo & Hhi & _).
  destruct (wf_disj_page_grp A HW pg mr mtr aibr slr Hpg Hmr Hrr Hml); llia.
Qed.

End WithLayout.

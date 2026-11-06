(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RelSpec ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Cfg.
From Stdlib Require Classical_Prop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_of_Z : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. apply unsigned_lit. assumption. Qed.

Lemma w_is0_false : forall z, 0 < z < 2^64 -> w_is0 (Z_to_bv 64 z) = false.
Proof. intros z Hz. apply w_is0_pos. rewrite u64_of_Z; lia. Qed.

Lemma w_is0_true : w_is0 (Z_to_bv 64 0) = true.
Proof. reflexivity. Qed.

Lemma two_pow_64_val : two_pow_64 = 2^64.
Proof. reflexivity. Qed.

Lemma page_size_val : page_size = 4096.
Proof. reflexivity. Qed.

Lemma mmap_len_ge : forall l, l <= mmap_len l.
Proof.
  intros l. unfold mmap_len, page_round_up_Z. rewrite page_size_val.
  pose proof (Z_div_mod_eq_full (l + 4096 - 1) 4096). pose proof (Z.mod_pos_bound (l + 4096 - 1) 4096). lia.
Qed.

Lemma mmap_len_lt : forall l, mmap_len l < l + 4096.
Proof.
  intros l. unfold mmap_len, page_round_up_Z. rewrite page_size_val.
  pose proof (Z_div_mod_eq_full (l + 4096 - 1) 4096). pose proof (Z.mod_pos_bound (l + 4096 - 1) 4096). lia.
Qed.

Lemma mmap_len_aligned : forall l, mmap_len l mod 4096 = 0.
Proof. intros. unfold mmap_len, page_round_up_Z. rewrite page_size_val. apply Z_mod_mult. Qed.

Lemma mmap_len_of_aligned : forall l, l mod 4096 = 0 -> mmap_len l = l.
Proof.
  intros l Hl. unfold mmap_len, page_round_up_Z. rewrite page_size_val.
  pose proof (Z_div_mod_eq_full l 4096). pose proof (Z_div_mod_eq_full (l + 4096 - 1) 4096).
  pose proof (Z.mod_pos_bound (l + 4096 - 1) 4096). nia.
Qed.

Lemma mmap_len_pos : forall l, 0 < l -> 0 < mmap_len l.
Proof. intros. pose proof (mmap_len_ge l). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition alloc_node (n : node) : bool :=
  match n with
  | NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ _ => true
  | _ => false
  end.

(* [comment removed for export] *)
Section Models.
  Variable mo : Model.
  Let h := m_vmmaps mo.

  (* [comment removed for export] *)
  Definition mm_anon_model (a n : word) : Model :=
    with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) (vm_noaccess h)
                   (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo.
  (* [comment removed for export] *)
  Definition mm_none_model (a n : word) : Model :=
    with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) ((a, n) :: vm_noaccess h)
                   (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo.
  (* [comment removed for export] *)
  Definition mm_fixed_model (addr n : word) : Model :=
    vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
      (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
                      ((addr, n) :: maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                      (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo).
  (* [comment removed for export] *)
  Definition mm_destroyed_model (addr n : word) : Model :=
    vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
      (with_vmmaps (mkVmMapsFull (vm_reserved h)
                      (maps_subtract (vm_maps h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                      (maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                      (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo).
  (* [comment removed for export] *)
  Definition mm_unmapped_model (addr n : word) : Model :=
    vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
      (with_vmmaps (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) addr)
                      (maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                      (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo).
End Models.

(* [comment removed for export] *)
Definition mm_grant_rw (mo : Model) (hint a : word) (nZ : Z) : Prop :=
  let h := m_vmmaps mo in
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top h /\
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true /\
  (vm_backing_used mo + nZ <=? vm_limit h) = true.

Definition mm_grant_none (mo : Model) (hint a : word) (nZ : Z) : Prop :=
  let h := m_vmmaps mo in
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top h /\
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.

(* [comment removed for export] *)
Definition mm_refusable (mo : Model) (prot flags : Z) (nZ : Z) : bool :=
  if (prot =? mm_prot_rw) && (flags =? mm_flags_anon) then mmap_grant_refusable (Z_to_bv 64 flags) mo nZ
  else if (prot =? mm_prot_none) && (flags =? mm_flags_anon) then mmap_reserve_refusable mo nZ
  else false.

(* [comment removed for export] *)
Definition anstep (n : node) (mo : Model) (rsp : resp) (mo' : Model) : Prop :=
  let h := m_vmmaps mo in
  match n with
  | NBrk req =>
      let rq := Z_to_bv 64 req in
      exists r, brk_r_ok mo rq r = true /\
        rsp = mkEffectU r [] (brk_zeros rq r (vm_brk h)) (brk_unmaps r (vm_brk h)) [] [] /\
        mo' = with_brk_next mo rq r
  | NMmap addr len prot flags =>
      let nZ := mmap_len len in
      let n := Z_to_bv 64 nZ in
      let hint := Z_to_bv 64 addr in
      (* [comment removed for export] *)
      (exists e, (In e mmap_errnos /\ mm_refusable mo prot flags nZ = true) /\ rsp = efferr e /\ mo' = mo)
      \/ (prot = mm_prot_rw /\ flags = mm_flags_anon /\
          exists a, mm_grant_rw mo hint a nZ /\ rsp = mkEffect a [] [(a, n)] /\ mo' = mm_anon_model mo a n)
      \/ (prot = mm_prot_none /\ flags = mm_flags_anon /\
          exists a, mm_grant_none mo hint a nZ /\ rsp = mkEffectU a [] [] [(a, n)] [] [] /\ mo' = mm_none_model mo a n)
      \/ (prot = mm_prot_none /\ flags = mm_flags_fixed /\
          (  (rsp = mkEffectU hint [] [] [(hint, n)] [] [] /\ mo' = mm_fixed_model mo hint n)
          \/ (exists e, In e mmap_destructive_errnos /\ rsp = mkEffectU (errno_ret e) [] [] [(hint, n)] [] [] /\
                        mo' = mm_destroyed_model mo hint n)))
          (* [comment removed for export] *)
  | NMunmap addr len =>
      let a := Z_to_bv 64 addr in
      let n := Z_to_bv 64 (mmap_len len) in
      rsp = mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] [] /\ mo' = mm_unmapped_model mo a n
  | NMprotect addr len prot =>
      let a := Z_to_bv 64 addr in
      let n := Z_to_bv 64 (mmap_len len) in
      (* [comment removed for export] *)
      (exists e, (In e mprotect_errnos /\ mprotect_refusable mo a n = true) /\ rsp = efferr e /\ mo' = mo)
      \/ (mprotect_budget_ok mo a n = true /\ rsp = mkEffect (Z_to_bv 64 0) [] [(a, n)] /\
          mo' = mprotect_model_next mo a n)
  | NMremap old ol nl fl =>
      let o := Z_to_bv 64 old in
      let onZ := mmap_len ol in let nnZ := mmap_len nl in
      let on := Z_to_bv 64 onZ in let nn := Z_to_bv 64 nnZ in
      (* [comment removed for export] *)
      (onZ = nnZ /\ rsp = eff0 o /\ mo' = mo)
      \/ (onZ <> nnZ /\
          (  (exists e, In e mremap_errnos /\ rsp = efferr e /\ mo' = mo)
          \/ (nnZ < onZ /\ rsp = mkEffectU o [] [] [((o + nn)%bv, Z_to_bv 64 (onZ - nnZ))] [] [] /\
              mo' = mremap_model_next mo o on o nn)
          \/ (onZ < nnZ /\ mremap_inplace_grow_b mo o on nn onZ nnZ = true /\
              rsp = mkEffect o [] [((o + on)%bv, Z_to_bv 64 (nnZ - onZ))] /\
              mo' = mremap_model_next mo o on o nn)
          \/ (onZ < nnZ /\ exists d, mremap_fresh_b mo onZ nnZ o on d nn = true /\
              rsp = mkEffectU d [] [((d + on)%bv, Z_to_bv 64 (nnZ - onZ))] [(o, on)] [mkCopy o d on] [] /\
              mo' = mremap_model_next mo o on d nn)))
  | _ => False
  end.

Definition rnstep (n : node) (mo : Model) (rsp : resp) (mo' : Model) : Prop :=
  match n with
  | NMmap addr len prot flags =>
      let nZ := mmap_len len in
      let n := Z_to_bv 64 nZ in
      let hint := Z_to_bv 64 addr in
      (exists e, In e mmap_errnos /\ rsp = efferr e /\ mo' = mo)
      \/ (prot = mm_prot_rw /\ flags = mm_flags_anon /\
          exists a, mm_grant_rw mo hint a nZ /\ rsp = mkEffect a [] [(a, n)] /\ mo' = mm_anon_model mo a n)
      \/ (prot = mm_prot_none /\ flags = mm_flags_anon /\
          exists a, mm_grant_none mo hint a nZ /\ rsp = mkEffectU a [] [] [(a, n)] [] [] /\ mo' = mm_none_model mo a n)
      \/ (prot = mm_prot_none /\ flags = mm_flags_fixed /\
          (  (rsp = mkEffectU hint [] [] [(hint, n)] [] [] /\ mo' = mm_fixed_model mo hint n)
          \/ (exists e, In e mmap_errnos /\ rsp = mkEffectU (errno_ret e) [] [] [(hint, n)] [] [] /\
                        mo' = mm_destroyed_model mo hint n)))
  | NMprotect addr len prot =>
      let a := Z_to_bv 64 addr in
      let n := Z_to_bv 64 (mmap_len len) in
      (exists e, In e mprotect_errnos /\ rsp = efferr e /\ mo' = mo)
      \/ (mprotect_budget_ok mo a n = true /\ rsp = mkEffect (Z_to_bv 64 0) [] [(a, n)] /\
          mo' = mprotect_model_next mo a n)
  | NBrk _ | NMunmap _ _ | NMremap _ _ _ _ => anstep n mo rsp mo'
  | _ => False
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_spec_216 : forall i m o,
  bv_unsigned (in_sysno i) = 216%Z ->
  syscall_spec i m o <-> mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

(* [comment removed for export] *)
Lemma mremap_outcome : forall old old_size new_size flags i m o,
  bv_unsigned flags = MREMAP_MAYMOVE ->
  (bv_unsigned old mod page_size = 0)%Z ->
  page_align_is0_b new_size = false ->
  page_align_is0_b old_size = false ->
  m_vm_lazy m = [] ->
  let h := m_vmmaps m in
  let old_nZ := page_round_up_Z (bv_unsigned old_size) in
  let new_nZ := page_round_up_Z (bv_unsigned new_size) in
  let old_n := Z_to_bv 64 old_nZ in
  let new_n := Z_to_bv 64 new_nZ in
  mremap_source_b h old old_n old_nZ = true ->
  mremap_spec old old_size new_size flags i m o <->
    (old_nZ = new_nZ /\ o = Ok (mkEffect old [] []) m [])
    \/ (old_nZ <> new_nZ /\
        (  (exists e, In e mremap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
        \/ ((new_nZ < old_nZ)%Z /\
            o = Ok (mremap_inplace_effect old old_n new_n old_nZ new_nZ) (mremap_model_next m old old_n old new_n) [])
        \/ ((old_nZ < new_nZ)%Z /\ mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true /\
            o = Ok (mremap_inplace_effect old old_n new_n old_nZ new_nZ) (mremap_model_next m old old_n old new_n) [])
        \/ ((old_nZ < new_nZ)%Z /\ exists dst, mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true /\
            o = Ok (mremap_move_effect old old_n dst old_nZ new_nZ) (mremap_model_next m old old_n dst new_n) []))).
Proof.
  intros old old_size new_size flags i m o Hfl Hal Hnew Hold Hlazy. cbv zeta. intros Hsrc.
  unfold mremap_spec.
  rewrite Hfl. change (negb (Z.eqb MREMAP_MAYMOVE MREMAP_MAYMOVE)) with false. cbv iota.
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb]. rewrite Hnew, Hold.
  assert (Huni : mremap_backing_uniform_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) = true).
  { unfold mremap_backing_uniform_b. rewrite Hlazy. reflexivity. }
  cbv zeta.
  set (onZ := page_round_up_Z (bv_unsigned old_size)) in *.
  set (nnZ := page_round_up_Z (bv_unsigned new_size)) in *.
  destruct (onZ =? nnZ)%Z eqn:Heqb.
  { (* [comment removed for export] *)
    apply Z.eqb_eq in Heqb as Eeq.
    sys_unfold. split.
    - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hsrc, Huni in *; cbn [andb negb] in *; inv_sys.
      left. split; [exact Eeq|reflexivity].
    - intros [[_ ->]|[Hne _]]; [|exfalso; exact (Hne Eeq)].
      eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Huni. cbn [andb negb]. split; reflexivity. }
  apply Z.eqb_neq in Heqb as Ene.
  destruct (nnZ <? onZ)%Z eqn:Hltb.
  { (* [comment removed for export] *)
    apply Z.ltb_lt in Hltb as Hlt.
    sys_unfold. split.
    - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hsrc, Huni in *; cbn [andb negb] in *; inv_sys.
      + right. split; [exact Ene|]. left. eexists; split; [eassumption|reflexivity].
      + right. split; [exact Ene|]. right; left. split; [exact Hlt|reflexivity].
    - intros [[E _]|[_ [(e & He & ->)|[[_ ->]|[[Hc _]|[Hc _]]]]]]; [congruence| | |lia|lia].
      + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Huni. cbn [andb negb]. split; [|reflexivity].
        left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
      + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Huni. cbn [andb negb]. split; [|reflexivity].
        right. eexists _, _, _, _. repeat split; reflexivity. }
  apply Z.ltb_ge in Hltb as Hge. assert (Hgt : (onZ < nnZ)%Z) by lia.
  destruct (mremap_inplace_grow_b m old (Z_to_bv 64 onZ) (Z_to_bv 64 nnZ) onZ nnZ) eqn:Hig.
  { (* [comment removed for export] *)
    sys_unfold. split.
    - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hsrc, Huni in *; cbn [andb negb] in *; inv_sys;
        rewrite ?Hig in *; inv_sys.
      + right. split; [exact Ene|]. left. eexists; split; [eassumption|reflexivity].
      + right. split; [exact Ene|]. right; right; left. split; [exact Hgt|]. split; [reflexivity|reflexivity].
      + right. split; [exact Ene|]. right; right; right. split; [exact Hgt|]. eexists; split; [eassumption|reflexivity].
    - intros [[E _]|[_ [(e & He & ->)|[[Hc _]|[(_ & _ & ->)|(_ & dst & Hd & ->)]]]]]; [congruence| |lia| |].
      + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Huni. cbn [andb negb]. split; [|reflexivity].
        left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
      + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Huni. cbn [andb negb]. split; [|reflexivity].
        right. rewrite Hig. left. eexists _, _, _, _. repeat split; reflexivity.
      + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Huni. cbn [andb negb]. split; [|reflexivity].
        right. rewrite Hig. right. eexists _, _, _, _. split; [exists dst; split; [exact Hd|reflexivity]|].
        split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity. }
  { (* [comment removed for export] *)
    sys_unfold. split.
    - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hsrc, Huni in *; cbn [andb negb] in *; inv_sys;
        rewrite ?Hig in *; inv_sys.
      + right. split; [exact Ene|]. left. eexists; split; [eassumption|reflexivity].
      + right. split; [exact Ene|]. right; right; right. split; [exact Hgt|]. eexists; split; [eassumption|reflexivity].
    - intros [[E _]|[_ [(e & He & ->)|[[Hc _]|[(_ & Hc & _)|(_ & dst & Hd & ->)]]]]]; [congruence| |lia|congruence|].
      + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Huni. cbn [andb negb]. split; [|reflexivity].
        left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
      + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Huni. cbn [andb negb]. split; [|reflexivity].
        right. rewrite Hig. eexists _, _, _, _. split; [exists dst; split; [exact Hd|reflexivity]|].
        split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity. }
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition input_at (n : node) (i : SyscallInput) : Prop :=
  match n with
  | NBrk req => bv_unsigned (in_sysno i) = 214 /\ in_arg i 0 = Z_to_bv 64 req
  | NMmap addr len prot flags =>
      bv_unsigned (in_sysno i) = 222 /\ in_arg i 0 = Z_to_bv 64 addr /\ in_arg i 1 = Z_to_bv 64 len /\
      in_arg i 2 = Z_to_bv 64 prot /\ in_arg i 3 = Z_to_bv 64 flags /\
      in_arg i 4 = Z_to_bv 64 (-1) /\ in_arg i 5 = Z_to_bv 64 0
  | NMunmap addr len => bv_unsigned (in_sysno i) = 215 /\ in_arg i 0 = Z_to_bv 64 addr /\ in_arg i 1 = Z_to_bv 64 len
  | NMprotect addr len prot =>
      bv_unsigned (in_sysno i) = 226 /\ in_arg i 0 = Z_to_bv 64 addr /\ in_arg i 1 = Z_to_bv 64 len /\
      in_arg i 2 = Z_to_bv 64 prot
  | NMremap old ol nl fl =>
      bv_unsigned (in_sysno i) = 216 /\ in_arg i 0 = Z_to_bv 64 old /\ in_arg i 1 = Z_to_bv 64 ol /\
      in_arg i 2 = Z_to_bv 64 nl /\ in_arg i 3 = Z_to_bv 64 fl
  | _ => False
  end.

Lemma input_at_node_input : forall n i, node_input n = Some i -> input_at n i.
Proof.
  intros n i H; destruct n; cbn in H; try discriminate; injection H as <-; cbn; repeat split; reflexivity.
Qed.

Lemma input_at_sys_input : forall segs n ms,
  alloc_node n = true -> at_node segs n ms ->
  exists x8, ms_svc_pending ms = Some x8 /\ input_at n (sys_input segs ms x8).
Proof.
  intros segs n ms Hn Hat; destruct n; cbn in Hn; try discriminate; cbn in Hat;
    eexists; (split; [apply (proj1 Hat)|]); cbn -[Z_to_bv bv_unsigned];
    rewrite ?in_a0_si, ?in_a1_si, ?in_a2_si, ?in_a3_si, ?in_a4_si, ?in_a5_si;
    unfold in_sysno, sys_input; rewrite ?unsigned_lit by lia; tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac lit_tf := vm_compute; reflexivity.

Lemma brk_outcome_i : forall req i mo, input_at (NBrk req) i ->
  forall o, syscall_spec i mo o <-> exists rsp mo', o = Ok rsp mo' [] /\ anstep (NBrk req) mo rsp mo'.
Proof.
  intros req i mo [Hno Ha0] o. rewrite (syscall_spec_214 i mo o Hno), Ha0, brk_outcome. cbn [anstep].
  split.
  - intros (r & Hr & ->). eexists _, _. split; [reflexivity|]. exists r. auto.
  - intros (rsp & mo' & -> & r & Hr & -> & ->). exists r. auto.
Qed.

Lemma mm_refusable_rw : forall mo nZ,
  mm_refusable mo mm_prot_rw mm_flags_anon nZ = mmap_grant_refusable (Z_to_bv 64 mm_flags_anon) mo nZ.
Proof. reflexivity. Qed.
Lemma mm_refusable_none : forall mo nZ,
  mm_refusable mo mm_prot_none mm_flags_anon nZ = mmap_reserve_refusable mo nZ.
Proof. reflexivity. Qed.
Lemma mm_refusable_fixed : forall mo nZ, mm_refusable mo mm_prot_none mm_flags_fixed nZ = false.
Proof. reflexivity. Qed.

Lemma mmap_outcome_i : forall addr len prot flags i mo, input_at (NMmap addr len prot flags) i ->
  m_vm_lazy mo = [] -> nsafe (NMmap addr len prot flags) mo ->
  forall o, syscall_spec i mo o <-> exists rsp mo', o = Ok rsp mo' [] /\ rnstep (NMmap addr len prot flags) mo rsp mo'.
Proof.
  intros addr len prot flags i mo (Hno & H0 & H1 & H2 & H3 & H4 & H5) Hlazy Hsafe o.
  cbn [nsafe] in Hsafe. destruct Hsafe as (Haddr & Hlen & Hshape).
  assert (E1 : w_is0 (Z_to_bv 64 len) = false) by (apply w_is0_false; lia).
  rewrite (syscall_spec_222 i mo o Hno), H0, H1, H2, H3, H4, H5. cbn [rnstep].
  unfold mmap_len. 
  destruct Hshape as [[-> ->] | [[-> ->] | (-> & -> & Hal & Hpos & Hce & Hrf & Hmc)]].
  - (* [comment removed for export] *)
    rewrite (mmap_rw_outcome (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 mm_prot_rw) (Z_to_bv 64 mm_flags_anon)
               (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i mo o ltac:(lit_tf) ltac:(lit_tf) E1 ltac:(lit_tf)).
    unfold mmap_err_out, mmap_noreserve_backed_ok, with_mmap_backing.
    replace (mmap_noreserve_b (Z_to_bv 64 mm_flags_anon)) with false by lit_tf.
    rewrite (u64_of_Z len) by lia.
    split.
    + intros [(e & He & ->) | (a & Hg & ->)]; eexists _, _; (split; [reflexivity|]).
      * left. exists e. split; [exact He|]. split; reflexivity.
      * right; left. split; [reflexivity|]. split; [reflexivity|]. exists a. split; [exact Hg|]. split; reflexivity.
    + intros (rsp & mo' & -> & [(e & He & -> & ->) | [(_ & _ & a & Hg & -> & ->) | [(Hc & _) | (Hc & _)]]]);
        [ left; exists e; split; [exact He | reflexivity] | right; exists a; split; [exact Hg | reflexivity]
        | exfalso | exfalso];
        unfold mm_prot_rw, mm_prot_none in Hc; lia.
  - (* [comment removed for export] *)
    rewrite (mmap_noaccess_outcome (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 mm_prot_none) (Z_to_bv 64 mm_flags_anon)
               (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i mo o ltac:(lit_tf) ltac:(lit_tf) E1 ltac:(lit_tf) ltac:(lit_tf)).
    unfold mmap_err_out, with_mmap_backing.
    replace (mmap_noreserve_b (Z_to_bv 64 mm_flags_anon)) with false by lit_tf.
    rewrite (u64_of_Z len) by lia.
    split.
    + intros [(e & He & ->) | (a & Hg & ->)]; eexists _, _; (split; [reflexivity|]).
      * left. exists e. split; [exact He|]. split; reflexivity.
      * right; right; left. split; [reflexivity|]. split; [reflexivity|]. exists a. split; [exact Hg|]. split; reflexivity.
    + intros (rsp & mo' & -> & [(e & He & -> & ->) | [(Hc & _) | [(_ & _ & a & Hg & -> & ->) | (_ & Hc & _)]]]);
        [ left; exists e; split; [exact He | reflexivity] | exfalso | right; exists a; split; [exact Hg | reflexivity]
        | exfalso].
      * unfold mm_prot_rw, mm_prot_none in Hc; lia.
      * unfold mm_flags_anon, mm_flags_fixed in Hc; lia.
  - (* [comment removed for export] *)
    assert (Hlen2 : len < 2^64).
    { pose proof (mmap_len_ge len). pose proof (alloc_top_lt (m_vmmaps mo)). unfold mmap_len in *. unfold two_pow_64 in *. lia. }
    rewrite (mmap_fixed_noaccess_outcome (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 mm_prot_none) (Z_to_bv 64 mm_flags_fixed)
               (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i mo o ltac:(lit_tf) ltac:(lit_tf) E1 ltac:(lit_tf) ltac:(lit_tf) ltac:(lit_tf));
      rewrite ?(u64_of_Z len) by lia; rewrite ?(u64_of_Z addr) by lia;
      [| exact Hce | exact Hal | exact Hpos | exact Hrf | exact Hmc].
    unfold mmap_err_out, with_mmap_replacement, with_mmap_backing.
    replace (mmap_noreserve_b (Z_to_bv 64 mm_flags_fixed)) with false by lit_tf.
    unfold mm_fixed_model. rewrite (u64_of_Z addr) by lia.
    split.
    + intros [(e & He & ->) | [-> | (e & He & ->)]]; eexists _, _; (split; [reflexivity|]).
      * left. exists e. split; [exact He|]. split; reflexivity.
      * right; right; right. split; [reflexivity|]. split; [reflexivity|]. left. split; reflexivity.
      * right; right; right. split; [reflexivity|]. split; [reflexivity|]. right.
        exists e. split; [exact He|]. split; reflexivity.
    + intros (rsp & mo' & -> & [(e & He & -> & ->) | [(_ & Hc & _) | [(_ & Hc & _) | (_ & _ & [(-> & ->) | (e & He & -> & ->)])]]]);
        [ left; exists e; split; [exact He | reflexivity] | exfalso | exfalso | right; left; reflexivity
        | right; right; exists e; split; [exact He | reflexivity] ];
        unfold mm_flags_anon, mm_flags_fixed in Hc; lia.
Qed.

Lemma munmap_outcome_i : forall addr len i mo, input_at (NMunmap addr len) i ->
  nsafe (NMunmap addr len) mo ->
  forall o, syscall_spec i mo o <-> exists rsp mo', o = Ok rsp mo' [] /\ anstep (NMunmap addr len) mo rsp mo'.
Proof.
  intros addr len i mo (Hno & H0 & H1) Hsafe o.
  cbn [nsafe] in Hsafe. destruct Hsafe as (Ha0 & Hal & Hlen & Hnw & Hhas).
  pose proof (mmap_len_ge len) as Hge. unfold mmap_len in Hge.
  assert (Hlen2 : len < 2^64) by (unfold TASK_SIZE in *; lia).
  assert (Hadd2 : addr < 2^64) by (unfold TASK_SIZE in *; lia).
  rewrite (syscall_spec_215 i mo o Hno), H0, H1. cbn [anstep]. unfold mmap_len, mm_unmapped_model.
  rewrite (munmap_exact_outcome (Z_to_bv 64 addr) (Z_to_bv 64 len) i mo o);
    rewrite ?(u64_of_Z len) by lia; rewrite ?(u64_of_Z addr) by lia;
    [| exact Hal | apply w_is0_false; lia | exact Hnw | exact Hhas].
  unfold with_mmap_destroyed. rewrite (u64_of_Z addr) by lia.
  split.
  - intros ->. eexists _, _. split; [reflexivity|]. split; reflexivity.
  - intros (rsp & mo' & -> & -> & ->). reflexivity.
Qed.

Lemma mprotect_outcome_i : forall addr len prot i mo, input_at (NMprotect addr len prot) i ->
  nsafe (NMprotect addr len prot) mo ->
  forall o, syscall_spec i mo o <-> exists rsp mo', o = Ok rsp mo' [] /\ rnstep (NMprotect addr len prot) mo rsp mo'.
Proof.
  intros addr len prot i mo (Hno & H0 & H1 & H2) Hsafe o.
  cbn [nsafe] in Hsafe. destruct Hsafe as (-> & Ha0 & Hal & Hlen & Hnw & Hna & Hma).
  pose proof (mmap_len_ge len) as Hge. unfold mmap_len in Hge.
  assert (Hlen2 : len < 2^64) by lia.
  rewrite (syscall_spec_226 i mo o Hno), H0, H1, H2. cbn [rnstep]. unfold mmap_len.
  rewrite (mprotect_expose_outcome (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 mm_prot_rw) i mo o);
    rewrite ?(u64_of_Z len) by lia; rewrite ?(u64_of_Z addr) by lia;
    [| lit_tf | exact Hal | apply w_is0_false; lia | rewrite two_pow_64_val; exact Hnw | lit_tf | exact Hna | exact Hma].
  split.
  - intros [(e & He & ->) | (Hb & ->)]; eexists _, _; (split; [reflexivity|]).
    + left. exists e. split; [exact He|]. split; reflexivity.
    + right. split; [exact Hb|]. split; reflexivity.
  - intros (rsp & mo' & -> & [(e & He & -> & ->) | (Hb & -> & ->)]).
    + left. exists e. split; [exact He | reflexivity].
    + right. split; [exact Hb | reflexivity].
Qed.

Lemma mremap_outcome_i : forall old ol nl fl i mo, input_at (NMremap old ol nl fl) i ->
  m_vm_lazy mo = [] -> nsafe (NMremap old ol nl fl) mo ->
  forall o, syscall_spec i mo o <-> exists rsp mo', o = Ok rsp mo' [] /\ anstep (NMremap old ol nl fl) mo rsp mo'.
Proof.
  intros old ol nl fl i mo (Hno & H0 & H1 & H2 & H3) Hlazy Hsafe o.
  cbn [nsafe] in Hsafe. destruct Hsafe as (-> & Hold & Hal & Hol & Hnl & Hnl2 & Hce & Hrf & Hhas & Hna).
  pose proof (mmap_len_ge ol) as Hge1. pose proof (mmap_len_ge nl) as Hge2. unfold mmap_len in Hge1, Hge2.
  assert (Hcv : alloc_top (m_vmmaps mo) < 2^64) by (pose proof (alloc_top_lt (m_vmmaps mo)); unfold two_pow_64 in *; lia).
  assert (Hol2 : ol < 2^64) by lia. assert (Hnl3 : nl < 2^64) by lia. assert (Hold2 : old < 2^64) by lia.
  rewrite (syscall_spec_216 i mo o Hno), H0, H1, H2, H3. cbn [anstep]. unfold mmap_len.
  rewrite (mremap_outcome (Z_to_bv 64 old) (Z_to_bv 64 ol) (Z_to_bv 64 nl) (Z_to_bv 64 MREMAP_MAYMOVE) i mo o);
    rewrite ?(u64_of_Z ol) by lia; rewrite ?(u64_of_Z nl) by lia; rewrite ?(u64_of_Z old) by lia;
    [| apply u64_of_Z; unfold MREMAP_MAYMOVE; lia | exact Hal
     | unfold page_align_is0_b; rewrite w_is0_false by lia; rewrite (u64_of_Z nl) by lia;
       rewrite two_pow_64_val; apply Z.leb_gt; lia
     | unfold page_align_is0_b; rewrite w_is0_false by lia; rewrite (u64_of_Z ol) by lia;
       rewrite two_pow_64_val; apply Z.leb_gt; lia
     | exact Hlazy
     | unfold mremap_source_b; rewrite (u64_of_Z old) by lia; rewrite (proj2 (Z.leb_le _ _) Hce), Hrf, Hhas, Hna; reflexivity ].
  unfold mremap_inplace_effect, mremap_move_effect, mremap_tail.
  set (onZ := page_round_up_Z ol). set (nnZ := page_round_up_Z nl).
  split.
  - intros [[E ->] | [Ene [(e & He & ->) | [[Hlt ->] | [(Hlt & Hig & ->) | (Hlt & d & Hd & ->)]]]]];
      eexists _, _; (split; [reflexivity|]).
    + left. auto.
    + right. split; [exact Ene|]. left. exists e. auto.
    + right. split; [exact Ene|]. right; left. rewrite (proj2 (Z.ltb_lt _ _) Hlt). auto.
    + right. split; [exact Ene|]. right; right; left. rewrite (proj2 (Z.ltb_ge nnZ onZ) ltac:(lia)), (proj2 (Z.ltb_lt _ _) Hlt). auto.
    + right. split; [exact Ene|]. right; right; right. split; [exact Hlt|]. exists d. rewrite (proj2 (Z.ltb_lt _ _) Hlt). auto.
  - intros (rsp & mo' & -> & [(E & -> & ->) | (Ene & [(e & He & -> & ->) | [(Hlt & -> & ->) | [(Hlt & Hig & -> & ->) | (Hlt & d & Hd & -> & ->)]]])]).
    + left. auto.
    + right. split; [exact Ene|]. left. exists e. auto.
    + right. split; [exact Ene|]. right; left. rewrite (proj2 (Z.ltb_lt _ _) Hlt). auto.
    + right. split; [exact Ene|]. right; right; left. rewrite (proj2 (Z.ltb_ge nnZ onZ) ltac:(lia)), (proj2 (Z.ltb_lt _ _) Hlt). auto.
    + right. split; [exact Ene|]. right; right; right. split; [exact Hlt|]. exists d. rewrite (proj2 (Z.ltb_lt _ _) Hlt). auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem alloc_outcome_i : forall n i mo,
  alloc_node n = true -> input_at n i -> m_vm_lazy mo = [] -> nsafe n mo ->
  forall o, syscall_spec i mo o <-> exists rsp mo', o = Ok rsp mo' [] /\ rnstep n mo rsp mo'.
Proof.
  intros n i mo Hn Hi Hlazy Hsafe; destruct n; cbn in Hn; try discriminate.
  - cbn [rnstep]. apply brk_outcome_i; assumption.
  - apply mmap_outcome_i; assumption.
  - cbn [rnstep]. apply munmap_outcome_i; assumption.
  - apply mprotect_outcome_i; assumption.
  - cbn [rnstep]. apply mremap_outcome_i; assumption.
Qed.

(* [comment removed for export] *)
Corollary nstep_alloc_iff : forall n mo rsp mo' evs,
  alloc_node n = true -> m_vm_lazy mo = [] -> nsafe n mo ->
  nstep n mo rsp mo' evs <-> evs = [] /\ rnstep n mo rsp mo'.
Proof.
  intros n mo rsp mo' evs Hn Hlazy Hsafe.
  destruct (node_input n) as [i|] eqn:Hi.
  2:{ exfalso. destruct n; cbn in Hn; try discriminate Hn; cbn in Hi; discriminate Hi. }
  pose proof (alloc_outcome_i n i mo Hn (input_at_node_input n i Hi) Hlazy Hsafe (Ok rsp mo' evs)) as HO.
  transitivity (evs = [] /\ syscall_spec i mo (Ok rsp mo' evs)).
  { destruct n; cbn in Hn; try discriminate; cbn [nstep]; rewrite Hi; tauto. }
  rewrite HO. split.
  - intros (-> & rsp1 & mo1 & E & Ha). injection E as <- <-. auto.
  - intros (-> & Ha). split; [reflexivity|]. eexists _, _. eauto.
Qed.

(* [comment removed for export] *)
Corollary at_node_outcome : forall segs n ms mo,
  alloc_node n = true -> at_node segs n ms -> m_vm_lazy mo = [] -> nsafe n mo ->
  exists x8, ms_svc_pending ms = Some x8 /\
    forall o, syscall_spec (sys_input segs ms x8) mo o <-> exists rsp mo', o = Ok rsp mo' [] /\ rnstep n mo rsp mo'.
Proof.
  intros segs n ms mo Hn Hat Hlazy Hsafe.
  destruct (input_at_sys_input segs n ms Hn Hat) as (x8 & Hsvc & Hi).
  exists x8. split; [exact Hsvc|]. apply alloc_outcome_i; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma vm_only_with_vmmaps : forall h mo, vm_only mo (with_vmmaps h mo).
Proof. intros; repeat split; reflexivity. Qed.

Lemma vm_only_with_vm_backing : forall l p mo, vm_only mo (with_vm_backing l p mo).
Proof. intros; repeat split; reflexivity. Qed.

Lemma vm_only_vm_forget_range : forall lo hi mo, vm_only mo (vm_forget_range lo hi mo).
Proof. intros. unfold vm_forget_range. apply vm_only_with_vm_backing. Qed.

Lemma vm_only_forget_vm_ranges : forall rs mo, vm_only mo (forget_vm_ranges rs mo).
Proof.
  induction rs as [|[a n] rs IH]; intros mo; cbn [forget_vm_ranges]; [apply vm_only_refl|].
  eapply vm_only_trans; [apply vm_only_vm_forget_range | apply IH].
Qed.

Lemma anstep_vm_only : forall n mo rsp mo', anstep n mo rsp mo' -> vm_only mo mo'.
Proof.
  intros n mo rsp mo' H; destruct n; cbn [anstep] in H; try contradiction.
  - destruct H as (r & _ & _ & ->). unfold with_brk_next.
    eapply vm_only_trans; [apply vm_only_with_vmmaps | apply vm_only_forget_vm_ranges].
  - destruct H as [(e & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | (_ & _ & [(_ & ->) | (e & _ & _ & ->)])]]];
      [apply vm_only_refl | apply vm_only_with_vmmaps | apply vm_only_with_vmmaps | | ];
      unfold mm_fixed_model, mm_destroyed_model;
      (eapply vm_only_trans; [apply vm_only_with_vmmaps | apply vm_only_vm_forget_range]).
  - destruct H as [_ ->]. unfold mm_unmapped_model.
    eapply vm_only_trans; [apply vm_only_with_vmmaps | apply vm_only_vm_forget_range].
  - destruct H as [(e & _ & _ & ->) | (_ & _ & ->)]; [apply vm_only_refl|]. unfold mprotect_model_next. apply vm_only_with_vmmaps.
  - destruct H as [(_ & _ & ->) | (_ & [(e & _ & _ & ->) | [(_ & _ & ->) | [(_ & _ & _ & ->) | (_ & d & _ & _ & ->)]]])];
      [apply vm_only_refl | apply vm_only_refl | | |];
      unfold mremap_model_next, vm_resize_backing;
      (eapply vm_only_trans; [apply vm_only_with_vmmaps | apply vm_only_with_vm_backing]).
Qed.

Lemma vm_forget_range_lazy : forall lo hi mo,
  m_vm_lazy (vm_forget_range lo hi mo) = maps_subtract (m_vm_lazy mo) lo hi.
Proof. reflexivity. Qed.

Lemma m_vm_lazy_with_vmmaps : forall h mo, m_vm_lazy (with_vmmaps h mo) = m_vm_lazy mo.
Proof. reflexivity. Qed.

Lemma m_vm_materialized_with_vmmaps : forall h mo, m_vm_materialized (with_vmmaps h mo) = m_vm_materialized mo.
Proof. reflexivity. Qed.

Lemma m_vm_lazy_with_vm_backing : forall l p mo, m_vm_lazy (with_vm_backing l p mo) = l.
Proof. reflexivity. Qed.

Lemma m_vm_materialized_with_vm_backing : forall l p mo, m_vm_materialized (with_vm_backing l p mo) = p.
Proof. reflexivity. Qed.

Lemma maps_subtract_nil : forall lo hi, maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.

Lemma forget_vm_ranges_lazy_nil : forall rs mo, m_vm_lazy mo = [] -> m_vm_lazy (forget_vm_ranges rs mo) = [].
Proof.
  induction rs as [|[a n] rs IH]; intros mo H; cbn [forget_vm_ranges]; [exact H|].
  apply IH. rewrite vm_forget_range_lazy, H. reflexivity.
Qed.

Lemma vm_forget_range_materialized : forall lo hi mo,
  m_vm_materialized (vm_forget_range lo hi mo) = List.filter (page_outside_range lo hi) (m_vm_materialized mo).
Proof. reflexivity. Qed.

Lemma forget_vm_ranges_materialized_nil : forall rs mo,
  m_vm_materialized mo = [] -> m_vm_materialized (forget_vm_ranges rs mo) = [].
Proof.
  induction rs as [|[a n] rs IH]; intros mo H; cbn [forget_vm_ranges]; [exact H|].
  apply IH. rewrite vm_forget_range_materialized, H. reflexivity.
Qed.

Lemma anstep_lazy_nil : forall n mo rsp mo', m_vm_lazy mo = [] -> anstep n mo rsp mo' -> m_vm_lazy mo' = [].
Proof.
  intros n mo rsp mo' Hl H; destruct n; cbn [anstep] in H; try contradiction.
  - destruct H as (r & _ & _ & ->). unfold with_brk_next. apply forget_vm_ranges_lazy_nil. exact Hl.
  - destruct H as [(e & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | (_ & _ & [(_ & ->) | (e & _ & _ & ->)])]]];
      [exact Hl | exact Hl | exact Hl | | ]; unfold mm_fixed_model, mm_destroyed_model;
      rewrite vm_forget_range_lazy, m_vm_lazy_with_vmmaps, Hl; apply maps_subtract_nil.
  - destruct H as [_ ->]. unfold mm_unmapped_model.
    rewrite vm_forget_range_lazy, m_vm_lazy_with_vmmaps, Hl; apply maps_subtract_nil.
  - destruct H as [(e & _ & _ & ->) | (_ & _ & ->)]; [exact Hl|]. unfold mprotect_model_next. rewrite m_vm_lazy_with_vmmaps. exact Hl.
  - destruct H as [(_ & _ & ->) | (_ & [(e & _ & _ & ->) | [(_ & _ & ->) | [(_ & _ & _ & ->) | (_ & d & _ & _ & ->)]]])];
      [exact Hl | exact Hl | | |];
      unfold mremap_model_next, vm_resize_backing, mremap_source_lazy_b; rewrite Hl; cbn [map_contains existsb];
      rewrite m_vm_lazy_with_vm_backing, m_vm_lazy_with_vmmaps, Hl, !maps_subtract_nil; reflexivity.
Qed.

Lemma anstep_materialized_nil : forall n mo rsp mo',
  m_vm_lazy mo = [] -> m_vm_materialized mo = [] -> anstep n mo rsp mo' -> m_vm_materialized mo' = [].
Proof.
  intros n mo rsp mo' Hl Hm H; destruct n; cbn [anstep] in H; try contradiction.
  - destruct H as (r & _ & _ & ->). unfold with_brk_next. apply forget_vm_ranges_materialized_nil. exact Hm.
  - destruct H as [(e & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | (_ & _ & [(_ & ->) | (e & _ & _ & ->)])]]];
      [exact Hm | exact Hm | exact Hm | | ]; unfold mm_fixed_model, mm_destroyed_model;
      rewrite vm_forget_range_materialized, m_vm_materialized_with_vmmaps, Hm; reflexivity.
  - destruct H as [_ ->]. unfold mm_unmapped_model.
    rewrite vm_forget_range_materialized, m_vm_materialized_with_vmmaps, Hm; reflexivity.
  - destruct H as [(e & _ & _ & ->) | (_ & _ & ->)]; [exact Hm|]. unfold mprotect_model_next. rewrite m_vm_materialized_with_vmmaps. exact Hm.
  - destruct H as [(_ & _ & ->) | (_ & [(e & _ & _ & ->) | [(_ & _ & ->) | [(_ & _ & _ & ->) | (_ & d & _ & _ & ->)]]])];
      [exact Hm | exact Hm | | |];
      unfold mremap_model_next, vm_resize_backing, mremap_source_lazy_b; rewrite Hl; cbn [map_contains existsb];
      rewrite m_vm_materialized_with_vm_backing, m_vm_materialized_with_vmmaps, Hm; reflexivity.
Qed.

Theorem anstep_MOK : forall n mo rsp mo', MOK mo -> anstep n mo rsp mo' -> MOK mo'.
Proof.
  intros n mo rsp mo' [Hh Hl] H. split.
  - destruct (vm_only_facts _ _ (anstep_vm_only _ _ _ _ H)) as (_ & _ & E & _). rewrite E. exact Hh.
  - eapply anstep_lazy_nil; eassumption.
Qed.

Theorem anstep_frame : forall n mo rsp mo', anstep n mo rsp mo' ->
  m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ m_halted mo' = m_halted mo /\
  m_tid mo' = m_tid mo /\ m_stdin mo' = m_stdin mo.
Proof. intros. apply vm_only_facts. eapply anstep_vm_only. eassumption. Qed.

(* [comment removed for export] *)
Theorem anstep_minv : forall n mo rsp mo', minv mo -> anstep n mo rsp mo' -> minv mo'.
Proof.
  intros n mo rsp mo' HM H.
  destruct (anstep_frame _ _ _ _ H) as (Hfds & Hfs & Hh & Htid & _).
  pose proof (anstep_lazy_nil _ _ _ _ (minv_lazy _ HM) H) as Hl.
  unfold minv in *. rewrite Hfds, Hfs, Htid. intuition.
Qed.

Lemma rnstep_vm_only : forall n mo rsp mo', rnstep n mo rsp mo' -> vm_only mo mo'.
Proof.
  intros n mo rsp mo' H; destruct n; cbn [rnstep] in H; try contradiction;
    try exact (anstep_vm_only _ _ _ _ H).
  - destruct H as [(e & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | (_ & _ & [(_ & ->) | (e & _ & _ & ->)])]]];
      [apply vm_only_refl | apply vm_only_with_vmmaps | apply vm_only_with_vmmaps | | ];
      unfold mm_fixed_model, mm_destroyed_model;
      (eapply vm_only_trans; [apply vm_only_with_vmmaps | apply vm_only_vm_forget_range]).
  - destruct H as [(e & _ & _ & ->) | (_ & _ & ->)]; [apply vm_only_refl|]. unfold mprotect_model_next. apply vm_only_with_vmmaps.
Qed.

Lemma rnstep_lazy_nil : forall n mo rsp mo', m_vm_lazy mo = [] -> rnstep n mo rsp mo' -> m_vm_lazy mo' = [].
Proof.
  intros n mo rsp mo' Hl H; destruct n; cbn [rnstep] in H; try contradiction;
    try exact (anstep_lazy_nil _ _ _ _ Hl H).
  - destruct H as [(e & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | (_ & _ & [(_ & ->) | (e & _ & _ & ->)])]]];
      [exact Hl | exact Hl | exact Hl | | ]; unfold mm_fixed_model, mm_destroyed_model;
      rewrite vm_forget_range_lazy, m_vm_lazy_with_vmmaps, Hl; apply maps_subtract_nil.
  - destruct H as [(e & _ & _ & ->) | (_ & _ & ->)]; [exact Hl|]. unfold mprotect_model_next. rewrite m_vm_lazy_with_vmmaps. exact Hl.
Qed.

Theorem rnstep_MOK : forall n mo rsp mo', MOK mo -> rnstep n mo rsp mo' -> MOK mo'.
Proof.
  intros n mo rsp mo' [Hh Hl] H. split.
  - destruct (vm_only_facts _ _ (rnstep_vm_only _ _ _ _ H)) as (_ & _ & E & _). rewrite E. exact Hh.
  - eapply rnstep_lazy_nil; eassumption.
Qed.

Lemma anstep_rnstep : forall n mo rsp mo', anstep n mo rsp mo' -> rnstep n mo rsp mo'.
Proof.
  intros n mo rsp mo' H; destruct n; try exact H; cbn [anstep] in H; cbn [rnstep].
  - destruct H as [(e & [He _] & -> & ->) | [Hg | [Hg | (Hp & Hf & [Hfx | (e & [] & _)])]]].
    + left. exists e. split; [exact He|]. split; reflexivity.
    + right; left. exact Hg.
    + right; right; left. exact Hg.
    + right; right; right. split; [exact Hp|]. split; [exact Hf|]. left. exact Hfx.
  - destruct H as [(e & [He _] & -> & ->) | Hb].
    + left. exists e. split; [exact He|]. split; reflexivity.
    + right. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ENOMEM_in_mmap_errnos : In ENOMEM mmap_errnos.
Proof. left. reflexivity. Qed.
Lemma ENOMEM_in_mprotect_errnos : In ENOMEM mprotect_errnos.
Proof. left. reflexivity. Qed.
Lemma ENOMEM_in_mremap_errnos : In ENOMEM mremap_errnos.
Proof. left. reflexivity. Qed.

Lemma brk_r_ok_refuse : forall mo req, brk_r_ok mo req (vm_brk (m_vmmaps mo)) = true.
Proof.
  intros mo req. unfold brk_r_ok.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps mo))))%Z; [apply bv_eqb_refl|].
  destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps mo)))%Z; rewrite bv_eqb_refl, orb_true_r; [reflexivity|].
  cbn [andb]. unfold brk_grow_ok. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mm_flags_anon_noreserve : mmap_noreserve_b (Z_to_bv 64 mm_flags_anon) = false.
Proof. vm_compute; reflexivity. Qed.

Lemma mm_grant_rw_not_refusable : forall mo hint a nZ,
  mm_grant_rw mo hint a nZ -> mm_refusable mo mm_prot_rw mm_flags_anon nZ = false.
Proof.
  intros mo hint a nZ (H1 & H2 & H3 & H4 & H5). rewrite mm_refusable_rw.
  unfold mmap_grant_refusable, mmap_noreserve_backed_ok. rewrite mm_flags_anon_noreserve, H5. cbn [negb orb].
  rewrite (vm_find_base_complete (m_vmmaps mo) nZ a); [reflexivity|].
  unfold vm_base_ok. rewrite (proj2 (Z.eqb_eq _ _) H1), (proj2 (Z.ltb_lt _ _) H2), (proj2 (Z.leb_le _ _) H3), H4. reflexivity.
Qed.

Lemma mm_grant_none_not_refusable : forall mo hint a nZ,
  mm_grant_none mo hint a nZ -> mm_refusable mo mm_prot_none mm_flags_anon nZ = false.
Proof.
  intros mo hint a nZ (H1 & H2 & H3 & H4). rewrite mm_refusable_none. unfold mmap_reserve_refusable.
  rewrite (vm_find_base_complete (m_vmmaps mo) nZ a); [reflexivity|].
  unfold vm_base_ok. rewrite (proj2 (Z.eqb_eq _ _) H1), (proj2 (Z.ltb_lt _ _) H2), (proj2 (Z.leb_le _ _) H3), H4. reflexivity.
Qed.

Lemma mm_not_refusable_grant_rw : forall mo hint nZ,
  mm_refusable mo mm_prot_rw mm_flags_anon nZ = false -> exists a, mm_grant_rw mo hint a nZ.
Proof.
  intros mo hint nZ H. rewrite mm_refusable_rw in H. unfold mmap_grant_refusable, mmap_noreserve_backed_ok in H.
  rewrite mm_flags_anon_noreserve in H. apply orb_false_iff in H as [Hb Hg].
  apply negb_false_iff in Hb. apply negb_false_iff in Hg.
  destruct (vm_gap_available_find _ _ Hg) as [a Ha]. destruct (vm_find_base_sound _ _ _ Ha) as (H1 & H2 & H3 & H4).
  exists a. repeat split; assumption.
Qed.

Lemma mm_not_refusable_grant_none : forall mo hint nZ,
  mm_refusable mo mm_prot_none mm_flags_anon nZ = false -> exists a, mm_grant_none mo hint a nZ.
Proof.
  intros mo hint nZ H. rewrite mm_refusable_none in H. unfold mmap_reserve_refusable in H.
  apply negb_false_iff in H.
  destruct (vm_gap_available_find _ _ H) as [a Ha]. destruct (vm_find_base_sound _ _ _ Ha) as (H1 & H2 & H3 & H4).
  exists a. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Theorem anstep_inhabited : forall n mo, alloc_node n = true -> nsafe n mo -> exists rsp mo', anstep n mo rsp mo'.
Proof.
  intros n mo Hn Hs; destruct n; cbn in Hn; try discriminate; cbn [anstep].
  - eexists _, _. exists (vm_brk (m_vmmaps mo)). split; [apply brk_r_ok_refuse|]. split; reflexivity.
  - cbn [nsafe] in Hs. destruct Hs as (_ & _ & [[-> ->] | [[-> ->] | (-> & -> & _)]]).
    + destruct (mm_refusable mo mm_prot_rw mm_flags_anon (mmap_len len)) eqn:Hf.
      * eexists _, _. left. exists ENOMEM. split; [split; [apply ENOMEM_in_mmap_errnos| reflexivity]|]. split; reflexivity.
      * destruct (mm_not_refusable_grant_rw mo (Z_to_bv 64 addr) _ Hf) as [a Ha].
        eexists _, _. right; left. split; [reflexivity|]. split; [reflexivity|]. exists a. split; [exact Ha|]. split; reflexivity.
    + destruct (mm_refusable mo mm_prot_none mm_flags_anon (mmap_len len)) eqn:Hf.
      * eexists _, _. left. exists ENOMEM. split; [split; [apply ENOMEM_in_mmap_errnos| reflexivity]|]. split; reflexivity.
      * destruct (mm_not_refusable_grant_none mo (Z_to_bv 64 addr) _ Hf) as [a Ha].
        eexists _, _. right; right; left. split; [reflexivity|]. split; [reflexivity|]. exists a. split; [exact Ha|]. split; reflexivity.
    + eexists _, _. right; right; right. split; [reflexivity|]. split; [reflexivity|]. left. split; reflexivity.
  - eexists _, _. split; reflexivity.
  - destruct (mprotect_budget_ok mo (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len))) eqn:Hb.
    + eexists _, _. right. split; [reflexivity|]. split; reflexivity.
    + eexists _, _. left. exists ENOMEM. split; [split; [apply ENOMEM_in_mprotect_errnos|]|split; reflexivity].
      unfold mprotect_refusable. rewrite Hb. reflexivity.
  - destruct (Z.eq_dec (mmap_len oldlen) (mmap_len newlen)).
    + eexists _, _. left. split; [assumption|]. split; reflexivity.
    + eexists _, _. right. split; [assumption|]. left. exists ENOMEM. split; [apply ENOMEM_in_mremap_errnos|]. split; reflexivity.
Qed.

Lemma mmap_ret_aligned_nonrefusal : forall r,
  bv_unsigned r mod page_size = 0 -> ret_in_errnos mmap_errnos r = false.
Proof.
  intros r Hr. unfold mmap_errnos. rewrite ret_in_errnos_ENOMEM.
  destruct (bv_eqb r (errno_ret ENOMEM)) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. subst r. vm_compute in Hr. discriminate Hr.
Qed.

Lemma mprotect_ret0_nonrefusal : ret_in_errnos mprotect_errnos (Z_to_bv 64 0) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma rnstep_spurious : forall n i mo rsp rsp' mo'',
  alloc_node n = true -> input_at n i -> m_vm_lazy mo = [] -> nsafe n mo ->
  injected_family_off ACFG i = true ->
  refusal_b i mo (eff_ret rsp) = true ->
  rnstep n mo rsp' mo'' -> refusal_b i mo (eff_ret rsp') = false ->
  spurious_refusal_cfg ACFG i mo rsp.
Proof.
  intros n i mo rsp rsp' mo'' Hn Hi Hl Hs Hoff Hr H' Hnr.
  apply (refusal_spurious_of_grant ACFG i mo rsp rsp' mo'' [] Hoff Hr); [|exact Hnr].
  apply (proj2 (alloc_outcome_i n i mo Hn Hi Hl Hs (Ok rsp' mo'' []))).
  eexists _, _. split; [reflexivity|exact H'].
Qed.

Lemma rnstep_nsp_anstep : forall segs n ms mo x8 rsp mo',
  alloc_node n = true -> at_node segs n ms -> MOK mo -> nsafe n mo ->
  ms_svc_pending ms = Some x8 ->
  rnstep n mo rsp mo' ->
  ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo rsp ->
  anstep n mo rsp mo'.
Proof.
  intros segs n ms mo x8 rsp mo' Hn Hat [_ Hl] Hs Hsvc H Hns.
  destruct (input_at_sys_input segs n ms Hn Hat) as (x8' & Hsvc' & Hi).
  rewrite Hsvc in Hsvc'. injection Hsvc' as <-.
  destruct n; cbn in Hn; try discriminate Hn; try exact H.
  - pose proof Hi as (Hno & _).
    assert (Hoff : injected_family_off ACFG (sys_input segs ms x8) = true)
      by (apply acfg_family_off_alloc; right; right; left; exact Hno).
    assert (SP : forall rsp' mo'', rnstep (NMmap addr len prot flags) mo rsp' mo'' ->
                   bv_unsigned (eff_ret rsp') mod page_size = 0 ->
                   refusal_b (sys_input segs ms x8) mo (eff_ret rsp) = true -> False).
    { intros rsp' mo'' H' Hal' Hr. apply Hns.
      apply (rnstep_spurious (NMmap addr len prot flags) _ mo rsp rsp' mo'' eq_refl Hi Hl Hs Hoff Hr H').
      rewrite (refusal_b_222 _ mo _ Hno). exact (mmap_ret_aligned_nonrefusal _ Hal'). }
    pose proof Hs as Hs'. cbn [nsafe] in Hs'. destruct Hs' as (Haddr & Hlen & Hshape).
    assert (FX : prot = mm_prot_none -> flags = mm_flags_fixed ->
                 refusal_b (sys_input segs ms x8) mo (eff_ret rsp) = true -> False).
    { intros -> -> Hr.
      destruct Hshape as [[_ Hc] | [[_ Hc] | (_ & _ & Hal & _)]];
        [unfold mm_flags_anon, mm_flags_fixed in Hc; lia | unfold mm_flags_anon, mm_flags_fixed in Hc; lia |].
      apply (SP (mkEffectU (Z_to_bv 64 addr) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] [])
                (mm_fixed_model mo (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)))); [| |exact Hr].
      - cbn [rnstep]. right; right; right. split; [reflexivity|]. split; [reflexivity|]. left. split; reflexivity.
      - change (bv_unsigned (Z_to_bv 64 addr) mod page_size = 0). rewrite (u64_of_Z addr) by lia. exact Hal. }
    cbn [rnstep] in H. cbn [anstep].
    destruct H as [(e & He & -> & ->) | [Hg | [Hg | (Hp & Hf & [Hfx | (e & He & -> & ->)])]]].
    + assert (Hr : refusal_b (sys_input segs ms x8) mo (eff_ret (efferr e)) = true)
        by (rewrite (refusal_b_222 _ mo _ Hno); exact (ret_in_errnos_errno _ _ He)).
      left. exists e. split; [|split; reflexivity]. split; [exact He|].
      destruct (mm_refusable mo prot flags (mmap_len len)) eqn:Hrf; [reflexivity|exfalso].
      destruct Hshape as [[-> ->] | [[-> ->] | (-> & -> & _)]].
      * destruct (mm_not_refusable_grant_rw mo (Z_to_bv 64 addr) _ Hrf) as [a Ha].
        pose proof Ha as (Hal & _).
        apply (SP (mkEffect a [] [(a, Z_to_bv 64 (mmap_len len))]) (mm_anon_model mo a (Z_to_bv 64 (mmap_len len))));
          [| exact Hal | exact Hr].
        cbn [rnstep]. right; left. split; [reflexivity|]. split; [reflexivity|].
        exists a. split; [exact Ha|]. split; reflexivity.
      * destruct (mm_not_refusable_grant_none mo (Z_to_bv 64 addr) _ Hrf) as [a Ha].
        pose proof Ha as (Hal & _).
        apply (SP (mkEffectU a [] [] [(a, Z_to_bv 64 (mmap_len len))] [] [])
                  (mm_none_model mo a (Z_to_bv 64 (mmap_len len))));
          [| exact Hal | exact Hr].
        cbn [rnstep]. right; right; left. split; [reflexivity|]. split; [reflexivity|].
        exists a. split; [exact Ha|]. split; reflexivity.
      * exact (FX eq_refl eq_refl Hr).
    + right; left. exact Hg.
    + right; right; left. exact Hg.
    + right; right; right. split; [exact Hp|]. split; [exact Hf|]. left. exact Hfx.
    + exfalso. apply (FX Hp Hf).
      rewrite (refusal_b_222 _ mo _ Hno). exact (ret_in_errnos_errno _ _ He).
  - pose proof Hi as (Hno & _).
    assert (Hoff : injected_family_off ACFG (sys_input segs ms x8) = true)
      by (apply acfg_family_off_alloc; right; right; right; exact Hno).
    cbn [rnstep] in H. cbn [anstep].
    destruct H as [(e & He & -> & ->) | Hb]; [|right; exact Hb].
    left. exists e. split; [|split; reflexivity]. split; [exact He|].
    unfold mprotect_refusable.
    destruct (mprotect_budget_ok mo (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len))) eqn:Hb; [exfalso|reflexivity].
    apply Hns.
    apply (rnstep_spurious (NMprotect addr len prot) _ mo (efferr e)
             (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))])
             (mprotect_model_next mo (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len))) eq_refl Hi Hl Hs Hoff).
    + rewrite (refusal_b_226 _ mo _ Hno). exact (ret_in_errnos_errno _ _ He).
    + cbn [rnstep]. right. split; [exact Hb|]. split; reflexivity.
    + rewrite (refusal_b_226 _ mo _ Hno). exact mprotect_ret0_nonrefusal.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition aidx (ms : machine_state) (n : node) (mo : Model) : Type :=
  { p : resp * Model | anstep n mo (fst p) (snd p) /\
      forall x8, ms_svc_pending ms = Some x8 -> ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo (fst p) }.

Definition aidx_nx (ms : machine_state) {n mo} (p : aidx ms n mo) : config :=
  mkCfg (nret ms (fst (proj1_sig p))) (snd (proj1_sig p)).

Theorem alloc_node_ok : forall n ms mo,
  alloc_node n = true -> at_node segs n ms -> MOK mo -> nsafe n mo ->
  node_ok segs (mkCfg ms mo) (aidx ms n mo) (fun _ => []) (aidx_nx ms).
Proof.
  intros n ms mo Hn Hat [Hh Hl] Hs.
  destruct (at_node_outcome segs n ms mo Hn Hat Hl Hs) as (x8 & Hsvc & Hiff).
  split.
  - intros [[rsp mo'] [Ha Hns]]. cbn [aidx_nx proj1_sig fst snd]. cbn [fst snd] in Ha, Hns.
    destruct (anstep_MOK n mo rsp mo' (conj Hh Hl) Ha) as [Hh' Hl'].
    apply (sstep_cfg_syscall segs ACFG ms mo x8 rsp mo' mo' [] Hh Hsvc).
    + apply Hiff. eexists _, _. split; [reflexivity| exact (anstep_rnstep _ _ _ _ Ha)].
    + exact (Hns x8 Hsvc).
    + exact Hh'.
    + apply materialize_model_accesses_no_lazy. exact Hl'.
  - intros e st Hss.
    destruct (sstep_cfg_sys_inv segs ACFG ms mo x8 e st Hsvc Hss)
      as [(eff & mo1 & evs1 & Hspec & Hns & Hh1 & Hm)
         | [(eff & mo1 & evs1 & code & Hspec & Hcode & _ & _ & _)
         | [(eff & mo1 & evs1 & sig & Hspec & Hk & _ & _) | (Hspec & _ & _)]]].
    + apply Hiff in Hspec as (rsp & mo' & E & Hr). injection E as <- <- ->.
      pose proof (rnstep_nsp_anstep segs n ms mo x8 eff mo1 Hn Hat (conj Hh Hl) Hs Hsvc Hr Hns) as Ha.
      rewrite (materialize_model_accesses_no_lazy _ _ (anstep_lazy_nil _ _ _ _ Hl Ha)) in Hm.
      cbv beta iota in Hm. destruct Hm as [-> ->].
      assert (Hns' : forall y, ms_svc_pending ms = Some y ->
                       ~ spurious_refusal_cfg ACFG (sys_input segs ms y) mo eff).
      { intros y Hy. rewrite Hsvc in Hy. injection Hy as <-. exact Hns. }
      exists (exist _ (eff, mo1) (conj Ha Hns')). split; reflexivity.
    + exfalso. apply Hiff in Hspec as (rsp & mo' & E & Hr). injection E as <- <- ->.
      destruct (rnstep_MOK n mo eff mo1 (conj Hh Hl) Hr) as [Hh' _]. rewrite Hh' in Hcode. discriminate Hcode.
    + exfalso. apply Hiff in Hspec as (rsp & mo' & E & Hr). injection E as <- <- ->.
      destruct (rnstep_MOK n mo eff mo1 (conj Hh Hl) Hr) as [Hh' _].
      rewrite (m_killed_of_m_halted_none _ Hh') in Hk. discriminate Hk.
    + exfalso. apply Hiff in Hspec as (rsp & mo' & E & _). discriminate E.
Qed.

(* [comment removed for export] *)
Theorem rz_alloc_node : forall n ms mo (T : TSet),
  alloc_node n = true -> at_node segs n ms -> MOK mo -> nsafe n mo ->
  (forall rsp mo', anstep n mo rsp mo' -> realizes segs (mkCfg (nret ms rsp) mo') T) ->
  realizes segs (mkCfg ms mo) T.
Proof.
  intros n ms mo T Hn Hat HM Hs HK.
  assert (Hex : exists p : resp * Model, anstep n mo (fst p) (snd p) /\
            forall y, ms_svc_pending ms = Some y -> ~ spurious_refusal_cfg ACFG (sys_input segs ms y) mo (fst p)).
  { destruct (at_node_outcome segs n ms mo Hn Hat (proj2 HM) Hs) as (x8 & Hsvc & Hiff).
    destruct (Classical_Prop.classic (exists eff' m' evs', syscall_spec (sys_input segs ms x8) mo (Ok eff' m' evs')
                         /\ refusal_b (sys_input segs ms x8) mo (eff_ret eff') = false))
      as [(eff' & m' & evs' & Hs' & Hr') | Hno].
    - apply Hiff in Hs' as (rsp & mo' & E & Hr). injection E as <- <- ->.
      assert (Hns : ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff')
        by (apply spurious_refusal_not_refusal; exact Hr').
      exists (eff', m'). split; [exact (rnstep_nsp_anstep segs n ms mo x8 eff' m' Hn Hat HM Hs Hsvc Hr Hns)|].
      intros y Hy. rewrite Hsvc in Hy. injection Hy as <-. exact Hns.
    - destruct (anstep_inhabited n mo Hn Hs) as (rsp0 & mo0 & Ha0).
      exists (rsp0, mo0). split; [exact Ha0|].
      intros y Hy. rewrite Hsvc in Hy. injection Hy as <-.
      intros (_ & _ & W). exact (Hno W). }
  destruct Hex as [p0 Hp0].
  pose (i0 := exist _ p0 Hp0 : aidx ms n mo).
  apply (rz_conseq segs _ (t_alt (fun _ : aidx ms n mo => t_emit [] T))).
  - apply (rz_node segs (mkCfg ms mo) (aidx ms n mo) (fun _ => []) (aidx_nx ms) (fun _ => T) i0
             (alloc_node_ok n ms mo Hn Hat HM Hs)).
    intros [[rsp mo'] [Ha Hns]]. cbn [aidx_nx proj1_sig fst snd]. apply HK. exact Ha.
  - assert (HT : T []).
    { eapply realizes_nonempty. apply (HK (fst p0) (snd p0) (proj1 Hp0)). }
    intros tr. split.
    + intros [_ Ht]. exact (proj1 (t_emit_nil_eq T HT tr) Ht).
    + intros Ht. exists i0. exact (proj2 (t_emit_nil_eq T HT tr) Ht).
Qed.

(* [comment removed for export] *)
Theorem scps_alloc_node : forall n ms mo,
  alloc_node n = true -> at_node segs n ms -> MOK mo -> nsafe n mo ->
  SCPS segs (fun ms' mo' => exists rsp, ms' = nret ms rsp /\ anstep n mo rsp mo' /\ MOK mo') ms mo.
Proof.
  intros n ms mo Hn Hat HM Hs T K.
  apply (rz_alloc_node n ms mo T Hn Hat HM Hs).
  intros rsp mo' Ha. apply K; [| eapply anstep_vm_only; exact Ha].
  exists rsp. split; [reflexivity|]. split; [exact Ha|].
  eapply anstep_MOK; eassumption.
Qed.

End WithSegs.

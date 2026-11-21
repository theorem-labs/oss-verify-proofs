(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the mmap nodes carry place_declined_b, munmap's post-state is the model's with_mmap_destroyed and its -ENOMEM is a raw (rnstep) outcome that ACFG reads as spurious, mprotect carries the vDSO premise, mremap answers the model's deterministic -EINVAL for a new length above TASK_SIZE (mremap_outcome_big, a new error arm of anstep), the node lemmas take the robustness premise sys_rob, and the kernel build is preserved by every node step. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RelSpec ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RomBase.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
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
  (* #38's munmap post-state, taken FROM THE MODEL rather than from this tree.
     munmap_spec at 75d69e00, the model's text (printed whole, the four values all
     present):
       if map_has (vm_maps h) addr n
       then alt (e <- errno_from munmap_errnos;; err_ret e)
                (set_vmmaps (mmap_fixed_destroyed_next h addr n);; forget_vm_range …;; pure …)
     The revision's own post-state IS mmap_fixed_destroyed_next, and with_mmap_destroyed is
     exactly vm_forget_range over with_vmmaps -- so this is the same shape written through
     the model's constructor instead of its record re-spelled by hand.  That removes the
     conversion gap at munmap_outcome_i at its source rather than rewriting around it.
     map_remove is load-bearing in six files, but that does not bind this definition:
     a census of THIS DEFINITION's own consumers finds eight lines, all of them at :188,
     :523, :680, :734, :751 here plus Spec/KB_SiteM0.v:500/:503 and Spec/KRaw.v:701.
     LRT/LSCPS2.v and Spec/KB_ReallocM.v reach map_remove through mm_unmap, a DIFFERENT
     definition, and never name this one.  The count that matters is of consumers of
     the DEFINITION, not of the SPELLING: a file that names map_remove through another
     definition is not a consumer of this one, and its spelling is not changed by this
     one's.
     Nothing that held of the old spelling stops holding: AsanNodesMmB.v:916 proves
     maps_subtract and map_remove equal under this ledger's standing condition. *)
  Definition mm_unmapped_model (addr n : word) : Model :=
    with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) mo.
End Models.

(* [comment removed for export] *)
(* LPS 08b1429: an anonymous mmap grants Linux's address ([Sys/Mm/Mmap.linux_place]: top-down search,
   THP padding, honoured hint), not any free one.  The four facts the old guard asked for follow from it
   ([Placement.linux_place_admissible]) and stay as conjuncts for the consumers that read them. *)
Definition mm_grant_rw (mo : Model) (hint a : word) (nZ : Z) : Prop :=
  let h := m_vmmaps mo in
  Mmap.linux_place h (kb_thp (m_kernel mo)) hint nZ (bv_unsigned a) /\
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top h /\
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true /\
  (vm_backing_used mo + nZ <=? vm_limit h) = true.

Definition mm_grant_none (mo : Model) (hint a : word) (nZ : Z) : Prop :=
  let h := m_vmmaps mo in
  Mmap.linux_place h (kb_thp (m_kernel mo)) hint nZ (bv_unsigned a) /\
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top h /\
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.

(* Linux has an address for the request ([Placement.linux_place_b] computes it). *)
Definition mm_place_ok (mo : Model) (hint : word) (nZ : Z) : bool :=
  match Placement.linux_place_b (m_vmmaps mo) (kb_thp (m_kernel mo)) hint nZ with
  | Some _ => true | None => false end.

(* [comment removed for export] *)
Definition mm_refusable (mo : Model) (prot flags : Z) (hint : word) (nZ : Z) : bool :=
  if (prot =? mm_prot_rw) && (flags =? mm_flags_anon)
  then negb (mmap_noreserve_backed_ok (Z_to_bv 64 flags) mo nZ) || negb (mm_place_ok mo hint nZ)
  else if (prot =? mm_prot_none) && (flags =? mm_flags_anon) then negb (mm_place_ok mo hint nZ)
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
      (exists e, (In e mmap_errnos /\ mm_refusable mo prot flags hint nZ = true) /\ rsp = efferr e /\ mo' = mo)
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
      (* The abstract step is munmap's success arm only.  At LPS 727298f3 the exact arm of
         [Mmap.munmap_spec] may also answer -ENOMEM, an injected allocation-family refusal that
         no state forces; under ACFG it is a spurious refusal whenever the success arm is there,
         so the run never takes it ([rnstep_nsp_anstep]).  The raw step [rnstep] keeps it. *)
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
          (* 727298f3: a page-rounded new length above TASK_SIZE is a deterministic -EINVAL
             ([Mremap.mremap_spec], before any mapping is looked up) *)
          (  (exists e, ((nnZ <= TASK_SIZE /\ In e mremap_errnos) \/ (TASK_SIZE < nnZ /\ e = EINVAL)) /\
                        rsp = efferr e /\ mo' = mo)
          \/ (nnZ < onZ /\ rsp = mkEffectU o [] [] [((o + nn)%bv, Z_to_bv 64 (onZ - nnZ))] [] [] /\
              mo' = mremap_model_next mo o on o nn)
          \/ (onZ < nnZ /\ mremap_inplace_grow_b mo o on nn onZ nnZ = true /\
              rsp = mkEffect o [] [((o + on)%bv, Z_to_bv 64 (nnZ - onZ))] /\
              mo' = mremap_model_next mo o on o nn)
          \/ (onZ < nnZ /\ mremap_inplace_room_b mo o on nn onZ nnZ = false /\
              exists d, mremap_dst_ok mo onZ nnZ o on d nn /\
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
  | NMunmap addr len =>
      let a := Z_to_bv 64 addr in
      let n := Z_to_bv 64 (mmap_len len) in
      (exists e, In e munmap_errnos /\ rsp = efferr e /\ mo' = mo)
      \/ (rsp = mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] [] /\ mo' = mm_unmapped_model mo a n)
  | NBrk _ | NMremap _ _ _ _ => anstep n mo rsp mo'
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
  (page_round_up_Z (bv_unsigned new_size) <= TASK_SIZE)%Z ->
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
        \/ ((old_nZ < new_nZ)%Z /\ mremap_inplace_room_b m old old_n new_n old_nZ new_nZ = false /\
            exists dst, mremap_dst_ok m old_nZ new_nZ old old_n dst new_n /\
            o = Ok (mremap_move_effect old old_n dst old_nZ new_nZ) (mremap_model_next m old old_n dst new_n) []))).
Proof.
  intros old old_size new_size flags i m o Hfl Hal Hnew Hts Hold Hlazy. cbv zeta. intros Hsrc.
  unfold mremap_spec.
  rewrite Hfl. change (negb (Z.eqb MREMAP_MAYMOVE MREMAP_MAYMOVE)) with false. cbv iota.
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb]. rewrite Hnew.
  (* 08b1429: a page-rounded new length above TASK_SIZE is a deterministic -EINVAL *)
  rewrite (proj2 (Z.ltb_ge _ _) Hts). rewrite Hold.
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
  (* 08b1429 GROW: with room above the source the call expands there and only the charge can
     refuse it; without room it moves to Linux's address (linux_place, no hint). *)
  destruct (mremap_inplace_room_b m old (Z_to_bv 64 onZ) (Z_to_bv 64 nnZ) onZ nnZ) eqn:Hroom.
  - destruct (mremap_final_budget_b m old (Z_to_bv 64 onZ) old (Z_to_bv 64 nnZ)) eqn:Hbud.
    + assert (Hig : mremap_inplace_grow_b m old (Z_to_bv 64 onZ) (Z_to_bv 64 nnZ) onZ nnZ = true)
        by (unfold mremap_inplace_grow_b; rewrite Hroom, Hbud; reflexivity).
      sys_unfold. split.
      * destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hsrc, Huni in *; cbn [andb negb] in *; inv_sys;
          rewrite ?Hroom, ?Hbud in *; try inv_sys.
        all: right; split; [exact Ene|].
        all: first [ left; eexists; split; [eassumption|reflexivity]
                   | right; right; left; split; [exact Hgt|]; split; [exact Hig|reflexivity] ].
      * intros [[E _]|[_ [(e & He & ->)|[[Hc _]|[(_ & _ & ->)|(_ & Hc & _)]]]]]; [congruence| |lia| |congruence].
        -- eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Huni. cbn [andb negb]. split; [|reflexivity].
           left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
        -- eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Huni. cbn [andb negb]. split; [|reflexivity].
           right. rewrite Hroom. eexists _, _, _, _. split; [exists tt; split; [exact Hbud|reflexivity]|].
           split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
    + assert (Hig : mremap_inplace_grow_b m old (Z_to_bv 64 onZ) (Z_to_bv 64 nnZ) onZ nnZ = false)
        by (unfold mremap_inplace_grow_b; rewrite Hroom, Hbud; reflexivity).
      sys_unfold. split.
      * destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hsrc, Huni in *; cbn [andb negb] in *; inv_sys;
          rewrite ?Hroom, ?Hbud in *; try inv_sys.
        all: try congruence.
        all: right; split; [exact Ene|]. all: left; eexists; split; [eassumption|reflexivity].
      * intros [[E _]|[_ [(e & He & ->)|[[Hc _]|[(_ & Hc & _)|(_ & Hc & _)]]]]]; [congruence| |lia|congruence|congruence].
        eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Huni. cbn [andb negb]. split; [|reflexivity].
        left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
  - assert (Hig : mremap_inplace_grow_b m old (Z_to_bv 64 onZ) (Z_to_bv 64 nnZ) onZ nnZ = false)
      by (unfold mremap_inplace_grow_b; rewrite Hroom; reflexivity).
    sys_unfold. split.
    + destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hsrc, Huni in *; cbn [andb negb] in *; inv_sys;
        rewrite ?Hroom in *; try inv_sys.
      all: right; split; [exact Ene|].
      all: first [ left; eexists; split; [eassumption|reflexivity]
                 | right; right; right; split; [exact Hgt|]; split; [first [exact Hroom | reflexivity]|];
                   eexists; split; [eassumption | reflexivity] ].
    + intros [[E _]|[_ [(e & He & ->)|[[Hc _]|[(_ & Hc & _)|(_ & _ & dst & Hd & ->)]]]]]; [congruence| |lia|congruence|].
      * eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Huni. cbn [andb negb]. split; [|reflexivity].
        left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
      * eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Huni. cbn [andb negb]. split; [|reflexivity].
        right. rewrite Hroom. eexists _, _, _, _. split; [exists dst; split; [exact Hd|reflexivity]|].
        split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* 727298f3: above TASK_SIZE the page-rounded new length is a deterministic -EINVAL, answered
   before any mapping is looked up ([check_mremap_params]). *)
Lemma mremap_outcome_big : forall old old_size new_size flags i m o,
  bv_unsigned flags = MREMAP_MAYMOVE ->
  (bv_unsigned old mod page_size = 0)%Z ->
  page_align_is0_b new_size = false ->
  (TASK_SIZE < page_round_up_Z (bv_unsigned new_size))%Z ->
  mremap_spec old old_size new_size flags i m o <-> o = Ok (mkEffect (errno_ret EINVAL) [] []) m [].
Proof.
  intros old old_size new_size flags i m o Hfl Hal Hnew Hts.
  unfold mremap_spec.
  rewrite Hfl. change (negb (Z.eqb MREMAP_MAYMOVE MREMAP_MAYMOVE)) with false. cbv iota.
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb]. rewrite Hnew.
  rewrite (proj2 (Z.ltb_lt _ _) Hts). cbv iota.
  unfold err_ret, ret_only, pure. split; intros H; exact H.
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

Lemma mm_refusable_rw : forall mo hint nZ,
  mm_refusable mo mm_prot_rw mm_flags_anon hint nZ
  = negb (mmap_noreserve_backed_ok (Z_to_bv 64 mm_flags_anon) mo nZ) || negb (mm_place_ok mo hint nZ).
Proof. reflexivity. Qed.
Lemma mm_refusable_none : forall mo hint nZ,
  mm_refusable mo mm_prot_none mm_flags_anon hint nZ = negb (mm_place_ok mo hint nZ).
Proof. reflexivity. Qed.
Lemma mm_refusable_fixed : forall mo hint nZ, mm_refusable mo mm_prot_none mm_flags_fixed hint nZ = false.
Proof. reflexivity. Qed.

(* The model's grant guard and this file's grant. *)
Lemma mm_place_facts : forall mo hint nZ (a : word), 0 < nZ -> nZ mod page_size = 0 ->
  Mmap.linux_place (m_vmmaps mo) (kb_thp (m_kernel mo)) hint nZ (bv_unsigned a) ->
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top (m_vmmaps mo) /\
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 nZ) = true.
Proof.
  intros mo hint nZ a Hp Ha HL.
  destruct (Placement.linux_place_admissible _ _ _ _ _ Hp Ha HL) as (A1 & A2 & A3 & A4).
  rewrite Z_to_bv_bv_unsigned in A4. repeat split; assumption.
Qed.

Lemma mm_grant_rw_of_place : forall mo hint (a : word) nZ, 0 < nZ -> nZ mod page_size = 0 ->
  Mmap.linux_place (m_vmmaps mo) (kb_thp (m_kernel mo)) hint nZ (bv_unsigned a)
  /\ (vm_backing_used mo + nZ <=? vm_limit (m_vmmaps mo)) = true ->
  mm_grant_rw mo hint a nZ.
Proof.
  intros mo hint a nZ Hp Ha [HL Hb]. destruct (mm_place_facts mo hint nZ a Hp Ha HL) as (A1 & A2 & A3 & A4).
  unfold mm_grant_rw. repeat split; assumption.
Qed.

Lemma mm_grant_rw_place : forall mo hint a nZ, mm_grant_rw mo hint a nZ ->
  Mmap.linux_place (m_vmmaps mo) (kb_thp (m_kernel mo)) hint nZ (bv_unsigned a)
  /\ (vm_backing_used mo + nZ <=? vm_limit (m_vmmaps mo)) = true.
Proof. intros mo hint a nZ (HL & _ & _ & _ & _ & Hb). split; assumption. Qed.

Lemma mm_grant_none_of_place : forall mo hint (a : word) nZ, 0 < nZ -> nZ mod page_size = 0 ->
  Mmap.linux_place (m_vmmaps mo) (kb_thp (m_kernel mo)) hint nZ (bv_unsigned a) ->
  mm_grant_none mo hint a nZ.
Proof.
  intros mo hint a nZ Hp Ha HL. destruct (mm_place_facts mo hint nZ a Hp Ha HL) as (A1 & A2 & A3 & A4).
  unfold mm_grant_none. repeat split; assumption.
Qed.

Lemma mmap_outcome_i : forall addr len prot flags i mo, input_at (NMmap addr len prot flags) i ->
  m_vm_lazy mo = [] -> nsafe (NMmap addr len prot flags) mo ->
  forall o, syscall_spec i mo o <-> exists rsp mo', o = Ok rsp mo' [] /\ rnstep (NMmap addr len prot flags) mo rsp mo'.
Proof.
  intros addr len prot flags i mo (Hno & H0 & H1 & H2 & H3 & H4 & H5) Hlazy Hsafe o.
  cbn [nsafe] in Hsafe. destruct Hsafe as (Haddr & Hlen & Hshape & Hdg).
  assert (E1 : w_is0 (Z_to_bv 64 len) = false) by (apply w_is0_false; lia).
  rewrite (syscall_spec_222 i mo o Hno), H0, H1, H2, H3, H4, H5. cbn [rnstep].
  unfold mmap_len. 
  destruct Hshape as [[-> ->] | [[-> ->] | (-> & -> & Hal & Hpos & Hce & Hrf & Hmc)]].
  - (* [comment removed for export] *)
    rewrite (mmap_rw_outcome (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 mm_prot_rw) (Z_to_bv 64 mm_flags_anon)
               (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i mo o ltac:(lit_tf) ltac:(lit_tf) E1 ltac:(lit_tf)
               ltac:(rewrite (u64_of_Z len) by lia; exact (Hdg ltac:(lit_tf)))).
    unfold mmap_err_out, mmap_noreserve_backed_ok, with_mmap_backing.
    replace (mmap_noreserve_b (Z_to_bv 64 mm_flags_anon)) with false by lit_tf.
    rewrite (u64_of_Z len) by lia.
    pose proof (Placement.page_round_up_Z_ge len) as HnP. pose proof (Placement.page_round_up_Z_aligned len) as HnA.
    split.
    + intros [(e & He & ->) | (a & Hg & ->)]; eexists _, _; (split; [reflexivity|]).
      * left. exists e. split; [exact He|]. split; reflexivity.
      * right; left. split; [reflexivity|]. split; [reflexivity|]. exists a.
        split; [exact (mm_grant_rw_of_place mo (Z_to_bv 64 addr) a (page_round_up_Z len) ltac:(lia) HnA Hg)|]. split; reflexivity.
    + intros (rsp & mo' & -> & [(e & He & -> & ->) | [(_ & _ & a & Hg & -> & ->) | [(Hc & _) | (Hc & _)]]]);
        [ left; exists e; split; [exact He | reflexivity] | right; exists a; split; [exact (mm_grant_rw_place _ _ _ _ Hg) | reflexivity]
        | exfalso | exfalso];
        unfold mm_prot_rw, mm_prot_none in Hc; lia.
  - (* [comment removed for export] *)
    rewrite (mmap_noaccess_outcome (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 mm_prot_none) (Z_to_bv 64 mm_flags_anon)
               (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i mo o ltac:(lit_tf) ltac:(lit_tf) E1 ltac:(lit_tf) ltac:(lit_tf)
               ltac:(rewrite (u64_of_Z len) by lia; exact (Hdg ltac:(lit_tf)))).
    unfold mmap_err_out, with_mmap_backing.
    replace (mmap_noreserve_b (Z_to_bv 64 mm_flags_anon)) with false by lit_tf.
    rewrite (u64_of_Z len) by lia.
    pose proof (Placement.page_round_up_Z_ge len) as HnP. pose proof (Placement.page_round_up_Z_aligned len) as HnA.
    split.
    + intros [(e & He & ->) | (a & Hg & ->)]; eexists _, _; (split; [reflexivity|]).
      * left. exists e. split; [exact He|]. split; reflexivity.
      * right; right; left. split; [reflexivity|]. split; [reflexivity|]. exists a.
        split; [exact (mm_grant_none_of_place mo (Z_to_bv 64 addr) a (page_round_up_Z len) ltac:(lia) HnA Hg)|]. split; reflexivity.
    + intros (rsp & mo' & -> & [(e & He & -> & ->) | [(Hc & _) | [(_ & _ & a & Hg & -> & ->) | (_ & Hc & _)]]]);
        [ left; exists e; split; [exact He | reflexivity] | exfalso | right; exists a; split; [exact (proj1 Hg) | reflexivity]
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
  forall o, syscall_spec i mo o <-> exists rsp mo', o = Ok rsp mo' [] /\ rnstep (NMunmap addr len) mo rsp mo'.
Proof.
  intros addr len i mo (Hno & H0 & H1) Hsafe o.
  cbn [nsafe] in Hsafe. destruct Hsafe as (Ha0 & Hal & Hlen & Hnw & Hhas).
  pose proof (mmap_len_ge len) as Hge. unfold mmap_len in Hge.
  assert (Hlen2 : len < 2^64) by (unfold TASK_SIZE in *; lia).
  assert (Hadd2 : addr < 2^64) by (unfold TASK_SIZE in *; lia).
  rewrite (syscall_spec_215 i mo o Hno), H0, H1. cbn [rnstep]. unfold mmap_len, mm_unmapped_model.
  rewrite (munmap_exact_outcome (Z_to_bv 64 addr) (Z_to_bv 64 len) i mo o);
    rewrite ?(u64_of_Z len) by lia; rewrite ?(u64_of_Z addr) by lia;
    [| exact Hal | apply w_is0_false; lia | exact Hnw | exact Hhas].
  (* The two sides of the failing conversion at :523 are identical except in ONE
     position -- anstep's side has the record literal
     `{| vm_maps := map_remove … ; vm_noaccess := maps_subtract … ; … |}` where the outcome
     lemma's side still has `mmap_fixed_destroyed_next (m_vmmaps mo) (Z_to_bv 64 addr)
     (Z_to_bv 64 (page_round_up_Z len))`, which is exactly that record's definition.  So
     one more unfold closes it.  Read off the two printed terms, not guessed: both were
     printed whole, none truncated. *)
  unfold with_mmap_destroyed, mmap_fixed_destroyed_next. rewrite (u64_of_Z addr) by lia.
  (* both directions mirror mprotect_outcome_i four lines below -- the SAME file's own
     already-green treatment of the same transformation, a lemma whose outcome gained an
     errno disjunct.  munmap's success arm carries no budget guard, so where mprotect
     threads `Hb` this threads nothing; everything else is the donor unchanged. *)
  split.
  - intros [(e & He & ->) | ->]; eexists _, _; (split; [reflexivity|]).
    + left. exists e. split; [exact He|]. split; reflexivity.
    + right. split; reflexivity.
  - intros (rsp & mo' & -> & [(e & He & -> & ->) | (-> & ->)]).
    + left. exists e. split; [exact He | reflexivity].
    + right. reflexivity.
Qed.

(* #38 gave mprotect_expose_outcome a SIXTH premise, between mprotect_modeled_b and the two
   map_contains facts (RelSpec.v:563):
     region_free (vdso_reserved (m_kernel m) (vdso_top h)) addr n = true
   A call that supplies seven of eight slides Hna into the vDSO slot, reported as a
   well-typed term in the wrong place -- the SHRINK shape, with nothing actually missing
   from what was written and one premise missing from what was needed.  Read from the
   callee's own Section at this sha, not from the error and not from a donor tree.
   THREADED, NOT DISCHARGED, and the tree has already chosen this resolution TWICE in the
   identical position: AS/AsanNodesMmLib.v:1251-1255 and AS/RefNodes.v:890-893 both carry
   this exact premise as a hypothesis of their own statement, immediately before the two
   map_contains facts.  Same premise, same slot, same unit -- so this is the established
   in-tree shape rather than a port.
   NOT added to nsafe: that is a conjunct on a soundness predicate, it touches every
   NMprotect consumer, and whether nsafe lies in the published unfold cone is not
   settled by this file, so it is not assumed here.  P/Drv_heap.v:220-242's vdso_resv_facts
   -- proved here, via State.vdso_reserved_above -- is the fallback if threading dead-ends
   at a root that cannot supply the premise.
   SCOPE: this is a proofs/lib statement, not a published one.  Nothing in Statements.v or
   any proofs/*/Proof.v unfolds to mprotect_outcome_i; the premise is strictly a new
   hypothesis, so the lemma is WEAKENED in the sense of assuming more, never strengthened
   in its conclusion, and no consumer silently gains a fact it did not have. *)
Lemma mprotect_outcome_i : forall addr len prot i mo, input_at (NMprotect addr len prot) i ->
  nsafe (NMprotect addr len prot) mo ->
  let n := Z_to_bv 64 (mmap_len len) in
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) (Z_to_bv 64 addr) n = true ->
  forall o, syscall_spec i mo o <-> exists rsp mo', o = Ok rsp mo' [] /\ rnstep (NMprotect addr len prot) mo rsp mo'.
Proof.
  intros addr len prot i mo (Hno & H0 & H1 & H2) Hsafe. cbv zeta. intros Hvd o.
  cbn [nsafe] in Hsafe. destruct Hsafe as (-> & Ha0 & Hal & Hlen & Hnw & Hna & Hma).
  pose proof (mmap_len_ge len) as Hge. unfold mmap_len in Hge.
  assert (Hlen2 : len < 2^64) by lia.
  rewrite (syscall_spec_226 i mo o Hno), H0, H1, H2. cbn [rnstep]. unfold mmap_len.
  rewrite (mprotect_expose_outcome (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 mm_prot_rw) i mo o);
    rewrite ?(u64_of_Z len) by lia; rewrite ?(u64_of_Z addr) by lia;
    [| lit_tf | exact Hal | apply w_is0_false; lia | rewrite two_pow_64_val; exact Hnw | lit_tf
     | exact Hvd | exact Hna | exact Hma].
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
  cbn [nsafe] in Hsafe. destruct Hsafe as (-> & Hold & Hal & Hol & Hnl & Hnl2 & Htop & Hce & Hrf & Hhas & Hna).
  pose proof (mmap_len_ge ol) as Hge1. pose proof (mmap_len_ge nl) as Hge2. unfold mmap_len in Hge1, Hge2.
  assert (Hcv : alloc_top (m_vmmaps mo) < 2^64) by (pose proof (alloc_top_lt (m_vmmaps mo)); unfold two_pow_64 in *; lia).
  assert (Hol2 : ol < 2^64) by lia. assert (Hnl3 : nl < 2^64) by lia. assert (Hold2 : old < 2^64) by lia.
  rewrite (syscall_spec_216 i mo o Hno), H0, H1, H2, H3. cbn [anstep]. unfold mmap_len.
  (* #38 moved the RIGHT disjunct of page_align_is0_b under page_round_up_Z (PAGE_ALIGN wraps):
     after `rewrite w_is0_false` and `cbn [orb]` each length arm is `page_round_up_Z len < 2^64`,
     from nsafe's bound for nl and from old + page_round_up_Z ol <= alloc_top < 2^64 for ol. *)
  destruct (Z.ltb_spec TASK_SIZE (page_round_up_Z nl)) as [Hts|Hts].
  - (* 727298f3: above TASK_SIZE the call is a deterministic -EINVAL; nsafe's alloc_top bound
       makes every other arm of anstep impossible there. *)
    rewrite (mremap_outcome_big (Z_to_bv 64 old) (Z_to_bv 64 ol) (Z_to_bv 64 nl) (Z_to_bv 64 MREMAP_MAYMOVE) i mo o);
      rewrite ?(u64_of_Z old) by lia;
      [| apply u64_of_Z; unfold MREMAP_MAYMOVE; lia | exact Hal
       | unfold page_align_is0_b; rewrite w_is0_false by lia; cbn [orb];
         rewrite (u64_of_Z nl) by lia; rewrite two_pow_64_val; apply Z.leb_gt; lia
       | rewrite (u64_of_Z nl) by lia; exact Hts ].
    set (onZ := page_round_up_Z ol) in *. set (nnZ := page_round_up_Z nl) in *.
    split.
    + intros ->. eexists _, _. split; [reflexivity|]. right. split; [lia|].
      left. exists EINVAL. split; [right; split; [exact Hts|reflexivity]|]. split; reflexivity.
    + intros (rsp & mo' & -> & [(E & -> & ->) | (Ene & [(e & [[Hc _]|[_ ->]] & -> & ->) | [(Hlt & -> & ->) | [(Hlt & Hig & -> & ->) | (Hlt & Hro & d & (Hpl & _) & -> & ->)]]])]).
      * exfalso. lia.
      * exfalso. lia.
      * reflexivity.
      * exfalso. lia.
      * exfalso. unfold mremap_inplace_grow_b, mremap_inplace_room_b in Hig. cbv zeta in Hig.
        apply andb_prop in Hig as [Hig _]. apply andb_prop in Hig as [Hig _]. apply Z.leb_le in Hig.
        rewrite (u64_of_Z old) in Hig by lia. lia.
      * exfalso. pose proof (mmap_len_aligned nl) as Hna2. unfold mmap_len in Hna2.
        assert (Hnpos : 0 < nnZ) by lia.
        assert (Hnal : nnZ mod page_size = 0) by (rewrite page_size_val; exact Hna2).
        destruct (Placement.linux_place_admissible _ _ _ _ _ Hnpos Hnal Hpl) as (_ & A2 & A3 & _). lia.
  - rewrite (mremap_outcome (Z_to_bv 64 old) (Z_to_bv 64 ol) (Z_to_bv 64 nl) (Z_to_bv 64 MREMAP_MAYMOVE) i mo o);
      rewrite ?(u64_of_Z ol) by lia; rewrite ?(u64_of_Z nl) by lia; rewrite ?(u64_of_Z old) by lia;
      [| apply u64_of_Z; unfold MREMAP_MAYMOVE; lia | exact Hal
       | unfold page_align_is0_b; rewrite w_is0_false by lia; cbn [orb];
         rewrite (u64_of_Z nl) by lia; rewrite two_pow_64_val; apply Z.leb_gt; lia
       | exact Hts
       | unfold page_align_is0_b; rewrite w_is0_false by lia; cbn [orb];
         rewrite (u64_of_Z ol) by lia; rewrite two_pow_64_val; apply Z.leb_gt; lia
       | exact Hlazy
       | unfold mremap_source_b; rewrite (u64_of_Z old) by lia; rewrite (proj2 (Z.leb_le _ _) Hce), Hrf, Hhas, Hna; reflexivity ].
    unfold mremap_inplace_effect, mremap_move_effect, mremap_tail.
    set (onZ := page_round_up_Z ol) in *. set (nnZ := page_round_up_Z nl) in *.
    split.
    + intros [[E ->] | [Ene [(e & He & ->) | [[Hlt ->] | [(Hlt & Hig & ->) | (Hlt & Hro & d & Hd & ->)]]]]];
        eexists _, _; (split; [reflexivity|]).
      * left. auto.
      * right. split; [exact Ene|]. left. exists e. split; [left; split; [exact Hts|exact He]|auto].
      * right. split; [exact Ene|]. right; left. rewrite (proj2 (Z.ltb_lt _ _) Hlt). auto.
      * right. split; [exact Ene|]. right; right; left. rewrite (proj2 (Z.ltb_ge nnZ onZ) ltac:(lia)), (proj2 (Z.ltb_lt _ _) Hlt). auto.
      * right. split; [exact Ene|]. right; right; right. split; [exact Hlt|]. split; [exact Hro|]. exists d. rewrite (proj2 (Z.ltb_lt _ _) Hlt). auto.
    + intros (rsp & mo' & -> & [(E & -> & ->) | (Ene & [(e & [[_ He]|[Hc _]] & -> & ->) | [(Hlt & -> & ->) | [(Hlt & Hig & -> & ->) | (Hlt & Hro & d & Hd & -> & ->)]]])]).
      * left. auto.
      * right. split; [exact Ene|]. left. exists e. auto.
      * exfalso. lia.
      * right. split; [exact Ene|]. right; left. rewrite (proj2 (Z.ltb_lt _ _) Hlt). auto.
      * right. split; [exact Ene|]. right; right; left. rewrite (proj2 (Z.ltb_ge nnZ onZ) ltac:(lia)), (proj2 (Z.ltb_lt _ _) Hlt). auto.
      * right. split; [exact Ene|]. right; right; right. split; [exact Hlt|]. split; [exact Hro|]. exists d. rewrite (proj2 (Z.ltb_lt _ _) Hlt). auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* #38's vDSO premise, threaded from mprotect_outcome_i to the layer that can discharge it.
   A node-kind-specific side condition cannot be stated on a `forall n` root directly, so it
   is carried the way nsafe already carries its own per-constructor conditions: as a match on
   the node, trivially True everywhere except NMprotect.  This does NOT touch nsafe -- that is
   a conjunct on a soundness predicate, it reaches every NMprotect consumer, and whether nsafe
   lies in the published unfold cone is unmeasured; the lead holds that question.
   The terminus is measured, not hoped for: Lib.NodesSound has TWELVE out-of-file requirers and
   projects/cjson/cjson_read_fuzzer/proofs/lib/P/Drv_heap.v is one of them AND already proves
   vdso_resv_facts at :220-242 via State.vdso_reserved_above, with the U twin alongside.
   projects/cjson/cjson_read_fuzzer/proofs/lib/AS/AsanNodesMmA.v:520 is a second, independent
   discharge: region_free_In composed with co_vdso from the plan invariant.
   So this is a pass-through to a file that already holds the fact, not a new obligation. *)
Definition nvdso_free (n : node) (mo : Model) : Prop :=
  match n with
  | NMprotect addr len _ =>
      region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo)))
        (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
  | _ => True
  end.

Theorem alloc_outcome_i : forall n i mo,
  alloc_node n = true -> input_at n i -> m_vm_lazy mo = [] -> nsafe n mo -> nvdso_free n mo ->
  forall o, syscall_spec i mo o <-> exists rsp mo', o = Ok rsp mo' [] /\ rnstep n mo rsp mo'.
Proof.
  intros n i mo Hn Hi Hlazy Hsafe Hvd; destruct n; cbn in Hn; try discriminate.
  - cbn [rnstep]. apply brk_outcome_i; assumption.
  - apply mmap_outcome_i; assumption.
  - apply munmap_outcome_i; assumption.
  - cbn [nvdso_free] in Hvd. apply mprotect_outcome_i; assumption.
  - cbn [rnstep]. apply mremap_outcome_i; assumption.
Qed.

(* [comment removed for export] *)
Corollary nstep_alloc_iff : forall n mo rsp mo' evs,
  alloc_node n = true -> m_vm_lazy mo = [] -> nsafe n mo -> nvdso_free n mo ->
  nstep n mo rsp mo' evs <-> evs = [] /\ rnstep n mo rsp mo'.
Proof.
  intros n mo rsp mo' evs Hn Hlazy Hsafe Hvd.
  destruct (node_input n) as [i|] eqn:Hi.
  2:{ exfalso. destruct n; cbn in Hn; try discriminate Hn; cbn in Hi; discriminate Hi. }
  pose proof (alloc_outcome_i n i mo Hn (input_at_node_input n i Hi) Hlazy Hsafe Hvd (Ok rsp mo' evs)) as HO.
  transitivity (evs = [] /\ syscall_spec i mo (Ok rsp mo' evs)).
  { destruct n; cbn in Hn; try discriminate; cbn [nstep]; rewrite Hi; tauto. }
  rewrite HO. split.
  - intros (-> & rsp1 & mo1 & E & Ha). injection E as <- <-. auto.
  - intros (-> & Ha). split; [reflexivity|]. eexists _, _. eauto.
Qed.

(* [comment removed for export] *)
Corollary at_node_outcome : forall segs n ms mo,
  alloc_node n = true -> at_node segs n ms -> m_vm_lazy mo = [] -> nsafe n mo -> nvdso_free n mo ->
  exists x8, ms_svc_pending ms = Some x8 /\
    forall o, syscall_spec (sys_input segs ms x8) mo o <-> exists rsp mo', o = Ok rsp mo' [] /\ rnstep n mo rsp mo'.
Proof.
  intros segs n ms mo Hn Hat Hlazy Hsafe Hvd.
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
  (* The NMremap move arm has SIX components, not five: `onZ < nnZ`, `room_b = false`,
     the witness `d`, `mremap_dst_ok`, the `rsp` equation and the `mo'` equation (:213-216).
     A five-component pattern binds `d` to the boolean equation and lets `_` swallow the
     witness as `_H1`, so the trailing `->` lands on the rsp equation instead of the mo'
     equation and rewrites nothing: "Found no subterm matching rsp = {| ... copy_dst := _H1 ... |}".
     The same pattern is written at four more places (:795, :846, :863 and Spec/KRaw.v:324),
     which only the file stopping here kept silent. *)
  - destruct H as [(_ & _ & ->) | (_ & [(e & _ & _ & ->) | [(_ & _ & ->) | [(_ & _ & _ & ->) | (_ & _ & d & _ & _ & ->)]]])];
      [apply vm_only_refl | apply vm_only_refl | | |];
      unfold mremap_model_next, vm_resize_backing;
      (eapply vm_only_trans; [apply vm_only_with_vmmaps | apply vm_only_with_vm_backing]).
Qed.


(* #38's vDSO premise is stated over m_kernel, and vm_only does not mention it (SCPS.v:45-47
   lists m_fd, m_io, m_fsys, m_proc, m_lim, m_time).  Rather than widen vm_only -- whose
   six-conjunct destructuring pattern is used throughout the unit -- the kernel build is given
   its own preservation lemma, with the same case split as anstep_vm_only above.  Every model
   an allocation node produces is built by with_vmmaps, with_vm_backing, vm_forget_range or
   forget_vm_ranges, none of which writes m_kernel. *)
Lemma kernel_forget_vm_ranges : forall rs mo, m_kernel (forget_vm_ranges rs mo) = m_kernel mo.
Proof.
  induction rs as [|[a n] rs IH]; intros mo; cbn [forget_vm_ranges]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma anstep_kernel : forall n mo rsp mo', anstep n mo rsp mo' -> m_kernel mo' = m_kernel mo.
Proof.
  intros n mo rsp mo' H; destruct n; cbn [anstep] in H; try contradiction.
  (* with_brk_next is forget_vm_ranges OUTSIDE with_vmmaps, so `apply` unifies the lemma's
     conclusion m_kernel (forget_vm_ranges rs ?mo) = m_kernel ?mo with ?mo := the with_vmmaps
     model and then owes m_kernel mo = m_kernel (with_vmmaps … mo) -- Rocq's message is
     "Unable to unify mo with with_vmmaps (brk_model_next …) mo".
     Rewriting instead leaves exactly that step, which with_vmmaps discharges by conversion. *)
  - destruct H as (r & _ & _ & ->). unfold with_brk_next. rewrite kernel_forget_vm_ranges. reflexivity.
  - destruct H as [(e & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | (_ & _ & [(_ & ->) | (e & _ & _ & ->)])]]];
      try reflexivity; unfold mm_fixed_model, mm_destroyed_model; reflexivity.
  - destruct H as [_ ->]. unfold mm_unmapped_model. reflexivity.
  - destruct H as [(e & _ & _ & ->) | (_ & _ & ->)]; [reflexivity|]. unfold mprotect_model_next. reflexivity.
  - destruct H as [(_ & _ & ->) | (_ & [(e & _ & _ & ->) | [(_ & _ & ->) | [(_ & _ & _ & ->) | (_ & _ & d & _ & _ & ->)]]])];
      try reflexivity; unfold mremap_model_next, vm_resize_backing; reflexivity.
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
  (* mm_unmapped_model is now the MODEL's post-state, with_mmap_destroyed (:121-122), and the
     vm_forget_range it is built from is one delta step further in.  `apply` sees through that
     (which is why the same arm of anstep_vm_only and anstep_kernel compiles untouched) but
     `rewrite` MATCHES SYNTACTICALLY, so vm_forget_range_lazy found no subterm.  In-unit donor
     for the spelling: AS/AsanNodesLibE.v:226-228, with_mmap_destroyed_halted, which unfolds
     with_mmap_destroyed first and then rewrites with its vm_forget_range_* lemma. *)
  - destruct H as [_ ->]. unfold mm_unmapped_model, with_mmap_destroyed.
    rewrite vm_forget_range_lazy, m_vm_lazy_with_vmmaps, Hl; apply maps_subtract_nil.
  - destruct H as [(e & _ & _ & ->) | (_ & _ & ->)]; [exact Hl|]. unfold mprotect_model_next. rewrite m_vm_lazy_with_vmmaps. exact Hl.
  - destruct H as [(_ & _ & ->) | (_ & [(e & _ & _ & ->) | [(_ & _ & ->) | [(_ & _ & _ & ->) | (_ & _ & d & _ & _ & ->)]]])];
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
  (* same delta step as the lazy twin at :855 *)
  - destruct H as [_ ->]. unfold mm_unmapped_model, with_mmap_destroyed.
    rewrite vm_forget_range_materialized, m_vm_materialized_with_vmmaps, Hm; reflexivity.
  - destruct H as [(e & _ & _ & ->) | (_ & _ & ->)]; [exact Hm|]. unfold mprotect_model_next. rewrite m_vm_materialized_with_vmmaps. exact Hm.
  - destruct H as [(_ & _ & ->) | (_ & [(e & _ & _ & ->) | [(_ & _ & ->) | [(_ & _ & _ & ->) | (_ & _ & d & _ & _ & ->)]]])];
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
  - destruct H as [(e & _ & _ & ->) | (_ & ->)]; [apply vm_only_refl|]. unfold mm_unmapped_model.
    eapply vm_only_trans; [apply vm_only_with_vmmaps | apply vm_only_vm_forget_range].
  - destruct H as [(e & _ & _ & ->) | (_ & _ & ->)]; [apply vm_only_refl|]. unfold mprotect_model_next. apply vm_only_with_vmmaps.
Qed.

Lemma rnstep_lazy_nil : forall n mo rsp mo', m_vm_lazy mo = [] -> rnstep n mo rsp mo' -> m_vm_lazy mo' = [].
Proof.
  intros n mo rsp mo' Hl H; destruct n; cbn [rnstep] in H; try contradiction;
    try exact (anstep_lazy_nil _ _ _ _ Hl H).
  - destruct H as [(e & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | [(_ & _ & a & _ & _ & ->) | (_ & _ & [(_ & ->) | (e & _ & _ & ->)])]]];
      [exact Hl | exact Hl | exact Hl | | ]; unfold mm_fixed_model, mm_destroyed_model;
      rewrite vm_forget_range_lazy, m_vm_lazy_with_vmmaps, Hl; apply maps_subtract_nil.
  - destruct H as [(e & _ & _ & ->) | (_ & ->)]; [exact Hl|]. unfold mm_unmapped_model, with_mmap_destroyed.
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
  - right. exact H.
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

Lemma mm_place_ok_of_place : forall mo hint nZ (a : word), 0 < nZ -> nZ mod page_size = 0 ->
  Mmap.linux_place (m_vmmaps mo) (kb_thp (m_kernel mo)) hint nZ (bv_unsigned a) -> mm_place_ok mo hint nZ = true.
Proof.
  intros mo hint nZ a Hp Ha HL. unfold mm_place_ok.
  destruct (Placement.linux_place_b_spec (m_vmmaps mo) (kb_thp (m_kernel mo)) hint nZ Hp Ha) as [Hs _].
  rewrite (proj2 (Hs _) HL). reflexivity.
Qed.

Lemma mm_place_of_ok : forall mo hint nZ, 0 < nZ -> nZ mod page_size = 0 ->
  mm_place_ok mo hint nZ = true ->
  exists a : word, Mmap.linux_place (m_vmmaps mo) (kb_thp (m_kernel mo)) hint nZ (bv_unsigned a).
Proof.
  intros mo hint nZ Hp Ha H. unfold mm_place_ok in H.
  destruct (Placement.linux_place_b_spec (m_vmmaps mo) (kb_thp (m_kernel mo)) hint nZ Hp Ha) as [Hs _].
  destruct (Placement.linux_place_b _ _ _ _) as [z|] eqn:Ez; [|discriminate H].
  (* `destruct … eqn:Ez` rewrites HYPOTHESES as well as the goal, so Hs -- introduced on the
     line above and mentioning linux_place_b -- became `forall a, Some z = Some a <-> …`.
     Ez still has the UNrewritten type, which is why it no longer fits: "The term Ez has type
     Placement.linux_place_b … = Some z while it is expected to have type Some z = Some z"
     (measured).  The premise Hs now wants is eq_refl.  The sibling at
     :977 is unaffected because it uses Hs in the OTHER direction, where nothing was rewritten. *)
  pose proof (proj1 (Hs z) eq_refl) as HL.
  destruct (Placement.linux_place_admissible _ _ _ _ _ Hp Ha HL) as (_ & A2 & A3 & _).
  pose proof (Placement.alloc_top_lt_two_pow_64 (m_vmmaps mo)) as Hat. rewrite two_pow_64_val in Hat.
  exists (Z_to_bv 64 z). rewrite (u64_of_Z z) by lia. exact HL.
Qed.

(* A grant exists as soon as Linux has an address (a free gap in a window: [Placement.linux_place_exists]). *)
Lemma mm_grant_rw_exists_of_place : forall mo hint nZ, 0 < nZ -> nZ mod page_size = 0 ->
  (exists z, Mmap.linux_place (m_vmmaps mo) (kb_thp (m_kernel mo)) hint nZ z) ->
  (vm_backing_used mo + nZ <=? vm_limit (m_vmmaps mo)) = true ->
  exists a, mm_grant_rw mo hint a nZ.
Proof.
  intros mo hint nZ Hp Ha [z HL] Hb.
  destruct (Placement.linux_place_admissible _ _ _ _ _ Hp Ha HL) as (_ & A2 & A3 & _).
  pose proof (Placement.alloc_top_lt_two_pow_64 (m_vmmaps mo)) as Hat. rewrite two_pow_64_val in Hat.
  exists (Z_to_bv 64 z). apply (mm_grant_rw_of_place mo hint _ nZ Hp Ha).
  rewrite (u64_of_Z z) by lia. split; assumption.
Qed.

Lemma mm_grant_none_exists_of_place : forall mo hint nZ, 0 < nZ -> nZ mod page_size = 0 ->
  (exists z, Mmap.linux_place (m_vmmaps mo) (kb_thp (m_kernel mo)) hint nZ z) ->
  exists a, mm_grant_none mo hint a nZ.
Proof.
  intros mo hint nZ Hp Ha [z HL].
  destruct (Placement.linux_place_admissible _ _ _ _ _ Hp Ha HL) as (_ & A2 & A3 & _).
  pose proof (Placement.alloc_top_lt_two_pow_64 (m_vmmaps mo)) as Hat. rewrite two_pow_64_val in Hat.
  exists (Z_to_bv 64 z). apply (mm_grant_none_of_place mo hint _ nZ Hp Ha).
  rewrite (u64_of_Z z) by lia. exact HL.
Qed.

Lemma mm_grant_rw_not_refusable : forall mo hint a nZ, 0 < nZ -> nZ mod page_size = 0 ->
  mm_grant_rw mo hint a nZ -> mm_refusable mo mm_prot_rw mm_flags_anon hint nZ = false.
Proof.
  intros mo hint a nZ Hp Ha (HL & H1 & H2 & H3 & H4 & H5). rewrite mm_refusable_rw.
  unfold mmap_noreserve_backed_ok. rewrite mm_flags_anon_noreserve, H5.
  rewrite (mm_place_ok_of_place mo hint nZ a Hp Ha HL). reflexivity.
Qed.

Lemma mm_grant_none_not_refusable : forall mo hint a nZ, 0 < nZ -> nZ mod page_size = 0 ->
  mm_grant_none mo hint a nZ -> mm_refusable mo mm_prot_none mm_flags_anon hint nZ = false.
Proof.
  intros mo hint a nZ Hp Ha (HL & _). rewrite mm_refusable_none.
  rewrite (mm_place_ok_of_place mo hint nZ a Hp Ha HL). reflexivity.
Qed.

Lemma mm_not_refusable_grant_rw : forall mo hint nZ, 0 < nZ -> nZ mod page_size = 0 ->
  mm_refusable mo mm_prot_rw mm_flags_anon hint nZ = false -> exists a, mm_grant_rw mo hint a nZ.
Proof.
  intros mo hint nZ Hp Ha H. rewrite mm_refusable_rw in H. unfold mmap_noreserve_backed_ok in H.
  rewrite mm_flags_anon_noreserve in H. apply orb_false_iff in H as [Hb Hg].
  apply negb_false_iff in Hb. apply negb_false_iff in Hg.
  destruct (mm_place_of_ok mo hint nZ Hp Ha Hg) as [a HL].
  exists a. apply (mm_grant_rw_of_place mo hint a nZ Hp Ha). split; [exact HL|].
  cbn [orb] in Hb. exact Hb.
Qed.

Lemma mm_not_refusable_grant_none : forall mo hint nZ, 0 < nZ -> nZ mod page_size = 0 ->
  mm_refusable mo mm_prot_none mm_flags_anon hint nZ = false -> exists a, mm_grant_none mo hint a nZ.
Proof.
  intros mo hint nZ Hp Ha H. rewrite mm_refusable_none in H. apply negb_false_iff in H.
  destruct (mm_place_of_ok mo hint nZ Hp Ha H) as [a HL].
  exists a. exact (mm_grant_none_of_place mo hint a nZ Hp Ha HL).
Qed.

(* [comment removed for export] *)
Theorem anstep_inhabited : forall n mo, alloc_node n = true -> nsafe n mo -> exists rsp mo', anstep n mo rsp mo'.
Proof.
  intros n mo Hn Hs; destruct n; cbn in Hn; try discriminate; cbn [anstep].
  - eexists _, _. exists (vm_brk (m_vmmaps mo)). split; [apply brk_r_ok_refuse|]. split; reflexivity.
  - cbn [nsafe] in Hs. destruct Hs as (_ & Hlen & [[-> ->] | [[-> ->] | (-> & -> & _)]] & _).
    + destruct (mm_refusable mo mm_prot_rw mm_flags_anon (Z_to_bv 64 addr) (mmap_len len)) eqn:Hf.
      * eexists _, _. left. exists ENOMEM. split; [split; [apply ENOMEM_in_mmap_errnos| reflexivity]|]. split; reflexivity.
      * destruct (mm_not_refusable_grant_rw mo (Z_to_bv 64 addr) _ (mmap_len_pos len ltac:(lia))
                    ltac:(rewrite page_size_val; apply mmap_len_aligned) Hf) as [a Ha].
        eexists _, _. right; left. split; [reflexivity|]. split; [reflexivity|]. exists a. split; [exact Ha|]. split; reflexivity.
    + destruct (mm_refusable mo mm_prot_none mm_flags_anon (Z_to_bv 64 addr) (mmap_len len)) eqn:Hf.
      * eexists _, _. left. exists ENOMEM. split; [split; [apply ENOMEM_in_mmap_errnos| reflexivity]|]. split; reflexivity.
      * destruct (mm_not_refusable_grant_none mo (Z_to_bv 64 addr) _ (mmap_len_pos len ltac:(lia))
                    ltac:(rewrite page_size_val; apply mmap_len_aligned) Hf) as [a Ha].
        eexists _, _. right; right; left. split; [reflexivity|]. split; [reflexivity|]. exists a. split; [exact Ha|]. split; reflexivity.
    + eexists _, _. right; right; right. split; [reflexivity|]. split; [reflexivity|]. left. split; reflexivity.
  (* NMunmap is inhabited by its success arm. *)
  - eexists _, _. split; reflexivity.
  - destruct (mprotect_budget_ok mo (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len))) eqn:Hb.
    + eexists _, _. right. split; [reflexivity|]. split; reflexivity.
    + eexists _, _. left. exists ENOMEM. split; [split; [apply ENOMEM_in_mprotect_errnos|]|split; reflexivity].
      unfold mprotect_refusable. rewrite Hb. reflexivity.
  - destruct (Z.eq_dec (mmap_len oldlen) (mmap_len newlen)).
    + eexists _, _. left. split; [assumption|]. split; reflexivity.
    + destruct (Z.ltb_spec TASK_SIZE (mmap_len newlen)) as [Hts|Hts].
      * eexists _, _. right. split; [assumption|]. left. exists EINVAL. split; [right; split; [exact Hts|reflexivity]|]. split; reflexivity.
      * eexists _, _. right. split; [assumption|]. left. exists ENOMEM. split; [left; split; [exact Hts|apply ENOMEM_in_mremap_errnos]|]. split; reflexivity.
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
  alloc_node n = true -> input_at n i -> m_vm_lazy mo = [] -> nsafe n mo -> nvdso_free n mo ->
  injected_family_off ACFG i = true ->
  refusal_b i mo (eff_ret rsp) = true ->
  rnstep n mo rsp' mo'' -> refusal_b i mo (eff_ret rsp') = false ->
  spurious_refusal_cfg ACFG i mo rsp.
Proof.
  intros n i mo rsp rsp' mo'' Hn Hi Hl Hs Hvd Hoff Hr H' Hnr.
  apply (refusal_spurious_of_grant ACFG i mo rsp rsp' mo'' [] Hoff Hr); [|exact Hnr].
  apply (proj2 (alloc_outcome_i n i mo Hn Hi Hl Hs Hvd (Ok rsp' mo'' []))).
  eexists _, _. split; [reflexivity|exact H'].
Qed.

Lemma rnstep_nsp_anstep : forall segs n ms mo x8 rsp mo',
  alloc_node n = true -> at_node segs n ms -> MOK mo -> nsafe n mo -> nvdso_free n mo ->
  ms_svc_pending ms = Some x8 ->
  rnstep n mo rsp mo' ->
  ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo rsp ->
  anstep n mo rsp mo'.
Proof.
  intros segs n ms mo x8 rsp mo' Hn Hat [_ Hl] Hs Hvd Hsvc H Hns.
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
      apply (rnstep_spurious (NMmap addr len prot flags) _ mo rsp rsp' mo'' eq_refl Hi Hl Hs Hvd Hoff Hr H').
      rewrite (refusal_b_222 _ mo _ Hno). exact (mmap_ret_aligned_nonrefusal _ Hal'). }
    pose proof Hs as Hs'. cbn [nsafe] in Hs'. destruct Hs' as (Haddr & Hlen & Hshape & _).
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
      destruct (mm_refusable mo prot flags (Z_to_bv 64 addr) (mmap_len len)) eqn:Hrf; [reflexivity|exfalso].
      destruct Hshape as [[-> ->] | [[-> ->] | (-> & -> & _)]].
      * destruct (mm_not_refusable_grant_rw mo (Z_to_bv 64 addr) _ (mmap_len_pos len ltac:(lia))
                    ltac:(rewrite page_size_val; apply mmap_len_aligned) Hrf) as [a Ha].
        pose proof Ha as (_ & Hal & _).
        apply (SP (mkEffect a [] [(a, Z_to_bv 64 (mmap_len len))]) (mm_anon_model mo a (Z_to_bv 64 (mmap_len len))));
          [| exact Hal | exact Hr].
        cbn [rnstep]. right; left. split; [reflexivity|]. split; [reflexivity|].
        exists a. split; [exact Ha|]. split; reflexivity.
      * destruct (mm_not_refusable_grant_none mo (Z_to_bv 64 addr) _ (mmap_len_pos len ltac:(lia))
                    ltac:(rewrite page_size_val; apply mmap_len_aligned) Hrf) as [a Ha].
        pose proof Ha as (_ & Hal & _).
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
      by (apply acfg_family_off_215; exact Hno).
    cbn [rnstep] in H. cbn [anstep].
    destruct H as [(e & He & -> & ->) | Hok]; [exfalso | exact Hok].
    apply Hns.
    apply (rnstep_spurious (NMunmap addr len) _ mo (efferr e)
             (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] [])
             (mm_unmapped_model mo (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len))) eq_refl Hi Hl Hs Hvd Hoff).
    + rewrite (refusal_b_215 _ mo _ Hno). exact (ret_in_errnos_errno _ _ He).
    + cbn [rnstep]. right. split; reflexivity.
    + rewrite (refusal_b_215 _ mo _ Hno). vm_compute. reflexivity.
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
             (mprotect_model_next mo (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len))) eq_refl Hi Hl Hs Hvd Hoff).
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
  alloc_node n = true -> at_node segs n ms -> MOK mo -> nsafe n mo -> nvdso_free n mo ->
  node_ok segs (mkCfg ms mo) (aidx ms n mo) (fun _ => []) (aidx_nx ms).
Proof.
  intros n ms mo Hn Hat [Hh Hl] Hs Hvd.
  destruct (at_node_outcome segs n ms mo Hn Hat Hl Hs Hvd) as (x8 & Hsvc & Hiff).
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
      (* rnstep_nsp_anstep gained nvdso_free between Hs and Hsvc (:1095); :1247 was updated
         and this one was not, because the file has never compiled past :768. *)
      pose proof (rnstep_nsp_anstep segs n ms mo x8 eff mo1 Hn Hat (conj Hh Hl) Hs Hvd Hsvc Hr Hns) as Ha.
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

(* LPS 08b1429: an allocation node's call (brk, mmap, munmap, mprotect, mremap) reads no user memory. *)
Lemma alloc_node_rob : forall n ms mo,
  alloc_node n = true -> at_node segs n ms -> sys_rob segs (mkCfg ms mo).
Proof.
  intros n ms mo Hn Hat.
  destruct (input_at_sys_input segs n ms Hn Hat) as (x8 & Hsvc & Hin).
  apply (sys_rob_memfree segs ms mo x8 Hsvc).
  destruct n; cbn in Hn; try discriminate Hn; cbn [input_at] in Hin; destruct Hin as [Hno _];
    change (bv_unsigned (in_sysno (sys_input segs ms x8))) with (bv_unsigned x8) in Hno;
    rewrite Hno; memfree_lit.
Qed.

(* [comment removed for export] *)
Theorem rz_alloc_node : forall n ms mo (T : TSet),
  alloc_node n = true -> at_node segs n ms -> MOK mo -> nsafe n mo -> nvdso_free n mo ->
  (forall rsp mo', anstep n mo rsp mo' -> realizes segs (mkCfg (nret ms rsp) mo') T) ->
  realizes segs (mkCfg ms mo) T.
Proof.
  intros n ms mo T Hn Hat HM Hs Hvd HK.
  assert (Hex : exists p : resp * Model, anstep n mo (fst p) (snd p) /\
            forall y, ms_svc_pending ms = Some y -> ~ spurious_refusal_cfg ACFG (sys_input segs ms y) mo (fst p)).
  { destruct (at_node_outcome segs n ms mo Hn Hat (proj2 HM) Hs Hvd) as (x8 & Hsvc & Hiff).
    destruct (Classical_Prop.classic (exists eff' m' evs', syscall_spec (sys_input segs ms x8) mo (Ok eff' m' evs')
                         /\ refusal_b (sys_input segs ms x8) mo (eff_ret eff') = false))
      as [(eff' & m' & evs' & Hs' & Hr') | Hno].
    - apply Hiff in Hs' as (rsp & mo' & E & Hr). injection E as <- <- ->.
      assert (Hns : ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff')
        by (apply spurious_refusal_not_refusal; exact Hr').
      exists (eff', m'). split; [exact (rnstep_nsp_anstep segs n ms mo x8 eff' m' Hn Hat HM Hs Hvd Hsvc Hr Hns)|].
      intros y Hy. rewrite Hsvc in Hy. injection Hy as <-. exact Hns.
    - destruct (anstep_inhabited n mo Hn Hs) as (rsp0 & mo0 & Ha0).
      exists (rsp0, mo0). split; [exact Ha0|].
      intros y Hy. rewrite Hsvc in Hy. injection Hy as <-.
      intros (_ & _ & W). exact (Hno W). }
  destruct Hex as [p0 Hp0].
  pose (i0 := exist _ p0 Hp0 : aidx ms n mo).
  apply (rz_conseq segs _ (t_alt (fun _ : aidx ms n mo => t_emit [] T))).
  - apply (rz_node segs (mkCfg ms mo) (aidx ms n mo) (fun _ => []) (aidx_nx ms) (fun _ => T) i0
             (alloc_node_ok n ms mo Hn Hat HM Hs Hvd) (alloc_node_rob n ms mo Hn Hat)).
    intros [[rsp mo'] [Ha Hns]]. cbn [aidx_nx proj1_sig fst snd]. apply HK. exact Ha.
  - assert (HT : T []).
    { eapply realizes_nonempty. apply (HK (fst p0) (snd p0) (proj1 Hp0)). }
    intros tr. split.
    + intros [_ Ht]. exact (proj1 (t_emit_nil_eq T HT tr) Ht).
    + intros Ht. exists i0. exact (proj2 (t_emit_nil_eq T HT tr) Ht).
Qed.

(* [comment removed for export] *)
Theorem scps_alloc_node : forall n ms mo,
  alloc_node n = true -> at_node segs n ms -> MOK mo -> nsafe n mo -> nvdso_free n mo ->
  SCPS segs (fun ms' mo' => exists rsp, ms' = nret ms rsp /\ anstep n mo rsp mo' /\ MOK mo') ms mo.
Proof.
  intros n ms mo Hn Hat HM Hs Hvd T K.
  apply (rz_alloc_node n ms mo T Hn Hat HM Hs Hvd).
  intros rsp mo' Ha. apply K; [| eapply anstep_vm_only; exact Ha].
  exists rsp. split; [reflexivity|]. split; [exact Ha|].
  eapply anstep_MOK; eassumption.
Qed.

End WithSegs.

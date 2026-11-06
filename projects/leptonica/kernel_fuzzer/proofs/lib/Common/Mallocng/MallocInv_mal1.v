(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_wf4 MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_usage MallocInv_ops MallocInv_hints MallocInv_sc
  MallocInv_sc3 MallocInv_actw MallocInv_free MallocInv_ameta_iface MallocInv_ntfree MallocInv_ntpost MallocInv_ntq MallocInv_ntg MallocInv_take MallocInv_agm2.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Unset Lia Cache.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mal_sc (n : word) : M word :=
  let a0 := v_addi n 3 in
  let n16 := v_srli a0 4 in
  if c_ltu n (wlit 157) then mret n16 else m_size_to_class_big A_SIZE_CLASSES n16.

(* [comment removed for export] *)
Definition mal_coarse (sc0 g0 : word) : M (word * option word)%type :=
  let sc1 := v_addiw sc0 0 in
  if negb (is0 g0) then mret (sc0, Some g0)
  else if c_eq sc1 (wlit 6) then mret (sc0, Some g0)
  else if c_ltu (wlit 27) (v_addiw sc0 (-4)) then mret (sc0, Some g0)
  else if negb (is0 (v_andi sc0 1)) then mret (sc0, None)
  else us <- m_ld (at_ (v_add A_LOCK (v_slli sc1 3)) 472) ;;
       if negb (is0 us) then mret (sc0, None)
       else
         let sco := v_ori sc0 1 in
         let a1 := v_add A_LOCK (v_slli (v_addiw sco 0) 3) in
         g1 <- m_ld (at_ a1 88) ;;
         u1 <- m_ld (at_ a1 472) ;;
         u2 <- (if is0 g1 then mret (v_addi u1 3)
                else am <- m_lw (at_ g1 24) ;;
                     if negb (is0 am) then mret u1
                     else fm <- m_lw (at_ g1 28) ;;
                          if negb (is0 fm) then mret u1
                          else mret (v_addi u1 3)) ;;
         let sc2 := if c_ltu u2 (wlit 13) then sco else sc0 in
         g2 <- m_ld (at_ (v_add A_LOCK (v_slli (v_addiw sc2 0) 3)) 88) ;;
         mret (sc2, Some g2).

(* [comment removed for export] *)
Definition mal_mk (go : option word) : M word :=
  match go with
  | None => mret w0
  | Some g => if is0 g then mret w0 else m_lw (at_ g 24)
  end.

(* [comment removed for export] *)
Definition mal_gi (sp n sc : word) (go : option word) (mk : word) : M (option (word * word))%type :=
  let first := v_and mk (v_subw w0 mk) in
  if negb (is0 first)
  then match go with
       | None => mcrash
       | Some g => idx <- m_lbu (v_add A_DEBRUIJN (v_srliw (v_mul (v_and mk (v_subw w0 mk)) DEBRUIJN_MULT) 27)) ;;
                   m_sw (at_ g 24) (v_subw mk first) ;;
                   mret (Some (g, idx))
       end
  else let sc3 := v_addiw sc 0 in
       idx <- m_alloc_slot ALLOC_FUEL (at_ sp (-144)) sc3 n ;;
       if c_lts idx w0 then m_unlock ;; mret None
       else g <- m_ld (at_ (v_add A_LOCK (v_slli sc3 3)) 88) ;;
            mret (Some (g, idx)).

(* [comment removed for export] *)
Definition mal_fin (n : word) (gi : option (word * word)) : M word :=
  match gi with
  | None => mret w0
  | Some (g, idx) =>
      ctr <- m_lw (at_ A_LOCK 20) ;;
      m_unlock ;;
      m_enframe g idx n ctr
  end.

(* [comment removed for export] *)
Definition mal_big (sp n : word) : M word :=
  let needed := v_addi n 20 in
  p <- sys_mmap MMrw needed ;;
  if c_eq p wm1 then mret w0
  else
  mt <- m_lbu A_NEED_LOCKS ;; massert (is0 mt) ;;
  sq <- m_lbu (at_ A_LOCK 920) ;;
  sq' <- ag_seq sq ;;
  m_sb (at_ A_LOCK 920) sq' ;;
  g <- m_alloc_meta (at_ sp (-64)) ;;
  (if is0 g then
     m_unlock ;;
     r <- sys_munmap p needed ;; mret w0
   else
     m_sd (at_ g 16) p ;;
     m_sd p g ;;
     m_sd (at_ g 32) (v_or (v_andi (v_addi (v_add n (wlit 4064)) 51) (-2048)) (wlit 4064)) ;;
     m_sw (at_ g 28) w0 ;;
     m_sw (at_ g 24) w0 ;;
     c <- m_lw (at_ A_LOCK 20) ;;
     m_sw (at_ A_LOCK 20) (v_addi c 1) ;;
     ctr <- m_lw (at_ A_LOCK 20) ;;
     m_unlock ;;
     m_enframe g w0 n ctr).

Lemma m_malloc_eq : forall sp n, m_malloc sp n =
  (if negb (c_ltu n (wlit 0x7fffffffffffefff))
   then m_sw A_ERRNO (wlit 12) ;; mret w0
   else if negb (c_ltu n MMAP_THRESHOLD_W) then mal_big sp n
   else sc0 <- mal_sc n ;;
        mt <- m_lbu A_NEED_LOCKS ;; massert (is0 mt) ;;
        g0 <- m_ld (at_ (v_add A_LOCK (v_slli (v_addiw sc0 0) 3)) 88) ;;
        r <- mal_coarse sc0 g0 ;;
        let '(sc, go) := r in
        mk <- mal_mk go ;;
        gi <- mal_gi sp n sc go mk ;;
        mal_fin n gi).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition chk_mono (sc : Z) : bool := size_class sc <=? size_class (sc + 1).
Lemma chk_monos : forallb chk_mono (Zseq 0 47) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma size_class_mono1 : forall sc, 0 <= sc < 47 -> size_class sc <= size_class (sc + 1).
Proof.
  intros sc Hsc. pose proof (proj1 (forallb_forall _ _) chk_monos sc (Zseq_In 47 0 sc ltac:(lia))) as H.
  apply Z.leb_le in H. exact H.
Qed.

Definition chk_small10 (sc : Z) : bool := size_class sc =? sc + 1.
Lemma chk_small10s : forallb chk_small10 (Zseq 0 10) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma size_class_small10 : forall sc, 0 <= sc < 10 -> size_class sc = sc + 1.
Proof.
  intros sc Hsc. pose proof (proj1 (forallb_forall _ _) chk_small10s sc (Zseq_In 10 0 sc ltac:(lia))) as H.
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma lor1_even : forall sc, 0 <= sc -> sc mod 2 = 0 -> Z.lor sc 1 = sc + 1.
Proof.
  intros sc Hsc Hev. pose proof (Z.div_mod sc 2 ltac:(lia)) as E. rewrite Hev, Z.add_0_r in E.
  set (q := sc / 2) in *. rewrite E.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Z.testbit_even_0, Z.testbit_odd_0. reflexivity.
  - replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ, Z.testbit_odd_succ by lia.
    rewrite (Z.bits_above_log2 1 (Z.succ (i - 1))) by (cbn; lia). rewrite Bool.orb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma addr_active_lock : forall sc, 0 <= sc < 64 ->
  at_ (v_add A_LOCK (v_slli (Z_to_bv 64 sc) 3)) 88 = Z_to_bv 64 (caddr (KActive sc)).
Proof. intros sc Hsc. rewrite A_LOCK_eq, v_slli_Z, v_add_Z, at_Z by lia. f_equal. cbn. unfold C_ACTIVE. change (2^3) with 8. lia. Qed.
Lemma addr_usage_lock : forall sc, 0 <= sc < 64 ->
  at_ (v_add A_LOCK (v_slli (Z_to_bv 64 sc) 3)) 472 = Z_to_bv 64 (caddr (KUsage sc)).
Proof. intros sc Hsc. rewrite A_LOCK_eq, v_slli_Z, v_add_Z, at_Z by lia. f_equal. cbn. unfold C_USAGE. change (2^3) with 8. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Pure.
  Context {R : Type}.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop).

  (* [comment removed for export] *)
  Lemma size_to_class_z_n16 : forall n, 0 <= n -> size_to_class_z n = size_to_class_z (16 * ((n + 3) / 16)).
  Proof.
    intros n Hn. unfold size_to_class_z.
    replace ((16 * ((n + 3) / 16) + 3) / 16) with ((n + 3) / 16); [reflexivity|].
    rewrite (Z.mul_comm 16 ((n + 3) / 16)), Z.div_add_l by lia. change (3 / 16) with 0. lia.
  Qed.

  Theorem mal_sc_ok : forall s (n : Z) (k : word -> M R) P,
    rodata_clear (ms_mem s) -> WIN s -> 0 <= n < MMAP_THRESHOLD ->
    (forall sc0, 0 <= sc0 < 48 -> n + 4 <= 16 * size_class sc0 -> sc0 = size_to_class_z n -> tsafe (k (Z_to_bv 64 sc0) s) P) ->
    tsafe ((x <- mal_sc (Z_to_bv 64 n) ;; k x) s) P.
  Proof.
    intros s n k P HRO HWIN Hn HK. unfold MMAP_THRESHOLD in Hn. unfold mal_sc. cbv zeta. unfold wlit.
    rewrite v_addi_Z. rewrite v_srli_Z by (clear - Hn; lia). change (2^4) with 16.
    pose proof (size_to_class_z_n16 n ltac:(clear - Hn; lia)) as Hz.
    pose proof (Z.div_mod (n + 3) 16 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (n + 3) 16 ltac:(lia)) as Hmb.
    set (n16 := (n + 3) / 16) in *.
    rewrite c_ltu_Z by (clear - Hn; lia).
    destruct (Z.ltb_spec n 157) as [Hs | Hb].
    - apply ts_bind_ret. assert (Hn16 : 0 <= n16 < 10) by (clear - Hs Hn Hdm Hmb; lia).
      apply HK; [clear - Hn16; lia| |]. { rewrite (size_class_small10 n16 Hn16). clear - Hdm Hmb. lia. }
      rewrite Hz. unfold size_to_class_z. replace ((16 * n16 + 3) / 16) with n16 by (rewrite (Z.mul_comm 16 n16), Z.div_add_l by lia; change (3 / 16) with 0; lia).
      cbv zeta. replace (n16 <? 10) with true by (symmetry; apply Z.ltb_lt; clear - Hn16; lia). reflexivity.
    - assert (Hn16 : 10 <= n16 < 8191) by (clear - Hb Hn Hdm Hmb; lia).
      apply (ts_size_to_class_big s n16 k P HRO HWIN Hn16).
      destruct (stc_facts n16 Hn16) as (_ & _ & _ & _ & _ & _ & Hs & Hlt & Hstc).
      apply HK; [exact Hs| | rewrite Hz; exact Hstc]. clear - Hlt Hdm Hmb. lia.
  Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition coarse_post (A : astate) (n sc0 : Z) (r : word * option word) : Prop :=
    exists sc', 0 <= sc' < 48 /\ n + 4 <= 16 * size_class sc' /\ (sc' = sc0 \/ (sc' = sc0 + 1 /\ 4 <= sc0 < 32)) /\
      (r = (Z_to_bv 64 sc', Some (Z_to_bv 64 (a_ctx A (KActive sc')))) \/
       (r = (Z_to_bv 64 sc', None) /\ a_ctx A (KActive sc') = 0)).

  Theorem mal_coarse_ok : forall A s (n sc0 : Z) (k : word * option word -> M R) P,
    WF A -> Rep A (ms_mem s) -> WIN s -> 0 <= sc0 < 48 -> n + 4 <= 16 * size_class sc0 ->
    (forall c, 0 <= c < 48 -> 0 <= a_ctx A (KUsage c) < 2^47) ->
    (forall r, coarse_post A n sc0 r -> tsafe (k r s) P) ->
    tsafe ((r <- mal_coarse (Z_to_bv 64 sc0) (Z_to_bv 64 (a_ctx A (KActive sc0))) ;; k r) s) P.
  Proof.
    intros A s n sc0 k P HW HR HWIN Hsc Hfit Hus HK.
    pose proof (repw_init A (ms_mem s) HW HR) as RW0.
    assert (SELF : forall go, (go = Some (Z_to_bv 64 (a_ctx A (KActive sc0))) \/ (go = None /\ a_ctx A (KActive sc0) = 0)) ->
                   tsafe (k (Z_to_bv 64 sc0, go) s) P).
    { intros go Hgo. apply HK. exists sc0. split; [exact Hsc|]. split; [exact Hfit|]. split; [left; reflexivity|].
      destruct Hgo as [-> | [-> H0]]; [left; reflexivity | right; auto]. }
    pose proof (wf_ctx_nonneg A HW (KActive sc0)) as Hg0.
    assert (Hg0r : a_ctx A (KActive sc0) < 2^64).
    { rewrite (wf_act_head A HW sc0 Hsc). destruct (a_active A sc0) as [|h t] eqn:E; [cbn; clear; lia|]. cbn.
      destruct (wf_act_mem A HW sc0 h ltac:(rewrite E; left; reflexivity)) as (mt & aib & sl & Hm & _).
      pose proof (meta_facts A h mt HW Hm) as (_ & M2 & _). pose proof alloc_ceiling_val. clear - M2 H. lia. }
    unfold mal_coarse. cbv zeta. unfold wlit. rewrite sextw_small by (clear - Hsc; lia).
    rewrite is0_Z by (clear - Hg0 Hg0r; lia).
    destruct (Z.eqb_spec (a_ctx A (KActive sc0)) 0) as [E0 | N0]; cbn [negb]; [| apply ts_bind_ret; apply SELF; left; reflexivity].
    rewrite c_eq_Z by (clear - Hsc; lia).
    destruct (Z.eqb_spec sc0 6) as [E6 | N6]; [apply ts_bind_ret; apply SELF; left; reflexivity|].
    (* [comment removed for export] *)
    rewrite v_addiw_Z by (clear - Hsc; lia). rewrite swrap32_small by (clear - Hsc; lia).
    destruct (Z.lt_ge_cases sc0 4) as [H4 | H4].
    { rewrite <- (ZZ_mod (sc0 + -4)). rewrite c_ltu_Z by (pose proof (Z.mod_pos_bound (sc0 + -4) (2^64)); clear - H Hsc; lia).
      replace ((sc0 + -4) mod 2^64) with (2^64 + (sc0 - 4)) by (apply (Z.mod_unique_pos _ _ (-1)); clear - H4 Hsc; lia).
      rewrite (proj2 (Z.ltb_lt _ _)) by (clear - H4 Hsc; lia). apply ts_bind_ret. apply SELF. left. reflexivity. }
    rewrite c_ltu_Z by (clear - H4 Hsc; lia).
    destruct (Z.ltb_spec 27 (sc0 + -4)) as [H32 | H32]; [apply ts_bind_ret; apply SELF; left; reflexivity|].
    rewrite v_andi_Z by (clear - Hsc; lia). change 1 with (2^1 - 1) at 1. rewrite land_ones_low by (clear - Hsc; lia). change (2^1) with 2.
    pose proof (Z.mod_pos_bound sc0 2 ltac:(lia)) as Hm2. rewrite is0_Z by (clear - Hm2; lia).
    destruct (Z.eqb_spec (sc0 mod 2) 0) as [Ev | Od]; cbn [negb]; [| apply ts_bind_ret; apply SELF; right; auto].
    (* [comment removed for export] *)
    apply ts_assoc. rewrite (addr_usage_lock sc0) by (clear - Hsc; lia).
    pose proof (Hus sc0 Hsc) as Hu0.
    eapply (ts_ld_ctxfW A HW s (ms_mem s) [] (KUsage sc0)); [exact RW0 | exact HWIN | cbn; clear - Hsc; lia | reflexivity | apply wfree_range_nil |].
    rewrite is0_Z by (clear - Hu0; lia).
    destruct (Z.eqb_spec (a_ctx A (KUsage sc0)) 0) as [Eu | Nu]; cbn [negb]; [| apply ts_bind_ret; apply SELF; right; auto].
    (* [comment removed for export] *)
    rewrite v_ori_Z by (clear - Hsc; lia). rewrite (lor1_even sc0) by (try exact Ev; clear - Hsc; lia).
    set (sco := sc0 + 1) in *. assert (Hsco : 0 <= sco < 48) by (clear - H4 H32; subst sco; lia).
    assert (Hfit1 : n + 4 <= 16 * size_class sco) by (pose proof (size_class_mono1 sc0 ltac:(clear - H4 H32; lia)) as M; subst sco; clear - M Hfit; lia).
    assert (OTHER : forall go, go = Some (Z_to_bv 64 (a_ctx A (KActive sco))) -> tsafe (k (Z_to_bv 64 sco, go) s) P).
    { intros go ->. apply HK. exists sco. split; [exact Hsco|]. split; [exact Hfit1|]. split; [right; split; [reflexivity | clear - H4 H32; lia]|]. left. reflexivity. }
    rewrite sextw_small by (clear - Hsco; lia).
    apply ts_assoc. rewrite (addr_active_lock sco) by (clear - Hsco; lia).
    eapply (ts_ld_ctxfW A HW s (ms_mem s) [] (KActive sco)); [exact RW0 | exact HWIN | cbn; clear - Hsco; lia | reflexivity | apply wfree_range_nil |].
    apply ts_assoc. rewrite (addr_usage_lock sco) by (clear - Hsco; lia).
    pose proof (Hus sco Hsco) as Hu1.
    eapply (ts_ld_ctxfW A HW s (ms_mem s) [] (KUsage sco)); [exact RW0 | exact HWIN | cbn; clear - Hsco; lia | reflexivity | apply wfree_range_nil |].
    apply ts_assoc.
    (* [comment removed for export] *)
    assert (BUMP : forall (u2 : word) , tsafe ((y <- (g2 <- m_ld (at_ (v_add A_LOCK (v_slli (v_addiw (if c_ltu u2 (Z_to_bv 64 13) then Z_to_bv 64 sco else Z_to_bv 64 sc0) 0) 3)) 88) ;;
                                                     mret (if c_ltu u2 (Z_to_bv 64 13) then Z_to_bv 64 sco else Z_to_bv 64 sc0, Some g2)) ;; k y) s) P).
    { intros u2. apply ts_assoc. destruct (c_ltu u2 (Z_to_bv 64 13)).
      - rewrite sextw_small by (clear - Hsco; lia). rewrite (addr_active_lock sco) by (clear - Hsco; lia).
        eapply (ts_ld_ctxfW A HW s (ms_mem s) [] (KActive sco)); [exact RW0 | exact HWIN | cbn; clear - Hsco; lia | reflexivity | apply wfree_range_nil |].
        apply ts_bind_ret. apply OTHER. reflexivity.
      - rewrite sextw_small by (clear - Hsc; lia). rewrite (addr_active_lock sc0) by (clear - Hsc; lia).
        eapply (ts_ld_ctxfW A HW s (ms_mem s) [] (KActive sc0)); [exact RW0 | exact HWIN | cbn; clear - Hsc; lia | reflexivity | apply wfree_range_nil |].
        apply ts_bind_ret. apply SELF. left. reflexivity. }
    pose proof (wf_ctx_nonneg A HW (KActive sco)) as Hg1. rewrite (wf_act_head A HW sco Hsco) in Hg1 |- *.
    destruct (a_active A sco) as [|h t] eqn:Eact.
    - cbn [hd]. rewrite is0_Z by (clear; lia). cbn [Z.eqb]. apply ts_bind_ret. apply BUMP.
    - cbn [hd] in Hg1 |- *.
      destruct (wf_act_mem A HW sco h ltac:(rewrite Eact; left; reflexivity)) as (mt & aib & sl & Hm & Hr & _).
      pose proof (meta_facts A h mt HW Hm) as (M1 & M2 & M3 & M4 & Mdom). pose proof alloc_ceiling_val as HCV.
      destruct (wf_grp A HW h mt aib sl Hm Hr) as (Hw32 & _ & _ & _ & Hav & Hfr & _). pose proof (w_last_range (mt_w32 mt)) as Hl.
      assert (Hc32 : 2 ^ mt_cnt mt <= 2^32) by (apply Z.pow_le_mono_r; unfold mt_cnt, mt_last in *; clear - Hl; lia).
      rewrite is0_Z by (clear - M1 M2 HCV; lia). replace (h =? 0) with false by (symmetry; apply Z.eqb_neq; clear - M1; lia).
      apply ts_assoc. rewrite at_Z. change (h + 24) with (h + moff FAvail).
      eapply (ts_lw_metaW A HW s (ms_mem s) [] h mt FAvail); [exact RW0 | exact HWIN | exact Hm | reflexivity | apply wfree_range_nil | change (mt_f mt FAvail) with (mt_avail mt); clear - Hav Hc32; lia |].
      change (mt_f mt FAvail) with (mt_avail mt). rewrite is0_w32, (Z.mod_small (mt_avail mt) (2^32)) by (clear - Hav Hc32; lia).
      destruct (Z.eqb_spec (mt_avail mt) 0) as [Ea | Na]; cbn [negb]; [| apply ts_bind_ret; apply BUMP].
      apply ts_assoc. rewrite at_Z. change (h + 28) with (h + moff FFreed).
      eapply (ts_lw_metaW A HW s (ms_mem s) [] h mt FFreed); [exact RW0 | exact HWIN | exact Hm | reflexivity | apply wfree_range_nil | change (mt_f mt FFreed) with (mt_freed mt); clear - Hfr Hc32; lia |].
      change (mt_f mt FFreed) with (mt_freed mt). rewrite is0_w32, (Z.mod_small (mt_freed mt) (2^32)) by (clear - Hfr Hc32; lia).
      destruct (Z.eqb_spec (mt_freed mt) 0); cbn [negb]; apply ts_bind_ret; apply BUMP.
  Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem mal_mk_ok : forall A s (n sc : Z) (go : option word) (k : word -> M R) P,
    WF A -> Rep A (ms_mem s) -> WIN s -> 0 <= sc < 48 ->
    (go = Some (Z_to_bv 64 (a_ctx A (KActive sc))) \/ (go = None /\ a_ctx A (KActive sc) = 0)) ->
    (a_active A sc = [] -> tsafe (k (w32 0) s) P) ->
    (forall g mt aib sl, a_active A sc <> [] -> g = hd 0 (a_active A sc) -> a_meta A g = Some mt -> mt_role mt = RGroup aib sl ->
       0 <= mt_avail mt < 2^32 -> tsafe (k (w32 (mt_avail mt)) s) P) ->
    tsafe ((x <- mal_mk go ;; k x) s) P.
  Proof.
    intros A s n sc go k P HW HR HWIN Hsc Hgo HK0 HK1.
    pose proof (repw_init A (ms_mem s) HW HR) as RW0. pose proof (wf_act_head A HW sc Hsc) as Hhd.
    destruct Hgo as [-> | [-> H0]].
    - unfold mal_mk. rewrite Hhd. destruct (a_active A sc) as [|g t] eqn:Eact.
      + cbn [hd]. rewrite is0_Z by (clear; lia). cbn [Z.eqb]. apply ts_bind_ret. rewrite w0_w32. apply HK0. reflexivity.
      + cbn [hd]. destruct (wf_act_mem A HW sc g ltac:(rewrite Eact; left; reflexivity)) as (mt & aib & sl & Hm & Hr & _).
        pose proof (meta_facts A g mt HW Hm) as (M1 & M2 & M3 & M4 & Mdom). pose proof alloc_ceiling_val as HCV.
        destruct (wf_grp A HW g mt aib sl Hm Hr) as (Hw32 & _ & _ & _ & Hav & _). pose proof (w_last_range (mt_w32 mt)) as Hl.
        assert (Hc32 : 2 ^ mt_cnt mt <= 2^32) by (apply Z.pow_le_mono_r; unfold mt_cnt, mt_last in *; clear - Hl; lia).
        rewrite is0_Z by (clear - M1 M2 HCV; lia). replace (g =? 0) with false by (symmetry; apply Z.eqb_neq; clear - M1; lia).
        rewrite at_Z. change (g + 24) with (g + moff FAvail).
        eapply (ts_lw_metaW A HW s (ms_mem s) [] g mt FAvail); [exact RW0 | exact HWIN | exact Hm | reflexivity | apply wfree_range_nil | change (mt_f mt FAvail) with (mt_avail mt); clear - Hav Hc32; lia |].
        apply (HK1 g mt aib sl); [discriminate | reflexivity | exact Hm | exact Hr | clear - Hav Hc32; lia].
    - unfold mal_mk. apply ts_bind_ret. rewrite w0_w32. apply HK0.
      rewrite Hhd in H0. destruct (a_active A sc) as [|g t] eqn:Eact; [reflexivity|]. exfalso. cbn in H0.
      destruct (wf_act_mem A HW sc g ltac:(rewrite Eact; left; reflexivity)) as (mt & aib & sl & Hm & _).
      pose proof (meta_facts A g mt HW Hm) as (M1 & _). clear - M1 H0. lia.
  Qed.
End Pure.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Fast.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A : astate) (s : mstate).
  Hypothesis HII : II sp0 argv envp cb D A s.
  Variables (sc g : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hne : a_active A sc <> [].
  Hypothesis Hhd : g = hd 0 (a_active A sc).
  Hypothesis Hg : a_meta A g = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hav : mt_avail mt <> 0.

  Let av := mt_avail mt.
  Let i := ctz32 av.

  Theorem mal_take_ok : forall (K : option (word * word) -> M R) P,
    (forall s', II sp0 argv envp cb D (tkA A g mt aib slots i) s' -> ntframe A s s' ->
       0 <= i <= aib mod 32 -> i <= mt_last mt -> nth_error slots (Z.to_nat i) = Some SIdle ->
       tsafe (K (Some (Z_to_bv 64 g, Z_to_bv 64 i)) s') P) ->
    tsafe ((r <- (idx <- m_lbu (v_add A_DEBRUIJN (v_srliw (v_mul (v_and (w32 av) (v_subw w0 (w32 av))) DEBRUIJN_MULT) 27)) ;;
                  m_sw (at_ (Z_to_bv 64 g) 24) (v_subw (w32 av) (v_and (w32 av) (v_subw w0 (w32 av)))) ;;
                  mret (Some (Z_to_bv 64 g, idx))) ;; K r) s) P.
  Proof.
    intros K P HK. pose proof (ii_is HII) as HIS. destruct HIS as [HW HR HC HWIN HE HG].
    pose proof (envok_rodata _ _ _ _ HE) as HRO.
    pose proof (take_facts sp0 argv envp cb D A s HII sc g mt aib slots Hsc Hg Hr Hav) as (Hv & Hi & Hbit). fold av i in Hv, Hi, Hbit.
    pose proof (meta_facts A g mt HW Hg) as (M1 & M2 & M3 & M4 & Mdom).
    pose proof (repw_init A (ms_mem s) HW HR) as RW0.
    apply ts_assoc. change (m_lbu (v_add A_DEBRUIJN (v_srliw (v_mul (v_and (w32 av) (v_subw w0 (w32 av))) DEBRUIJN_MULT) 27))) with (m_ctz32 (w32 av)).
    eapply ts_ctz32; [exact HRO | exact HWIN | exact Hv |]. fold i.
    rewrite lowbit_w32 by exact Hv. fold i. rewrite v_subw_w32.
    apply ts_assoc. rewrite (at_Z g 24). unfold m_sw.
    eapply (ts_st_domW A HW s (ms_mem s) [] 4 (g + 24)); [exact RW0 | exact HWIN | clear; lia | intros j Hj; rewrite <- Z.add_assoc; apply Mdom; clear - Hj; lia |]. intros m1 RW1.
    apply ts_bind_ret.
    (* [comment removed for export] *)
    set (A' := tkA A g mt aib slots i).
    assert (HW' : WF A') by (apply (WF_tkA A HW sc g mt aib slots i Hsc Hhd Hne Hg Hr ltac:(clear - Hi; lia) Hbit)).
    change (Z.of_nat 4) with 4 in RW1.
    assert (WO : writes_ok A [FCT (g + 24) 4 (bv_unsigned (w32 (av - 2 ^ i)))]).
    { apply (writes_ok_meta A [] g mt 24 4); [exact HW | apply writes_ok_nil | exact Hg | clear; lia | clear; lia]. }
    assert (HR' : Rep A' m1).
    { apply (repw_commit2 A A' (ms_mem s) _ m1 HW' RW1).
      - intros f Hf. destruct (has_tkA A HW sc g mt aib slots i Hsc Hhd Hne Hg Hr ltac:(clear - Hi; lia) Hbit f Hf) as [Ho | ->]; [left; exact Ho | right].
        intros x Hx. cbn [f_a f_n f_v] in Hx. rewrite wlook_hit by (cbn [f_a f_n]; clear - Hx; lia). discriminate.
      - intros x b Hw. destruct (Z.lt_ge_cases x (g + 24)) as [Hlt | Hge]; [rewrite wlook_skip in Hw by (cbn [f_a f_n]; clear - Hlt; lia); discriminate Hw|].
        destruct (Z.lt_ge_cases x (g + 28)) as [Hlt' | Hge']; [| rewrite wlook_skip in Hw by (cbn [f_a f_n]; clear - Hge'; lia); discriminate Hw].
        rewrite wlook_hit in Hw by (cbn [f_a f_n]; clear - Hge Hlt'; lia). cbn [f_a f_v] in Hw. injection Hw as <-.
        left. exists g, (tk_mt mt aib slots i), FAvail. split; [apply tkA_meta_same|]. cbn [moff mlen]. split; [clear - Hge Hlt'; lia|].
        rewrite tk_mt_f. destruct (mfield_eq_dec FAvail FAvail); [| contradiction]. unfold tk_av, av. rewrite u_w32.
        apply byte_of_sx32. clear - Hge Hlt'. lia.
      - intros x Hx. apply (proj1 (dom_tkA A g mt aib slots i Hg Hr x)). exact Hx. }
    apply HK.
    - apply II_intro.
      + apply (IS_commit sp0 argv envp cb A A' s _ m1 (ii_is HII) RW1 WO HW' HR').
      + cbn [ms_vm upd]. apply (VMok_tkA A g mt aib slots i Hg Hr). exact (ii_vm HII).
      + apply (AvOK_transfer A A' (ii_av HII)); [reflexivity | reflexivity |].
        intros x mt' Hx Hrx. destruct (tkA_meta_inv A g mt aib slots i x mt' Hx) as [(-> & ->) | (Hn & H)]; [cbn in Hrx; discriminate Hrx | eauto].
      + apply (UsOK_transfer A A' (ii_us HII)); [reflexivity | intros c Hc; reflexivity | intros c x; apply meta_usage_tkA; assumption].
      + apply (deads_transfer A A' D (ii_dd HII)). intros x. split.
        * intros (mt' & Hx & Hrx). destruct (tkA_meta_inv A g mt aib slots i x mt' Hx) as [(-> & ->) | (Hn & H)]; [cbn in Hrx; discriminate Hrx | eauto].
        * intros (mt0 & Hx & Hrx). destruct (Z.eq_dec x g) as [-> | Hn]; [rewrite Hg in Hx; injection Hx as <-; rewrite Hr in Hrx; discriminate Hrx|].
          exists mt0. unfold A'. rewrite (tkA_meta_other A g mt aib slots i x Hn). auto.
    - apply (ntframe_commit A s _ m1 HW RW1 WO).
    - pose proof (tk_i_aib A HW sc g mt aib slots i Hsc Hhd Hne Hg Hr ltac:(clear - Hi; lia) Hbit). clear - H Hi. lia.
    - exact (tk_i_last A HW sc g mt aib slots i Hsc Hhd Hne Hg Hr ltac:(clear - Hi; lia) Hbit).
    - exact (tk_slot_idle A HW sc g mt aib slots i Hsc Hhd Hne Hg Hr ltac:(clear - Hi; lia) Hbit).
  Qed.
End Fast.

End WithLayout.

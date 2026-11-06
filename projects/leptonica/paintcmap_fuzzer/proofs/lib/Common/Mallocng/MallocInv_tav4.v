(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf MallocInv_wf2 MallocInv_wf3 MallocInv_wf4 MallocInv_dll MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_sc MallocInv_sc2 MallocInv_ameta_iface MallocInv_tryavail MallocInv_free MallocInv_actw MallocInv_act MallocInv_ntfree MallocInv_ntpost MallocInv_ntq MallocInv_ntg MallocInv_aspieces MallocInv_tav_iface MallocInv_tav2 MallocInv_tav3.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tv_act (m3 : word) : M (option (word * word)%type) :=
  am3 <- m_lw (at_ m3 24) ;; massert (is0 am3) ;;
  mp3 <- m_ld (at_ m3 16) ;;
  ab <- m_lbu (at_ mp3 8) ;;
  let act2 := v_sllw (wlit 2) ab in
  massert (is0 (v_andi (at_ m3 28) 3)) ;;
  fr4 <- m_lw (at_ m3 28) ;;
  m_sw (at_ m3 28) (v_and fr4 (v_subw w0 act2)) ;;
  let mask := v_and fr4 (v_addiw act2 (-1)) in
  m_sw (at_ m3 24) mask ;;
  massert (negb (is0 mask)) ;;
  w32 <- m_lw (at_ m3 32) ;;
  let d := v_addi (v_srli (v_slli w32 52) 58) (-7) in
  (if c_ltu (wlit 31) d then mret tt
   else b <- m_lbu (at_ (v_add A_LOCK d) 888) ;;
        if is0 b then mret tt
        else m_sb (at_ (v_add A_LOCK d) 888) (v_addi b (-1))) ;;
  mret (Some (m3, mask)).

(* [comment removed for export] *)
Definition tv_ext (m2 mp ai : word) : M (option word) :=
  let a5 := v_andi ai 31 in
  w5 <- m_ld (at_ m2 32) ;;
  szc <- m_lhu (v_add A_SIZE_CLASSES (v_andi (v_srli w5 5) 126)) ;;
  let a6 := v_addi a5 2 in
  let a4 := v_addi a5 1 in
  let t0 := v_addi (v_slli a5 4) 48 in
  let size := v_slli szc 4 in
  let a7 := v_mul t0 szc in
  let t0' := v_mul size a6 in
  let a6' := v_addiw a7 15 in
  let t0'' := v_addiw t0' 16 in
  match m_span_loop 40 a6' t0'' a4 size with
  | None => mcrash
  | Some cnt =>
    let lim := v_addi (v_andi w5 31) 1 in
    let cnt' := if c_ltu cnt lim then cnt else lim in
    m_sb (at_ mp 8) (v_or (v_andi (v_addi cnt' (-1)) 31) (v_andi ai 224)) ;;
    mret (Some m2)
  end.

Definition tv_tail3 (pm m2 fr2 : word) : M (option (word * word)%type) :=
  mp <- m_ld (at_ m2 16) ;;
  ai <- m_lbu (at_ mp 8) ;;
  let act := v_addiw (v_sllw (wlit 2) ai) (-1) in
  m3o <- (if negb (is0 (v_and act fr2)) then mret (Some m2)
          else nx3 <- m_ld (at_ m2 8) ;;
               if negb (c_eq nx3 m2)
               then m_sd pm nx3 ;; mret (Some nx3)
               else tv_ext m2 mp ai) ;;
  match m3o with
  | None => mret None
  | Some m3 => tv_act m3
  end.

Definition tv_tail2 (pm m : word) : M (option (word * word)%type) :=
  fr1 <- m_lw (at_ m 28) ;;
  w <- m_ld (at_ m 32) ;;
  mf <- (if negb (is0 (v_andi w 32))
            && c_eq fr1 (v_addiw (v_sllw (wlit 2) w) (-1))
         then m' <- m_ld (at_ m 8) ;;
              m_sd pm m' ;;
              fr' <- m_lw (at_ m' 28) ;;
              mret (m', fr')
         else mret (m, fr1)) ;;
  let '(m2, fr2) := mf in
  tv_tail3 pm m2 fr2.

Definition tv_all (pm m0 : word) : M (option (word * word)%type) :=
  if is0 m0 then mret None
  else
    am <- m_lw (at_ m0 24) ;;
    if negb (is0 am) then mret (Some (m0, am))
    else
      fr <- m_lw (at_ m0 28) ;;
      nx <- m_ld (at_ m0 8) ;;
      mo <- (if negb (is0 fr)
             then m_sd pm nx ;; mret (Some nx)
             else
               (if c_eq nx m0 then m_sd pm w0
                else pv <- m_ld m0 ;;
                     m_sd (at_ pv 8) nx ;;
                     pv2 <- m_ld m0 ;;
                     nx2 <- m_ld (at_ m0 8) ;;
                     m_sd nx2 pv2 ;;
                     h <- m_ld pm ;;
                     if c_eq h m0 then n3 <- m_ld (at_ m0 8) ;; m_sd pm n3
                     else mret tt) ;;
               m_sd m0 w0 ;; m_sd (at_ m0 8) w0 ;;
               m1 <- m_ld pm ;;
               if is0 m1 then mret None else mret (Some m1)) ;;
      match mo with
      | None => mret None
      | Some m => tv_tail2 pm m
      end.

Lemma as_tryavail_eq : forall pm m0, as_tryavail pm m0 = tv_all pm m0.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition allz (A : astate) (sc : Z) : Prop :=
  forall x mtx, In x (a_active A sc) -> a_meta A x = Some mtx -> mt_avail mtx = 0 /\ mt_freed mtx <> 0.

Lemma allz_intro : forall A sc h rest mth, WF A -> a_active A sc = h :: rest -> a_meta A h = Some mth ->
  mt_avail mth = 0 -> mt_freed mth <> 0 -> allz A sc.
Proof.
  intros A sc h rest mth HW Hact Hh Hav Hfr x mtx Hx Hmx. destruct (Z.eq_dec x h) as [-> | Hne].
  - rewrite Hh in Hmx. injection Hmx as <-. auto.
  - apply (wf_act_nonhead A HW sc x mtx Hx); [rewrite Hact; cbn; congruence | exact Hmx].
Qed.

Lemma allz_rotA : forall A sc h rest, a_active A sc = h :: rest -> allz A sc -> allz (rotA A sc h rest) sc.
Proof.
  intros A sc h rest Hact HZ x mtx Hx Hmx. rewrite (rotA_active_sc A sc h rest) in Hx. rewrite (rotA_meta A sc h rest) in Hmx.
  apply (HZ x mtx); [| exact Hmx]. rewrite Hact. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
Qed.

(* [comment removed for export] *)
Lemma allz_deqA : forall A sc h rest, WF A -> a_active A sc = h :: rest -> allz (deqA A sc h [] rest) sc.
Proof.
  intros A sc h rest HW Hact x mtx Hx Hmx. rewrite (deqA_active_sc A sc h [] rest) in Hx. cbn in Hx.
  rewrite (deqA_meta A sc h [] rest x) in Hmx. destruct (a_meta A x) as [mt0|] eqn:E; [| discriminate]. cbn in Hmx. injection Hmx as <-.
  rewrite MallocInv_wf3.rl_avail, MallocInv_wf3.rl_freed.
  pose proof (proj1 (NoDup_ListNoDup _) (wf_act_nodup A HW sc)) as ND. rewrite Hact in ND. apply List.NoDup_cons_iff in ND. destruct ND as [Hnin _].
  apply (wf_act_nonhead A HW sc x mt0); [rewrite Hact; right; exact Hx | | exact E].
  rewrite Hact. cbn. intros ->. exact (Hnin Hx).
Qed.

Lemma allz_meta_eq : forall A A' sc, a_active A' sc = a_active A sc -> (forall x, In x (a_active A sc) -> forall mtx, a_meta A' x = Some mtx ->
  exists mt0, a_meta A x = Some mt0 /\ mt_avail mtx = mt_avail mt0 /\ mt_freed mtx = mt_freed mt0) -> allz A sc -> allz A' sc.
Proof.
  intros A A' sc Hact Hm HZ x mtx Hx Hmx. rewrite Hact in Hx. destruct (Hm x Hx mtx Hmx) as (mt0 & H0 & -> & ->). exact (HZ x mt0 Hx H0).
Qed.

(* [comment removed for export] *)
Lemma ring_member : forall A sc x, WF A -> 0 <= sc < 48 -> In x (a_active A sc) ->
  exists mt aib sl, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl /\ mt_sc mt = sc /\
    0 <= mt_w32 mt < 2^64 /\ 0 <= mt_freed mt < 2 ^ (mt_cnt mt) /\ mt_cnt mt <= 32 /\ 0 <= aib < 256 /\ aib mod 32 <= mt_last mt /\
    0x1000 <= x /\ x + 40 <= alloc_ceiling /\ 0 <= mt_mem mt /\ mt_mem mt + 16 <= alloc_ceiling.
Proof.
  intros A sc x HW Hsc Hx. destruct (wf_act_mem A HW sc x Hx) as (mt & aib & sl & Hm & Hr & Hs).
  destruct (wf_grp A HW x mt aib sl Hm Hr) as (H1 & _ & _ & H4 & _ & H6 & _ & H8 & _ & H10 & _ & _ & Hmem & _ & Hce & _).
  pose proof (w_last_range (mt_w32 mt)) as Hl. pose proof (meta_facts A x mt HW Hm) as (M1 & M2 & _).
  assert (Hc : mt_cnt mt <= 32) by (unfold mt_cnt, mt_last in *; llia).
  assert (0 <= mt_cnt mt * mt_stride mt) by (pose proof (stride_ge16 mt ltac:(llia) ltac:(left; llia)); unfold mt_cnt, mt_last in *; nia).
  exists mt, aib, sl. repeat split; auto; llia.
Qed.

(* [comment removed for export] *)
Lemma head_next : forall A sc h rest mth, WF A -> 0 <= sc < 48 -> a_active A sc = h :: rest -> a_meta A h = Some mth ->
  (rest = [] -> mt_next mth = h) /\ (rest <> [] -> mt_next mth = hd 0 rest /\ mt_next mth <> h /\ In (mt_next mth) rest).
Proof.
  intros A sc h rest mth HW Hsc Hact Hh. rewrite (rot_next A HW sc h rest mth Hsc Hact Hh).
  pose proof (proj1 (NoDup_ListNoDup _) (wf_act_nodup A HW sc)) as ND. rewrite Hact in ND. apply List.NoDup_cons_iff in ND. destruct ND as [Hnin _].
  destruct rest as [|r rest']; cbn; split; intros Hr; try congruence.
  split; [reflexivity|]. split; [intros ->; apply Hnin; left; reflexivity | left; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_31 : forall a, 0 <= a -> Z.land a 31 = a mod 32.
Proof. intros a Ha. change 31 with (2^5 - 1). rewrite land_ones_low by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma freeable_test : forall W, 0 <= W < 2^64 -> w_freeable W = 1 -> negb (is0 (v_andi (Z_to_bv 64 W) 32)) = true.
Proof.
  intros W HW Hf. rewrite v_andi_Z by lia.
  assert (Hb : Z.testbit (Z.land W 32) 5 = true).
  { rewrite Z.land_spec. change 32 with (2^5) at 1. rewrite Z.pow2_bits_true by lia. rewrite Bool.andb_true_r.
    apply Z.testbit_true; [lia|]. unfold w_freeable in Hf. change (2^5) with 32. exact Hf. }
  pose proof (Z.land_nonneg W 32) as Hn. pose proof (land_le_left W 32) as Hle.
  rewrite is0_Z by lia. destruct (Z.eqb_spec (Z.land W 32) 0) as [E | NE]; [| reflexivity].
  rewrite E in Hb. rewrite Z.bits_0 in Hb. discriminate.
Qed.

(* [comment removed for export] *)
Lemma allfree_test : forall fr W, 0 <= fr < 2^32 -> 0 <= W < 2^64 ->
  c_eq (w32 fr) (v_addiw (v_sllw (wlit 2) (Z_to_bv 64 W)) (-1)) = (fr =? 2 ^ (w_last W + 1) - 1).
Proof.
  intros fr W Hfr HW. rewrite v_sllw_2 by lia. unfold w_last. rewrite v_addiw_w32. rewrite c_eq_w32.
  pose proof (Z.mod_pos_bound W 32 ltac:(lia)) as Hk.
  assert (Hp : 0 < 2 ^ (W mod 32 + 1) <= 2^32) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  rewrite (Z.mod_small fr) by lia. rewrite Z.mod_small by lia. f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma act_test : forall fr aib, 0 <= fr < 2^32 -> 0 <= aib < 2^64 ->
  is0 (v_and (v_addiw (v_sllw (wlit 2) (Z_to_bv 64 aib)) (-1)) (w32 fr)) = (fr mod 2 ^ (aib mod 32 + 1) =? 0).
Proof.
  intros fr aib Hfr Haib. rewrite v_sllw_2 by lia. rewrite v_addiw_w32.
  pose proof (Z.mod_pos_bound aib 32 ltac:(lia)) as Hk.
  assert (Hp : 0 < 2 ^ (aib mod 32 + 1) <= 2^32) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  rewrite <- (w32_mod (2 ^ (aib mod 32 + 1) + -1)). rewrite (Z.mod_small (2 ^ (aib mod 32 + 1) + -1)) by lia.
  rewrite v_and_w32 by lia. rewrite is0_w32.
  replace (2 ^ (aib mod 32 + 1) + -1) with (2 ^ (aib mod 32 + 1) - 1) by lia. rewrite Z.land_comm, land_ones_low by lia.
  pose proof (Z.mod_pos_bound fr (2 ^ (aib mod 32 + 1)) ltac:(lia)).
  rewrite Z.mod_small; [reflexivity|]. lia.
Qed.

(* [comment removed for export] *)
Lemma partial_of_masks : forall A m mt aib sl, WF A -> a_meta A m = Some mt -> mt_role mt = RGroup aib sl ->
  mt_freed mt <> 0 -> mt_freed mt mod 2 ^ (aib mod 32 + 1) = 0 ->
  aib mod 32 < mt_last mt /\ 7 <= mt_sc mt /\ forall c, aib mod 32 + 2 <= c -> mt_freed mt mod 2 ^ c <> 0.
Proof.
  intros A m mt aib sl HW Hm Hr Hfr Hlow.
  destruct (wf_grp A HW m mt aib sl Hm Hr) as (Hw32 & _ & _ & _ & _ & Hfrr & _ & Haib & _ & Haibl & _).
  pose proof (Z.mod_pos_bound aib 32 ltac:(lia)) as Hk. set (k := aib mod 32) in *.
  assert (Hlt : k < mt_last mt).
  { destruct (Z.lt_ge_cases k (mt_last mt)) as [H | H]; [exact H | exfalso].
    assert (E : k = mt_last mt) by lia. apply Hfr. rewrite <- Hlow. symmetry. apply Z.mod_small. unfold mt_cnt in Hfrr. rewrite <- E in Hfrr. lia. }
  split; [exact Hlt|]. split; [exact (wf_partial_sc A HW m mt aib sl Hm Hr Hlt)|].
  intros c Hc E. pose proof (wf_inactive A HW m mt aib sl (k + 1) Hm Hr ltac:(lia)) as Hb.
  assert (Hb' : Z.testbit (mt_freed mt mod 2 ^ c) (k + 1) = true) by (rewrite Z.mod_pow2_bits_low by lia; exact Hb).
  rewrite E, Z.bits_0 in Hb'. discriminate.
Qed.

(* [comment removed for export] *)
Lemma full_nz : forall A m mt aib sl, WF A -> a_meta A m = Some mt -> mt_role mt = RGroup aib sl ->
  mt_freed mt <> 0 -> mt_last mt <= aib mod 32 -> mt_freed mt mod 2 ^ (aib mod 32 + 1) <> 0.
Proof.
  intros A m mt aib sl HW Hm Hr Hfr Hge.
  destruct (wf_grp A HW m mt aib sl Hm Hr) as (Hw32 & _ & _ & _ & _ & Hfrr & _).
  rewrite Z.mod_small; [exact Hfr|]. unfold mt_cnt in Hfrr. split; [lia|].
  apply Z.lt_le_trans with (2 ^ (mt_last mt + 1)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Lemma span_run_zeta : forall a sc,
  m_span_loop 40 (v_addiw (v_mul (v_addi (v_slli (Z_to_bv 64 a) 4) 48) (Z_to_bv 64 (size_class sc))) 15)
                 (v_addiw (v_mul (v_slli (Z_to_bv 64 (size_class sc)) 4) (v_addi (Z_to_bv 64 a) 2)) 16)
                 (v_addi (Z_to_bv 64 a) 1) (v_slli (Z_to_bv 64 (size_class sc)) 4) = span_run a sc.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TavExt.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (B : astate) (s1 : mstate).
  Hypothesis HII : II sp0 argv envp cb D B s1.
  Variables (sc m2 : Z) (rest : list Z) (mt2 : meta_rec) (aib2 : Z) (sl2 : list slot_st).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact : a_active B sc = m2 :: rest.
  Hypothesis Hm2 : a_meta B m2 = Some mt2.
  Hypothesis Hr2 : mt_role mt2 = RGroup aib2 sl2.
  Hypothesis Hav0 : mt_avail mt2 = 0.
  Hypothesis Hfr : mt_freed mt2 <> 0.
  Hypothesis Hlow : mt_freed mt2 mod 2 ^ (aib2 mod 32 + 1) = 0.
  Implicit Types (P : R -> mstate -> Prop).

  Theorem ts_tv_ext : forall (K : option word -> M R) P,
    (forall s' aib', II sp0 argv envp cb D (xaA B m2 mt2 sl2 aib') s' -> ntframe B s1 s' ->
       tavrel B (xaA B m2 mt2 sl2 aib') sc -> 0 <= aib' < 256 -> aib2 mod 32 <= aib' mod 32 <= mt_last mt2 ->
       mt_freed mt2 mod 2 ^ (aib' mod 32 + 1) <> 0 ->
       tsafe (K (Some (Z_to_bv 64 m2)) s') P) ->
    tsafe ((x <- tv_ext (Z_to_bv 64 m2) (Z_to_bv 64 (mt_mem mt2)) (Z_to_bv 64 aib2) ;; K x) s1) P.
  Proof.
    intros K P HK. pose proof (ii_is HII) as HI. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof (repw_init B (ms_mem s1) HW HR) as RW0. ceil. pose proof (envok_rodata _ _ _ _ HE) as HRO.
    destruct (ring_member B sc m2 HW Hsc ltac:(rewrite Hact; left; reflexivity)) as (mt' & aibx & slx & Hm' & Hr' & Hs2 & Hw32 & Hfrr & Hc32 & Haib & Haibl & Mlo & Mhi & Hmem0 & Hmem1).
    rewrite Hm2 in Hm'. injection Hm' as <-. rewrite Hr2 in Hr'. injection Hr' as <- <-.
    destruct (partial_of_masks B m2 mt2 aib2 sl2 HW Hm2 Hr2 Hfr Hlow) as (Hpart & Hsc7 & Hnzc).
    pose proof (Z.mod_pos_bound aib2 32 ltac:(lia)) as Hk. set (a := aib2 mod 32) in *.
    pose proof (w_last_range (mt_w32 mt2)) as Hl. change (w_last (mt_w32 mt2)) with (mt_last mt2) in Hl.
    unfold tv_ext. cbv zeta.
    (* [comment removed for export] *)
    apply ts_assoc. rewrite at_Z. change (m2 + 32) with (m2 + moff FW32).
    eapply (ts_ld_metaW B HW s1 (ms_mem s1) [] m2 mt2 FW32); [exact RW0 | exact HWIN | exact Hm2 | reflexivity | apply wfree_range_nil | change (mt_f mt2 FW32) with (mt_w32 mt2); llia |].
    change (mt_f mt2 FW32) with (mt_w32 mt2).
    (* [comment removed for export] *)
    apply ts_assoc.
    assert (H5 : 0 <= mt_w32 mt2 / 2^5 < 2^64) by (split; [apply Z.div_pos; llia | apply Z.div_lt_upper_bound; llia]).
    rewrite (v_srli_Z (mt_w32 mt2) 5) by llia. rewrite (v_andi_Z (mt_w32 mt2 / 2^5) 126) by llia. change (2^5) with 32. rewrite (sc_index (mt_w32 mt2)) by llia.
    change ((mt_w32 mt2 / 64) mod 64) with (mt_sc mt2). rewrite Hs2.
    rewrite A_SIZE_CLASSES_eq, v_add_Z.
    eapply ts_lhu_size_class; [exact HRO | exact HWIN | llia |].
    pose proof (size_class_bound sc Hsc) as Hszc.
    (* [comment removed for export] *)
    rewrite (v_andi_Z aib2 31) by llia. rewrite (land_31 aib2) by llia. fold a.
    rewrite span_run_zeta. destruct (span_ok sc a ltac:(llia) ltac:(llia)) as [-> Hcnt]. set (c := span_cnt a sc) in *. cbv beta iota.
    (* [comment removed for export] *)
    rewrite (wlast_eq mt2) by llia. rewrite (v_addi_Z (mt_last mt2) 1). rewrite (c_ltu_Z c (mt_last mt2 + 1)) by llia.
    set (c' := Z.min c (mt_last mt2 + 1)).
    replace (if c <? mt_last mt2 + 1 then Z_to_bv 64 c else Z_to_bv 64 (mt_last mt2 + 1)) with (Z_to_bv 64 c')
      by (subst c'; destruct (Z.ltb_spec c (mt_last mt2 + 1)); f_equal; lia).
    assert (Hc' : a + 2 <= c' <= mt_last mt2 + 1) by (subst c'; lia).
    rewrite (v_addi_Z c' (-1)). rewrite (v_andi_Z (c' + -1) 31) by llia. rewrite (land_31 (c' + -1)) by llia. rewrite (Z.mod_small (c' + -1) 32) by llia.
    assert (Hl224 : 0 <= Z.land aib2 224 <= aib2) by (split; [apply Z.land_nonneg; lia | apply land_le_left; lia]).
    rewrite (v_andi_Z aib2 224) by llia. rewrite (v_or_Z (c' + -1) (Z.land aib2 224)) by llia.
    destruct (aib_byte_facts (c' + -1) aib2 ltac:(llia) ltac:(llia)) as [Hab Habm]. set (aib' := Z.lor (c' + -1) (Z.land aib2 224)) in *.
    (* [comment removed for export] *)
    apply ts_assoc. rewrite at_Z. unfold m_sb at 1.
    eapply (ts_st_domW B HW s1 (ms_mem s1) [] 1 (mt_mem mt2 + 8)); [exact RW0 | exact HWIN | lia | intros j Hj; rewrite <- Z.add_assoc; apply (hdr_dom B HW m2 mt2 aib2 sl2 Hm2 Hr2); lia |].
    intros mm RW1. rewrite uZ in RW1 by llia. change (Z.of_nat 1) with 1 in RW1. cbn [ms_vm upd].
    (* [comment removed for export] *)
    pose proof (WF_xaA B HW sc m2 rest mt2 aib2 sl2 Hsc Hact Hm2 Hr2 Hav0 aib' Hab ltac:(llia) ltac:(llia)) as HW'.
    pose proof (xaA_commit B HW sc m2 rest mt2 aib2 sl2 Hsc Hact Hm2 Hr2 Hav0 aib' Hab ltac:(llia) ltac:(llia) (ms_mem s1) mm RW1) as HR'.
    pose proof (writes_ok_aib B HW m2 mt2 aib2 sl2 Hm2 Hr2 [] aib' (writes_ok_nil B)) as WO.
    set (B' := xaA B m2 mt2 sl2 aib') in *.
    apply ts_bind_ret. apply (HK (upd s1 mm (ms_vm s1)) aib').
    - apply II_intro.
      + exact (IS_commit sp0 argv envp cb B B' s1 _ mm HI RW1 WO HW' HR').
      + cbn [ms_vm upd]. apply (VMok_xaA B m2 mt2 aib2 sl2 Hm2 Hr2 aib'). exact (ii_vm HII).
      + apply (AvOK_transfer B B' (ii_av HII)); try reflexivity. intros x mt' Hx Hrl.
        destruct (xaA_meta_inv B m2 mt2 sl2 aib' x mt' Hx) as [(-> & ->) | (Hne & Hx')]; [cbn in Hrl; discriminate | exists mt'; auto].
      + apply (UsOK_transfer B B' (ii_us HII)); [reflexivity | intros; reflexivity | intros cc x; apply (meta_usage_xaA B m2 mt2 aib2 sl2 Hm2 Hr2 aib')].
      + apply (deads_transfer B B' D (ii_dd HII)). intros x. split.
        * intros (mt' & Hx & Hrl). destruct (xaA_meta_inv B m2 mt2 sl2 aib' x mt' Hx) as [(-> & ->) | (Hne & Hx')]; [cbn in Hrl; discriminate | exists mt'; auto].
        * intros (mt0 & Hx & Hrl). exists mt0. destruct (Z.eq_dec x m2) as [-> | Hne].
          -- rewrite Hm2 in Hx. injection Hx as <-. rewrite Hr2 in Hrl. discriminate.
          -- unfold B'. rewrite (xaA_meta_other B m2 mt2 sl2 aib' x Hne). auto.
    - exact (ntframe_commit B s1 _ mm HW RW1 WO).
    - exact (tavrel_xaA B sc m2 mt2 aib2 sl2 Hsc Hm2 Hr2 aib' Hab).
    - exact Hab.
    - rewrite Habm. llia.
    - rewrite Habm. apply Hnzc. llia.
  Qed.
End TavExt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ts_tv_act : forall {R : Type} sp0 argv envp cb D B s1 sc m2 rest mt2 aib2 sl2 (K : option (word * word) -> M R) (P : R -> mstate -> Prop),
  II sp0 argv envp cb D B s1 -> 0 <= sc < 48 -> a_active B sc = m2 :: rest -> a_meta B m2 = Some mt2 -> mt_role mt2 = RGroup aib2 sl2 ->
  mt_avail mt2 = 0 -> mt_freed mt2 mod 2 ^ (aib2 mod 32 + 1) <> 0 ->
  (forall s' Bf, II sp0 argv envp cb D Bf s' -> ntframe B s1 s' -> tavrel B Bf sc ->
     a_active Bf sc = m2 :: rest -> a_meta Bf m2 = Some (ac_mt mt2 aib2 sl2) ->
     tsafe (K (Some (Z_to_bv 64 m2, w32 (ac_av mt2 aib2))) s') P) ->
  tsafe ((x <- tv_act (Z_to_bv 64 m2) ;; K x) s1) P.
Proof.
  intros R sp0 argv envp cb D B s1 sc m2 rest mt2 aib2 sl2 K P HII Hsc Hact Hm2 Hr2 Hav0 Hnz HK. unfold tv_act.
  exact (ts_tav_activate sp0 argv envp cb D B s1 HII sc m2 rest mt2 aib2 sl2 Hsc Hact Hm2 Hr2 Hav0 Hnz K P HK).
Qed.

End WithLayout.

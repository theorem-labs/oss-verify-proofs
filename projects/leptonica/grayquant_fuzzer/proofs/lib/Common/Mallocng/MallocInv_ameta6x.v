(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocInv_defs MallocInv_heap MallocInv_word
  MallocInv_sep MallocInv_wf MallocInv_wf3 MallocInv_wf4 MallocInv_dll MallocInv_tables MallocInv_steps MallocInv_repw
  MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_vmops MallocInv_auxv
  MallocInv_ameta_base MallocInv_ameta_iface MallocInv_ameta1 MallocInv_ameta2 MallocInv_ameta3
  MallocInv_budget MallocInv_ameta4 MallocInv_ameta5 MallocInv_ametax_iface MallocInv_ameta5x MallocSureLedger.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition am_mmap : M (option (word * bool)) :=
  sh <- m_ld A_META_SHIFT ;;
  let n := v_sll (wlit 2) sh in
  p <- sys_mmap MMnone (v_mul n PZ) ;;
  if c_eq p wm1 then mret None
  else sh2 <- m_ld A_META_SHIFT ;;
       m_sd A_AVAIL_AREA_CNT (v_mul (v_addi n (-1)) (v_srli PZ 12)) ;;
       m_sd A_META_SHIFT (v_addi sh2 1) ;;
       m_sd A_AVAIL_AREAS (v_add p PZ) ;;
       mret (Some (v_add p PZ, true)).

Definition am_brk (cb : word) : M (option (word * bool)) :=
  if c_eq cb wm1 then mret None
  else if negb (is0 cb)
  then let new := v_add cb PZ in
       r <- sys_brk_grow new ;;
       mret (Some (new, c_eq r new))
  else r0 <- sys_brk_query ;;
       let al := v_add (v_and (v_addi PZ (-1)) (v_sub w0 r0)) r0 in
       m_sd A_BRK al ;;
       let new := v_add al (v_slli PZ 1) in
       r <- sys_brk_grow new ;;
       (if c_eq r new
        then b <- m_ld A_BRK ;;
             g <- sys_mmap_fixed_none b PZ ;;
             mret (Some (new, true))
        else mret (Some (new, false))).

Definition am_after (aac : word) (br : option (word * bool)) : M (option (word * bool)) :=
  match br with
  | Some (new, true) =>
      m_sd A_BRK new ;;
      m_sd A_AVAIL_AREA_CNT (v_srli PZ 12) ;;
      mret (Some (v_sub new PZ, false))
  | _ =>
      aac2 <- (match br with
               | Some _ => a <- m_ld A_AVAIL_AREA_CNT ;; m_sd A_BRK wm1 ;; mret a
               | None => mret aac end) ;;
      if negb (is0 aac2) then p <- m_ld A_AVAIL_AREAS ;; mret (Some (p, true))
      else am_mmap
  end.

Definition am_prov (aac : word) : M (option (word * bool)) :=
  if negb (is0 aac)
  then p <- m_ld A_AVAIL_AREAS ;; mret (Some (p, true))
  else cb <- m_ld A_BRK ;;
       br <- am_brk cb ;;
       am_after aac br.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma heap_page_not_ctx : forall p k x, heap_range p (p + 4096) -> cvalid k -> clen k = 8 ->
  p <= x < p + 4096 -> caddr k <= x < caddr k + 8 -> False.
Proof.
  intros p k x Hh Hk Hl Hx Hc. pose proof (heap_avoids_ctx p (p + 4096) Hh k Hk) as X. rewrite Hl in X. lia.
Qed.

(* [comment removed for export] *)
Lemma FR_ctxwrites : forall A A' s (m' : word -> option byte) h',
  WF A -> (forall x, dom A' x <-> dom A x) -> a_live A' = a_live A ->
  vm_limit h' = vm_limit (ms_vm s) ->
  (forall a : word, m' a = ms_mem s a \/ LOCKA <= bv_unsigned a < CTX_END) ->
  (forall a : word, ms_mem s a <> None -> m' a <> None) ->
  FR A s A' (upd s m' h').
Proof using MLok. pu_keep (MLok).
  intros A A' s m' h' HW Hd Hl Hlim Hm Hk. constructor; cbn; auto.
  - intros x [Hc | Hx]; [left; exact Hc | right; apply (proj2 (Hd x)); exact Hx].
  - intros a Ho He. destruct (Hm a) as [E | Hc]; [exact E | exfalso]. apply Ho. left. exact Hc.
  - intros p n. rewrite Hl. exact (fun H => H).
  - intros p n a Hp Ha. destruct (Hm a) as [E | Hc]; [exact E | exfalso].
    destruct (live_heap A p n HW Hp) as (Hn & H1 & H2 & H3 & _). pose proof (MallocInv_live.round16_ge n).
    unfold LOCKA, CTX_END in Hc. ceil. llia.
Qed.

(* [comment removed for export] *)
Lemma shift_block : forall sh, 0 <= sh < 48 ->
  2 <= 2 * 2 ^ sh /\ 2 * 2 ^ sh * 4096 = 2 ^ (sh + 13) /\ 8192 <= 2 ^ (sh + 13) <= 2 ^ 60 /\ 2 * 2 ^ sh = 2 ^ (sh + 1).
Proof using Type. pu_keep tt.
  intros sh Hsh.
  assert (E1 : 2 * 2 ^ sh = 2 ^ (sh + 1)) by (rewrite Z.pow_add_r, Z.pow_1_r by lia; lia).
  assert (E2 : 2 * 2 ^ sh * 4096 = 2 ^ (sh + 13)).
  { replace (sh + 13) with (sh + 1 + 12) by lia. rewrite (Z.pow_add_r 2 (sh + 1) 12) by lia. rewrite <- E1. change (2 ^ 12) with 4096. lia. }
  assert (L1 : 2 ^ 13 <= 2 ^ (sh + 13)) by (apply Z.pow_le_mono_r; lia).
  assert (L2 : 2 ^ (sh + 13) <= 2 ^ 60) by (apply Z.pow_le_mono_r; lia).
  assert (L3 : 2 ^ 0 <= 2 ^ sh) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 13) with 8192 in L1. change (2 ^ 0) with 1 in L3. lia.
Qed.

(* [comment removed for export] *)
Lemma nafree_of_apart : forall A h lo n, VMcore A h -> 0 < lo -> 0 < n -> lo + n <= 2^64 ->
  (forall b sz, In (b, sz) (vm_maps h) -> lo + n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned sz <= lo) ->
  region_free (vm_noaccess h) (Z_to_bv 64 lo) (Z_to_bv 64 n) = true.
Proof using Type. pu_keep tt.
  intros A h lo n HV Hlo Hn Hnw Hap. apply (proj2 (region_free_spec _ _ _)). intros b' sz' Hin.
  rewrite !uZ by lia.
  destruct (vc_na_in A h HV b' sz' Hin) as [Hsz (b & sz & HinB & H1 & H2)].
  destruct (Hap b sz HinB); lia.
Qed.

Lemma VMok_upd_brk_neg1 : forall A h, VMok A h -> VMok (actx_upd A KBrk (2^64 - 1)) h.
Proof using Type. pu_keep tt.
  intros A h HV. unfold actx_upd. apply VMok_set_ctx; [exact HV | | |].
  - right; left. apply cupd_same.
  - rewrite !cupd_other by discriminate. exact (vm_areas_res A h HV).
  - rewrite cupd_same. intros H. exfalso. lia.
Qed.

Lemma is0_false : forall z, 0 < z < 2^64 -> is0 (Z_to_bv 64 z) = false.
Proof using Type. pu_keep tt. intros z Hz. rewrite is0_Z by lia. apply Z.eqb_neq. lia. Qed.
Lemma is0_true : is0 (Z_to_bv 64 0) = true.
Proof using Type. pu_keep tt. reflexivity. Qed.

Lemma errno_mem_other : forall m e (a : word), ~ (ERRNO <= bv_unsigned a < ERRNO + 4) -> errno_mem m e a = m a.
Proof using HT MLok. pu_keep (HT, MLok).
  intros m e a Ha. unfold errno_mem. rewrite A_ERRNO_eq. pose proof layout_nums.
  apply wbytes_other_Z; rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold ERRNO in *; try llia.
Qed.

Lemma errno_mem_keeps : forall m e (a : word), m a <> None -> errno_mem m e a <> None.
Proof using HT MLok. pu_keep (HT, MLok).
  intros m e a Ha. unfold errno_mem. pose proof layout_nums. apply wbytes_keeps; [| exact Ha].
  rewrite length_N_to_le_bytes. cbn. llia.
Qed.

Lemma gsame_apA : forall A pg, gsame A (apA A pg).
Proof using Type. pu_keep tt. intros A pg. constructor; cbn; auto. Qed.

Section Tools2.
  Context {R : Type}.
  Variable W : wmode.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte).
  Implicit Types (s : mstate) (P : R -> mstate -> Prop).

  Lemma tw_sd_ctx1 : forall A s ck (v : word) (k : unit -> M R) P,
    IS sp0 argv envp cb A s -> cvalid ck -> ck <> KSecret -> clen ck = 8 ->
    WF (actx_upd A ck (u v)) ->
    (forall s', IS sp0 argv envp cb (actx_upd A ck (u v)) s' -> FR A s (actx_upd A ck (u v)) s' -> ms_vm s' = ms_vm s ->
       (forall a : word, ms_mem s' a = ms_mem s a \/ caddr ck <= u a < caddr ck + 8) ->
       tsall W (k tt s') P) ->
    tsall W ((x <- m_sd (Z_to_bv 64 (caddr ck)) v ;; k x) s) P.
  Proof using MLok. pu_keep (MLok).
    intros A s ck v k P HI Hk Hks Hlen HW' Hk'.
    eapply (tw_lift W (m_sd (Z_to_bv 64 (caddr ck)) v) s
              (fun _ s' => IS sp0 argv envp cb (actx_upd A ck (u v)) s' /\ FR A s (actx_upd A ck (u v)) s' /\ ms_vm s' = ms_vm s /\
                           (forall a : word, ms_mem s' a = ms_mem s a \/ caddr ck <= u a < caddr ck + 8))).
    - intros K' P' HK'. eapply (ts_sd_ctx1 sp0 argv envp cb A s ck v); try assumption.
      intros s' H1 H2 H3 H4. apply HK'. auto.
    - intros [] s' (H1 & H2 & H3 & H4). apply Hk'; assumption.
  Qed.
End Tools2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Prov.
  Variable W : wmode.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A0 : astate) (s0 : mstate).

  Local Notation FailPost := (FailPostX W sp0 argv envp cb D A0 s0).
  Local Notation PreT := (PreTX W sp0 argv envp cb D A0 s0).
  Local Notation PreF := (PreFX W sp0 argv envp cb D A0 s0).
  Local Notation BodyPost := (BodyPostX W sp0 argv envp cb D A0 s0).
  Local Notation apart0 := (apart0X s0).

  Definition ProvPost (r : option (word * bool)) (s' : mstate) : Prop :=
    match r with
    | None => FailPost s'
    | Some (pw, true) => exists k A p, pw = Z_to_bv 64 p /\ PreT k A s' p
    | Some (pw, false) => exists k A p, pw = Z_to_bv 64 p /\ PreF k A s' p
    end.

  Lemma tail_ok : forall r s, ProvPost r s -> tsall W (am_tail r s) BodyPost.
  Proof using MLok. pu_keep (MLok).
    intros [[pw [|]]|] s HP; cbn [ProvPost] in HP.
    - destruct HP as (k & A & p & -> & PT). exact (tailT_okX W sp0 argv envp cb D A0 s0 k A s p PT).
    - destruct HP as (k & A & p & -> & PF). exact (tailF_okX W sp0 argv envp cb D A0 s0 k A s p PF).
    - apply tw_ret'. left. split; [reflexivity | exact HP].
  Qed.

  (* [comment removed for export] *)
  Record PreS (k : Z) (A : astate) (s : mstate) (p : Z) : Prop := {
    ps_is : IS sp0 argv envp cb A s;
    ps_vc : VMcore A (ms_vm s);
    ps_va : VMall A (ms_vm s);
    ps_av : AvOK A;
    ps_us : UsOK A;
    ps_dd : deads A D;
    ps_frh : FRH (fun x => p <= x < p + 4096) A0 s0 A s;
    ps_gs : gsame A0 A;
    ps_areas : a_areas A = a_areas A0;
    ps_amk : AMK k A0 A s0 s;
    ps_k : 0 <= k <= 12288;
    ps_spare0 : spare A0 = 0;
    ps_init : a_ctx A KInit = 1;
    ps_amc : a_ctx A KAmc = 0;
    ps_fl : a_freelist A = [];
    ps_brk : a_ctx A KBrk <> 0;
    ps_aac : a_ctx A KAac = 0;
    ps_al : page_aligned p;
    ps_heap : heap_range p (p + 4096);
    ps_pdom : forall x, p <= x < p + 4096 -> ~ dom A x;
    ps_zero : forall x, p <= x < p + 4096 -> ms_mem s (Z_to_bv 64 x) = Some (Z_to_bv 8 0);
    ps_cov : mcov (vm_maps (ms_vm s)) p 4096;
    ps_nafree : region_free (vm_noaccess (ms_vm s)) (Z_to_bv 64 p) (Z_to_bv 64 4096) = true;
    ps_brkv : u (vm_brk (ms_vm s)) = p + 4096 /\ u (vm_start_brk (ms_vm s)) <= u (vm_brk (ms_vm s));
    ps_span : u (vm_brk (ms_vm s)) - u (vm_start_brk (ms_vm s)) <= 4096 * (Z.of_nat (length (a_areas A)) + 2);
    ps_apart : apart0 p;
    ps_xm : a_xmaps A = a_xmaps A0;
    ps_nok : W = WOk -> False;
    ps_grow : am_grow (ms_vm s0) (ms_vm s) (* [comment removed for export] *) }.

  Lemma after_true_ok : forall k A s p (aacw : word), PreS k A s p ->
    tsall W (am_after aacw (Some (Z_to_bv 64 (p + 4096), true)) s) ProvPost.
  Proof using MLok. pu_keep (MLok).
    intros k A s p aacw PS. destruct PS. pose proof ps_is0 as [HW HR HC HWIN HE HG]. ceil.
    pose proof ps_heap0 as (Hp1 & Hp2 & Hp3 & Hp4). destruct ps_brkv0 as [Eb Hsb].
    cbn [am_after]. rewrite A_BRK_eq.
    eapply (tw_sd_ctx1 W sp0 argv envp cb A); [exact ps_is0 | exact I | discriminate | reflexivity | |].
    { rewrite uZ by lia. apply WF_upd_brk; [exact HW | exact ps_init0 | lia | lia]. }
    intros s1 HI1 HF1 Hvm1 Hm1. rewrite uZ in * by lia.
    set (A1 := actx_upd A KBrk (p + 4096)) in *.
    pose proof (is_wf _ _ _ _ _ _ HI1) as HW1.
    rewrite A_AVAIL_AREA_CNT_eq. unfold PZ at 1. unfold wlit. rewrite v_srli_Z by lia. change (4096 / 2 ^ 12) with 1.
    eapply (tw_sd_ctx1 W sp0 argv envp cb A1); [exact HI1 | exact I | discriminate | reflexivity | |].
    { rewrite uZ by lia. apply WF_upd_aac1; [exact HW1 | reflexivity || exact ps_init0 | | exact ps_aac0].
      unfold A1, actx_upd, set_ctx. cbn [a_ctx]. rewrite cupd_same. lia. }
    intros s2 HI2 HF2 Hvm2 Hm2. rewrite uZ in * by lia.
    set (A2 := actx_upd A1 KAac 1) in *.
    apply tw_ret'. cbn [ProvPost]. exists k, A2, p.
    unfold PZ, wlit. rewrite v_sub_Z. replace (p + 4096 - 4096) with p by lia. split; [reflexivity|].
    assert (Hdom2 : forall x, dom A2 x <-> dom A x) by (intros x; reflexivity).
    assert (HG2 : gsame A A2).
    { constructor; try reflexivity; try (intros; assumption). intros kk Hk Hv. unfold A2, A1, actx_upd, set_ctx. cbn [a_ctx].
      rewrite !cupd_other by (destruct kk; cbn in Hk; try contradiction; discriminate). reflexivity. }
    pose proof (ctx_slot_range KBrk I) as (C1 & C2 & C3). pose proof (ctx_slot_range KAac I) as (C4 & C5 & C6).
    assert (MEM : forall a : word, p <= u a < p + 4096 -> ms_mem s2 a = ms_mem s a).
    { intros a Ha.
      destruct (Hm2 a) as [-> | X]; [| exfalso; exact (heap_page_not_ctx p KAac (u a) ps_heap0 I eq_refl Ha X)].
      destruct (Hm1 a) as [-> | X]; [reflexivity | exfalso; exact (heap_page_not_ctx p KBrk (u a) ps_heap0 I eq_refl Ha X)]. }
    constructor.
    - exact HI2.
    - rewrite Hvm2, Hvm1. apply (VMcore_same A A2 _ ps_vc0); [intros ma mt aib sl Hma _; exact Hma | reflexivity | reflexivity].
    - rewrite Hvm2, Hvm1. apply VMall_actx_upd. apply VMall_actx_upd. exact ps_va0.
    - intros ma mt Hma Hr. exact (ps_av0 ma mt Hma Hr).
    - apply (UsOK_transport A A2 HG2); [reflexivity | exact ps_us0].
    - intros x. exact (ps_dd0 x).
    - apply (FRH_FR _ A0 s0 A s); [exact ps_frh0|]. apply (FR_trans A s A1 s1); assumption.
    - exact (gsame_trans _ _ _ ps_gs0 HG2).
    - cbn [a_areas A2 A1 actx_upd set_ctx]. exact ps_areas0.
    - apply (AMK_weaken (k + 0)); [| lia]. apply (AMK_trans k 0 A0 A A2 s0 s); [exact ps_amk0 | | exact ps_areas0].
      apply AMK_vm; [rewrite Hvm2, Hvm1; reflexivity | intros x Hx; exact Hx | lia].
    - exact ps_k0.
    - exact ps_spare1.
    - unfold A2, A1, actx_upd, set_ctx. cbn [a_ctx]. rewrite !cupd_other by discriminate. exact ps_init0.
    - unfold A2, A1, actx_upd, set_ctx. cbn [a_ctx]. rewrite !cupd_other by discriminate. exact ps_amc0.
    - cbn [a_freelist A2 A1 actx_upd set_ctx]. exact ps_fl0.
    - unfold A2, A1, actx_upd, set_ctx. cbn [a_ctx]. rewrite cupd_other by discriminate. rewrite cupd_same. lia.
    - unfold A2, A1, actx_upd, set_ctx. cbn [a_ctx]. rewrite cupd_same. reflexivity.
    - exact ps_al0.
    - exact ps_heap0.
    - intros x Hx. exact (ps_pdom0 x Hx).
    - intros x Hx. pose proof Hx as Hx'. rewrite <- (uZ x) in Hx' by lia. rewrite (MEM _ Hx'). exact (ps_zero0 x Hx).
    - rewrite Hvm2, Hvm1. exact ps_cov0.
    - rewrite Hvm2, Hvm1. exact ps_nafree0.
    - rewrite Hvm2, Hvm1. unfold A2, A1, actx_upd, set_ctx. cbn [a_ctx]. rewrite cupd_other by discriminate. rewrite cupd_same.
      destruct (vc_brk_valid A _ ps_vc0) as (K1 & K2 & K3 & K4). auto.
    - rewrite Hvm2, Hvm1. cbn [a_areas A2 A1 actx_upd set_ctx]. exact ps_span0.
    - exact ps_apart0.
    - etransitivity; [| exact ps_xm0]. reflexivity.
    - exact ps_nok0.
    - rewrite Hvm2, Hvm1. exact ps_grow0.
  Qed.
  (* [comment removed for export] *)
  Record PreM (A : astate) (s : mstate) : Prop := {
    pm_ii : II sp0 argv envp cb D A s;
    pm_fr : FR A0 s0 A s;
    pm_gs : gsame A0 A;
    pm_areas : a_areas A = a_areas A0;
    pm_dom : forall x, dom A x -> dom A0 x;
    pm_vm : ms_vm s = ms_vm s0;
    pm_spare0 : spare A0 = 0;
    pm_init : a_ctx A KInit = 1;
    pm_amc : a_ctx A KAmc = 0;
    pm_fl : a_freelist A = [];
    pm_aac : a_ctx A KAac = 0;
    pm_aacA0 : a_ctx A0 KAac = 0;
    pm_xm : a_xmaps A = a_xmaps A0;
    pm_dom2 : forall x, dom A x <-> dom A0 x;
    pm_shift : a_ctx A KShift = a_ctx A0 KShift (* [comment removed for export] *) }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem mm_ok : forall A s, PreM A s -> a_ctx A KBrk = 2^64 - 1 -> tsall W (am_mmap s) ProvPost.
  Proof using MLok. pu_keep (MLok).
    intros A s PM Hbrk. destruct PM as [HII HFR HGS Hareas Hdom Hvm Hsp0 Hinit Hamc Hfl Haac HaacA0 Hxm Hdom2 Hshift].
    pose proof HII as [HI HVo HAV HUS HD]. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof (VMok_core A _ HVo) as HVc. ceil.
    pose proof (wf_shift A HW) as Hsh48. pose proof (wf_ctx_nonneg A HW KShift) as Hsh0.
    set (sh := a_ctx A KShift) in *.
    destruct (shift_block sh ltac:(lia)) as (SB1 & SB2 & SB3 & SB4).
    set (L := 2 ^ (sh + 13)) in *.
    unfold am_mmap. rewrite A_META_SHIFT_eq.
    eapply (tw_ld_ctx W A); [exact HW | exact HR | exact HWIN | exact I | reflexivity | fold sh; lia |]. fold sh.
    cbv beta zeta. unfold wlit. rewrite (v_sll_Z 2 sh) by lia. unfold PZ at 1. unfold wlit. rewrite v_mul_Z. rewrite SB2. fold L.
    assert (HLu : u (Z_to_bv 64 L) = L) by (apply uZ; lia).
    assert (HprZ : page_round_up_Z L = L).
    { apply page_round_up_Z_aligned; [lia|]. unfold L, page_size. replace (sh + 13) with (sh + 1 + 12) by lia.
      rewrite Z.pow_add_r by lia. change (2 ^ 12) with 4096. apply Z_mod_mult. }
    assert (Hpr : page_round_up (Z_to_bv 64 L) = Z_to_bv 64 L) by (unfold page_round_up; rewrite HLu, HprZ; reflexivity).
    eapply tw_sys_mmap04; [rewrite HLu; lia | rewrite HLu; lia | |].
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      intros Hnone. assert (HWf : W <> WOk \/ forall a0, mmap_grant_ok MMnone (ms_vm s) a0 (mm_len (Z_to_bv 64 L)) = false) by (right; exact Hnone).
      eapply tw_set_errno; [exact HWIN|]. cbv beta.
      unfold MAP_FAILED at 1. rewrite wm1_eq, c_eq_Z by lia. rewrite Z.eqb_refl.
      apply tw_ret'. cbn [ProvPost]. exists A.
      split.
      { (* [comment removed for export] *)
        split; [cbn [ms_vm upd]; rewrite Hvm; apply am_grow_refl|].
        intros _ Hroom. destruct Hroom as [Hsp | [_ [Hpos | [a0 Ha0]]]]; [lia | lia |].
        specialize (Hnone a0). unfold mm_len in Hnone. rewrite HLu, HprZ in Hnone. cbn [mmap_grant_ok] in Hnone.
        assert (EL : L = 2 ^ (a_ctx A0 KShift + 13)) by (rewrite <- Hshift; reflexivity).
        rewrite Hvm, EL in Hnone. rewrite Ha0 in Hnone. discriminate Hnone. }
      split; [apply II_errno; exact HII|]. split; [| split; [exact HGS | split; [| split; [exact Hsp0 | split; [exact Hareas | split; [| split; [exact Hxm | exact Hdom2]]]]]]].
      + apply (FR_trans A0 s0 A s); [exact HFR | apply FR_errno; exact HW].
      + apply (AMvm_of_AMK 0); [| lia]. apply AMK_vm; [cbn; exact Hvm | intros x Hx; exact (Hdom x Hx) | lia].
      + intros HWk Hb. destruct HWf as [HWf | Hall]; [exact (HWf HWk)|].
        destruct Hb as [Hsp | [_ [Hpos | [Har [a Ha]]]]]; [lia | lia |].
        assert (Hsh : sh = 0) by (unfold sh; apply (wf_noarea_shift A HW); [rewrite Hareas; exact Har | exact Haac]).
        specialize (Hall a). unfold mm_len in Hall. rewrite HLu, HprZ in Hall. cbn [mmap_grant_ok] in Hall. rewrite Hvm in Hall.
        unfold L in Hall. rewrite Hsh in Hall. change (2 ^ (0 + 13)) with 8192 in Hall. rewrite Ha in Hall. discriminate Hall.
    - (* [comment removed for export] *)
      intros HWs a Hg. cbn [mmap_grant_ok] in Hg. unfold mm_len in Hg. rewrite HLu in Hg.
      destruct (mmap_none_facts sp0 argv envp cb A s a (Z_to_bv 64 L) HI HVc ltac:(rewrite HLu; lia) ltac:(rewrite HLu; lia) ltac:(rewrite HLu; exact Hg))
        as (EnZ & _ & G1 & Glo & Gce & Gimg & Gm & Gna & Gdom & Gdisj).
      destruct (mmap_none_state sp0 argv envp cb A s a (Z_to_bv 64 L) HI HVc ltac:(rewrite HLu; lia) ltac:(rewrite HLu; lia) ltac:(rewrite HLu; exact Hg))
        as (HI1 & HVc1 & SAME).
      rewrite HLu, HprZ in *. rewrite Hpr in *.
      set (n := Z_to_bv 64 L) in *. set (s1 := upd s (unfill a n (ms_mem s)) (vm_noacc a n (ms_vm s))) in *.
      pose proof (u64_range a) as Ha.
      cbv beta. rewrite wm1_eq. rewrite <- (Z_to_bv_bv_unsigned 64 a). rewrite c_eq_Z by lia.
      replace (u a =? 2 ^ 64 - 1) with false by (symmetry; apply Z.eqb_neq; lia).
      pose proof HI1 as [_ HR1 HC1 HWIN1 HE1 HG1].
      eapply (tw_ld_ctx W A); [exact HW | exact HR1 | exact HWIN1 | exact I | reflexivity | fold sh; lia |]. fold sh.
      (* [comment removed for export] *)
      apply tsall_of_tsafe.
      unfold PZ, wlit. rewrite !v_addi_Z. rewrite v_srli_Z by lia. change (4096 / 2 ^ 12) with 1. rewrite v_mul_Z, Z.mul_1_r. rewrite !v_add_Z.
      pose proof (repw_init A _ HW HR1) as RW0. replace (2 * 2 ^ sh + -1) with (2 * 2 ^ sh - 1) by lia.
      rewrite A_AVAIL_AREA_CNT_eq. unfold m_sd at 1.
      eapply (ts_st_ctxw A s1 (ms_mem s1) []); [exact RW0 | exact HWIN1 | exact I |].
      pose proof (repw_st_ctx A s1 (ms_mem s1) [] KAac (Z_to_bv 64 (2 * 2 ^ sh - 1)) RW0 I) as RW1.
      set (m1 := wbytes (ms_mem s1) (Z_to_bv 64 (caddr KAac)) (word_to_le_bytes (Z.to_nat (clen KAac)) (Z_to_bv 64 (2 * 2 ^ sh - 1)))) in RW1 |- *.
      cbn [ms_mem ms_vm upd].
      unfold m_sd at 1.
      eapply (ts_st_ctxw A (upd s1 m1 (ms_vm s1)) (ms_mem s1)); [exact RW1 | apply WIN_upd; exact HWIN1 | exact I |]. cbn [ms_mem ms_vm upd].
      pose proof (repw_st_ctx A (upd s1 m1 (ms_vm s1)) (ms_mem s1) _ KShift (Z_to_bv 64 (sh + 1)) RW1 I) as RW2. cbn [ms_mem upd] in RW2.
      set (m2 := wbytes m1 (Z_to_bv 64 (caddr KShift)) (word_to_le_bytes (Z.to_nat (clen KShift)) (Z_to_bv 64 (sh + 1)))) in RW2 |- *.
      rewrite A_AVAIL_AREAS_eq. unfold m_sd at 1.
      eapply (ts_st_ctxw A (upd s1 m2 (ms_vm s1)) (ms_mem s1)); [exact RW2 | apply WIN_upd; exact HWIN1 | exact I |]. cbn [ms_mem ms_vm upd].
      pose proof (repw_st_ctx A (upd s1 m2 (ms_vm s1)) (ms_mem s1) _ KAareas (Z_to_bv 64 (u a + 4096)) RW2 I) as RW3. cbn [ms_mem upd] in RW3.
      set (m3 := wbytes m2 (Z_to_bv 64 (caddr KAareas)) (word_to_le_bytes (Z.to_nat (clen KAareas)) (Z_to_bv 64 (u a + 4096)))) in RW3 |- *.
      rewrite !uZ in RW3 by lia.
      apply ts_ret. cbn [ProvPost].
      (* [comment removed for export] *)
      assert (HshE : a_ctx A KShift = sh) by reflexivity.
      exists 8192, (mbA A (u a) L sh), (u a + 4096). split; [reflexivity|].
      pose proof (WF_mbA A HW (u a) L sh HshE Haac Hinit ltac:(rewrite Hbrk; lia) Glo eq_refl Gce) as HW3.
      pose proof (mb_l A HW (u a) L sh HshE Glo eq_refl Gce) as (ML1 & ML2 & ML3).
      assert (HR3 : Rep (mbA A (u a) L sh) m3).
      { apply (Rep_mbA A HW (u a) L sh HshE Glo eq_refl Gce (ms_mem s1) m3). unfold mb_n. rewrite <- SB4. exact RW3. }
      pose proof (ctx_slot_range KAac I) as (C1 & C2 & _). pose proof (ctx_slot_range KShift I) as (C3 & C4 & _). pose proof (ctx_slot_range KAareas I) as (C5 & C6 & _).
      cbn [clen] in C2, C4, C6.
      assert (FRM : forall x : word, m3 x = ms_mem s1 x \/ LOCKA + 8 <= u x < CTX_END).
      { intros x. pose proof (u64_range x).
        assert (DQrng : (caddr KAac) <= (u x) < (caddr KAac + 8) \/ (caddr KShift) <= (u x) < (caddr KShift + 8) \/ (caddr KAareas) <= (u x) < (caddr KAareas + 8) \/
                       (~ ((caddr KAac) <= (u x) < (caddr KAac + 8)) /\ ~ ((caddr KShift) <= (u x) < (caddr KShift + 8)) /\ ~ ((caddr KAareas) <= (u x) < (caddr KAareas + 8)))) by lia.
        destruct DQrng as [DQrng | [DQrng | [DQrng | DQrng]]];
          [ right; lia
          | right; lia
          | right; lia |].
         
        left; unfold m3, m2, m1; cbn [caddr clen Z.to_nat Pos.to_nat] in *;
        rewrite !wbytes_other_Z by (rewrite ?length_N_to_le_bytes; cbn; llia); reflexivity. }
      assert (KEEP : forall x : word, ms_mem s1 x <> None -> m3 x <> None).
      { intros x Hx. unfold m3, m2, m1. cbn [caddr clen Z.to_nat Pos.to_nat] in *.
        apply wbytes_keeps; [rewrite length_N_to_le_bytes, uZ by (cbn; llia); cbn; llia|].
        apply wbytes_keeps; [rewrite length_N_to_le_bytes, uZ by (cbn; llia); cbn; llia|].
        apply wbytes_keeps; [rewrite length_N_to_le_bytes, uZ by (cbn; llia); cbn; llia|]. exact Hx. }
      assert (HG3 : gsame A (mbA A (u a) L sh)).
      { constructor; try reflexivity; try (intros; assumption). intros kk Hk Hv. unfold mbA, set_ctx, set_mblocks. cbn [a_ctx].
        apply mb_ctx_other; destruct kk; cbn in Hk; try contradiction; discriminate. }
      assert (HI3 : IS sp0 argv envp cb (mbA A (u a) L sh) (upd s1 m3 (ms_vm s1))).
      { apply (IS_mem sp0 argv envp cb A _ s1 m3 HI1 HW3 HR3).
        - intros x. destruct (FRM x) as [E | X]; [left; exact E | right]. unfold mzone. do 3 right. clear -X HT MLok. llia.
        - intros x Hx. destruct (FRM x) as [E | X]; [left; rewrite <- E; exact Hx | right; left]. clear -X HT MLok. llia. }
      constructor.
      + constructor; [exact HI3 | | | | exact HD].
        * cbn [ms_vm upd s1]. apply (VMok_mbA A HW (u a) L sh HshE ltac:(rewrite Hbrk; lia) Glo eq_refl Gce (ms_vm s) a n HVo HVc1 eq_refl ltac:(unfold n; apply uZ; lia)).
          unfold page_aligned. exact G1.
        * intros ma mt Hma Hr. unfold mbA, set_ctx, set_mblocks. cbn [a_ctx a_areas]. rewrite mb_ctx_other by discriminate. exact (HAV ma mt Hma Hr).
        * apply (UsOK_transport A _ HG3); [reflexivity | exact HUS].
      + apply (FR_trans A0 s0 A s); [exact HFR|]. unfold s1. cbn [ms_mem ms_vm upd].
        change (upd (upd s (unfill a n (ms_mem s)) (vm_noacc a n (ms_vm s))) m3 (vm_noacc a n (ms_vm s))) with (upd s m3 (vm_noacc a n (ms_vm s))).
        apply (FR_ctxwrites A _ s m3 _ HW); [intros x; apply dom_mbA | reflexivity | reflexivity | |].
        * intros x. destruct (FRM x) as [E | X]; [left; rewrite E; apply SAME | right; lia].
        * intros x Hx. apply KEEP. unfold s1. cbn [ms_mem upd]. rewrite SAME. exact Hx.
      + exact (gsame_trans _ _ _ HGS HG3).
      + cbn. exact Hareas.
      + constructor; unfold s1; cbn [ms_vm upd vm_maps vm_noaccess vm_noacc]; rewrite <- ?Hvm.
        * intros b sz Hin. right. exact Hin.
        * intros b sz Hin Hf. cbn [region_free]. rewrite Hf.
          destruct (Gdisj b sz Hin) as [X|X]; unfold iv_overlap; rewrite HLu;
            [rewrite (proj2 (Z.ltb_ge (u b) (u a + L))) by lia | rewrite (proj2 (Z.ltb_ge (u a) (u b + u sz))) by lia];
            cbn; rewrite ?andb_false_r; reflexivity.
        * intros x Hx. left. apply Hdom. apply (proj1 (dom_mbA A (u a) L sh x)). exact Hx.
        * intros Har. assert (Hsh : sh = 0) by (unfold sh; apply (wf_noarea_shift A HW); [rewrite Hareas; exact Har | exact Haac]).
          unfold vm_live_bytes. cbn [vm_maps live_bytes vm_noacc]. rewrite HLu.
          unfold L. rewrite Hsh. change (2 ^ (0 + 13)) with 8192. lia.
      + lia.
      + exact Hsp0.
      + unfold mbA, set_ctx, set_mblocks. cbn [a_ctx]. rewrite mb_ctx_other by discriminate. exact Hinit.
      + unfold mbA, set_ctx, set_mblocks. cbn [a_ctx]. rewrite mb_ctx_other by discriminate. exact Hamc.
      + cbn. exact Hfl.
      + unfold mbA, set_ctx, set_mblocks. cbn [a_ctx]. rewrite mb_ctx_aac. lia.
      + unfold mbA, set_ctx, set_mblocks. cbn [a_ctx]. rewrite mb_ctx_aareas. reflexivity.
      + intros b sz Hin Hf. rewrite <- Hvm in Hin. destruct (Gdisj b sz Hin); lia.
      + intros Hb. unfold s1. cbn [ms_vm upd]. rewrite (vm_noacc_limit a n (ms_vm s)).
        destruct Hb as [Hsp | [Hbud _]]; [lia|]. rewrite <- Hvm in Hbud.
        pose proof (backed_noacc_le (ms_vm s) a n (maps_nw_of A _ HVc) ltac:(unfold n; rewrite uZ by lia; lia)). lia.
      + etransitivity; [| exact Hxm]. reflexivity.
      + intros x. rewrite (dom_mbA A (u a) L sh x). apply Hdom2.
      + (* [comment removed for export] *) intros HWk Har0. unfold am_pre, s1. cbn [ms_vm upd vm_maps vm_init_sp vm_reserved vm_limit vm_noacc]. rewrite <- Hvm.
        assert (Hsh : sh = 0) by (unfold sh; apply (wf_noarea_shift A HW); [rewrite Hareas; exact Har0 | exact Haac]).
        split; [left; exists a; unfold n, L; rewrite Hsh; reflexivity|].
        split; [| repeat split; reflexivity].
        exact (backed_noacc_le (ms_vm s) a n (maps_nw_of A _ HVc) ltac:(unfold n; rewrite uZ by lia; lia)).
      + (* [comment removed for export] *)
        unfold am_preg, s1. cbn [ms_vm upd vm_maps vm_init_sp vm_reserved vm_limit vm_noacc length]. rewrite <- Hvm.
        rewrite Nat2Z.inj_succ. split; [lia|].
        split; [| repeat split; reflexivity].
        exact (backed_noacc_le (ms_vm s) a n (maps_nw_of A _ HVc) ltac:(unfold n; rewrite uZ by lia; lia)).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma PreM_brkstore : forall A s s', PreM A s ->
    IS sp0 argv envp cb (actx_upd A KBrk (2^64 - 1)) s' -> FR A s (actx_upd A KBrk (2^64 - 1)) s' -> ms_vm s' = ms_vm s ->
    PreM (actx_upd A KBrk (2^64 - 1)) s'.
  Proof using Type. pu_keep tt.
    intros A s s' PM HI' HF' Hvm'. destruct PM as [HII HFR HGS Hareas Hdom Hvm Hsp0 Hinit Hamc Hfl Haac HaacA0 Hxm Hdom2 Hshift].
    pose proof HII as [HI HVo HAV HUS HD].
    assert (HG' : gsame A (actx_upd A KBrk (2^64 - 1))).
    { constructor; try reflexivity; try (intros; assumption). intros kk Hk Hv. unfold actx_upd, set_ctx. cbn [a_ctx].
      rewrite cupd_other by (destruct kk; cbn in Hk; try contradiction; discriminate). reflexivity. }
    constructor.
    - constructor; [exact HI' | rewrite Hvm'; apply VMok_upd_brk_neg1; exact HVo | intros ma mt Hma Hr; exact (HAV ma mt Hma Hr) | apply (UsOK_transport A _ HG'); [reflexivity | exact HUS] | intros x; exact (HD x)].
    - apply (FR_trans A0 s0 A s); assumption.
    - exact (gsame_trans _ _ _ HGS HG').
    - cbn. exact Hareas.
    - intros x Hx. apply Hdom. exact Hx.
    - rewrite Hvm'. exact Hvm.
    - exact Hsp0.
    - unfold actx_upd, set_ctx. cbn [a_ctx]. rewrite cupd_other by discriminate. exact Hinit.
    - unfold actx_upd, set_ctx. cbn [a_ctx]. rewrite cupd_other by discriminate. exact Hamc.
    - cbn. exact Hfl.
    - unfold actx_upd, set_ctx. cbn [a_ctx]. rewrite cupd_other by discriminate. exact Haac.
    - exact HaacA0.
    - etransitivity; [| exact Hxm]. reflexivity.
    - intros x. apply Hdom2.
    - unfold actx_upd, set_ctx. cbn [a_ctx]. rewrite cupd_other by discriminate. exact Hshift.
  Qed.

  (* [comment removed for export] *)
  Lemma after_false_ok : forall A s (neww : word), PreM A s -> a_ctx A KBrk <> 0 ->
    tsall W (am_after (Z_to_bv 64 0) (Some (neww, false)) s) ProvPost.
  Proof using MLok. pu_keep (MLok).
    intros A s neww PM Hbrk. pose proof PM as [HII HFR HGS Hareas Hdom Hvm Hsp0 Hinit Hamc Hfl Haac HaacA0 Hxm Hdom2 Hshift].
    pose proof HII as [HI HVo HAV HUS HD]. pose proof HI as [HW HR HC HWIN HE HG].
    cbn [am_after]. treassoc. rewrite A_AVAIL_AREA_CNT_eq.
    eapply (tw_ld_ctx W A); [exact HW | exact HR | exact HWIN | exact I | reflexivity | rewrite Haac; lia |]. rewrite Haac.
    treassoc. rewrite A_BRK_eq, wm1_eq.
    eapply (tw_sd_ctx1 W sp0 argv envp cb A); [exact HI | exact I | discriminate | reflexivity | |].
    { rewrite uZ by lia. apply WF_upd_brk; [exact HW | exact Hinit | lia | lia]. }
    intros s1 HI1 HF1 Hvm1 _. rewrite uZ in * by lia.
    apply tw_bind_ret. rewrite is0_true. cbn [negb].
    apply (mm_ok (actx_upd A KBrk (2^64 - 1)) s1).
    - apply (PreM_brkstore A s s1 PM HI1 HF1 Hvm1).
    - unfold actx_upd, set_ctx. cbn [a_ctx]. apply cupd_same.
  Qed.

  Theorem brk_a_ok : forall A s, PreM A s -> a_ctx A KBrk = 2^64 - 1 ->
    tsall W ((br <- am_brk (Z_to_bv 64 (2^64 - 1)) ;; am_after (Z_to_bv 64 0) br) s) ProvPost.
  Proof using MLok. pu_keep (MLok).
    intros A s PM Hbrk. unfold am_brk. rewrite wm1_eq, c_eq_Z by lia. rewrite Z.eqb_refl.
    apply tw_bind_ret. cbn [am_after]. apply tw_bind_ret. rewrite is0_true. cbn [negb].
    apply (mm_ok A s PM Hbrk).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem brk_b_ok : forall A s, PreM A s -> a_ctx A KBrk = u (vm_brk (ms_vm s)) ->
    tsall W ((br <- am_brk (Z_to_bv 64 (a_ctx A KBrk)) ;; am_after (Z_to_bv 64 0) br) s) ProvPost.
  Proof using MLok. pu_keep (MLok).
    intros A s PM Hbrk. pose proof PM as [HII HFR HGS Hareas Hdom Hvm Hsp0 Hinit Hamc Hfl Haac HaacA0 Hxm Hdom2 Hshift].
    pose proof HII as [HI HVo HAV HUS HD]. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof (VMok_core A _ HVo) as HVc. ceil.
    destruct (vc_brk_valid A _ HVc) as (K1 & K2 & K3 & K4).
    set (B := u (vm_brk (ms_vm s))) in *.
    unfold am_brk. rewrite Hbrk. rewrite wm1_eq, c_eq_Z by lia.
    replace (B =? 2 ^ 64 - 1) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite is0_false by lia. cbn [negb]. cbv zeta. unfold PZ, wlit. rewrite v_add_Z.
    treassoc.
    eapply tw_sys_brk_grow; [lia | rewrite uZ by lia; lia | rewrite uZ by lia; lia | |].
    - (* [comment removed for export] *)
      rewrite <- (Z_to_bv_bv_unsigned 64 (vm_brk (ms_vm s))). fold B. rewrite c_eq_Z by lia.
      replace (B =? B + 4096) with false by (symmetry; apply Z.eqb_neq; lia).
      apply tw_bind_ret. apply (after_false_ok A s _ PM). rewrite Hbrk. lia.
    - (* [comment removed for export] *)
      intros HWa Hok. rewrite c_eq_Z by lia. rewrite Z.eqb_refl.
      apply tw_bind_ret.
      destruct (brk_grow_state sp0 argv envp cb A s (Z_to_bv 64 (B + 4096)) HI HVc Hok ltac:(rewrite uZ by lia; lia)
                  ltac:(unfold page_aligned in *; rewrite uZ by lia; rewrite <- Zplus_mod_idemp_l, K3; reflexivity))
        as (HI1 & HVc1 & Emaps & NOD & APART & ZIN & ZOUT & Hce & Hlo & Himg & Hlive & Hbud).
      rewrite !uZ in * by lia. fold B in HI1, HVc1, Emaps, NOD, APART, ZIN, ZOUT, Hce, Hlo, Himg, Hlive, Hbud.
      set (s1 := upd s (apply_zeros (ms_mem s) (brk_zeros (Z_to_bv 64 (B + 4096)) (Z_to_bv 64 (B + 4096)) (vm_brk (ms_vm s))))
                       (vm_brk_grow (Z_to_bv 64 (B + 4096)) (ms_vm s))) in *.
      apply (after_true_ok 4096 A s1 B).
      assert (Hvm1 : ms_vm s1 = vm_brk_grow (Z_to_bv 64 (B + 4096)) (ms_vm s)) by reflexivity.
      constructor.
      + exact HI1.
      + exact HVc1.
      + rewrite Hvm1. apply VMall_brk_grow; [| lia | rewrite uZ by lia; lia]. pose proof HVo as [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vtop]. exact Vall.
      + exact HAV.
      + exact HUS.
      + exact HD.
      + eapply FRH_mono.
        * apply (FRH_extend (fun _ => False) (fun x => B <= x < B + 4096) A0 s0 A s A s1); cbn [ms_lo ms_hi ms_vm ms_mem upd s1].
          -- apply FRH_of_FR. exact HFR.
          -- exact HW.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
          -- auto.
          -- reflexivity.
          -- intros a. pose proof (u64_range a).
             assert (CASE : B <= u a < B + 4096 \/ ~ (B <= u a < B + 4096)) by lia.
             destruct CASE as [IN | NI]; [right; right; right; split; [exact IN | exact (proj1 (NOD (u a) IN))] | left; apply ZOUT; exact NI].
          -- intros a Ha. pose proof (u64_range a). assert (CASE : B <= u a < B + 4096 \/ ~ (B <= u a < B + 4096)) by lia.
             destruct CASE as [IN | NI]; [rewrite (ZIN a IN); discriminate | rewrite (ZOUT a NI); exact Ha].
        * intros x [F | Hx]; [destruct F | exact Hx].
      + exact HGS.
      + exact Hareas.
      + constructor; cbn [ms_vm upd s1]; rewrite <- ?Hvm.
        * intros b sz Hin. rewrite Emaps. right. exact Hin.
        * intros b sz Hin Hf. exact Hf.
        * intros x Hx. left. exact (Hdom x Hx).
        * intros _. rewrite Hlive. lia.
      + lia.
      + exact Hsp0.
      + exact Hinit.
      + exact Hamc.
      + exact Hfl.
      + rewrite Hbrk. lia.
      + exact Haac.
      + exact K3.
      + split; [lia|]. split; [lia|]. split; [lia | exact Himg].
      + intros x Hx. exact (proj1 (NOD x Hx)).
      + intros x Hx. cbn [ms_mem upd s1]. apply ZIN. rewrite uZ by lia. exact Hx.
      + cbn [ms_vm upd s1]. rewrite Emaps. exists (vm_brk (ms_vm s)), (Z_to_bv 64 (B + 4096 - B)). split; [left; reflexivity | rewrite uZ by lia; lia].
      + cbn [ms_vm upd s1]. change (vm_noaccess (vm_brk_grow (Z_to_bv 64 (B + 4096)) (ms_vm s))) with (vm_noaccess (ms_vm s)).
        apply (nafree_of_apart A); [exact HVc | lia | lia | lia |].
        intros b sz Hin. destruct (APART b sz Hin); lia.
      + cbn [ms_vm upd s1 vm_brk vm_start_brk vm_brk_grow]. rewrite uZ by lia. lia.
      + cbn [ms_vm upd s1 vm_brk vm_start_brk vm_brk_grow a_areas]. rewrite uZ by lia.
        pose proof (proj2 (vm_brk_span A _ HVo)). fold B in H. rewrite Hareas in *. lia.
      + intros b sz Hin Hf. rewrite <- Hvm in Hin. destruct (APART b sz Hin); lia.
      + exact Hxm.
      + intros HWo. rewrite HWo in HWa. discriminate HWa.
      + (* [comment removed for export] *)
        unfold am_grow. cbn [ms_vm upd s1]. rewrite Emaps. cbn [length]. rewrite Nat2Z.inj_succ. rewrite <- Hvm.
        split; [lia|]. split; [| repeat split; reflexivity].
        pose proof (backed_cons_le (ms_vm s) (vm_brk_grow (Z_to_bv 64 (B + 4096)) (ms_vm s)) _ _ Emaps eq_refl (maps_nw_of A _ HVc)
                      ltac:(rewrite uZ by lia; fold B; lia)) as BB.
        rewrite uZ in BB by lia. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_compute : forall r0 : word, 0 < u r0 -> u r0 mod 4096 = 0 ->
    v_add (v_and (v_addi PZ (-1)) (v_sub w0 r0)) r0 = r0.
  Proof using Type. pu_keep tt.
    intros r0 H0 Hal. pose proof (u64_range r0) as Hr. set (B := u r0) in *.
    rewrite <- (Z_to_bv_bv_unsigned 64 r0). fold B. unfold PZ, wlit. rewrite w0_eq, v_addi_Z, v_sub_Z.
    change (4096 + -1) with 4095. rewrite <- (ZZ_mod (0 - B)).
    replace ((0 - B) mod 2 ^ 64) with (2 ^ 64 - B) by (apply (Z.mod_unique_pos (0 - B) (2 ^ 64) (-1)); lia).
    rewrite v_and_Z by lia. rewrite Z.land_comm. change 4095 with (2 ^ 12 - 1). rewrite land_ones_low by lia.
    replace ((2 ^ 64 - B) mod 2 ^ 12) with 0.
    2:{ change (2 ^ 12) with 4096. rewrite Zminus_mod, Hal. reflexivity. }
    rewrite v_add_Z. reflexivity.
  Qed.

  Lemma PreM_brkB : forall A s s' (B : Z), PreM A s -> a_ctx A KBrk = 0 ->
    B = u (vm_brk (ms_vm s)) ->
    IS sp0 argv envp cb (actx_upd A KBrk B) s' -> FR A s (actx_upd A KBrk B) s' -> ms_vm s' = ms_vm s ->
    PreM (actx_upd A KBrk B) s'.
  Proof using Type. pu_keep tt.
    intros A s s' B PM Hb0 EB HI' HF' Hvm'. destruct PM as [HII HFR HGS Hareas Hdom Hvm Hsp0 Hinit Hamc Hfl Haac HaacA0 Hxm Hdom2 Hshift].
    pose proof HII as [HI HVo HAV HUS HD]. pose proof (VMok_core A _ HVo) as HVc.
    destruct (vc_brk_valid A _ HVc) as (K1 & K2 & K3 & K4).
    assert (HG' : gsame A (actx_upd A KBrk B)).
    { constructor; try reflexivity; try (intros; assumption). intros kk Hk Hv. unfold actx_upd, set_ctx. cbn [a_ctx].
      rewrite cupd_other by (destruct kk; cbn in Hk; try contradiction; discriminate). reflexivity. }
    constructor.
    - constructor; [exact HI' | | intros ma mt Hma Hr; exact (HAV ma mt Hma Hr) | apply (UsOK_transport A _ HG'); [reflexivity | exact HUS] | intros x; exact (HD x)].
      rewrite Hvm'. unfold actx_upd. apply VMok_set_ctx; [exact HVo | | |].
      + right; right. rewrite cupd_same. rewrite EB. auto.
      + rewrite !cupd_other by discriminate. exact (vm_areas_res A _ HVo).
      + rewrite cupd_same. intros HB. exfalso. lia.
    - apply (FR_trans A0 s0 A s); assumption.
    - exact (gsame_trans _ _ _ HGS HG').
    - cbn. exact Hareas.
    - intros x Hx. apply Hdom. exact Hx.
    - rewrite Hvm'. exact Hvm.
    - exact Hsp0.
    - unfold actx_upd, set_ctx. cbn [a_ctx]. rewrite cupd_other by discriminate. exact Hinit.
    - unfold actx_upd, set_ctx. cbn [a_ctx]. rewrite cupd_other by discriminate. exact Hamc.
    - cbn. exact Hfl.
    - unfold actx_upd, set_ctx. cbn [a_ctx]. rewrite cupd_other by discriminate. exact Haac.
    - exact HaacA0.
    - etransitivity; [| exact Hxm]. reflexivity.
    - intros x. apply Hdom2.
    - unfold actx_upd, set_ctx. cbn [a_ctx]. rewrite cupd_other by discriminate. exact Hshift.
  Qed.

  Theorem brk_c_ok : forall A s, PreM A s -> a_ctx A KBrk = 0 ->
    tsall W ((br <- am_brk (Z_to_bv 64 0) ;; am_after (Z_to_bv 64 0) br) s) ProvPost.
  Proof using MLok. pu_keep (MLok).
    intros A s PM Hbrk0. pose proof PM as [HII HFR HGS Hareas Hdom Hvm Hsp0 Hinit Hamc Hfl Haac HaacA0 Hxm Hdom2 Hshift].
    pose proof HII as [HI HVo HAV HUS HD]. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof (VMok_core A _ HVo) as HVc. ceil.
    destruct (vc_brk_valid A _ HVc) as (K1 & K2 & K3 & K4).
    destruct (wf_brk0 A HW Hbrk0) as (Har0 & Hpg0 & _).
    pose proof (proj1 (vm_brk_span A _ HVo) Hbrk0) as Ebs.
    set (B := u (vm_brk (ms_vm s))) in *.
    assert (EBs : u (vm_start_brk (ms_vm s)) = B) by (unfold B; rewrite Ebs; reflexivity).
    unfold am_brk. rewrite wm1_eq, c_eq_Z by lia. change (0 =? 2 ^ 64 - 1) with false. rewrite is0_true. cbn [negb].
    treassoc. apply tw_sys_brk_query. cbv beta zeta.
    rewrite (al_compute (vm_brk (ms_vm s))) by (fold B; first [lia | exact K3]).
    rewrite <- (Z_to_bv_bv_unsigned 64 (vm_brk (ms_vm s))). fold B.
    replace (v_add (Z_to_bv 64 B) (v_slli PZ 1)) with (Z_to_bv 64 (B + 8192))
      by (unfold PZ, wlit; rewrite v_slli_Z by lia; rewrite v_add_Z; reflexivity).
    treassoc. rewrite A_BRK_eq.
    eapply (tw_sd_ctx1 W sp0 argv envp cb A); [exact HI | exact I | discriminate | reflexivity | |].
    { rewrite uZ by lia. apply WF_upd_brk; [exact HW | exact Hinit | lia | lia]. }
    intros s1 HI1 HF1 Hvm1 Hm1. rewrite uZ in * by lia.
    set (A1 := actx_upd A KBrk B) in *.
    pose proof (PreM_brkB A s s1 B PM Hbrk0 eq_refl HI1 HF1 Hvm1) as PM1. fold A1 in PM1.
    pose proof (is_wf _ _ _ _ _ _ HI1) as HW1.
    assert (HVc1 : VMcore A1 (ms_vm s1)).
    { rewrite Hvm1. apply (VMcore_same A A1 _ HVc); [intros ma mt aib sl Hma _; exact Hma | reflexivity | reflexivity]. }
    assert (EA1brk : a_ctx A1 KBrk = B) by (unfold A1, actx_upd, set_ctx; cbn [a_ctx]; apply cupd_same).
    treassoc.
    eapply tw_sys_brk_grow; [rewrite Hvm1; lia | rewrite Hvm1, uZ by lia; lia | rewrite Hvm1, uZ by lia; lia | |].
    - (* [comment removed for export] *)
      rewrite Hvm1. rewrite <- (Z_to_bv_bv_unsigned 64 (vm_brk (ms_vm s))). fold B. rewrite c_eq_Z by lia.
      replace (B =? B + 8192) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota. cbv beta.
      apply tw_bind_ret. apply (after_false_ok A1 s1 _ PM1). rewrite EA1brk. lia.
    - (* [comment removed for export] *)
      intros HWa Hok. rewrite c_eq_Z by lia. rewrite Z.eqb_refl. cbv iota. cbv beta.
      destruct (brk_grow_state sp0 argv envp cb A1 s1 (Z_to_bv 64 (B + 8192)) HI1 HVc1 Hok ltac:(rewrite Hvm1, uZ by lia; lia)
                  ltac:(unfold page_aligned in *; rewrite uZ by lia; rewrite <- Zplus_mod_idemp_l, K3; reflexivity))
        as (HI2 & HVc2 & Emaps & NOD & APART & ZIN & ZOUT & Hce & Hlo & Himg & Hlive & Hbud).
      rewrite ?Hvm1 in HI2. rewrite ?Hvm1 in HVc2. rewrite ?Hvm1 in Emaps. rewrite ?Hvm1 in NOD. rewrite ?Hvm1 in APART. rewrite ?Hvm1 in ZIN. rewrite ?Hvm1 in ZOUT. rewrite ?Hvm1 in Hlo. rewrite ?Hvm1 in Himg. rewrite ?Hvm1 in Hlive. rewrite ?Hvm1 in Hbud. rewrite ?Hvm1.
      rewrite !uZ in * by lia. fold B in HI2, HVc2, Emaps, NOD, APART, ZIN, ZOUT, Hce, Hlo, Himg, Hlive, Hbud.
      rewrite Hvm1 in Hok.
      destruct (brk_grow_facts A (ms_vm s) (Z_to_bv 64 (B + 8192)) HVc Hok ltac:(rewrite uZ by lia; lia)
                  ltac:(unfold page_aligned in *; rewrite uZ by lia; rewrite <- Zplus_mod_idemp_l, K3; reflexivity)) as (_ & Hrfree & _).
      rewrite uZ in Hrfree by lia. fold B in Hrfree. rewrite region_free_app in Hrfree. apply andb_true_iff in Hrfree. destruct Hrfree as [Hrres _].
      set (h2 := vm_brk_grow (Z_to_bv 64 (B + 8192)) (ms_vm s)) in *.
      set (m2 := apply_zeros (ms_mem s1) (brk_zeros (Z_to_bv 64 (B + 8192)) (Z_to_bv 64 (B + 8192)) (vm_brk (ms_vm s)))) in *.
      set (s2 := upd s1 m2 h2) in *.
      pose proof HI2 as [_ HR2 HC2 HWIN2 HE2 HG2].
      pose proof PM1 as [HII1 HFR1 HGS1 Hareas1 Hdom1 _ _ Hinit1 Hamc1 Hfl1 Haac1 _ Hxm1 _].
      pose proof HII1 as [_ HVo1 HAV1 HUS1 HD1].
      assert (Hapart : forall b sz, In (b, sz) (vm_maps (ms_vm s)) -> B + 8192 <= u b \/ u b + u sz <= B).
      { intros b sz Hin. exact (APART b sz Hin). }
      assert (Eh2maps : vm_maps h2 = (vm_brk (ms_vm s), Z_to_bv 64 (B + 8192 - B)) :: vm_maps (ms_vm s)) by exact Emaps.
      assert (Eh2na : vm_noaccess h2 = vm_noaccess (ms_vm s)) by reflexivity.
      assert (Eh2brk : u (vm_brk h2) = B + 8192) by (unfold h2; rewrite vm_brk_grow_brk; apply uZ; lia).
      assert (Eh2sb : vm_start_brk h2 = vm_start_brk (ms_vm s)) by reflexivity.
      assert (Eh2top : alloc_top h2 = alloc_ceiling) by (unfold h2; rewrite vm_brk_grow_alloc_top; exact (vc_top A _ HVc)).
      assert (Hcov2 : forall x k, B <= x -> x + k <= B + 8192 -> mcov (vm_maps h2) x k).
      { intros x k Hx Hk. rewrite Eh2maps. exists (vm_brk (ms_vm s)), (Z_to_bv 64 (B + 8192 - B)). split; [left; reflexivity | fold B; rewrite uZ by lia; lia]. }
      assert (Hnaf : forall lo n, B <= lo -> 0 < n -> lo + n <= B + 8192 -> region_free (vm_noaccess (ms_vm s)) (Z_to_bv 64 lo) (Z_to_bv 64 n) = true).
      { intros lo n H1 H2 H3. apply (nafree_of_apart A); [exact HVc | lia | lia | lia |]. intros b sz Hin. destruct (Hapart b sz Hin); lia. }
      assert (Vall2 : VMall A1 h2).
      { unfold h2. apply VMall_brk_grow; [apply VMall_actx_upd | lia | rewrite uZ by lia; lia]. pose proof HVo as [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vtop]. exact Vall. }
      assert (Hdom1' : forall x, dom A1 x <-> dom A x) by (intros x; reflexivity).
      treassoc.
      eapply (tw_ld_ctx W A1); [exact HW1 | exact HR2 | exact HWIN2 | exact I | reflexivity | rewrite EA1brk; lia |]. rewrite EA1brk.
      treassoc.
      (* [comment removed for export] *)
      eapply tw_sys_mmap_fixed_none04;
        [rewrite PZ_u; lia | rewrite PZ_u; lia | cbn [ms_vm upd s2]; rewrite pruZ_PZ, Eh2top, uZ by lia; lia
        | unfold page_size; rewrite uZ by lia; exact K3 | rewrite uZ by lia; lia
        | cbn [ms_vm upd s2]; rewrite pru_PZ; unfold h2; rewrite vm_brk_grow_reserved; apply (region_free_sub _ _ _ _ _ Hrres); rewrite ?uZ by lia; lia
        | cbn [ms_vm upd s2]; rewrite pru_PZ; apply (proj2 (map_contains_mcov _ _ _)); rewrite !uZ by lia; apply Hcov2; lia |].
      + (* [comment removed for export] *)
        intros HWs. apply tw_bind_ret. rewrite pru_PZ. cbn [ms_mem ms_vm upd s2].
        replace (B + 8192) with (B + 4096 + 4096) at 1 by lia.
        set (n4 := Z_to_bv 64 4096). assert (En4 : u n4 = 4096) by (unfold n4; apply uZ; lia).
        set (m3 := unfill (Z_to_bv 64 B) n4 m2). set (h3 := vm_fixed_ok (Z_to_bv 64 B) n4 h2).
        assert (M3in : forall a : word, B <= u a < B + 4096 -> m3 a = None) by (intros a Ha; unfold m3; apply unfill_in; rewrite uZ, En4 by lia; exact Ha).
        assert (M3out : forall a : word, ~ (B <= u a < B + 4096) -> m3 a = m2 a) by (intros a Ha; unfold m3; apply unfill_out; rewrite uZ, En4 by lia; lia).
        assert (HI3 : IS sp0 argv envp cb A1 (upd s2 m3 h3)).
        { apply (IS_region sp0 argv envp cb A1 s2 m3 h3 B 4096 HI2); cbn [ms_mem ms_vm upd s2].
          - intros a. pose proof (u64_range a). assert (CASE : B <= u a < B + 4096 \/ ~ (B <= u a < B + 4096)) by lia.
            destruct CASE as [IN | NI]; [right; exact IN | left; exact (M3out a NI)].
          - lia. - lia. - lia.
          - intros x Hd Hx. apply (proj1 (NOD x ltac:(lia))). exact (proj2 (Hdom1' x) Hd).
          - intros a _ _ Hc. exact Hc.
          - intros a Ha Hm. exfalso. apply Hm. apply M3in. exact Ha. }
        assert (HVc3 : VMcore A1 h3).
        { unfold h3, vm_fixed_ok. rewrite uZ, En4 by lia.
          pose proof (VMcore_fixed_ok A1 h2 (Z_to_bv 64 B) n4 HW1 HVc2 ltac:(lia) ltac:(rewrite uZ, En4 by lia; lia)
                        ltac:(rewrite uZ, En4 by lia; apply Hcov2; lia)) as X.
          rewrite uZ, En4 in X by lia. apply X. intros x Hd Hx. apply (proj1 (NOD x ltac:(lia))). exact (proj2 (Hdom1' x) Hd). }
        apply (after_true_ok 8192 A1 (upd s2 m3 h3) (B + 4096)).
        constructor; cbn [ms_vm ms_mem upd].
        * exact HI3.
        * exact HVc3.
        * apply (VMall_restate A1 A1 h2 h3 Vall2); try reflexivity. auto.
        * exact HAV1.
        * exact HUS1.
        * exact HD1.
        * eapply FRH_mono.
          -- apply (FRH_extend (fun _ => False) (fun x => B + 4096 <= x < B + 4096 + 4096) A0 s0 A1 s1 A1 (upd s2 m3 h3)); cbn [ms_lo ms_hi ms_vm ms_mem upd s2].
             ++ apply FRH_of_FR. exact HFR1.
             ++ exact HW1.
             ++ reflexivity.
             ++ reflexivity.
             ++ rewrite Hvm1. reflexivity.
             ++ auto.
             ++ reflexivity.
             ++ intros a. pose proof (u64_range a).
                assert (CASE : (B <= u a < B + 4096 \/ B + 4096 <= u a < B + 8192) \/ ~ (B <= u a < B + 8192)) by lia.
                destruct CASE as [[IN1 | IN2] | NI].
                ** left. rewrite (M3in a IN1). symmetry. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (proj2 (NOD (u a) ltac:(lia))).
                ** right; right; right. split; [lia | exact (proj1 (NOD (u a) ltac:(lia)))].
                ** left. rewrite (M3out a) by lia. apply ZOUT. exact NI.
             ++ intros a Ha. pose proof (u64_range a).
                assert (CASE : B <= u a < B + 8192 \/ ~ (B <= u a < B + 8192)) by lia.
                destruct CASE as [IN | NI].
                ** exfalso. apply Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (proj2 (NOD (u a) IN)).
                ** rewrite (M3out a) by lia. rewrite (ZOUT a NI). exact Ha.
          -- intros x [F | Hx]; [destruct F | exact Hx].
        * exact HGS1.
        * exact Hareas1.
        * constructor; cbn [ms_vm upd]; rewrite <- ?Hvm.
          -- intros b sz Hin. unfold h3, vm_fixed_ok. cbn [vm_maps]. rewrite Eh2maps. right. exact Hin.
          -- intros b sz Hin Hf. unfold h3, vm_fixed_ok. cbn [vm_noaccess region_free]. rewrite Eh2na.
             apply andb_true_iff. split.
             ++ apply negb_true_iff. unfold iv_overlap. rewrite uZ, En4 by lia. apply andb_false_iff.
                destruct (Hapart b sz Hin); [left | right]; apply Z.ltb_ge; lia.
             ++ apply maps_subtract_free; [exact (na_nw A _ HVc) | exact Hf].
          -- intros x Hx. left. exact (Hdom1 x Hx).
          -- intros _. change (vm_live_bytes h3) with (vm_live_bytes h2). rewrite Hlive. lia.
        * lia.
        * exact Hsp0.
        * exact Hinit1.
        * exact Hamc1.
        * exact Hfl1.
        * rewrite EA1brk. lia.
        * exact Haac1.
        * unfold page_aligned in *. rewrite <- Zplus_mod_idemp_l, K3. reflexivity.
        * split; [lia|]. split; [lia|]. split; [lia | lia].
        * intros x Hx Hd. exact (proj1 (NOD x ltac:(lia)) (proj2 (Hdom1' x) Hd)).
        * intros x Hx. rewrite M3out by (rewrite uZ by lia; lia). apply ZIN. rewrite uZ by lia. lia.
        * unfold h3, vm_fixed_ok. cbn [vm_maps]. apply Hcov2; lia.
        * unfold h3, vm_fixed_ok. cbn [vm_noaccess region_free]. rewrite Eh2na. apply andb_true_iff. split.
          -- apply negb_true_iff. unfold iv_overlap. rewrite !uZ, En4 by lia. apply andb_false_iff. left. apply Z.ltb_ge. lia.
          -- apply maps_subtract_free; [exact (na_nw A _ HVc) | apply Hnaf; lia].
        * unfold h3, vm_fixed_ok. cbn [vm_brk vm_start_brk]. rewrite Eh2brk, Eh2sb, EBs. lia.
        * unfold h3, vm_fixed_ok. cbn [vm_brk vm_start_brk]. rewrite Eh2brk, Eh2sb, EBs. lia.
        * intros b sz Hin Hf. rewrite <- Hvm in Hin. destruct (Hapart b sz Hin); lia.
        * etransitivity; [| exact Hxm1]. reflexivity.
        * intros HWo. rewrite HWo in HWa. discriminate HWa.
        * (* [comment removed for export] *)
          unfold am_grow, h3. cbn [vm_maps vm_init_sp vm_reserved vm_limit vm_fixed_ok].
          rewrite Eh2maps. cbn [length]. rewrite Nat2Z.inj_succ. rewrite <- Hvm.
          split; [lia|]. split; [| unfold h2; repeat split; reflexivity].
          pose proof (backed_fixed_ok_le h2 (Z_to_bv 64 B) n4 (maps_nw_of A1 _ HVc2) (na_nw A1 _ HVc2)) as BF.
          pose proof (backed_cons_le (ms_vm s) h2 _ _ Eh2maps Eh2na (maps_nw_of A _ HVc) ltac:(fold B; rewrite uZ by lia; lia)) as BB.
          rewrite uZ in BB by lia. fold h3 in BF. unfold h3 in BF. lia.
  Qed.
End Prov.
End WithLayout.

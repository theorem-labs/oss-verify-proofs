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
  MallocLayout MallocTree MallocTreeW MallocOps MallocInv_defs MallocInv_heap MallocInv_word
  MallocInv_sep MallocInv_wf MallocInv_wf3 MallocInv_wf4 MallocInv_dll MallocInv_tables MallocInv_steps MallocInv_repw
  MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_vmops MallocInv_auxv
  MallocInv_ameta_base MallocInv_ameta_iface MallocInv_budget.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma VMall_set_ctx : forall A c h, VMall A h -> VMall (set_ctx A c) h.
Proof. intros A c h H. exact H. Qed.

(* [comment removed for export] *)
Lemma VMall_cons : forall A A' h res (e : word * word) na sb br lim mb isp,
  VMall A h -> vm_start_brk h = sb -> u (vm_brk h) <= u br ->
  a_meta A' = a_meta A -> (forall c l, In (c, l) (a_mblocks A ++ a_xmaps A) -> In (c, l) (a_mblocks A' ++ a_xmaps A')) ->
  ((u sb <= u (fst e) /\ u (fst e) + u (snd e) <= u br) \/
   (exists c l, In (c, l) (a_mblocks A' ++ a_xmaps A') /\ c <= u (fst e) /\ u (fst e) + u (snd e) <= c + l)) ->
  VMall A' (mkVmMapsFull res (e :: vm_maps h) na sb br lim mb isp).
Proof.
  intros A A' h res [a n] na sb br lim mb isp HV Hsb Hbr Hmeta Hincl He b sz Hin.
  cbn [vm_maps vm_start_brk vm_brk fst snd] in *.
  destruct Hin as [E | Hin].
  - injection E as <- <-. destruct He as [He | He]; [right; left; exact He | right; right; exact He].
  - destruct (HV b sz Hin) as [G | [Bk | (c & l & Hcl & H1 & H2)]].
    + left. rewrite Hmeta. exact G.
    + right; left. rewrite <- Hsb. llia.
    + right; right. exists c, l. split; [apply Hincl; exact Hcl | llia].
Qed.

(* [comment removed for export] *)
Lemma VMall_restate : forall A A' h h',
  VMall A h -> vm_maps h' = vm_maps h -> vm_start_brk h' = vm_start_brk h -> u (vm_brk h) <= u (vm_brk h') ->
  a_meta A' = a_meta A -> (forall c l, In (c, l) (a_mblocks A ++ a_xmaps A) -> In (c, l) (a_mblocks A' ++ a_xmaps A')) ->
  VMall A' h'.
Proof.
  intros A A' h h' HV Em Es Eb Hmeta Hincl b sz Hin. rewrite Em in Hin. rewrite Es.
  destruct (HV b sz Hin) as [G | [Bk | (c & l & Hcl & H1 & H2)]].
  - left. rewrite Hmeta. exact G.
  - right; left. llia.
  - right; right. exists c, l. split; [apply Hincl; exact Hcl | llia].
Qed.

Lemma VMall_brk_grow : forall A h (req : word),
  VMall A h -> u (vm_start_brk h) <= u (vm_brk h) -> u (vm_brk h) <= u req ->
  VMall A (vm_brk_grow req h).
Proof.
  intros A h req HV Hsb Hle. unfold vm_brk_grow.
  pose proof (u64_range req). pose proof (u64_range (vm_brk h)).
  apply (VMall_cons A A h); auto.
  left. cbn [fst snd]. rewrite u_sub_small by llia. llia.
Qed.

(* [comment removed for export] *)
Lemma maps_fixed_destroy_head : forall (b n : word) l (pg : word),
  u pg = 4096 -> 4096 < u n -> u b + u n <= 2^64 ->
  (forall b0 sz, In (b0, sz) l -> 0 < u sz /\ u b0 + u sz <= 2^64 /\ (u b0 + u sz <= u b \/ u b + 4096 <= u b0)) ->
  maps_subtract ((b, n) :: l) (u b) (u b + u pg) = (Z_to_bv 64 (u b + 4096), Z_to_bv 64 (u n - 4096)) :: l.
Proof.
  intros b n l pg Hpg Hn Hnw Hl. cbn [maps_subtract]. rewrite Hpg.
  rewrite (iv_subtract_prefix b n (u b) (u b + 4096)); try llia.
  rewrite (maps_subtract_apart l (u b) (u b + 4096)); [| llia | exact Hl].
  cbn [app]. replace (u b + u n - (u b + 4096)) with (u n - 4096) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma VMcore_fixed_destroy : forall A h (lo hi : Z),
  WF A -> VMcore A h -> lo < hi ->
  (forall x, dom A x -> ~ (lo <= x < hi)) ->
  VMcore A (mkVmMapsFull (vm_reserved h) (maps_subtract (vm_maps h) lo hi) (maps_subtract (vm_noaccess h) lo hi)
                         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros A h lo hi HW HV Hlh Hdom. pose proof (na_nw A h HV) as NW. pose proof (maps_nw_of A h HV) as NWM.
  pose proof HV as [Vg Vres Vbv Vpw Vmw Vna Vac Vpc Vtop]. ceil.
  (* [comment removed for export] *)
  assert (APART : forall x k, 0 < k -> (forall y, x <= y < x + k -> dom A y) -> x + k <= lo \/ hi <= x).
  { intros x k Hk Hd.
    destruct (Z.lt_ge_cases (x + k) (lo + 1)) as [L | L]; [left; llia|].
    destruct (Z.lt_ge_cases hi (x + 1)) as [L2 | L2]; [right; llia|].
    exfalso. destruct (Z.lt_ge_cases x lo) as [L3 | L3].
    - apply (Hdom lo); [apply Hd; llia | llia].
    - apply (Hdom x); [apply Hd; llia | llia]. }
  constructor; cbn [vm_maps vm_noaccess vm_reserved vm_brk vm_start_brk vm_limit vm_init_sp alloc_top]; try assumption.
  - intros ma mt aib slots Hma Hr Hml. destruct (Vg ma mt aib slots Hma Hr Hml) as [H1 H2].
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hce & Hpg).
    destruct (Hpg Hml) as [_ (R1 & R2 & R3 & R4)].
    assert (Hgl : 0 < grp_map_len mt) by (unfold grp_map_len; llia).
    pose proof (APART (mt_mem mt) (grp_map_len mt) Hgl ltac:(intros y Hy; right; left; exists ma, mt, aib, slots; auto)) as AP.
    split; [| apply maps_subtract_free; [exact NW | exact H2]].
    pose proof (NWM _ _ H1) as NW1. rewrite !uZ in NW1 by llia.
    apply (maps_subtract_in_intro _ lo hi _ _ _ H1). rewrite (iv_subtract_apart _ _ lo hi); rewrite ?uZ by llia; try llia. left; reflexivity.
  - apply maps_subtract_pw; [exact NWM | llia | exact Vpw].
  - intros b' sz' Hin. destruct (in_maps_subtract _ lo hi b' sz' Hin) as (b & sz & H0 & H1).
    destruct (iv_subtract_in b sz lo hi b' sz' (NWM b sz H0) H1) as (A1 & A2 & A3 & A4).
    destruct (Vmw b sz H0) as (W1 & W2 & W3 & W4). repeat split; llia.
  - intros b' sz' Hin. destruct (in_maps_subtract _ lo hi b' sz' Hin) as (b & sz & H0 & H1).
    destruct (iv_subtract_in b sz lo hi b' sz' (NW b sz H0) H1) as (A1 & A2 & A3 & A4).
    destruct (Vna b sz H0) as [Hsz Hcb]. split; [exact (A4 Hsz)|].
    apply maps_subtract_cover; [exact NWM | apply (mcov_sub _ (u b) (u sz)); [exact Hcb | llia | llia] | exact (A4 Hsz) | exact A3].
  - intros pg Hpg. destruct (Vac pg Hpg) as [H1 H2]. destruct (wf_areas_al A HW pg Hpg) as [_ (R1 & R2 & R3 & R4)].
    split; [| apply maps_subtract_free; [exact NW | exact H2]].
    apply maps_subtract_cover; [exact NWM | exact H1 | llia | apply (APART pg 4096); [llia | intros y Hy; left; exists pg; auto]].
  - intros pg Hpg. destruct (Vpc pg Hpg) as [H1 H2]. destruct (wf_pages_al A HW pg Hpg) as [_ (R1 & R2 & R3 & R4)].
    split; [| apply maps_subtract_free; [exact NW | exact H2]].
    apply maps_subtract_cover; [exact NWM | exact H1 | llia | apply (APART pg 4096); [llia | intros y Hy; right; right; exists pg; auto]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_none_facts : forall sp0 argv envp cb A s (a len : word),
  IS sp0 argv envp cb A s -> VMcore A (ms_vm s) -> 0 < u len -> u len < 2^62 ->
  grant_ok_na_vm (ms_vm s) a (page_round_up_Z (u len)) = true ->
  u (page_round_up len) = page_round_up_Z (u len) /\
  u len <= page_round_up_Z (u len) /\
  u a mod 4096 = 0 /\ 0x1000 <= u a /\ u a + page_round_up_Z (u len) <= alloc_ceiling /\
  (u a + page_round_up_Z (u len) <= IMG_LO \/ IMG_HI <= u a) /\
  region_free (vm_maps (ms_vm s)) a (page_round_up len) = true /\
  region_free (vm_noaccess (ms_vm s)) a (page_round_up len) = true /\
  (forall x, u a <= x < u a + page_round_up_Z (u len) -> ~ dom A x /\ ms_mem s (Z_to_bv 64 x) = None) /\
  (forall b sz, In (b, sz) (vm_maps (ms_vm s)) -> u a + page_round_up_Z (u len) <= u b \/ u b + u sz <= u a).
Proof.
  intros sp0 argv envp cb A s a len HI HV Hlen Hlen2 Hg.
  pose proof alloc_ceiling_val as HCV. pose proof (u64_range a).
  pose proof (is_wf _ _ _ _ _ _ HI) as HW. pose proof (is_cov _ _ _ _ _ _ HI) as HC.
  pose proof (page_round_up_Z_bounds (u len) ltac:(llia)) as [B1 B2]. unfold page_size in B2.
  apply grant_ok_na_vm_spec in Hg. destruct Hg as (G1 & G2 & G3 & G4). rewrite (vc_top A _ HV) in G3.
  assert (EnZ : u (page_round_up len) = page_round_up_Z (u len)) by (unfold page_round_up; apply uZ; llia).
  assert (En : Z_to_bv 64 (page_round_up_Z (u len)) = page_round_up len) by reflexivity.
  rewrite En in G4. rewrite region_free_app in G4. apply andb_true_iff in G4. destruct G4 as [Gr Gm].
  pose proof (region_free_image a (page_round_up len) ltac:(rewrite <- (vc_res A _ HV); exact Gr) ltac:(rewrite EnZ; llia)) as Himg.
  rewrite EnZ in Himg.
  pose proof (proj1 (region_free_spec _ _ _) Gm) as FREE. rewrite EnZ in FREE.
  pose proof (aligned_ge_page (u a) G1 G2) as Hlo.
  assert (NODOM : forall x, u a <= x < u a + page_round_up_Z (u len) -> ~ dom A x).
  { intros x Hx Hd. pose proof (dom_mcov_core A (ms_vm s) x HW HV Hd) as Hc.
    destruct (mcov_free_disj _ x 1 a (page_round_up len) Hc Gm); rewrite ?EnZ in *; llia. }
  split; [exact EnZ|]. split; [exact B1|]. split; [exact G1|]. split; [exact Hlo|]. split; [exact G3|]. split; [exact Himg|].
  split; [exact Gm|]. split; [| split; [| exact FREE]].
  - apply (proj2 (region_free_spec _ _ _)). intros b sz Hin. rewrite EnZ.
    destruct (vc_na_in A _ HV b sz Hin) as [Hsz (B & SZ & HinB & HB1 & HB2)].
    destruct (FREE B SZ HinB); llia.
  - intros x Hx. split; [exact (NODOM x Hx)|].
    destruct (ms_mem s (Z_to_bv 64 x)) eqn:E; [| reflexivity]. exfalso.
    pose proof (HC (Z_to_bv 64 x) ltac:(rewrite E; discriminate) ltac:(rewrite uZ by llia; llia) ltac:(rewrite uZ by llia; llia)) as Hc.
    rewrite uZ in Hc by llia. destruct (mcov_free_disj _ x 1 a (page_round_up len) Hc Gm); rewrite ?EnZ in *; llia.
Qed.

(* [comment removed for export] *)
Lemma mmap_none_state : forall sp0 argv envp cb A s (a len : word),
  IS sp0 argv envp cb A s -> VMcore A (ms_vm s) -> 0 < u len -> u len < 2^62 ->
  grant_ok_na_vm (ms_vm s) a (page_round_up_Z (u len)) = true ->
  let n := page_round_up len in
  IS sp0 argv envp cb A (upd s (unfill a n (ms_mem s)) (vm_noacc a n (ms_vm s))) /\
  VMcore A (vm_noacc a n (ms_vm s)) /\
  (forall x : word, unfill a n (ms_mem s) x = ms_mem s x).
Proof.
  intros sp0 argv envp cb A s a len HI HV Hlen Hlen2 Hg. cbn beta zeta.
  pose proof alloc_ceiling_val as HCV. pose proof (u64_range a).
  destruct (mmap_none_facts sp0 argv envp cb A s a len HI HV Hlen Hlen2 Hg) as (EnZ & B1 & G1 & Glo & Gce & Gimg & Gm & Gna & Gdom & Gdisj).
  set (n := page_round_up len) in *. set (nZ := page_round_up_Z (u len)) in *.
  assert (SAME : forall x : word, unfill a n (ms_mem s) x = ms_mem s x).
  { intros x. pose proof (u64_range x).
    assert (CASE : u a <= u x < u a + nZ \/ ~ (u a <= u x < u a + nZ)) by llia. destruct CASE as [IN | NI].
    - rewrite (unfill_in a n (ms_mem s) x) by (rewrite EnZ; exact IN).
      destruct (Gdom (u x) IN) as [_ E]. rewrite Z_to_bv_bv_unsigned in E. rewrite E. reflexivity.
    - apply unfill_out. rewrite EnZ. llia. }
  split; [| split; [| exact SAME]].
  - apply (IS_region sp0 argv envp cb A s _ _ (u a) nZ HI).
    + intros x. left. apply SAME.
    + exact Glo.
    + exact Gce.
    + exact Gimg.
    + intros x Hd Hx. exact (proj1 (Gdom x Hx) Hd).
    + intros x _ _ Hc. cbn [vm_maps vm_noacc]. apply mcov_cons. exact Hc.
    + intros x Hx Hm. exfalso. apply Hm. apply unfill_in. rewrite EnZ. exact Hx.
  - unfold vm_noacc. apply (VMcore_add_noacc A (ms_vm s) a n HV); rewrite ?EnZ; try assumption; llia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CtxStore.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte).
  Implicit Types (P : R -> mstate -> Prop).

  (* [comment removed for export] *)
  Lemma sd_ctx1_state : forall A s ck (v : word),
    IS sp0 argv envp cb A s -> cvalid ck -> ck <> KSecret -> clen ck = 8 ->
    WF (actx_upd A ck (u v)) ->
    let m' := wbytes (ms_mem s) (Z_to_bv 64 (caddr ck)) (word_to_le_bytes 8 v) in
    IS sp0 argv envp cb (actx_upd A ck (u v)) (upd s m' (ms_vm s)) /\
    FR A s (actx_upd A ck (u v)) (upd s m' (ms_vm s)) /\
    (forall a : word, m' a = ms_mem s a \/ caddr ck <= u a < caddr ck + 8).
  Proof.
    intros A s ck v HI Hk Hks Hlen HW'. cbn beta zeta. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof (ctx_slot_range ck Hk) as (C1 & C2 & C3). pose proof (u64_range v) as Hv.
    set (m' := wbytes (ms_mem s) (Z_to_bv 64 (caddr ck)) (word_to_le_bytes 8 v)).
    pose proof (repw_st_ctx A s (ms_mem s) [] ck v (repw_init A _ HW HR) Hk) as RW1. rewrite Hlen in RW1. fold m' in RW1.
    assert (HR' : Rep (actx_upd A ck (u v)) m').
    { apply (repw_final A _ (ms_mem s) _ m' RW1).
      - intros x b (f & Hf & [Hx ->]).
        destruct (has_actx_upd A HW ck (u v) f Hk Hks Hf) as [-> | [Hold Hdisj]]; cbn [f_a f_n f_v] in *.
        + left. rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. reflexivity.
        + right. split; [rewrite wlook_skip by (cbn [f_a f_n]; llia); reflexivity|].
          exists f. split; [exact Hold | split; [exact Hx | reflexivity]].
      - intros x Hx. exact (proj1 (dom_actx_upd A ck (u v) x) Hx). }
    assert (FRM : forall a : word, m' a = ms_mem s a \/ caddr ck <= u a < caddr ck + 8).
    { intros a. pose proof (u64_range a).
      destruct (Z.lt_ge_cases (u a) (caddr ck)) as [L1|L1]; [| destruct (Z.lt_ge_cases (u a) (caddr ck + 8)) as [L2|L2]; [right; llia|]];
        left; unfold m'; rewrite wbytes_other_Z by (rewrite ?length_N_to_le_bytes; cbn; llia); reflexivity. }
    assert (KEEP : forall a : word, ms_mem s a <> None -> m' a <> None).
    { intros a Ha. unfold m'. apply wbytes_keeps; [rewrite length_N_to_le_bytes, uZ by (cbn; llia); cbn; llia | exact Ha]. }
    split; [| split; [| exact FRM]].
    - apply (IS_mem sp0 argv envp cb A _ s m' HI HW' HR').
      + intros a. destruct (FRM a) as [E | X]; [left; exact E | right]. unfold mzone, CTX, CTX_END. unfold LOCKA, CTX_END in *. llia.
      + intros a Ha. destruct (FRM a) as [E | X]; [left; rewrite <- E; exact Ha | right; left]. unfold LOCKA, CTX_END in *. llia.
    - apply (FR_memA A _ s m' HW); [intros x; apply dom_actx_upd | reflexivity | | exact KEEP].
      intros a. destruct (FRM a) as [E | X]; [left; exact E | right; left]. unfold LOCKA, CTX_END in *. llia.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_sd_ctx1 : forall A s ck (v : word) (k : unit -> M R) P,
    IS sp0 argv envp cb A s -> cvalid ck -> ck <> KSecret -> clen ck = 8 ->
    WF (actx_upd A ck (u v)) ->
    (forall s', IS sp0 argv envp cb (actx_upd A ck (u v)) s' -> FR A s (actx_upd A ck (u v)) s' -> ms_vm s' = ms_vm s ->
       (forall a : word, ms_mem s' a = ms_mem s a \/ caddr ck <= u a < caddr ck + 8) ->
       tsafe (k tt s') P) ->
    tsafe ((x <- m_sd (Z_to_bv 64 (caddr ck)) v ;; k x) s) P.
  Proof.
    intros A s ck v k P HI Hk Hks Hlen HW' Hk'. pose proof HI as [HW HR HC HWIN HE HG].
    unfold m_sd. change (m_st 8) with (m_st (Z.to_nat 8)). rewrite <- Hlen.
    eapply (ts_st_ctxw A s (ms_mem s) []); [apply repw_init; [exact HW | exact HR] | exact HWIN | exact Hk |].
    rewrite Hlen. change (Z.to_nat 8) with 8%nat.
    destruct (sd_ctx1_state A s ck v HI Hk Hks Hlen HW') as (H1 & H2 & H3).
    apply Hk'; [exact H1 | exact H2 | reflexivity | exact H3].
  Qed.
End CtxStore.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma WF_upd_brk : forall A v, WF A -> a_ctx A KInit = 1 -> v <> 0 -> 0 <= v -> WF (actx_upd A KBrk v).
Proof.
  intros A v HW Hinit Hv Hv0. unfold actx_upd.
  apply WF_set_ctx; try exact HW; rewrite ?cupd_same; rewrite ?cupd_other by discriminate.
  - exact (wf_init A HW).
  - intros H0. rewrite Hinit in H0. discriminate H0.
  - exact (wf_amc A HW).
  - exact (wf_am A HW).
  - exact (wf_atail A HW).
  - exact (wf_ahead A HW).
  - exact (wf_fl_head A HW).
  - intros sc Hsc. rewrite cupd_other by discriminate. exact (wf_act_head A HW sc Hsc).
  - intros k. unfold cupd. destruct (cslot_eq_dec k KBrk); [lia | exact (wf_ctx_nonneg A HW k)].
  - exact (wf_shift A HW).
  - exact (wf_noarea_shift A HW).
  - intros H0. exfalso. exact (Hv H0).
  - exact (wf_mblocks_len A HW).
  - exact (wf_shift_mblocks A HW).
  - exact (wf_shift_acct A HW).
Qed.

(* [comment removed for export] *)
Lemma WF_upd_aac1 : forall A, WF A -> a_ctx A KInit = 1 -> a_ctx A KBrk <> 0 -> a_ctx A KAac = 0 ->
  WF (actx_upd A KAac 1).
Proof.
  intros A HW Hinit Hbrk Haac. unfold actx_upd. pose proof (wf_mblocks_len A HW) as Hml. rewrite Haac in Hml. cbn in Hml.
  apply WF_set_ctx; try exact HW; rewrite ?cupd_same; rewrite ?cupd_other by discriminate.
  - exact (wf_init A HW).
  - intros H0. rewrite Hinit in H0. discriminate H0.
  - exact (wf_amc A HW).
  - exact (wf_am A HW).
  - exact (wf_atail A HW).
  - exact (wf_ahead A HW).
  - exact (wf_fl_head A HW).
  - intros sc Hsc. rewrite cupd_other by discriminate. exact (wf_act_head A HW sc Hsc).
  - intros k. unfold cupd. destruct (cslot_eq_dec k KAac); [lia | exact (wf_ctx_nonneg A HW k)].
  - exact (wf_shift A HW).
  - intros _ H1. discriminate H1.
  - intros H0. exfalso. exact (Hbrk H0).
  - cbn. lia.
  - exact (wf_shift_mblocks A HW).
  - (* [comment removed for export] *)
    destruct (wf_shift_acct A HW) as (Q1 & Q2 & Q3). rewrite Haac in Q1. repeat split; [lia | exact Q2 | exact Q3].
Qed.

Lemma VMall_actx_upd : forall A k v h, VMall A h -> VMall (actx_upd A k v) h.
Proof. intros A k v h H. exact H. Qed.

(* [comment removed for export] *)
Section AddMBlock.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variables (c l sh : Z).
  Hypothesis Hsh : a_ctx A KShift = sh.
  Hypothesis Haac0 : a_ctx A KAac = 0.
  Hypothesis Hinit : a_ctx A KInit = 1.
  Hypothesis Hbrk : a_ctx A KBrk <> 0.
  Hypothesis Hc : 0x1000 <= c.
  Hypothesis Hl : l = 2 ^ (sh + 13).
  Hypothesis Hce : c + l <= alloc_ceiling.

  Definition mb_n : Z := 2 ^ (sh + 1).
  Definition mb_ctx : ctx_rec := cupd (cupd (cupd (a_ctx A) KAac (mb_n - 1)) KShift (sh + 1)) KAareas (c + 4096).
  Definition mbA : astate := set_ctx (set_mblocks A ((c, l) :: a_mblocks A)) mb_ctx.

  Lemma mb_sh : 0 <= sh <= 34.
  Proof.
    pose proof (wf_ctx_nonneg A HW KShift) as H0. rewrite Hsh in H0. split; [exact H0|]. ceil.
    destruct (Z.le_gt_cases sh 34) as [L|L]; [exact L|]. exfalso.
    assert (2 ^ 48 <= 2 ^ (sh + 13)) by (apply Z.pow_le_mono_r; lia). lia.
  Qed.

  Lemma mb_l : l = 4096 * mb_n /\ 2 <= mb_n /\ 8192 <= l.
  Proof.
    pose proof mb_sh as [S0 S1]. unfold mb_n. rewrite Hl.
    replace (sh + 13) with (12 + (sh + 1)) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 12) with 4096.
    assert (2 ^ 1 <= 2 ^ (sh + 1)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 1) with 2 in H. lia.
  Qed.

  Lemma mb_ctx_other : forall k, k <> KAac -> k <> KShift -> k <> KAareas -> mb_ctx k = a_ctx A k.
  Proof. intros k H1 H2 H3. unfold mb_ctx. rewrite !cupd_other by assumption. reflexivity. Qed.
  Lemma mb_ctx_aac : mb_ctx KAac = mb_n - 1.
  Proof. unfold mb_ctx. rewrite !cupd_other by discriminate. apply cupd_same. Qed.
  Lemma mb_ctx_shift : mb_ctx KShift = sh + 1.
  Proof. unfold mb_ctx. rewrite cupd_other by discriminate. apply cupd_same. Qed.
  Lemma mb_ctx_aareas : mb_ctx KAareas = c + 4096.
  Proof. unfold mb_ctx. apply cupd_same. Qed.

  Theorem WF_mbA : WF mbA.
  Proof.
    pose proof mb_sh as [S0 S1]. pose proof mb_l as (L1 & L2 & L3).
    pose proof (wf_mblocks_len A HW) as Hml. rewrite Haac0 in Hml. cbn [Z.eqb] in Hml.
    pose proof (wf_shift_mblocks A HW) as Hsm. rewrite Hsh in Hsm.
    pose proof HW as W. destruct W as [wf_areas_nodup0 wf_areas_al0 wf_meta_dom0 wf_init0 wf_uninit0 wf_amc0 wf_am0 wf_atail0 wf_ahead0 wf_avail_zero0 wf_free_zero0 wf_fl_nodup0 wf_fl_head0 wf_fl_mem0 wf_fl_dll0 wf_grp0 wf_live0 wf_nested0 wf_nested_parent0 wf_grp_root0 wf_laminar0 wf_act_head0 wf_act_nodup0 wf_act_dll0 wf_act_mem0 wf_unlinked0 wf_act_nonhead0 wf_act630 wf_disj_area_grp0 wf_disj_grp_grp0 wf_grp_mem_inj0 wf_live_map0 wf_span0 wf_single0 wf_inactive0 wf_partial0 wf_ctx_nonneg0 wf_nested_small0 wf_reusable0 wf_cover0 wf_shift0 wf_noarea_shift0 wf_brk00 wf_stride200 wf_pages_al0 wf_disj_page_area0 wf_disj_page_grp0 wf_partial_sc0 wf_mblocks_len0 wf_mblocks_sz0 wf_shift_mblocks0 wf_shift_acct0].
    constructor; cbn [a_ctx a_areas a_meta a_freelist a_active a_pages a_brk_lo a_live a_mblocks a_xmaps set_ctx set_mblocks mbA];
      rewrite ?mb_ctx_aac, ?mb_ctx_shift, ?mb_ctx_aareas; rewrite ?mb_ctx_other by discriminate; try assumption.
    - (* [comment removed for export] *) intros H0. rewrite Hinit in H0. discriminate H0.
    - (* [comment removed for export] *) intros k. unfold mb_ctx, cupd.
      destruct (cslot_eq_dec k KAareas); [lia|]. destruct (cslot_eq_dec k KShift); [lia|]. destruct (cslot_eq_dec k KAac); [lia|]. apply wf_ctx_nonneg0.
    - (* [comment removed for export] *) lia.
    - (* [comment removed for export] *) intros _ H1. exfalso. lia.
    - (* [comment removed for export] *) intros H0. exfalso. exact (Hbrk H0).
    - (* [comment removed for export] *) cbn [length]. rewrite Nat2Z.inj_succ. destruct (mb_n - 1 =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia].
    - (* [comment removed for export] *) intros c0 l0 [E | Hin].
      + injection E as <- <-. cbn [length]. rewrite Nat2Z.inj_succ. split; [exact Hc|]. split; [| exact Hce].
        split; [lia|]. rewrite Hl. apply Z.pow_le_mono_r; lia.
      + destruct (wf_mblocks_sz0 c0 l0 Hin) as (M1 & M2 & M3). cbn [length]. rewrite Nat2Z.inj_succ.
        split; [exact M1|]. split; [| exact M3]. split; [lia|].
        eapply Z.le_trans; [apply (proj2 M2)|]. apply Z.pow_le_mono_r; lia.
    - (* [comment removed for export] *) cbn [length]. rewrite Nat2Z.inj_succ. lia.
    - (* [comment removed for export] *)
      destruct wf_shift_acct0 as (Q1 & Q2 & Q3). rewrite Hsh in Q1, Q2, Q3. rewrite Haac0 in Q1.
      assert (P2 : 2 ^ (sh + 1 + 1) = 2 * 2 ^ (sh + 1)) by (rewrite (Z.pow_add_r 2 (sh + 1) 1) by lia; lia).
      cbn [length]. rewrite Nat2Z.inj_succ. unfold mb_n. rewrite P2. repeat split; lia.
  Qed.

  Lemma has_mbA : forall f, has mbA f ->
    (exists k, cvalid k /\ f = FCT (caddr k) (clen k) (mb_ctx k)) \/
    (has A f /\ ~ has_ctx A f).
  Proof.
    intros f Hf. unfold mbA in Hf.
    destruct (has_set_ctx (set_mblocks A ((c, l) :: a_mblocks A)) mb_ctx f Hf) as [Hk | [(Har & E) | [(pg & Hpg & ->) | Hrest]]].
    - left. exact Hk.
    - right. destruct Har as (pg & Hpg & ->). cbn [a_areas a_ctx set_mblocks] in Hpg |- *. split.
      + right; left. exists pg. auto.
      + intros (k & Hk & Ek). pose proof (nonctx_fact_avoids_ctx A HW (FCT pg 8 (a_ctx A KSecret)) ltac:(left; exists pg; auto) k Hk) as X.
        injection Ek as E1 E2 E3. cbn [f_a f_n] in X. pose proof (ctx_slot_range k Hk) as (C1 & C2 & C3). lia.
    - right. cbn [a_areas set_mblocks] in Hpg. rewrite mb_ctx_other by discriminate. split.
      + right; left. exists pg. auto.
      + intros (k & Hk & Ek). pose proof (nonctx_fact_avoids_ctx A HW (FCT pg 8 (a_ctx A KSecret)) ltac:(left; exists pg; auto) k Hk) as X.
        injection Ek as E1 E2 E3. cbn [f_a f_n] in X. pose proof (ctx_slot_range k Hk) as (C1 & C2 & C3). lia.
    - right. assert (Hold : has_meta A f \/ has_grp A f) by exact Hrest. split.
      + destruct Hold as [Hm | Hg]; [right; right; left; exact Hm | right; right; right; exact Hg].
      + intros (k & Hk & Ek). pose proof (nonctx_fact_avoids_ctx A HW f ltac:(right; exact Hold) k Hk) as X.
        rewrite Ek in X. cbn [f_a f_n] in X. pose proof (ctx_slot_range k Hk) as (C1 & C2 & C3). lia.
  Qed.

  Lemma dom_mbA : forall x, dom mbA x <-> dom A x.
  Proof. intros x. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma Rep_mbA : forall m0 m,
    RepW A m0 [FCT (caddr KAareas) (clen KAareas) (c + 4096); FCT (caddr KShift) (clen KShift) (sh + 1);
               FCT (caddr KAac) (clen KAac) (mb_n - 1)] m ->
    Rep mbA m.
  Proof.
    intros m0 m RW. pose proof mb_sh as [S0 S1]. pose proof mb_l as (L1 & L2 & L3). ceil.
    apply (repw_final A mbA m0 _ m RW).
    - intros x b (f & Hf & [Hx ->]).
      destruct (has_mbA f Hf) as [(k & Hk & ->) | [Hold Hnc]]; cbn [f_a f_n f_v] in *.
      + destruct (cslot_eq_dec k KAareas) as [-> | N1].
        { left. rewrite mb_ctx_aareas. rewrite wlook_hit by (cbn [f_a f_n]; lia). reflexivity. }
        destruct (cslot_eq_dec k KShift) as [-> | N2].
        { left. rewrite mb_ctx_shift. pose proof (ctx_slot_disj KShift KAareas I I ltac:(discriminate)) as D1.
          rewrite wlook_skip by (cbn [f_a f_n]; lia). rewrite wlook_hit by (cbn [f_a f_n]; lia). reflexivity. }
        destruct (cslot_eq_dec k KAac) as [-> | N3].
        { left. rewrite mb_ctx_aac. pose proof (ctx_slot_disj KAac KAareas I I ltac:(discriminate)) as D1.
          pose proof (ctx_slot_disj KAac KShift I I ltac:(discriminate)) as D2.
          rewrite !wlook_skip by (cbn [f_a f_n]; lia). rewrite wlook_hit by (cbn [f_a f_n]; lia). reflexivity. }
        right. rewrite (mb_ctx_other k N3 N2 N1).
        pose proof (ctx_slot_disj k KAareas Hk I N1) as D1. pose proof (ctx_slot_disj k KShift Hk I N2) as D2. pose proof (ctx_slot_disj k KAac Hk I N3) as D3.
        split; [rewrite !wlook_skip by (cbn [f_a f_n]; lia); reflexivity|].
        exists (FCT (caddr k) (clen k) (a_ctx A k)). split; [left; exists k; auto | split; [exact Hx | reflexivity]].
      + right.
        assert (AV : forall k, cvalid k -> f_a f + f_n f <= caddr k \/ caddr k + clen k <= f_a f).
        { intros k Hk. apply (nonctx_fact_avoids_ctx A HW f); [| exact Hk].
          destruct Hold as [Hcx | Hr]; [exfalso; exact (Hnc Hcx) | exact Hr]. }
        pose proof (AV KAareas I) as D1. pose proof (AV KShift I) as D2. pose proof (AV KAac I) as D3.
        split; [rewrite !wlook_skip by (cbn [f_a f_n]; lia); reflexivity|].
        exists f. split; [exact Hold | split; [exact Hx | reflexivity]].
    - intros x Hx. exact Hx.
  Qed.

  (* [comment removed for export] *)
  Lemma VMok_mbA : forall h (cw lw : word),
    VMok A h -> VMcore A (vm_noacc cw lw h) -> u cw = c -> u lw = l -> page_aligned c ->
    VMok mbA (vm_noacc cw lw h).
  Proof.
    intros h cw lw HVo HVc Ecw Elw Hal. pose proof mb_sh as [S0 S1]. pose proof mb_l as (L1 & L2 & L3). ceil.
    pose proof HVo as [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vtop].
    apply VMcore_ok.
    - apply (VMcore_same A mbA _ HVc); [| reflexivity | reflexivity]. intros ma mt aib sl Hma Hr. exact Hma.
    - unfold vm_noacc. apply (VMall_cons A mbA h); cbn [fst snd a_meta a_mblocks a_xmaps mbA set_ctx set_mblocks].
      + exact Vall. + reflexivity. + lia. + reflexivity.
      + intros c0 l0 Hin. right. exact Hin.
      + right. exists c, l. split; [left; reflexivity | lia].
    - cbn [a_ctx a_areas mbA set_ctx set_mblocks vm_brk vm_start_brk vm_noacc]. rewrite mb_ctx_other by discriminate.
      split; [intros H0; exfalso; exact (Hbrk H0) | exact (proj2 Vspan)].
    - cbn [a_ctx mbA set_ctx set_mblocks vm_brk vm_start_brk vm_noacc]. rewrite mb_ctx_other by discriminate. exact Vb.
    - cbn [a_ctx mbA set_ctx set_mblocks vm_maps vm_noaccess vm_noacc]. rewrite mb_ctx_aac, mb_ctx_aareas. intros _.
      assert (MC : forall l0, map_contains ((cw, lw) :: l0) (Z_to_bv 64 (c + 4096)) (Z_to_bv 64 (4096 * (mb_n - 1))) = true).
      { intros l0. unfold map_contains. cbn [existsb fst snd]. rewrite Ecw, Elw, !uZ by lia.
        rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
      split; [unfold page_aligned in *; rewrite <- Zplus_mod_idemp_l, Hal; reflexivity|].
      split; [lia|]. split; apply MC.
  Qed.
End AddMBlock.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma UsOK_transport : forall A A', gsame A A' -> a_areas A' = a_areas A -> UsOK A -> UsOK A'.
Proof.
  intros A A' HG Ea HU sc Hsc. rewrite (gs_ctx A A' HG (KUsage sc) I Hsc).
  rewrite (usage_of_ext A A' sc Ea); [exact (HU sc Hsc)|].
  intros ma. unfold meta_usage.
  destruct (a_meta A ma) as [mt|] eqn:E.
  - destruct (mt_role mt) as [| | |aib sl] eqn:Er.
    + destruct (a_meta A' ma) as [mt'|] eqn:E'; [| reflexivity].
      destruct (mt_role mt') as [| | |aib' sl'] eqn:Er'; try reflexivity.
      rewrite (gs_grp_back A A' HG ma mt' aib' sl' E' Er') in E. injection E as ->. rewrite Er' in Er. discriminate Er.
    + destruct (a_meta A' ma) as [mt'|] eqn:E'; [| reflexivity].
      destruct (mt_role mt') as [| | |aib' sl'] eqn:Er'; try reflexivity.
      rewrite (gs_grp_back A A' HG ma mt' aib' sl' E' Er') in E. injection E as ->. rewrite Er' in Er. discriminate Er.
    + destruct (a_meta A' ma) as [mt'|] eqn:E'; [| reflexivity].
      destruct (mt_role mt') as [| | |aib' sl'] eqn:Er'; try reflexivity.
      rewrite (gs_grp_back A A' HG ma mt' aib' sl' E' Er') in E. injection E as ->. rewrite Er' in Er. discriminate Er.
    + rewrite (gs_grp A A' HG ma mt aib sl E Er). rewrite Er. reflexivity.
  - destruct (a_meta A' ma) as [mt'|] eqn:E'; [| reflexivity].
    destruct (mt_role mt') as [| | |aib' sl'] eqn:Er'; try reflexivity.
    rewrite (gs_grp_back A A' HG ma mt' aib' sl' E' Er') in E. discriminate E.
Qed.

Lemma got_meta_pre : forall A0 A D A' m, gsame A0 A -> got_meta A D A' m -> got_meta A0 D A' m.
Proof.
  intros A0 A D A' m HG [G1 G2 G3 G4 G5 G6 G7 G8]. constructor; auto. exact (gsame_trans _ _ _ HG G7).
Qed.

(* [comment removed for export] *)
Lemma freelist_nil_of_fmh0 : forall A, WF A -> a_ctx A KFmh = 0 -> a_freelist A = [].
Proof.
  intros A HW H0. pose proof (wf_fl_head A HW) as Hh. rewrite H0 in Hh.
  destruct (a_freelist A) as [|x l] eqn:E; [reflexivity|]. exfalso. cbn in Hh.
  destruct (proj1 (wf_fl_mem A HW x) ltac:(rewrite E; left; reflexivity)) as (mt & Hx & _).
  destruct (proj1 (wf_meta_dom A HW x) ltac:(rewrite Hx; discriminate)) as (pg & k & Hpg & Hk & Ex).
  destruct (wf_areas_al A HW pg Hpg) as [_ (R1 & _)]. unfold meta_addr in Ex. llia.
Qed.

End WithLayout.

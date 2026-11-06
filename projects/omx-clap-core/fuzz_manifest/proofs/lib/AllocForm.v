(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCut.v, with its module paths changed; 178 of its 317 lines of code are new or changed and 323 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0s YK0i YM06 YP09 YM05 YK15 YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO16 YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK1j.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO10 YO0s YO0u YO15 YN03 YN2b YN33.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract AllocSlots AllocCut AllocRealloc AllocReallocOK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Record FormLaws (F : ResForm) : Prop := {
  fl_II : forall A b, rf_ok F A b -> II A;
  fl_n : forall b n, rf_room F b n -> 0 <= n < 2 ^ 62 /\ size_overflows n = false;
  fl_ok04 : forall A b n, WF A -> rf_ok F A b -> rf_room F b n -> ok04 mgrant (malloc n A);
  fl_malloc : forall A b n tr r A', WF A -> rf_ok F A b -> rf_room F b n -> cpath04 (malloc n A) tr (r, A') ->
    (exists q, r = Some q) /\ rf_ok F A' (rf_malloc F b n);
  fl_free : forall A b p n tr u A', WF A -> In (p, n) (user_blocks A) -> rf_ok F A b ->
    cpath04 (free (Some p) A) tr (u, A') -> rf_ok F A' (rf_free F b n);
  fl_realloc_ok04 : forall A b p k n, WF A -> In (p, k) (user_blocks A) -> rf_ok F A b -> rf_room F b n ->
    ok04 mgrant (realloc (Some p) n A);
  fl_realloc : forall A b p k n tr r A', WF A -> In (p, k) (user_blocks A) -> rf_ok F A b -> rf_room F b n ->
    cpath04 (realloc (Some p) n A) tr (r, A') -> (exists q, r = Some q) /\ rf_ok F A' (rf_realloc F b k n)
}.

Lemma sb_realloc_ok04 A b p k n : WF A -> In (p, k) (user_blocks A) -> res_ok_slots A b -> room_slots b n ->
  ok04 mgrant (realloc (Some p) n A).
Proof.
  intros HW Hin HR HRm.
  exact (realloc_ok04 A p k n HW Hin (proj1 HR) (proj1 (room_slots_n b n HRm)) (slots_room4 A b n HW HR HRm)
    (room_slots_req b n HRm)).
Qed.

Lemma sb_realloc A b p k n tr r A' : WF A -> In (p, k) (user_blocks A) -> res_ok_slots A b -> room_slots b n ->
  cpath04 (realloc (Some p) n A) tr (r, A') -> (exists q, r = Some q) /\ res_ok_slots A' (sb_realloc b k n).
Proof.
  intros HW Hin HR HRm Hp.
  pose proof (room_slots_n b n HRm) as [Hn Ov].
  destruct (realloc_cpath04_some A p k n tr r A' HW Hin Ov Hp) as [q ->].
  pose proof (realloc_II A p k n tr (Some q) A' HW Hin (proj1 HR) Hn (slots_room4 A b n HW HR HRm) (room_slots_req b n HRm) Hp) as II'.
  split; [exists q; reflexivity|].
  exact (proj2 (realloc_slots_step A b p k n tr (Some q) A' HW Hin HR HRm Hp II')).
Qed.

Lemma sb_laws : FormLaws sb_form.
Proof.
  split.
  - intros A b H. exact (proj1 H).
  - exact room_slots_n.
  - exact malloc_slots_ok04.
  - exact malloc_slots_step.
  - exact free_slots_step.
  - exact sb_realloc_ok04.
  - exact sb_realloc.
Qed.

Definition realloc_safe_p : Prop :=
  forall A p k n, WF A -> In (p, k) (user_blocks A) -> 0 <= n < 2 ^ 62 -> safe (realloc (Some p) n A).

Lemma regions_grow_realloc A p k n tr r A' : WF A -> In (p, k) (user_blocks A) -> 0 <= n ->
  cpath04 (realloc (Some p) n A) tr (r, A') -> (length (st_regions A) <= length (st_regions A'))%nat.
Proof.
  intros HW Hin Hn Hp.
  destruct (ra_cases canswer04 A p k n tr r A' HW Hin (rpath_cpath04 _ _ _ Hp)) as [[_ ->]|(g & am & i & fr & _ & _ & _ & _ & _ & _ & C)];
    [lia|].
  destruct C as [(_ & _ & ->)|[(_ & _ & _ & _ & ->)|[(_ & _ & _ & _ & ->)|(tr' & Hm)]]].
  - unfold upd_meta. cbn. lia.
  - unfold upd_meta. cbn. lia.
  - unfold rm_state, rm_mid, upd_meta. cbn [st_regions set_regions set_metas]. rewrite length_lupd, length_app. cbn [length]. lia.
  - destruct (ra_move canswer04 p n A tr' r A' Hm) as (tr1 & q & s1 & H1 & Hq).
    pose proof (cpath04_rpath _ _ _ H1) as H1'.
    pose proof (regions_grow_malloc A n tr1 q s1 HW Hn H1') as G1.
    destruct q as [q|]; [|destruct Hq as [_ ->]; exact G1].
    destruct Hq as [_ (tr2 & H2)].
    pose proof (malloc_wf A n tr1 (Some q) s1 HW Hn (cpath04_yields _ _ _ H1')) as HW1.
    destruct (malloc_blocks A n tr1 (Some q) s1 HW Hn (cpath04_yields _ _ _ H1')) as (l1 & l2 & E1 & E2 & _).
    pose proof (in_after_malloc A s1 l1 l2 q n (p, k) E1 E2 Hin) as Hin1.
    pose proof (regions_grow_free s1 p k tr2 A' HW1 Hin1 (cpath04_rpath _ _ _ H2)) as G2. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.
Let segs := ms_segs B.
Variable F : ResForm.
Hypothesis FL : FormLaws F.

Theorem malloc_SR_form :
  malloc_realizes B MR ->
  forall L A regs mem md n b,
  call_pre B MR L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> rf_ok F A b -> rf_room F b n ->
  SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
    (fun c' => exists p A' tr, cpath04 (malloc n A) tr (Some p, A') /\
       malloc_leaf B MR L A regs mem md n (Some p, A') c' /\ rf_ok F A' (rf_malloc F b n)).
Proof.
  intros HM L A regs mem md n b Hpre Hn HR HRm.
  assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
  pose proof (fl_n F FL b n HRm) as [Hn62 _].
  eapply SR_mono; [apply (malloc_SR_ok B MR HM L A regs mem md n Hpre Hn Hn62 (fl_ok04 F FL A b n HW HR HRm))|].
  intros c' ([r A'] & tr & Hp & HL).
  destruct (fl_malloc F FL A b n tr r A' HW HR HRm Hp) as [[q ->] HR'].
  exists q, A', tr. auto.
Qed.

Theorem free_SR_form :
  free_realizes B MR ->
  forall L A regs mem md p n b,
  call_pre B MR L A regs mem md -> In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
  rf_ok F A b ->
  SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
    (fun c' => exists A' tr, cpath04 (free (Some p) A) tr (tt, A') /\
       free_leaf B MR L A regs mem md p n (tt, A') c' /\ rf_ok F A' (rf_free F b n)).
Proof.
  intros HF L A regs mem md p n b Hpre Hin Hp HR.
  assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
  pose proof (free_reqs_ok A p n HW Hin) as RQ.
  pose proof (OK4_free (Some p) A RQ (fl_II F FL A b HR)) as [HOK _].
  eapply SR_mono; [apply (free_SR_ok B MR HF L A regs mem md p n Hpre Hin Hp HOK)|].
  intros c' ([[] A'] & tr & Hcp & HL). exists A', tr. split; [exact Hcp|]. split; [exact HL|].
  exact (fl_free F FL A b p n tr tt A' HW Hin HR Hcp).
Qed.
End a.

Lemma blocks_repl : forall (L L' : layout) (A A' : astate) p k q n l1 l2 m1 m2,
  (forall p0 n0, In (p0, n0) (user_blocks A) -> In (p0, n0) (user_blocks A') -> ptr_addr L' p0 = ptr_addr L p0) ->
  user_blocks A = l1 ++ (p, k) :: l2 -> m1 ++ m2 = l1 ++ l2 -> user_blocks A' = m1 ++ (q, n) :: m2 ->
  exists b1 b2 c1 c2, blocks L A = b1 ++ (ptr_addr L p, k) :: b2 /\ blocks L' A' = c1 ++ (ptr_addr L' q, n) :: c2 /\
    c1 ++ c2 = b1 ++ b2.
Proof.
  intros L L' A A' p k q n l1 l2 m1 m2 Hs E1 E3 E2.
  exists (map (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l1), (map (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l2),
    (map (fun b : sptr * Z => (ptr_addr L' (fst b), snd b)) m1), (map (fun b : sptr * Z => (ptr_addr L' (fst b), snd b)) m2).
  unfold blocks. rewrite E1, E2, !map_app. cbn [map fst snd]. split; [reflexivity|]. split; [reflexivity|].
  rewrite <- !map_app, E3. apply (blocks_map_stable L L' A A' (l1 ++ l2) Hs).
  - intros x Hx. rewrite E1. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx].
  - intros x Hx. rewrite E2. rewrite <- E3 in Hx.
    apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx].
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.
Variable F : ResForm.
Hypothesis FL : FormLaws F.

Theorem malloc_contract_form : AllocExtra B MR -> ro_apart_b B = true -> malloc_contract_r B API F.
Proof using FL.
intros AX HB L A regs mem md n b Hpre Hro Hn HR HRm.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
assert (Hn0 : 0 <= n) by (pose proof (fl_n F FL b n HRm) as [[R0 _] _]; exact R0).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
eapply SR_mono.
{ exact (malloc_SR_form B MR F FL (aa_malloc API) L A regs mem md n b Hpre Hn HR HRm). }
intros c' (p & A' & tr & Hp & (L' & regs' & mem' & md' & -> & Hpost & Ha0 & Hnz & (l1 & l2 & E1 & E2) & _) & HRA').
cbn [fst snd] in *.
assert (Hin : In (p, n) (user_blocks A')) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
assert (Hsub : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')).
{ intros q k Hq. rewrite E2 in Hq. rewrite E1. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff;
[left; exact Hq | right; right; exact Hq]. }
pose proof Hpost as (HMR & HW' & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
pose proof (proj1 (call_post_k_alloc B MR L A regs mem md _ L' A' regs' mem' md') Hpost) as Hpk.
unfold malloc_ret_r. exists L', A', regs', mem', md', (ptr_addr L' p).
split; [reflexivity|].
split; [exact Hpk|].
split; [exact Ha0|]. split; [exact Hnz|].
split; [exact (mr_blocks_aligned B MR (aa_laws API) _ _ _ _ _ _ HMR Hin)|].
split.
{ destruct (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin) as [R1 R2].
split; [exact R1|]. split; [exact R2|]. intros i Hi. exact (ax_blocks_img AX _ _ _ _ _ _ i HMR Hin Hi). }
split; [exact (blocks_add L L' A A' p n l1 l2 Hstab E1 E2)|].
split; [apply (kept_of_post B L A A' mem mem'); [exact Hkeep | intros q k Hq _; exact (Hsub q k Hq)]|].
split; [exact (ro_agree_post B MR ALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a (F0 : False) => match F0 with end) Hpk Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [exact (YI04.init_done_of_block A' (p, n) HW' Hin)|].
split; [exact (regions_grow_malloc A n tr (Some p) A' HW Hn0 Hp)|].
exact HRA'.
Qed.

Theorem free_contract_form : AllocExtra B MR -> ro_apart_b B = true -> free_contract_r B API F.
Proof using FL.
intros AX HB L A regs mem md p n b Hpre Hro Hin Hp HR.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
eapply SR_mono.
{ exact (free_SR_form B MR F FL (aa_free API) L A regs mem md p n b Hpre Hin Hp HR). }
intros c' (A' & tr & Hcp & (L' & regs' & mem' & md' & -> & Hpost & (l1 & l2 & E1 & E2)) & HRA').
cbn [fst snd] in *.
assert (Hsub : forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')).
{ intros q k Hq Hne. rewrite E1 in Hq. rewrite E2. apply in_app_iff in Hq as [Hq|[Hq|Hq]]; apply in_app_iff;
[left; exact Hq | injection Hq as -> _; exfalso; exact (Hne eq_refl) | right; exact Hq]. }
pose proof Hpost as (HMR & _ & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
pose proof (proj1 (call_post_k_alloc B MR L A regs mem md _ L' A' regs' mem' md') Hpost) as Hpk.
exists L', A', regs', mem', md'. split; [reflexivity|]. split; [exact Hpost|].
split; [exact (blocks_del L L' A A' p n l1 l2 Hstab E1 E2)|].
split.
{ apply (kept_of_post B L A A' mem mem'); [exact Hkeep|]. intros q k Hq Hg. apply Hsub; [exact Hq|]. intros ->. exact (Hg eq_refl). }
split; [exact (ro_agree_post B MR ALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a Ha => ex_intro _ p (ex_intro _ n (conj Hin Ha))) Hpk Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [intros Hd; exact (free_keeps_init_done (Some p) A tr tt A' Hd (cpath04_yields _ _ _ Hcp))|].
split; [exact (regions_grow_free A p n tr A' HW Hin Hcp)|].
exact HRA'.
Qed.

Theorem calloc_contract_form : AllocExtra B MR -> ro_apart_b B = true -> forall pc, calloc_contract_r B API F pc.
Proof using FL.
intros AX HB pc L A regs mem md m n b Hpre Hro Hm Hn Hrm Hrn Hsm Hpc HR HRm.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
eapply SR_mono.
{ apply (mreal_SR04 segs _ _ _ (aa_calloc API pc L A regs mem md m n Hpc Hpre Hm Hn Hrm Hrn Hsm Hro)).
- apply malloc_safe; [exact HW | nia].
- exact (fl_ok04 F FL A b (m * n) HW HR HRm). }
intros c' ([r A'] & tr & Hp & HL).
destruct (fl_malloc F FL A b (m * n) tr r A' HW HR HRm Hp) as [[q ->] HRA'].
destruct HL as (L' & regs' & mem' & md' & -> & Hpost & Ha0 & Hnz & (l1 & l2 & E1 & E2) & Hz). cbn [fst snd] in *.
assert (Hin : In (q, m * n) (user_blocks A')) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
assert (Hsub : forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')).
{ intros p k Hq. rewrite E2 in Hq. rewrite E1. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff;
[left; exact Hq | right; right; exact Hq]. }
pose proof Hpost as (HMR & HW' & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
split.
- unfold malloc_ret_r. exists L', A', regs', mem', md', (ptr_addr L' q).
split; [reflexivity|]. split; [exact Hpost|]. split; [exact Ha0|]. split; [exact Hnz|].
split; [exact (mr_blocks_aligned B MR (aa_laws API) _ _ _ _ _ _ HMR Hin)|].
split.
{ destruct (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin) as [R1 R2].
split; [exact R1|]. split; [exact R2|]. intros i Hi. exact (ax_blocks_img AX _ _ _ _ _ _ i HMR Hin Hi). }
split; [exact (blocks_add L L' A A' q (m * n) l1 l2 Hstab E1 E2)|].
split; [apply (kept_of_post B L A A' mem mem'); [exact Hkeep | intros p k Hq _; exact (Hsub p k Hq)]|].
split; [exact (ro_agree_post B MR CALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a (F0 : False) => match F0 with end) Hpost Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [exact (YI04.init_done_of_block A' (q, m * n) HW' Hin)|].
split; [exact (regions_grow_malloc A (m * n) tr (Some q) A' HW ltac:(nia) Hp)|].
exact HRA'.
- exists (mkst regs' (getr regs 1) mem' (seg_rom segs)), md'. split; [reflexivity|].
intros i Hi. cbn [ms_mem ms_regs mkst]. rewrite Ha0.
pose proof alloc_ceiling_lt as AC.
assert (Hq : 4096 <= ptr_addr L' q /\ ptr_addr L' q + m * n <= alloc_ceiling)
by exact (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin).
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
apply Hz. exact Hi.
Qed.

Theorem realloc_null_contract_form : AllocExtra B MR -> ro_apart_b B = true -> realloc_null_realizes B MR ->
forall pc, ms_realloc B = Some pc -> realloc_null_contract_r B API F pc.
Proof using FL.
intros AX HB HRz pc Hpc L A regs mem md n b Hpre Hro H10 H11 HR HRm.
destruct (fl_n F FL b n HRm) as [Hn _].
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
eapply SR_mono.
{ apply (mreal_SR04 segs _ _ _ (HRz pc L A regs mem md n Hpc Hpre H10 H11 Hn)).
- exact (malloc_safe A n HW ltac:(lia)).
- exact (fl_ok04 F FL A b n HW HR HRm). }
intros c' ([r A'] & tr & Hp & HL).
destruct (fl_malloc F FL A b n tr r A' HW HR HRm Hp) as [[q ->] HRA'].
destruct HL as (L' & regs' & mem' & md' & -> & Hpost & Ha0 & Hnz & (l1 & l2 & E1 & E2)). cbn [fst snd] in *.
assert (Hin : In (q, n) (user_blocks A')) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
assert (Hsub : forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')).
{ intros p k Hq. rewrite E2 in Hq. rewrite E1. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff;
[left; exact Hq | right; right; exact Hq]. }
pose proof Hpost as (HMR & HW' & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
unfold malloc_ret_r. exists L', A', regs', mem', md', (ptr_addr L' q).
split; [reflexivity|]. split; [exact Hpost|]. split; [exact Ha0|]. split; [exact Hnz|].
split; [exact (mr_blocks_aligned B MR (aa_laws API) _ _ _ _ _ _ HMR Hin)|].
split.
{ destruct (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin) as [R1 R2].
split; [exact R1|]. split; [exact R2|]. intros i Hi. exact (ax_blocks_img AX _ _ _ _ _ _ i HMR Hin Hi). }
split; [exact (blocks_add L L' A A' q n l1 l2 Hstab E1 E2)|].
split; [apply (kept_of_post B L A A' mem mem'); [exact Hkeep | intros p k Hq _; exact (Hsub p k Hq)]|].
split; [exact (ro_agree_post B MR REALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a (F0 : False) => match F0 with end) Hpost Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [exact (YI04.init_done_of_block A' (q, n) HW' Hin)|].
split; [exact (regions_grow_malloc A n tr (Some q) A' HW ltac:(lia) Hp)|].
exact HRA'.
Qed.

Theorem realloc_contract_form : AllocExtra B MR -> ro_apart_b B = true -> realloc_realizes B MR -> realloc_safe_p ->
  forall pc, ms_realloc B = Some pc -> realloc_contract_r B API F pc.
Proof using FL.
intros AX HB HRr HS pc Hpc L A regs mem md p k n old b Hpre Hro Hin H10 H11 Hold Hlen HR HRm.
destruct (fl_n F FL b n HRm) as [Hn _].
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
eapply SR_mono.
{ apply (mreal_SR04 segs _ _ _ (HRr pc L A regs mem md p k n Hpc Hpre Hin H10 H11 Hn)).
- exact (HS A p k n HW Hin Hn).
- exact (fl_realloc_ok04 F FL A b p k n HW Hin HR HRm). }
intros c' ([r A'] & tr & Hp & HL).
destruct (fl_realloc F FL A b p k n tr r A' HW Hin HR HRm Hp) as [[q ->] HRA'].
destruct HL as (L' & regs' & mem' & md' & -> & Hpost & HM). cbn [fst snd] in *.
destruct HM as (Ha0 & Hnz & (l1 & l2 & m1 & m2 & E1 & E3 & E2) & Hcp).
assert (Hin' : In (q, n) (user_blocks A')) by (rewrite E2; apply in_app_iff; right; left; reflexivity).
assert (Hsub : forall q0 k0, In (q0, k0) (user_blocks A) -> q0 <> p -> In (q0, k0) (user_blocks A')).
{ intros q0 k0 Hq Hne. rewrite E1 in Hq. rewrite E2.
  assert (H12 : In (q0, k0) (l1 ++ l2)).
  { apply in_app_iff in Hq as [Hq|[Hq|Hq]]; apply in_app_iff;
    [left; exact Hq | injection Hq as -> _; exfalso; exact (Hne eq_refl) | right; exact Hq]. }
  rewrite <- E3 in H12. apply in_app_iff in H12 as [H12|H12]; apply in_app_iff; [left; exact H12 | right; right; exact H12]. }
pose proof Hpost as (HMR & HW' & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
exists L', A', regs', mem', md', (ptr_addr L' q).
split; [reflexivity|]. split; [exact Hpost|]. split; [exact Ha0|]. split; [exact Hnz|].
split; [exact (mr_blocks_aligned B MR (aa_laws API) _ _ _ _ _ _ HMR Hin')|].
split.
{ destruct (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin') as [R1 R2].
split; [exact R1|]. split; [exact R2|]. intros i Hi. exact (ax_blocks_img AX _ _ _ _ _ _ i HMR Hin' Hi). }
split; [exact (blocks_repl L L' A A' p k q n l1 l2 m1 m2 Hstab E1 E3 E2)|].
split.
{ apply (kept_of_post B L A A' mem mem'); [exact Hkeep|]. intros q0 k0 Hq Hg. apply Hsub; [exact Hq|]. intros ->. exact (Hg eq_refl). }
split; [exact (ro_agree_post B MR REALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a Ha => ex_intro _ p (ex_intro _ k (conj Hin Ha))) Hpost Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [intros i Hi; rewrite Hcp by lia; apply Hold; lia|].
split; [exact (YI04.init_done_of_block A' (q, n) HW' Hin')|].
split; [exact (regions_grow_realloc A p k n tr (Some q) A' HW Hin (proj1 Hn) Hp)|].
exact HRA'.
Qed.
End c.

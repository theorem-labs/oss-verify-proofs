From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require YO10.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Exec MState PropExec.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c GrantSlotPlan SlotImg
  SlotIntegration SlotGlue.
Import ListNotations.
Local Open Scope Z_scope.


Section St.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis HB : ms_segs B = rsegs.
Hypothesis FA : frame_allocator B API.
Hypothesis Herr : errno_addr B + 4 <= alloc_ceiling.
Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).

Lemma wv_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma nodup_fst : forall (l : list (sptr * Z)) q k k', List.NoDup (map fst l) -> In (q, k) l -> In (q, k') l -> k = k'.
Proof.
  induction l as [|[q0 k0] l IH]; intros q k k' Hnd Hk Hk'; [destruct Hk|].
  cbn [map fst] in Hnd. apply List.NoDup_cons_iff in Hnd as [Hni Hnd'].
  destruct Hk as [Ek|Hk]; destruct Hk' as [Ek'|Hk'].
  - injection Ek as E1 E2. injection Ek' as E3 E4. congruence.
  - injection Ek as E1 E2. subst q0 k0. exfalso. apply Hni. apply (in_map fst l (q, k')). exact Hk'.
  - injection Ek' as E1 E2. subst q0 k0. exfalso. apply Hni. apply (in_map fst l (q, k)). exact Hk.
  - exact (IH q k k' Hnd' Hk Hk').
Qed.

Lemma ptr_sizes : forall A q k k', WF A -> In (q, k) (user_blocks A) -> In (q, k') (user_blocks A) -> k = k'.
Proof. intros A q k k' HW Hk Hk'. exact (nodup_fst _ q k k' (YO10.user_block_ptrs_NoDup A HW) Hk Hk'). Qed.

Lemma rel0_call : forall s s' L A md E L' A' regs' md',
  Rel0 B L0 A0 regs0 mem0 md0 s L A md -> aa_MR API L A (ms_mem s) md ->
  call_post_k B (aa_MR API) ALLOC_STACK L A (ms_regs s) (ms_mem s) md E L' A' regs' (ms_mem s') md' ->
  spZ (ms_regs s) = S0 regs0 - 608 -> alloc_ceiling + SLOT_STACK <= S0 regs0 -> S0 regs0 <= 2 ^ 47 ->
  (forall a, E a -> a < alloc_ceiling /\ ~ in_img B a) ->
  (forall q k, In (q, k) (user_blocks A0) ->
     exists q', In (q', k) (user_blocks A) /\ In (q', k) (user_blocks A') /\ ptr_addr L q' = ptr_addr L0 q) ->
  Rel0 B L0 A0 regs0 mem0 md0 s' L' A' md'.
Proof.
  intros s s' L A md E L' A' regs' md' (OUT & UB & SW & (vm & MD)) HMR HCP Hsp HSc HS47 HE HTR.
  pose proof HCP as (HMR' & _ & _ & _ & Hstab & _ & (vm' & Hvm) & Hfr & Hbk & Hscr).
  pose proof (aa_laws API) as LAWS.
  pose proof FA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbw & _ & _ & _ & AX & _).
  pose proof alloc_ceiling_value as (Hc1 & _).
  assert (Hsc : forall a, scratch_k B ALLOC_STACK (ms_regs s) a ->
            (S0 regs0 - 8800 <= a < S0 regs0 - 608) \/ (errno_addr B <= a < errno_addr B + 4)).
  { intros a [Ha|Ha]; [left; rewrite Hsp in Ha; unfold ALLOC_STACK in Ha; lia | right; exact Ha]. }
  assert (HIGH : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (S0 regs0 - 8800 <= a < S0 regs0 - 608) ->
            YP09.mbyte rsegs (ms_mem s') a = YP09.mbyte rsegs (ms_mem s) a /\
            (YP09.writable_at rsegs (ms_mem s) a <-> YP09.writable_at rsegs (ms_mem s') a)).
  { intros a Ha Hns. rewrite <- HB. apply Hfr.
    - left. exact Ha.
    - intros Ho. pose proof (mr_owned_low B _ LAWS _ _ _ _ a HMR Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS _ _ _ _ a HMR' Ho). lia.
    - intros Hs. destruct (Hsc a Hs) as [H|H]; [exact (Hns H) | lia].
    - intros He. destruct (HE a He). lia. }
  split; [|split; [|split]].
  - intros a Ho. destruct (OUT a Ho) as (E1 & E2). pose proof Ho as (Ha64 & Hcase).
    destruct Hcase as [(Hc & Hns) | [(Hi & Hst & Hctx & Herr') | (q & k & Hq & Hqa)]].
    + destruct (HIGH a ltac:(lia)) as (F1 & F2).
      { intros Hin. apply Hns. left. unfold S0 in Hin. unfold SLOT_STACK. lia. }
      rewrite F1, E1. split; [reflexivity | tauto].
    + assert (Himg : a < 0x51000) by (apply (in_img_rsegs B a HB) in Hi; lia).
      destruct (Hfr a) as (F1 & F2).
      * right. exact Hi.
      * intros [Ho'|Ho']; [apply Hctx; exact (ax_img AX L A _ md a HMR Hi Ho') | exact (Hst Ho')].
      * intros [Ho'|Ho']; [apply Hctx; exact (ax_img AX L' A' _ md' a HMR' Hi Ho') | exact (Hst Ho')].
      * intros Hs. destruct (Hsc a Hs) as [H|H]; [unfold SLOT_STACK in HSc; lia | exact (Herr' H)].
      * intros He. exact (proj2 (HE a He) Hi).
      * rewrite HB in F1, F2. rewrite F1, E1. split; [reflexivity | tauto].
    + destruct (HTR q k Hq) as (q' & Hq' & Hq'' & Hpq').
      assert (Hi : 0 <= a - ptr_addr L q' < k) by lia.
      pose proof (Hbk q' k (a - ptr_addr L q') Hq' Hq'' Hi) as F1.
      replace (ptr_addr L q' + (a - ptr_addr L q')) with a in F1 by lia. rewrite HB in F1.
      assert (W1 : YP09.writable_at rsegs (ms_mem s) a).
      { rewrite <- HB. replace a with (ptr_addr L q' + (a - ptr_addr L q')) by lia.
        apply (Hbw L A _ md (ptr_addr L q') k _ HMR (in_blocks L A q' k Hq') Hi). }
      assert (W2 : YP09.writable_at rsegs (ms_mem s') a).
      { rewrite <- HB. replace a with (ptr_addr L' q' + (a - ptr_addr L q')) by (rewrite (Hstab q' k Hq' Hq''); lia).
        apply (Hbw L' A' _ md' (ptr_addr L' q') k _ HMR' (in_blocks L' A' q' k Hq'') Hi). }
      rewrite F1, E1. split; [reflexivity|]. split; intros _; [exact W2 | apply E2; exact W1].
  - intros q k Hq. destruct (HTR q k Hq) as (q' & Hq' & Hq'' & Hpq').
    exists q'. split; [exact Hq'' | rewrite (Hstab q' k Hq' Hq''); exact Hpq'].
  - intros a Ha. destruct (Z_lt_le_dec a (S0 regs0 - 8800)) as [Hl|Hl];
      [| destruct (Z_lt_le_dec a (S0 regs0 - 608)) as [Hl2|Hl2]].
    + unfold SLOT_STACK in Ha. apply (proj1 (proj2 (HIGH a ltac:(unfold SLOT_STACK in HSc; lia) ltac:(lia)))). apply SW. exact Ha.
    + rewrite <- HB. apply Hscr. left. rewrite Hsp. unfold ALLOC_STACK. lia.
    + unfold SLOT_STACK in Ha. apply (proj1 (proj2 (HIGH a ltac:(unfold SLOT_STACK in HSc; lia) ltac:(lia)))). apply SW. exact Ha.
  - exists vm'. rewrite Hvm, MD. apply wv_twice.
Qed.

Theorem st_malloc_holds : st_malloc_ok B API L0 A0 regs0 mem0 md0.
Proof.
  unfold st_malloc_ok.
  intros x Live nb Post s md L A b owns c' HSx Hsp HSc HS47 (RO & Hfr & Hfc & AS & ER & PB & RL) Hown
    (s' & md' & L' & A' & r & Ec & GP & Hlive & HCP & Hfresh & H16 & Hsplit & Hkept & Hguard & Hub).
  destruct GP as (NP & RO' & Hfr' & Hfc' & AS' & ER' & PB' & LV').
  pose proof AS as (HMR & _). pose proof AS' as (HMR' & _).
  pose proof HCP as (_ & _ & _ & _ & Hstab & _).
  pose proof RL as (_ & UB & _).
  exists s', md', L', A', r.
  split; [exact Ec|]. split; [exact NP|].
  split.
  { split; [rewrite HB in RO'; exact RO'|]. split; [exact Hfr'|]. split; [exact Hfc'|].
    split; [exact AS'|]. split; [exact ER'|]. split; [exact PB'|].
    apply (rel0_call s s' L A md (fun _ => False) L' A' (ms_regs s') md' RL HMR HCP Hsp HSc HS47).
    - intros a [].
    - intros q k Hq. destruct (UB q k Hq) as (q' & Hq' & Hpq').
      exists q'. split; [exact Hq'|]. split; [exact (Hub q' k Hq') | exact Hpq']. }
  split; [exact LV'|].
  split.
  { unfold own_ok. split; [replace (r + nb - r) with nb by lia; exact Hlive|]. split.
    - intros q k Hq. destruct (UB q k Hq) as (q' & Hq' & Hpq'). rewrite <- Hpq'.
      exact (new_block_apart B API L A L' A' (ms_mem s') md' r nb _ _ HMR' Hsplit (in_blocks L A q' k Hq')).
    - intros a Ha. destruct Hfresh as (_ & _ & Hni). replace a with (r + (a - r)) by lia. apply Hni. lia. }
  intros lo hi Hin. destruct (Hown lo hi Hin) as ((q & Hq & Hpq) & H2 & H3).
  unfold own_ok. split; [|split; [exact H2 | exact H3]].
  exists q. split; [exact (Hub q _ Hq)|]. rewrite (Hstab q _ Hq (Hub q _ Hq)). exact Hpq.
Qed.

Theorem st_free_holds : st_free_ok B API L0 A0 regs0 mem0 md0.
Proof.
  unfold st_free_ok.
  intros x Live s0 nb Post s md L A b q owns c' HSx Hsp HSc HS47 (RO & Hfr & Hfc & AS & ER & PB & RL) Hnb
    (Hlv0 & Hap0 & Hni0) Hq Hpq Hown (s' & md' & L' & A' & Ec & GP & HCP & Hsplit & Hkept & Hguard & Hub).
  destruct GP as (NP & RO' & Hfr' & Hfc' & AS' & ER' & PB' & LV').
  pose proof AS as (HMR & HWF & _).
  apply call_post_k_alloc in HCP.
  pose proof HCP as (_ & _ & _ & _ & Hstab & _).
  pose proof (aa_laws API) as LAWS.
  pose proof RL as (_ & UB & _).
  exists s', md', L', A'.
  split; [exact Ec|]. split; [exact NP|].
  split.
  { split; [rewrite HB in RO'; exact RO'|]. split; [exact Hfr'|]. split; [exact Hfc'|].
    split; [exact AS'|]. split; [exact ER'|]. split; [exact PB'|].
    apply (rel0_call s s' L A md (fun a => s0 <= a < s0 + nb) L' A' (ms_regs s') md' RL HMR HCP Hsp HSc HS47).
    - intros a Ha. cbv beta in Ha. split.
      + destruct (mr_blocks_range B _ LAWS L A (ms_mem s) md q nb HMR Hq) as (_ & Hhi). lia.
      + exact (Hni0 a Ha).
    - intros q0 k Hq0. destruct (UB q0 k Hq0) as (q' & Hq' & Hpq').
      exists q'. split; [exact Hq'|]. split; [|exact Hpq'].
      apply Hub; [exact Hq'|]. intros E. subst q'.
      pose proof (ptr_sizes A q k nb HWF Hq' Hq) as Ek.
      destruct (Hap0 q0 k Hq0) as [Hc|Hc]; lia. }
  split; [exact LV'|].
  intros lo hi Hin. destruct (Hown lo hi Hin) as (((q1 & Hq1 & Hpq1) & H2 & H3) & Hne).
  assert (Hq1' : In (q1, hi - lo) (user_blocks A')).
  { apply Hub; [exact Hq1|]. intros E. subst q1. apply Hne. exact (ptr_sizes A q (hi - lo) nb HWF Hq1 Hq). }
  unfold own_ok. split; [|split; [exact H2 | exact H3]].
  exists q1. split; [exact Hq1'|]. rewrite (Hstab q1 _ Hq1 Hq1'). exact Hpq1.
Qed.

End St.

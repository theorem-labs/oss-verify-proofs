From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF FrameCF.
Import ListNotations.
Local Open Scope Z_scope.

(* The slot's running state against its start state: what lib_post_g asks of memory, the allocator and the
   model, for a slot with stack window [S - K, S) and writable globals G. *)

Section SlotInv.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Definition errno_at (a : Z) : Prop := errno_addr B <= a < errno_addr B + 4.

Definition slot_rel (G : list (Z * Z)) (K S : Z) (L0 : layout) (A0 : astate) (mem0 : word -> option byte)
    (md0 : Model) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) : Prop :=
  MR L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
  (exists vm', md = with_vmmaps vm' md0) /\
  (forall q k, In (q, k) (user_blocks A0) -> In (q, k) (user_blocks A) /\ ptr_addr L q = ptr_addr L0 q) /\
  (forall q k i, In (q, k) (user_blocks A0) -> 0 <= i < k ->
     mbyte (ms_segs B) mem (ptr_addr L0 q + i) = mbyte (ms_segs B) mem0 (ptr_addr L0 q + i)) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (S - K <= a < S) -> ~ errno_at a ->
     mbyte (ms_segs B) mem a = mbyte (ms_segs B) mem0 a /\ (writable_at (ms_segs B) mem0 a <-> writable_at (ms_segs B) mem a)) /\
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) -> ~ errno_at a ->
     ~ in_globals G a -> mbyte (ms_segs B) mem a = mbyte (ms_segs B) mem0 a /\ (writable_at (ms_segs B) mem0 a <-> writable_at (ms_segs B) mem a)) /\
  (forall a, (S - K <= a < S) \/ errno_at a -> writable_at (ms_segs B) mem a).

Lemma slot_rel_init : forall G K S L A mem md,
  MR L A mem md -> WF A -> bounded A -> st_init_done A = true ->
  (forall a, (S - K <= a < S) \/ errno_at a -> writable_at (ms_segs B) mem a) ->
  slot_rel G K S L A mem md L A mem md.
Proof.
  intros G K S L A mem md HM HW HB HI HS.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact HI|].
  split; [exists (m_vmmaps md); apply with_vmmaps_self|].
  split; [intros q k Hq; split; [exact Hq | reflexivity]|].
  split; [intros; reflexivity|].
  split; [intros; split; [reflexivity | tauto]|].
  split; [intros; split; [reflexivity | tauto]|].
  exact HS.
Qed.

Lemma slot_rel_not_owned_img : AllocExtra B MR -> forall L A mem md a,
  MR L A mem md -> in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) -> ~ owned B L A a.
Proof.
  intros AX L A mem md a HM Hi Hs Hc [Ho|Ho]; [apply Hc; exact (ax_img AX L A mem md a HM Hi Ho) | exact (Hs Ho)].
Qed.

Lemma slot_rel_call : AllocExtra B MR -> img_low B ->
  forall G K S L0 A0 mem0 md0 L1 A1 mem1 md1 Kc regs1 E L2 A2 regs2 mem2 md2,
  slot_rel G K S L0 A0 mem0 md0 L1 A1 mem1 md1 ->
  call_post_k B MR Kc L1 A1 regs1 mem1 md1 E L2 A2 regs2 mem2 md2 ->
  S - K <= spZ regs1 - Kc -> spZ regs1 <= S -> alloc_ceiling + K <= S -> S <= 2 ^ 64 -> 0 <= Kc ->
  errno_addr B + 4 <= alloc_ceiling ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (S - K <= a < S) -> ~ E a) ->
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) -> ~ errno_at a ->
     ~ in_globals G a -> ~ E a) ->
  (forall a, S - K <= a < S -> ~ (spZ regs1 - Kc <= a < spZ regs1) -> writable_at (ms_segs B) mem2 a \/ ~ E a) ->
  (forall q k, In (q, k) (user_blocks A0) -> In (q, k) (user_blocks A1) -> In (q, k) (user_blocks A2)) ->
  (st_init_done A1 = true -> st_init_done A2 = true) ->
  slot_rel G K S L0 A0 mem0 md0 L2 A2 mem2 md2.
Proof.
  intros AX [HI _] G K S L0 A0 mem0 md0 L1 A1 mem1 md1 Kc regs1 E L2 A2 regs2 mem2 md2
    (M1 & W1 & B1 & I1 & (v1 & D1) & U1 & C1 & H1 & G1 & SW1)
    (M2 & W2 & B2 & Y2 & P2 & RP & (v2 & D2) & F2 & K2 & S2)
    Hlo Hhi Hc HS64 HK Herr EH EI ES HU HI2.
  pose proof alloc_ceiling_lt as Hcl.
  assert (NOh : forall L A mem md a, MR L A mem md -> alloc_ceiling <= a -> ~ owned B L A a).
  { intros L A mem md a HM Ha Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho). lia. }
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|]. split; [exact (HI2 I1)|].
  split; [exists v2; rewrite D2, D1; apply with_vmmaps_twice|].
  split.
  { intros q k Hq. destruct (U1 q k Hq) as [Hq1 Hp1]. pose proof (HU q k Hq Hq1) as Hq2.
    split; [exact Hq2|]. rewrite (P2 q k Hq1 Hq2). exact Hp1. }
  split.
  { intros q k i Hq Hi. destruct (U1 q k Hq) as [Hq1 Hp1]. pose proof (HU q k Hq Hq1) as Hq2.
    rewrite <- Hp1. rewrite (K2 q k i Hq1 Hq2 Hi). rewrite Hp1. exact (C1 q k i Hq Hi). }
  split.
  { intros a Ha Hs He.
    destruct (F2 a (or_introl Ha) (NOh _ _ _ _ a M1 ltac:(lia)) (NOh _ _ _ _ a M2 ltac:(lia))
      ltac:(unfold scratch_k; intros [Hx|Hx]; [apply Hs; lia | exact (He Hx)]) (EH a Ha Hs)) as [E1 E2].
    destruct (H1 a Ha Hs He) as [E3 E4]. split; [congruence | tauto]. }
  split.
  { intros a Hi Hs Hct He Hg.
    pose proof (HI a Hi) as Har.
    destruct (F2 a (or_intror Hi) (slot_rel_not_owned_img AX _ _ _ _ a M1 Hi Hs Hct)
      (slot_rel_not_owned_img AX _ _ _ _ a M2 Hi Hs Hct)
      ltac:(unfold scratch_k; intros [Hx|Hx]; [lia | exact (He Hx)]) (EI a Hi Hs Hct He Hg)) as [E1 E2].
    destruct (G1 a Hi Hs Hct He Hg) as [E3 E4]. split; [congruence | tauto]. }
  intros a Ha.
  destruct Ha as [Ha|Ha]; [|apply S2; right; exact Ha].
  assert (Hns : ~ (spZ regs1 - Kc <= a < spZ regs1) -> ~ scratch_k B Kc regs1 a)
    by (intros Hn; unfold scratch_k; intros [Hx|Hx]; [exact (Hn Hx) | lia]).
  destruct (Z_le_gt_dec (spZ regs1 - Kc) a) as [Hx1|Hx1];
    [destruct (Z_lt_ge_dec a (spZ regs1)) as [Hx2|Hx2]; [apply S2; left; lia|] |].
  all: destruct (ES a Ha ltac:(lia)) as [Hw|Hne]; [exact Hw|].
  all: assert (Hah : alloc_ceiling <= a < 2 ^ 64) by lia.
  all: destruct (F2 a (or_introl Hah) (NOh _ _ _ _ a M1 ltac:(lia)) (NOh _ _ _ _ a M2 ltac:(lia))
         (Hns ltac:(lia)) Hne) as [_ Ew].
  all: apply Ew; apply SW1; left; exact Ha.
Qed.

Lemma slot_rel_A : img_low B ->
  forall G K S L0 A0 mem0 md0 L A mem md mem' W,
  slot_rel G K S L0 A0 mem0 md0 L A mem md ->
  Frame.munch W mem mem' -> Frame.wmono (ms_segs B) mem mem' ->
  (forall q n i, In (q, n) (user_blocks A) -> 0 <= i < n ->
     mem (Z_to_bv 64 (ptr_addr L q + i)) <> None -> mem' (Z_to_bv 64 (ptr_addr L q + i)) <> None) ->
  (forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (S - K <= x < S) -> Frame.outside W x) ->
  (forall x, in_img B x -> ~ in_globals G x -> Frame.outside W x) ->
  (forall x, 0 <= x < alloc_ceiling -> owned B L A x -> Frame.outside W x) ->
  (forall q k i, In (q, k) (user_blocks A0) -> 0 <= i < k -> Frame.outside W (ptr_addr L0 q + i)) ->
  slot_rel G K S L0 A0 mem0 md0 L A mem' md.
Proof.
  intros [HI _] G K S L0 A0 mem0 md0 L A mem md mem' W
    (M1 & W1 & B1 & I1 & D1 & U1 & C1 & H1 & G1 & SW1) Hm Hw Hp HW1 HWi HW2 HW3.
  pose proof alloc_ceiling_lt as Hcl.
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M1) as (Hh & Hl & Hmat).
  split.
  { apply (mr_frame _ _ (aa_laws API) L A mem mem' md md M1).
    - intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho).
      apply (mbyte_munch (ms_segs B) W); [exact Hm | lia | apply HW2; [lia | exact Ho]].
    - intros a Ho Hpr. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho).
      apply (present_munch W mem); [exact Hm | lia | apply HW2; [lia | exact Ho] | exact Hpr].
    - intros q n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q n i M1 Hin Hi) as ((b & Hb) & _).
      destruct (mem' (Z_to_bv 64 (ptr_addr L q + i))) as [b'|] eqn:E; [exists b'; exact E|].
      exfalso. apply (Hp q n i Hin Hi); [rewrite Hb; discriminate | exact E].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact W1|]. split; [exact B1|]. split; [exact I1|]. split; [exact D1|]. split; [exact U1|].
  split.
  { intros q k i Hq Hi. destruct (U1 q k Hq) as [Hq1 Hp1].
    destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k M1 Hq1) as [R1 R2]. rewrite Hp1 in R1, R2.
    rewrite (mbyte_munch (ms_segs B) W mem mem' (ptr_addr L0 q + i) Hm ltac:(lia) (HW3 q k i Hq Hi)).
    exact (C1 q k i Hq Hi). }
  split.
  { intros a Ha Hs He. destruct (H1 a Ha Hs He) as [E1 E2].
    assert (Ho : Frame.outside W a) by (apply HW1; [lia | exact Hs]).
    assert (Har : 0 <= a < 2 ^ 64) by (pose proof alloc_ceiling_val; lia).
    split.
    - rewrite (mbyte_munch (ms_segs B) W mem mem' a Hm Har Ho). exact E1.
    - rewrite E2. exact (writable_munch (ms_segs B) W mem mem' a Hm Har Ho). }
  split.
  { intros a Hi Hs Hct He Hg. destruct (G1 a Hi Hs Hct He Hg) as [E1 E2]. pose proof (HI a Hi) as Har.
    assert (Ho : Frame.outside W a) by (apply HWi; [exact Hi | exact Hg]).
    split.
    - rewrite (mbyte_munch (ms_segs B) W mem mem' a Hm ltac:(lia) Ho). exact E1.
    - rewrite E2. exact (writable_munch (ms_segs B) W mem mem' a Hm ltac:(lia) Ho). }
  intros a Ha. unfold writable_at. apply Hw. exact (SW1 a Ha).
Qed.

Lemma slot_rel_pre : forall G K S L0 A0 mem0 md0 L A mem md Kc regs,
  slot_rel G K S L0 A0 mem0 md0 L A mem md ->
  S - K <= spZ regs - Kc -> spZ regs <= S -> spZ regs mod 16 = 0 -> alloc_ceiling + Kc <= spZ regs -> spZ regs < 2 ^ 63 ->
  getr regs 4 = Z_to_bv 64 (ms_tp B) -> YK0s.ret_ok (getr regs 1) ->
  call_pre_k B MR Kc L A regs mem md.
Proof.
  intros G K S L0 A0 mem0 md0 L A mem md Kc regs (M1 & W1 & B1 & I1 & _ & _ & _ & _ & _ & SW1) H1 H2 H3 H4 H5 Htp Hra.
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact Hra|]. split; [exact H3|].
  split; [exact H4|]. split; [exact H5|].
  split; [intros a Ha; apply SW1; left; lia|].
  split; [exact Htp|].
  split; [intros a Ha; apply SW1; right; exact Ha|].
  intros Hd. rewrite I1 in Hd. discriminate.
Qed.

Section Post.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.

Lemma slot_post : forall G K L0 A0 regs0 mem0 md0 p n b L A regs mem md,
  slot_rel G K (spZ regs0) L0 A0 mem0 md0 L A mem md ->
  getr regs 10 = Z_to_bv 64 0 -> regs_preserved regs0 regs ->
  Fs.fs_sorted (m_fs md0) = true ->
  sink_none B mem0 md0 ->
  (forall a, (sk_ofl_head <= a < sk_ofl_head + 8) \/ a = sk_threaded \/ (sk_ofl_lock <= a < sk_ofl_lock + 4) ->
     in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ errno_at a /\
     ~ in_globals G a) ->
  (forall a, in_globals G a -> writable_at (ms_segs B) mem0 a /\ writable_at (ms_segs B) mem a) ->
  ro_agree (ms_segs B) mem ->
  res_ok_slots A (lib_delta n b) ->
  (n = 0 \/ (0 < n /\ exists q, In (q, n) (user_blocks A0) /\ ptr_addr L0 q = p)) ->
  lib_post_g B API G K L0 A0 regs0 mem0 md0 p n b (LL 0 (m_fs md0) []) L A regs mem md.
Proof.
  intros G K L0 A0 regs0 mem0 md0 p n b L A regs mem md
    (M & W & Bd & I & (vm & D) & U & C & H & Gi & SW) H10 RP Hfs (Henv & Hhead & Hnm) Hsk HGw RA RES Hp.
  assert (Fr : forall a, (sk_ofl_head <= a < sk_ofl_head + 8) \/ a = sk_threaded \/ (sk_ofl_lock <= a < sk_ofl_lock + 4) ->
            mbyte (ms_segs B) mem a = mbyte (ms_segs B) mem0 a).
  { intros a Ha. destruct (Hsk a Ha) as (H1 & H2 & H3 & H4 & H5). exact (proj1 (Gi a H1 H2 H3 H4 H5)). }
  split; [exact M|]. split; [exact W|]. split; [exact Bd|]. split; [exact I|].
  split; [exact H10|]. split; [exact RP|].
  split.
  { exists vm, (m_fds md0), (m_statpins md0). cbn [ll_fs]. split; [|intros; reflexivity].
    rewrite D. apply with_vmmaps_os_upd. }
  split; [intros q k Hq; exists q; exact (U q k Hq)|].
  split.
  { intros a Ha Hs. destruct (H a Ha ltac:(intros Hx; apply Hs; left; exact Hx) ltac:(intros Hx; apply Hs; right; exact Hx))
      as [E1 E2]. split; [exact E1 | exact E2]. }
  split.
  { intros a Hi Hs Hc He Hg. exact (Gi a Hi Hs Hc He Hg). }
  split; [intros a Ha; destruct (HGw a Ha) as [W0 W1]; tauto|].
  split; [intros q k i Hq _ Hi; exact (C q k i Hq Hi)|].
  split; [intros a Ha; apply SW; exact Ha|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hfs|].
  split.
  { unfold sink_none, closed_stdio_env in *. destruct Henv as [Ht Hl].
    split; [split|split].
    - intros k Hk. rewrite Fr; [apply Ht; exact Hk|]. right; left. cbn in Hk. lia.
    - intros k Hk. rewrite Fr; [apply Hl; exact Hk|]. right; right. cbn in Hk. lia.
    - intros k Hk. rewrite Fr; [apply Hhead; exact Hk|]. left. lia.
    - rewrite D, with_vmmaps_os_upd, os_upd_fds. exact Hnm. }
  split; [exact RA|]. split; [exact RES|].
  intros i Hi. destruct Hp as [Hn0|(_ & q & Hq & Hpq)]; [lia|].
  subst p. exact (C q n i Hq Hi).
Qed.

End Post.

End SlotInv.

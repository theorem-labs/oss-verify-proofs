From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO10 YO0u.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecKindB.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ub_region : forall s p n, WF s -> In (p, n) (user_blocks s) -> (prid p < length (st_regions s))%nat.
Proof.
  intros s p n HW Hin.
  destruct (YO10.in_user_blocks_inv s _ Hin) as (g & am & i & fr & Hg & _ & _ & _ & E).
  injection E as Ep _. subst p.
  apply (YO10.used_metas_usedX s g am HW) in Hg.
  unfold frame_ptr. rewrite YO0u.prid_padd, YO0u.prid_slot_start.
  exact (YO0u.used_group_prid_lt [] None U0 s g am HW Hg).
Qed.

Lemma ptr_stable : forall A L L1 p n, WF A -> layout_le A L L1 -> In (p, n) (user_blocks A) ->
  ptr_addr L1 p = ptr_addr L p.
Proof.
  intros A L L1 p n HW (_ & _ & _ & HL) Hin. unfold ptr_addr. rewrite !YO10.loc_addr_LMem.
  rewrite (HL (prid p) (ub_region A p n HW Hin)). reflexivity.
Qed.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis AX : AllocExtra B MR.
Hypothesis CTXO : ctx_owned B API.

Definition vr_rel (O : list (Z * Z)) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (L1 : layout) (A1 : astate) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  MR L1 A1 mem1 md1 /\ WF A1 /\ bounded A1 /\ layout_le A L L1 /\
  (length (st_regions A) <= length (st_regions A1))%nat /\
  (exists vm', md1 = with_vmmaps vm' md) /\
  (forall a, vr_dom B a -> ~ owned B L A a -> ~ owned B L1 A1 a -> ~ scratch_k B VR_K regs a -> ~ vr_writes a ->
     mbyte (ms_segs B) mem1 a = mbyte (ms_segs B) mem a /\ (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem1 a)) /\
  (forall a k i, In (a, k) (blocks L A) -> ~ In a (map fst O) -> 0 <= i < k ->
     mbyte (ms_segs B) mem1 (a + i) = mbyte (ms_segs B) mem (a + i)) /\
  (forall a, scratch_k B VR_K regs a -> writable_at (ms_segs B) mem1 a).

Lemma rel_of_since : forall O L A regs mem md L1 A1 mem1 md1,
  vr_since B API (fun _ => False) L A regs mem md L1 A1 mem1 md1 ->
  (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A1)) ->
  vr_rel O L A regs mem md L1 A1 mem1 md1.
Proof.
  intros O L A regs mem md L1 A1 mem1 md1 (HM1 & HW1 & HB1 & HL1 & HR1 & HP1 & HV1 & HF1 & HK1 & HS1) INC.
  split; [exact HM1|]. split; [exact HW1|]. split; [exact HB1|]. split; [exact HL1|]. split; [exact HR1|].
  split; [exact HV1|]. split; [exact HF1|]. split; [|exact HS1].
  intros a k i Hin _ Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbn in E. injection E as <- <-. exact (HK1 p k' i Hp (INC p k' Hp) (fun F => F) Hi).
Qed.

Lemma post_k_rec : forall K L A regs mem md E excl L' A' regs' mem' md',
  call_post_k B MR K L A regs mem md E L' A' regs' mem' md' ->
  RecKindB.call_post_rec B MR K L A regs mem md E excl L' A' regs' mem' md'.
Proof.
  intros K L A regs mem md E excl L' A' regs' mem' md' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [|exact H10].
  intros p n i Hp Hp' _ Hi. exact (H9 p n i Hp Hp' Hi).
Qed.

Lemma rel_call : forall O L A regs mem md L1 A1 mem1 md1 K R1 E excl1 L2 A2 R2 mem2 md2,
  vr_rel O L A regs mem md L1 A1 mem1 md1 ->
  RecKindB.call_post_rec B MR K L1 A1 R1 mem1 md1 E excl1 L2 A2 R2 mem2 md2 ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  (forall a, scratch_k B K R1 a -> scratch_k B VR_K regs a) ->
  (forall a, E a -> ~ vr_dom B a \/ vr_writes a) ->
  (forall a, scratch_k B VR_K regs a -> ~ scratch_k B K R1 a -> alloc_ceiling <= a < 2 ^ 64 /\ ~ vr_writes a) ->
  (forall a k i, In (a, k) (blocks L A) -> ~ In a (map fst O) -> 0 <= i < k ->
     mbyte (ms_segs B) mem2 (a + i) = mbyte (ms_segs B) mem1 (a + i)) ->
  vr_rel O L A regs mem md L2 A2 mem2 md2.
Proof.
  intros O L A regs mem md L1 A1 mem1 md1 K R1 E excl1 L2 A2 R2 mem2 md2
    (HM1 & HW1 & HB1 & HL1 & HR1 & HV1 & HF1 & HK1 & HS1)
    (HM2 & HW2 & HB2 & HL2 & HP2 & HPR & HV2 & HF2 & HK2 & HS2) HR12 SCR EX SD KEEP.
  pose proof (aa_laws API) as LAWS.
  destruct HV1 as [vm1 ->]. destruct HV2 as [vm2 ->].
  split; [exact HM2|]. split; [exact HW2|]. split; [exact HB2|].
  split; [exact (layout_le_trans A A1 L L1 L2 HL1 HL2 HR1)|]. split; [lia|].
  split; [exists vm2; apply with_vmmaps_twice|].
  split.
  { intros a D N N2 Ns Nw.
    pose proof (owned_dom B API AX CTXO L2 A2 mem2 _ L1 A1 mem1 _ a HM2 HM1 D N2) as N1.
    assert (Ns1 : ~ scratch_k B K R1 a) by (intros H; exact (Ns (SCR a H))).
    assert (NE : ~ E a) by (intros H; destruct (EX a H) as [H'|H']; [exact (H' D) | exact (Nw H')]).
    destruct (HF2 a D N1 N2 Ns1 NE) as [E2 W2]. destruct (HF1 a D N N1 Ns Nw) as [E1 W1].
    split; [rewrite E2; exact E1 | tauto]. }
  split.
  { intros a k i Hin Hx Hi. rewrite (KEEP a k i Hin Hx Hi). exact (HK1 a k i Hin Hx Hi). }
  intros a Ha. destruct (classic_scr B K R1 a) as [Hk|Hk]; [exact (HS2 a Hk)|].
  destruct (SD a Ha Hk) as [Hc Nw].
  assert (N1 : ~ owned B L1 A1 a) by (intros Ow; pose proof (mr_owned_low B _ LAWS _ _ _ _ a HM1 Ow); lia).
  assert (N2 : ~ owned B L2 A2 a) by (intros Ow; pose proof (mr_owned_low B _ LAWS _ _ _ _ a HM2 Ow); lia).
  assert (NE : ~ E a) by (intros H; destruct (EX a H) as [H'|H']; [exact (H' (or_introl Hc)) | exact (Nw H')]).
  destruct (HF2 a (or_introl Hc) N1 N2 Hk NE) as [_ W2]. apply W2. exact (HS1 a Ha).
Qed.

Lemma rel_mem : forall O L A regs mem md L1 A1 mem1 md1 mem2,
  vr_rel O L A regs mem md L1 A1 mem1 md1 ->
  MR L1 A1 mem2 md1 ->
  (forall a, vr_dom B a -> ~ owned B L1 A1 a -> ~ scratch_k B VR_K regs a -> ~ vr_writes a ->
     mbyte (ms_segs B) mem2 a = mbyte (ms_segs B) mem1 a /\
     (writable_at (ms_segs B) mem1 a <-> writable_at (ms_segs B) mem2 a)) ->
  (forall a k i, In (a, k) (blocks L A) -> ~ In a (map fst O) -> 0 <= i < k ->
     mbyte (ms_segs B) mem2 (a + i) = mbyte (ms_segs B) mem1 (a + i)) ->
  (forall a, scratch_k B VR_K regs a -> writable_at (ms_segs B) mem1 a -> writable_at (ms_segs B) mem2 a) ->
  vr_rel O L A regs mem md L1 A1 mem2 md1.
Proof.
  intros O L A regs mem md L1 A1 mem1 md1 mem2 (HM1 & HW1 & HB1 & HL1 & HR1 & HV1 & HF1 & HK1 & HS1) HM2 F2 K2 S2.
  split; [exact HM2|]. split; [exact HW1|]. split; [exact HB1|]. split; [exact HL1|]. split; [exact HR1|].
  split; [exact HV1|].
  split.
  { intros a D N N1 Ns Nw. destruct (HF1 a D N N1 Ns Nw) as [E1 W1]. destruct (F2 a D N1 Ns Nw) as [E2 W2].
    split; [rewrite E2; exact E1 | tauto]. }
  split.
  { intros a k i Hin Hx Hi. rewrite (K2 a k i Hin Hx Hi). exact (HK1 a k i Hin Hx Hi). }
  intros a Ha. apply S2; [exact Ha | apply HS1; exact Ha].
Qed.

Lemma rel_final : forall O L A regs mem md L1 A1 regs1 mem1 md1,
  WF A -> vr_rel O L A regs mem md L1 A1 mem1 md1 -> regs_preserved regs regs1 ->
  RecKindB.call_post_rec B MR VR_K L A regs mem md vr_writes (fun a => In a (map fst O)) L1 A1 regs1 mem1 md1.
Proof.
  intros O L A regs mem md L1 A1 regs1 mem1 md1 HWA (HM1 & HW1 & HB1 & HL1 & HR1 & HV1 & HF1 & HK1 & HS1) HPR.
  split; [exact HM1|]. split; [exact HW1|]. split; [exact HB1|]. split; [exact HL1|].
  split; [intros p n Hp _; exact (ptr_stable A L L1 p n HWA HL1 Hp)|].
  split; [exact HPR|]. split; [exact HV1|]. split; [exact HF1|]. split; [|exact HS1].
  intros p n i Hp _ Hx Hi. apply (HK1 (ptr_addr L p) n i); [|exact Hx|exact Hi].
  apply in_map_iff. exists (p, n). split; [reflexivity | exact Hp].
Qed.

End S.

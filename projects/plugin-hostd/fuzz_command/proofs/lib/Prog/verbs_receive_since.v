From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecKindB.
Import ListNotations.
Local Open Scope Z_scope.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis AX : AllocExtra B MR.
Hypothesis CTXO : ctx_owned B API.

Definition vr_dom (a : Z) : Prop := alloc_ceiling <= a < 2 ^ 64 \/ in_img B a.

Definition vr_since (excl : Z -> Prop) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (L1 : layout) (A1 : astate) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  MR L1 A1 mem1 md1 /\ WF A1 /\ bounded A1 /\ layout_le A L L1 /\
  (length (st_regions A) <= length (st_regions A1))%nat /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> ptr_addr L1 p = ptr_addr L p) /\
  (exists vm', md1 = with_vmmaps vm' md) /\
  (forall a, vr_dom a -> ~ owned B L A a -> ~ owned B L1 A1 a -> ~ scratch_k B VR_K regs a -> ~ vr_writes a ->
     mbyte (ms_segs B) mem1 a = mbyte (ms_segs B) mem a /\ (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem1 a)) /\
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> ~ excl (ptr_addr L p) -> 0 <= i < n ->
     mbyte (ms_segs B) mem1 (ptr_addr L p + i) = mbyte (ms_segs B) mem (ptr_addr L p + i)) /\
  (forall a, scratch_k B VR_K regs a -> writable_at (ms_segs B) mem1 a).

Lemma owned_dom : forall L A mem md L1 A1 mem1 md1 a, MR L A mem md -> MR L1 A1 mem1 md1 -> vr_dom a ->
  ~ owned B L A a -> ~ owned B L1 A1 a.
Proof.
  intros L A mem md L1 A1 mem1 md1 a HM HM1 D N O1.
  pose proof (aa_laws API) as LAWS.
  destruct D as [D|D].
  - pose proof (mr_owned_low B _ LAWS L1 A1 mem1 md1 a HM1 O1). lia.
  - destruct O1 as [O1|O1].
    + apply N. apply (CTXO L A mem md a HM). exact (ax_img AX L1 A1 mem1 md1 a HM1 D O1).
    + apply N. right. exact O1.
Qed.

Lemma layout_le_trans : forall A A1 L L1 L2,
  layout_le A L L1 -> layout_le A1 L1 L2 -> (length (st_regions A) <= length (st_regions A1))%nat ->
  layout_le A L L2.
Proof.
  intros A A1 L L1 L2 (H1 & H2 & H3 & H4) (K1 & K2 & K3 & K4) Hl.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite K4 by lia. apply H4. exact Hr.
Qed.

Lemma classic_scr : forall K R a, scratch_k B K R a \/ ~ scratch_k B K R a.
Proof.
  intros K R a. unfold scratch_k.
  destruct (Z_le_gt_dec (spZ R - K) a); destruct (Z_lt_ge_dec a (spZ R));
  destruct (Z_le_gt_dec (errno_addr B) a); destruct (Z_lt_ge_dec a (errno_addr B + 4)); try (left; lia); right; lia.
Qed.

Lemma since_init : forall excl L A regs mem md,
  call_pre_k B MR VR_K L A regs mem md -> vr_since excl L A regs mem md L A mem md.
Proof.
  intros excl L A regs mem md (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [apply layout_le_refl|].
  split; [lia|]. split; [reflexivity|]. split; [exists (m_vmmaps md); apply with_vmmaps_self|].
  split; [intros; split; [reflexivity | tauto]|].
  split; [intros; reflexivity|].
  intros a [Ha|Ha]; [apply HWS; exact Ha | apply HERR; exact Ha].
Qed.

Lemma since_mem : forall excl L A regs mem md L1 A1 mem1 md1 mem2,
  vr_since excl L A regs mem md L1 A1 mem1 md1 ->
  MR L1 A1 mem2 md1 ->
  (forall a, vr_dom a -> ~ owned B L1 A1 a -> ~ scratch_k B VR_K regs a -> ~ vr_writes a ->
     mbyte (ms_segs B) mem2 a = mbyte (ms_segs B) mem1 a /\ (writable_at (ms_segs B) mem1 a <-> writable_at (ms_segs B) mem2 a)) ->
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> ~ excl (ptr_addr L p) -> 0 <= i < n ->
     mbyte (ms_segs B) mem2 (ptr_addr L p + i) = mbyte (ms_segs B) mem1 (ptr_addr L p + i)) ->
  (forall a, scratch_k B VR_K regs a -> writable_at (ms_segs B) mem1 a -> writable_at (ms_segs B) mem2 a) ->
  vr_since excl L A regs mem md L1 A1 mem2 md1.
Proof.
  intros excl L A regs mem md L1 A1 mem1 md1 mem2 (HM1 & HW1 & HB1 & HL1 & HR1 & HP1 & HV1 & HF1 & HK1 & HS1)
    HM2 F2 K2 S2.
  split; [exact HM2|]. split; [exact HW1|]. split; [exact HB1|]. split; [exact HL1|]. split; [exact HR1|].
  split; [exact HP1|]. split; [exact HV1|].
  split.
  { intros a D N N1 Ns Nw. destruct (HF1 a D N N1 Ns Nw) as [E1 W1]. destruct (F2 a D N1 Ns Nw) as [E2 W2].
    split; [rewrite E2; exact E1 | tauto]. }
  split.
  { intros p n i Hp Hp1 Hx Hi. rewrite (K2 p n i Hp Hp1 Hx Hi). exact (HK1 p n i Hp Hp1 Hx Hi). }
  intros a Ha. apply S2; [exact Ha | apply HS1; exact Ha].
Qed.

Lemma since_call : forall excl L A regs mem md L1 A1 mem1 md1 K R1 E L2 A2 R2 mem2 md2,
  vr_since excl L A regs mem md L1 A1 mem1 md1 ->
  call_post_k B MR K L1 A1 R1 mem1 md1 E L2 A2 R2 mem2 md2 ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A2) -> In (p, n) (user_blocks A1)) ->
  (forall a, scratch_k B K R1 a -> scratch_k B VR_K regs a) ->
  (forall a, E a -> ~ vr_dom a \/ vr_writes a) ->
  (forall a, scratch_k B VR_K regs a -> ~ scratch_k B K R1 a -> alloc_ceiling <= a < 2 ^ 64 /\ ~ vr_writes a) ->
  vr_since excl L A regs mem md L2 A2 mem2 md2.
Proof.
  intros excl L A regs mem md L1 A1 mem1 md1 K R1 E L2 A2 R2 mem2 md2
    (HM1 & HW1 & HB1 & HL1 & HR1 & HP1 & HV1 & HF1 & HK1 & HS1)
    (HM2 & HW2 & HB2 & HL2 & HP2 & HPR & HV2 & HF2 & HK2 & HS2) HR12 INC SCR EX SD.
  pose proof (aa_laws API) as LAWS.
  destruct HV1 as [vm1 ->]. destruct HV2 as [vm2 ->].
  split; [exact HM2|]. split; [exact HW2|]. split; [exact HB2|].
  split; [exact (layout_le_trans A A1 L L1 L2 HL1 HL2 HR1)|]. split; [lia|].
  split.
  { intros p n Hp Hp2. pose proof (INC p n Hp Hp2) as Hp1. rewrite (HP2 p n Hp1 Hp2). exact (HP1 p n Hp Hp1). }
  split; [exists vm2; apply with_vmmaps_twice|].
  split.
  { intros a D N N2 Ns Nw.
    pose proof (owned_dom L2 A2 mem2 _ L1 A1 mem1 _ a HM2 HM1 D N2) as N1.
    assert (Ns1 : ~ scratch_k B K R1 a) by (intros H; exact (Ns (SCR a H))).
    assert (NE : ~ E a) by (intros H; destruct (EX a H) as [H'|H']; [exact (H' D) | exact (Nw H')]).
    destruct (HF2 a D N1 N2 Ns1 NE) as [E2 W2]. destruct (HF1 a D N N1 Ns Nw) as [E1 W1].
    split; [rewrite E2; exact E1 | tauto]. }
  split.
  { intros p n i Hp Hp2 Hx Hi. pose proof (INC p n Hp Hp2) as Hp1.
    pose proof (HK2 p n i Hp1 Hp2 Hi) as E2. rewrite (HP1 p n Hp Hp1) in E2. rewrite E2.
    exact (HK1 p n i Hp Hp1 Hx Hi). }
  intros a Ha. destruct (classic_scr K R1 a) as [Hk|Hk]; [exact (HS2 a Hk)|].
  destruct (SD a Ha Hk) as [Hc Nw].
  assert (N1 : ~ owned B L1 A1 a) by (intros O; pose proof (mr_owned_low B _ LAWS _ _ _ _ a HM1 O); lia).
  assert (N2 : ~ owned B L2 A2 a) by (intros O; pose proof (mr_owned_low B _ LAWS _ _ _ _ a HM2 O); lia).
  assert (NE : ~ E a) by (intros H; destruct (EX a H) as [H'|H']; [exact (H' (or_introl Hc)) | exact (Nw H')]).
  destruct (HF2 a (or_introl Hc) N1 N2 Hk NE) as [_ W2]. apply W2. exact (HS1 a Ha).
Qed.

Lemma since_final : forall excl L A regs mem md L1 A1 regs1 mem1 md1,
  vr_since excl L A regs mem md L1 A1 mem1 md1 -> regs_preserved regs regs1 ->
  RecKindB.call_post_rec B MR VR_K L A regs mem md vr_writes excl L1 A1 regs1 mem1 md1.
Proof.
  intros excl L A regs mem md L1 A1 regs1 mem1 md1 (HM1 & HW1 & HB1 & HL1 & HR1 & HP1 & HV1 & HF1 & HK1 & HS1) HPR.
  split; [exact HM1|]. split; [exact HW1|]. split; [exact HB1|]. split; [exact HL1|]. split; [exact HP1|].
  split; [exact HPR|]. split; [exact HV1|]. split; [exact HF1|]. split; [exact HK1|]. exact HS1.
Qed.

End S.

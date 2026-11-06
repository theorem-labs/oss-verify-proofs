(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v; 12442 of its 12533 lines of code are new or changed and 1138 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/drain_b.v, with its module paths changed; 2169 of its 2391 lines of code are new or changed and 12311 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/gestures_end_b.v, with its module names changed; 6115 of its 6343 lines of code are new or changed and 2163 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI04 YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import KindB pthread_mutex_lock_c pthread_mutex_unlock_c snprintf_c strlen_c strncmp_c printf_facts_c send_line_c gesture_end_c relay_event_c RelayFrame RelayRunT RelayRunF ListTr RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b_c relay_remove_b_c relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import relay_instance_gone_b_seg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import relay_instance_gone_b_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require gestures_end_b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rig_vm_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma rig_vm_self : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma rig_ub_nonneg : forall s p n, WF s -> In (p, n) (user_blocks s) -> 0 <= n.
Proof.
  intros s p n HW Hin.
  destruct (YO10.in_user_blocks_inv s (p, n) Hin) as (g & am & i & fr & Hg & Hi & Hfr & _ & E).
  apply (YO10.used_metas_usedX s g am HW) in Hg.
  destruct (YO10.block_in_slot s g am i fr HW Hg Hi Hfr) as (_ & _ & H).
  injection E as _ ->. exact H.
Qed.

Lemma rig_blocks_in : forall L A a n, In (a, n) (blocks L A) <-> exists p, ptr_addr L p = a /\ In (p, n) (user_blocks A).
Proof.
  intros L A a n. unfold blocks. rewrite in_map_iff. split.
  - intros ([p k] & H & Hin). cbn in H. injection H as <- <-. exists p. auto.
  - intros (p & <- & Hin). exists (p, n). auto.
Qed.

Lemma rig_present_writable : forall segs m a, present m a -> writable_at segs m a.
Proof. intros segs m a [b E]. unfold writable_at, wview. rewrite E. discriminate. Qed.

Lemma rig_ro_glob_chk : forallb (fun i => negb (ro_addr rsegs (Z_to_bv 64 (0x30fc0 + Z.of_nat i)))) (seq 0 512) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rig_ro_glob : forall a, 0x30fc0 <= a < 0x311c0 -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. pose proof (proj1 (forallb_forall _ _) rig_ro_glob_chk (Z.to_nat (a - 0x30fc0))) as H.
  rewrite in_seq in H. specialize (H ltac:(lia)). rewrite Z2Nat.id in H by lia.
  replace (0x30fc0 + (a - 0x30fc0)) with a in H by lia.
  destruct (ro_addr rsegs (Z_to_bv 64 a)); [discriminate H | reflexivity].
Qed.

Lemma rig_ro_client_chk : forallb (fun i => negb (ro_addr rsegs (Z_to_bv 64 (0x20d3c + Z.of_nat i)))) (seq 0 4) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rig_ro_client : forall a, 0x20d3c <= a < 0x20d40 -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. pose proof (proj1 (forallb_forall _ _) rig_ro_client_chk (Z.to_nat (a - 0x20d3c))) as H.
  rewrite in_seq in H. specialize (H ltac:(lia)). rewrite Z2Nat.id in H by lia.
  replace (0x20d3c + (a - 0x20d3c)) with a in H by lia.
  destruct (ro_addr rsegs (Z_to_bv 64 a)); [discriminate H | reflexivity].
Qed.

Lemma rig_reg_eqv : forall M R (k : Z), Regs6ss.xregs_eqv M R -> 0 < k < 32 -> YK11.getr R (Z_to_bv 5 k) = reg_get M (Z_to_bv 5 k).
Proof.
  intros M R k X Hk. apply getr_of_eqv; [exact X|].
  unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia.
Qed.

Section RIG.
Context {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Local Notation segs := (ms_segs Bm).
Local Notation MR := (aa_MR API).
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTX : ctx_owned Bm API.
Hypothesis SEGS : ms_segs Bm = rsegs.
Hypothesis BSP : block_slack_present Bm API.
Hypothesis LOCK : pthread_mutex_lock_contract.
Hypothesis UNLOCK : pthread_mutex_unlock_contract.
Hypothesis SNP : snprintf_contract.
Hypothesis SLEN : strlen_contract.
Hypothesis SNCMP : strncmp_contract.
Variable RF : ResFormT.
Hypothesis FREE : forall fx' : YK11.FPState, free_contract_rt (fx := fx') Bm API RF.
Hypothesis DRAIN : forall fx' : YK11.FPState, @drain_contract fx' rc Bm API RF.
Hypothesis GEND : forall fx' : YK11.FPState, @gesture_end_contract fx' rc Bm API RF.
Hypothesis FREE_PC : ms_free Bm = RIG_FREE.
Hypothesis NODUP : forall L A mem md, aa_MR API L A mem md -> NoDup (map fst (blocks L A)).

Lemma rig_laws : MR_laws Bm MR.
Proof. exact (aa_laws API). Qed.

Lemma rig_owned_low : forall L A mem md a, MR L A mem md -> owned Bm L A a -> 0 <= a < alloc_ceiling.
Proof. intros L A mem md a HM Ho. exact (mr_owned_low Bm MR rig_laws L A mem md a HM Ho). Qed.

Lemma rig_blk : forall L A mem md q k i, MR L A mem md -> In (q, k) (blocks L A) -> 0 <= i < k ->
  present mem (q + i) /\ 4096 <= q /\ q + k <= alloc_ceiling /\ ~ owned Bm L A (q + i).
Proof.
  intros L A mem md q k i HM Hin Hi. apply rig_blocks_in in Hin as (p & <- & Hp).
  exact (mr_blocks Bm MR rig_laws L A mem md p k i HM Hp Hi).
Qed.

Lemma rig_blk_lo : forall L A mem md q k, MR L A mem md -> In (q, k) (blocks L A) -> 4096 <= q.
Proof.
  intros L A mem md q k HM Hin. apply rig_blocks_in in Hin as (p & <- & Hp).
  exact (proj1 (mr_blocks_range Bm MR rig_laws L A mem md p k HM Hp)).
Qed.

Lemma scratch_dec : forall K regs a, scratch_k Bm K regs a \/ ~ scratch_k Bm K regs a.
Proof. intros K regs a. unfold scratch_k. lia. Qed.

Lemma rig_blk_disj : forall L A mem md p n q k, MR L A mem md -> In (p, n) (blocks L A) -> In (q, k) (blocks L A) ->
  p <> q -> p + n <= q \/ q + k <= p.
Proof. intros. eapply (blocks_disjoint Bm API); eassumption. Qed.

Lemma rig_plain_unowned : forall L A mem md a, MR L A mem md -> img_plain Bm a -> ~ owned Bm L A a.
Proof using AX.
  intros L A mem md a HM (Hi & Hs & Hc & He) [Ho|Ho].
  - exact (Hc (ax_img AX L A mem md a HM Hi Ho)).
  - exact (Hs Ho).
Qed.

Lemma rig_img_owned : forall L A mem md L' A' mem' md' a, MR L A mem md -> MR L' A' mem' md' -> in_img Bm a ->
  owned Bm L' A' a -> owned Bm L A a.
Proof using AX CTX.
  intros L A mem md L' A' mem' md' a HM HM' Hi [Ho|Ho].
  - apply (CTX L A mem md a HM). exact (ax_img AX L' A' mem' md' a HM' Hi Ho).
  - right. exact Ho.
Qed.

Definition chain (K : Z) (E F : Z -> Prop)
    (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ~ F (ptr_addr L p) ->
     ptr_addr L' p = ptr_addr L p) /\
  (forall p n, In (p, n) (user_blocks A) -> 0 < n -> ~ F (ptr_addr L p) -> In (p, n) (user_blocks A')) /\
  (forall p, In (p, 0) (user_blocks A) -> In (p, 0) (user_blocks A') /\ ptr_addr L' p = ptr_addr L p) /\
  (forall a, in_img Bm a -> owned Bm L' A' a -> owned Bm L A a) /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) ->
     ~ owned Bm L A a -> ~ owned Bm L' A' a -> ~ scratch_k Bm K regs a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ~ F (ptr_addr L p) -> 0 <= i < n ->
     ~ E (ptr_addr L p + i) ->
     mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
  (forall a, scratch_k Bm K regs a -> writable_at segs mem' a).

Lemma chain_post : forall K E F L A regs mem md L' A' regs' mem' md',
  chain K E F L A regs mem md L' A' mem' md' -> regs_preserved regs regs' ->
  relay_post Bm API K E F L A regs mem md L' A' regs' mem' md'.
Proof.
  intros K E F L A regs mem md L' A' regs' mem' md'
    (M & W & B & LE & RG & AD & SV & Z0 & IO & VM & FR & BY & SW) RP.
  repeat (split; [eassumption|]). exact SW.
Qed.

Lemma chain_refl : forall K E F L A regs mem md, MR L A mem md -> WF A -> bounded A ->
  (forall a, scratch_k Bm K regs a -> writable_at segs mem a) ->
  chain K E F L A regs mem md L A mem md.
Proof.
  intros K E F L A regs mem md HM HW HB HS.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [lia|]. split; [intros; reflexivity|]. split; [intros; assumption|].
  split; [intros p H; split; [exact H | reflexivity]|]. split; [intros; assumption|].
  split; [exists (m_vmmaps md); apply rig_vm_self|]. split; [intros; split; [reflexivity | tauto]|].
  split; [intros; reflexivity|]. exact HS.
Qed.

Lemma chain_mono : forall K E F E' F' L A regs mem md L' A' mem' md',
  chain K E F L A regs mem md L' A' mem' md' -> (forall a, E a -> E' a) -> (forall q, F q -> F' q) ->
  chain K E' F' L A regs mem md L' A' mem' md'.
Proof.
  intros K E F E' F' L A regs mem md L' A' mem' md'
    (M & W & B & LE & RG & AD & SV & Z0 & IO & VM & FR & BY & SW) HE HF.
  split; [exact M|]. split; [exact W|]. split; [exact B|]. split; [exact LE|]. split; [exact RG|].
  split; [intros p n H1 H2 H3; apply (AD p n H1 H2); intros X; exact (H3 (HF _ X))|].
  split; [intros p n H1 H2 H3; apply (SV p n H1 H2); intros X; exact (H3 (HF _ X))|].
  split; [exact Z0|]. split; [exact IO|]. split; [exact VM|].
  split; [intros a H1 H2 H3 H4 H5; apply FR; try assumption; intros X; exact (H5 (HE _ X))|].
  split; [intros p n i H1 H2 H3 H4 H5; apply (BY p n i H1 H2); try assumption; [intros X; exact (H3 (HF _ X)) | intros X; exact (H5 (HE _ X))]|].
  exact SW.
Qed.

Lemma chain_in : forall K E F L A regs mem md L1 A1 m1 md1 p n,
  WF A -> chain K E F L A regs mem md L1 A1 m1 md1 -> In (p, n) (user_blocks A) -> ~ F (ptr_addr L p) ->
  In (p, n) (user_blocks A1) /\ ptr_addr L1 p = ptr_addr L p.
Proof.
  intros K E F L A regs mem md L1 A1 m1 md1 p n HW
    (M & W & B & LE & RG & AD & SV & Z0 & IO & VM & FR & BY & SW) H0 HF.
  pose proof (rig_ub_nonneg A p n HW H0) as Hn.
  destruct (Z.eq_dec n 0) as [->|Hn'].
  - exact (Z0 p H0).
  - assert (H1 : In (p, n) (user_blocks A1)) by (apply SV; [exact H0 | lia | exact HF]).
    split; [exact H1 | exact (AD p n H0 H1 HF)].
Qed.

Lemma chain_callee : forall K E F L A regs mem md L1 A1 m1 md1 K' E' F' R1 L2 A2 R2 m2 md2,
  WF A ->
  chain K E F L A regs mem md L1 A1 m1 md1 ->
  relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  (forall a, scratch_k Bm K' R1 a -> scratch_k Bm K regs a) ->
  (forall a, scratch_k Bm K regs a -> ~ scratch_k Bm K' R1 a -> alloc_ceiling <= a < 2 ^ 64) ->
  (forall a, E' a -> a < alloc_ceiling /\ (in_img Bm a -> E a)) ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> 0 < n -> ~ F (ptr_addr L p) ->
     ~ F' (ptr_addr L p) /\ (forall i, 0 <= i < n -> ~ E (ptr_addr L p + i) -> ~ E' (ptr_addr L p + i))) ->
  chain K E F L A regs mem md L2 A2 m2 md2.
Proof.
  intros K E F L A regs mem md L1 A1 m1 md1 K' E' F' R1 L2 A2 R2 m2 md2 HW CH RP SC SC2 EH FB.
  pose proof (fun p n => chain_in K E F L A regs mem md L1 A1 m1 md1 p n HW CH) as IN1.
  destruct CH as (M1 & W1 & B1 & LE1 & RG1 & AD1 & SV1 & Z1 & IO1 & VM1 & FR1 & BY1 & SW1).
  destruct RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|].
  split.
  { destruct LE1 as (c1 & s1 & b1 & r1). destruct LE2 as (c2 & s2 & b2 & r2).
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros r Hr. rewrite r2 by lia. apply r1. exact Hr. }
  split; [lia|].
  split.
  { intros p n H0 H2 HF. destruct (IN1 p n H0 HF) as [H1 E1].
    pose proof (rig_ub_nonneg A p n HW H0) as Hn.
    destruct (Z.eq_dec n 0) as [->|Hn'].
    - destruct (Z1 p H0) as [H1' E1']. destruct (Z2 p H1') as [_ E2']. congruence.
    - rewrite <- E1. apply (AD2 p n H1 H2). rewrite E1. exact (proj1 (FB p n H0 H1 ltac:(lia) HF)). }
  split.
  { intros p n H0 Hn HF. destruct (IN1 p n H0 HF) as [H1 E1].
    apply (SV2 p n H1 Hn). rewrite E1. exact (proj1 (FB p n H0 H1 Hn HF)). }
  split.
  { intros p H0. destruct (Z1 p H0) as [H1 E1]. destruct (Z2 p H1) as [H2 E2]. split; [exact H2 | congruence]. }
  split.
  { intros a Ha Ho. apply IO1; [exact Ha|]. apply IO2; assumption. }
  split.
  { destruct VM1 as [v1 ->]. destruct VM2 as [v2 ->]. exists v2. apply rig_vm_twice. }
  split.
  { intros a Ha NO0 NO2 NS NE.
    assert (NO1 : ~ owned Bm L1 A1 a).
    { intros Ho. destruct Ha as [Ha|Ha].
      - destruct (rig_owned_low L1 A1 m1 md1 a M1 Ho). lia.
      - exact (NO0 (IO1 a Ha Ho)). }
    destruct (FR1 a Ha NO0 NO1 NS NE) as [E01 W01].
    assert (NS' : ~ scratch_k Bm K' R1 a) by (intros X; exact (NS (SC a X))).
    assert (NE' : ~ E' a).
    { intros X. destruct (EH a X) as [Hlt Hi]. destruct Ha as [Ha|Ha]; [lia|]. exact (NE (Hi Ha)). }
    destruct (FR2 a Ha NO1 NO2 NS' NE') as [E12 W12].
    split; [congruence | tauto]. }
  split.
  { intros p n i H0 H2 HF Hi HE.
    destruct (IN1 p n H0 HF) as [H1 E1].
    destruct (FB p n H0 H1 ltac:(lia) HF) as [HF' HE'].
    rewrite <- (BY1 p n i H0 H1 HF Hi HE).
    rewrite <- E1.
    apply (BY2 p n i H1 H2); [rewrite E1; exact HF' | exact Hi | rewrite E1; exact (HE' i Hi HE)]. }
  intros a Ha.
  destruct (scratch_dec K' R1 a) as [X|X].
  - exact (SW2 a X).
  - pose proof (SW1 a Ha) as W.
    pose proof (SC2 a Ha X) as Hr.
    assert (NO1 : ~ owned Bm L1 A1 a) by (intros Ho; destruct (rig_owned_low L1 A1 m1 md1 a M1 Ho); lia).
    assert (NO2 : ~ owned Bm L2 A2 a) by (intros Ho; destruct (rig_owned_low L2 A2 m2 md2 a M2 Ho); lia).
    assert (NE' : ~ E' a) by (intros Y; destruct (EH a Y); lia).
    exact (proj1 (proj2 (FR2 a (or_introl Hr) NO1 NO2 X NE')) W).
Qed.

Lemma rig_nodup_fst : forall {X Y} (l : list (X * Y)) p a b, List.NoDup (map fst l) -> In (p, a) l -> In (p, b) l -> a = b.
Proof.
  intros X Y l. induction l as [|[x y] l IH]; intros p a b ND Ha Hb; [destruct Ha|].
  cbn in ND. apply List.NoDup_cons_iff in ND as [Hn ND'].
  destruct Ha as [Ea|Ha]; destruct Hb as [Eb|Hb].
  - congruence.
  - injection Ea as Ex _. subst x. exfalso. apply Hn. apply in_map_iff. exists (p, b). auto.
  - injection Eb as Ex _. subst x. exfalso. apply Hn. apply in_map_iff. exists (p, a). auto.
  - exact (IH p a b ND' Ha Hb).
Qed.

Lemma rig_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|p W IH]; intros x; [left; exact I|]. destruct p as [lo hi]. cbn [outside].
  destruct (IH x) as [H|H]; [destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|]|].
  - right. intros [X _]. lia.
  - left. split; [lia | exact H].
  - left. split; [lia | exact H].
  - right. intros [_ X]. exact (H X).
Qed.

Lemma chain_free : forall K E F L A regs mem md L1 A1 m1 md1 R1 L2 A2 R2 m2 md2 p n,
  WF A -> chain K E F L A regs mem md L1 A1 m1 md1 ->
  call_post Bm MR L1 A1 R1 m1 md1 (fun a => ptr_addr L1 p <= a < ptr_addr L1 p + n) L2 A2 R2 m2 md2 ->
  (forall q k, In (q, k) (user_blocks A1) -> q <> p -> In (q, k) (user_blocks A2)) ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  In (p, n) (user_blocks A1) -> 0 < n ->
  (forall a, scratch Bm R1 a -> scratch_k Bm K regs a) ->
  (forall a, scratch_k Bm K regs a -> ~ scratch Bm R1 a -> alloc_ceiling <= a < 2 ^ 64) ->
  (forall p0 n0, In (p0, n0) (user_blocks A) -> In (p0, n0) (user_blocks A1) -> ~ F (ptr_addr L p0) -> p0 <> p) ->
  chain K E F L A regs mem md L2 A2 m2 md2.
Proof using AX CTX.
  intros K E F L A regs mem md L1 A1 m1 md1 R1 L2 A2 R2 m2 md2 p n HW CH CP KEEP RGN HIN HN SC SC2 NP.
  pose proof (fun p0 n0 => chain_in K E F L A regs mem md L1 A1 m1 md1 p0 n0 HW CH) as IN1.
  destruct CH as (M1 & W1 & B1 & LE1 & RG1 & AD1 & SV1 & Z1 & IO1 & VM1 & FR1 & BY1 & SW1).
  destruct CP as (M2 & W2 & B2 & LE2 & AD2 & RPr & VM2 & FR2 & BY2 & SW2).
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|].
  split.
  { destruct LE1 as (c1 & s1 & b1 & r1). destruct LE2 as (c2 & s2 & b2 & r2).
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros r Hr. rewrite r2 by lia. apply r1. exact Hr. }
  split; [lia|].
  split.
  { intros p0 n0 H0 H2 HF. destruct (IN1 p0 n0 H0 HF) as [H1 E1]. rewrite <- E1. exact (AD2 p0 n0 H1 H2). }
  split.
  { intros p0 n0 H0 Hn HF. destruct (IN1 p0 n0 H0 HF) as [H1 E1]. apply KEEP; [exact H1|].
    exact (NP p0 n0 H0 H1 HF). }
  split.
  { intros p0 H0. destruct (Z1 p0 H0) as [H1 E1].
    assert (Hne : p0 <> p).
    { intros ->. pose proof (rig_nodup_fst _ p 0 n (YO10.user_block_ptrs_NoDup A1 W1) H1 HIN). lia. }
    pose proof (KEEP p0 0 H1 Hne) as H2. split; [exact H2|]. rewrite (AD2 p0 0 H1 H2). exact E1. }
  split.
  { intros a Ha Ho. apply IO1; [exact Ha|]. exact (rig_img_owned L1 A1 m1 md1 L2 A2 m2 md2 a M1 M2 Ha Ho). }
  split.
  { destruct VM1 as [v1 ->]. destruct VM2 as [v2 ->]. exists v2. apply rig_vm_twice. }
  split.
  { intros a Ha NO0 NO2 NS NE.
    assert (NO1 : ~ owned Bm L1 A1 a).
    { intros Ho. destruct Ha as [Ha|Ha].
      - destruct (rig_owned_low L1 A1 m1 md1 a M1 Ho). lia.
      - exact (NO0 (IO1 a Ha Ho)). }
    destruct (FR1 a Ha NO0 NO1 NS NE) as [E01 W01].
    assert (NS' : ~ scratch Bm R1 a) by (intros X; exact (NS (SC a X))).
    assert (NE' : ~ (ptr_addr L1 p <= a < ptr_addr L1 p + n)).
    { intros X. pose proof (mr_blocks Bm MR rig_laws L1 A1 m1 md1 p n (a - ptr_addr L1 p) M1 HIN ltac:(lia)) as (_ & _ & Hc & _).
      destruct Ha as [Ha|Ha]; [lia|].
      apply (ax_blocks_img AX L1 A1 m1 md1 p n (a - ptr_addr L1 p) M1 HIN ltac:(lia)).
      replace (ptr_addr L1 p + (a - ptr_addr L1 p)) with a by ring. exact Ha. }
    destruct (FR2 a Ha NO1 NO2 NS' NE') as [E12 W12].
    split; [congruence | tauto]. }
  split.
  { intros p0 n0 i H0 H2 HF Hi HE.
    destruct (IN1 p0 n0 H0 HF) as [H1 E1].
    rewrite <- (BY1 p0 n0 i H0 H1 HF Hi HE). rewrite <- E1. exact (BY2 p0 n0 i H1 H2 Hi). }
  intros a Ha.
  destruct (scratch_dec ALLOC_STACK R1 a) as [X|X].
  - exact (SW2 a X).
  - pose proof (SW1 a Ha) as W.
    pose proof (SC2 a Ha X) as Hr.
    assert (NO1 : ~ owned Bm L1 A1 a) by (intros Ho; destruct (rig_owned_low L1 A1 m1 md1 a M1 Ho); lia).
    assert (NO2 : ~ owned Bm L2 A2 a) by (intros Ho; destruct (rig_owned_low L2 A2 m2 md2 a M2 Ho); lia).
    assert (NE' : ~ (ptr_addr L1 p <= a < ptr_addr L1 p + n)).
    { intros Y. pose proof (mr_blocks Bm MR rig_laws L1 A1 m1 md1 p n (a - ptr_addr L1 p) M1 HIN ltac:(lia)) as (_ & _ & Hc & _).
      lia. }
    exact (proj1 (proj2 (FR2 a (or_introl Hr) NO1 NO2 X NE')) W).
Qed.

Lemma chain_munch : forall K E F L A regs mem md L1 A1 m1 md1 W m2,
  chain K E F L A regs mem md L1 A1 m1 md1 -> munch W m1 m2 -> wmono segs m1 m2 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x ->
     (scratch_k Bm K regs x /\ alloc_ceiling <= x) \/ (E x /\ img_plain Bm x) \/
     ((exists q k, In (q, k) (blocks L1 A1) /\ q <= x < q + k) /\
      (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> ~ F (ptr_addr L p) ->
         ptr_addr L p <= x < ptr_addr L p + n -> E x))) ->
  chain K E F L A regs mem md L1 A1 m2 md1.
Proof using AX SEGS.
  intros K E F L A regs mem md L1 A1 m1 md1 W m2 CH MU WM HW.
  destruct CH as (M1 & W1 & B1 & LE1 & RG1 & AD1 & SV1 & Z1 & IO1 & VM1 & FR1 & BY1 & SW1).
  destruct (mr_model Bm MR rig_laws L1 A1 m1 md1 M1) as (Hh & Hl & Hm).
  assert (OWN : forall a, owned Bm L1 A1 a -> outside W a).
  { intros a Ho. pose proof (rig_owned_low L1 A1 m1 md1 a M1 Ho) as Hr.
    destruct (rig_outside_dec W a) as [O|O]; [exact O|].
    exfalso. destruct (HW a ltac:(pose proof alloc_ceiling_lt; lia) O) as [[_ X]|[[_ X]|[(q & k & Hq & Hx) _]]]; [lia| |].
    - exact (rig_plain_unowned L1 A1 m1 md1 a M1 X Ho).
    - pose proof (rig_blk L1 A1 m1 md1 q k (a - q) M1 Hq ltac:(lia)) as (_ & _ & _ & Hn).
      replace (q + (a - q)) with a in Hn by ring. exact (Hn Ho). }
  assert (M2 : MR L1 A1 m2 md1).
  { eapply (mr_frame Bm MR rig_laws L1 A1 m1 m2 md1 md1 M1).
    - intros a Ho. pose proof (rig_owned_low L1 A1 m1 md1 a M1 Ho).
      eapply munch_mbyte; [exact MU | pose proof alloc_ceiling_lt; lia | exact (OWN a Ho)].
    - intros a Ho Hp. pose proof (rig_owned_low L1 A1 m1 md1 a M1 Ho).
      eapply munch_present; [exact MU | pose proof alloc_ceiling_lt; lia | exact (OWN a Ho) | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks Bm MR rig_laws L1 A1 m1 md1 p n i M1 Hin Hi) as (Hp & H4 & Hc & _).
      pose proof alloc_ceiling_lt.
      apply (present_of_writable_out Bm SEGS m2 (ptr_addr L1 p + i) ltac:(lia)).
      + exact (ax_blocks_img AX L1 A1 m1 md1 p n i M1 Hin Hi).
      + rewrite <- SEGS. apply WM. exact (rig_present_writable segs m1 _ Hp).
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hm. }
  split; [exact M2|]. split; [exact W1|]. split; [exact B1|]. split; [exact LE1|]. split; [exact RG1|].
  split; [exact AD1|]. split; [exact SV1|]. split; [exact Z1|]. split; [exact IO1|]. split; [exact VM1|].
  split.
  { intros a Ha NO0 NO1 NS NE.
    assert (AR : 0 <= a < 2 ^ 64).
    { destruct Ha as [Ha|Ha]; [pose proof alloc_ceiling_val; lia|].
      pose proof (in_img_low Bm SEGS a Ha). lia. }
    assert (O : outside W a).
    { destruct (rig_outside_dec W a) as [O|O]; [exact O|].
      exfalso. destruct (HW a AR O) as [[X _]|[[X _]|[(q & k & Hq & Hx) _]]]; [exact (NS X) | exact (NE X) |].
      pose proof (rig_blk L1 A1 m1 md1 q k (a - q) M1 Hq ltac:(lia)) as (_ & H4 & Hc & _).
      destruct Ha as [Ha|Ha]; [lia|].
      apply rig_blocks_in in Hq as (p & Ep & Hp).
      apply (ax_blocks_img AX L1 A1 m1 md1 p k (a - q) M1 Hp ltac:(lia)). rewrite Ep.
      replace (q + (a - q)) with a by ring. exact Ha. }
    destruct (FR1 a Ha NO0 NO1 NS NE) as [E01 W01].
    split; [rewrite (munch_mbyte segs W m1 m2 a MU AR O); exact E01|].
    rewrite W01. exact (munch_writable segs W m1 m2 a MU AR O). }
  split.
  { intros p n i H0 H1 HF Hi HE.
    destruct (mr_blocks Bm MR rig_laws L1 A1 m1 md1 p n i M1 H1 Hi) as (_ & H4 & Hc & _).
    pose proof alloc_ceiling_lt.
    rewrite (AD1 p n H0 H1 HF) in H4, Hc.
    assert (O : outside W (ptr_addr L p + i)).
    { destruct (rig_outside_dec W (ptr_addr L p + i)) as [O|O]; [exact O|].
      exfalso. destruct (HW (ptr_addr L p + i) ltac:(lia) O) as [[_ X]|[[X _]|[_ X]]]; [lia | exact (HE X) |].
      exact (HE (X p n H0 H1 HF ltac:(lia))). }
    rewrite (munch_mbyte segs W m1 m2 (ptr_addr L p + i) MU ltac:(lia) O). exact (BY1 p n i H0 H1 HF Hi HE). }
  intros a Ha. apply WM. exact (SW1 a Ha).
Qed.

Definition kb2 (m m' : word -> option byte) (a : Z) : Prop :=
  mbyte segs m' a = mbyte segs m a /\ (writable_at segs m a -> writable_at segs m' a).

Definition bkept (L : layout) (A : astate) (m : word -> option byte) (L' : layout) (A' : astate)
    (m' : word -> option byte) (q : Z) : Prop :=
  forall k, In (q, k) (blocks L A) -> In (q, k) (blocks L' A') /\ forall i, 0 <= i < k -> kb2 m m' (q + i).

Lemma rw_kb2 : forall m m' a cs, rw_cells segs m a cs -> (forall i, 0 <= i < Z.of_nat (cells_size cs) -> kb2 m m' (a + i)) ->
  rw_cells segs m' a cs.
Proof. intros m m' a cs H K. apply (rw_cells_transfer segs m); [exact H|]. exact K. Qed.

Lemma bytes_kb2 : forall m m' a bs, bytes_at segs m a bs -> (forall i, 0 <= i < Z.of_nat (length bs) -> kb2 m m' (a + i)) ->
  bytes_at segs m' a bs.
Proof. intros m m' a bs H K. apply (bytes_at_transfer segs m); [exact H|]. intros i Hi. exact (proj1 (K i Hi)). Qed.

Lemma rw_in_block : forall L A m L' A' m' q k a cs, rw_cells segs m a cs -> bkept L A m L' A' m' q ->
  In (q, k) (blocks L A) -> q <= a -> a + Z.of_nat (cells_size cs) <= q + k -> rw_cells segs m' a cs.
Proof.
  intros L A m L' A' m' q k a cs H BK Hin H1 H2. apply (rw_kb2 m); [exact H|].
  intros i Hi. destruct (BK k Hin) as [_ X]. replace (a + i) with (q + (a + i - q)) by ring. apply X. lia.
Qed.

Lemma bytes_in_block : forall L A m L' A' m' q k a bs, bytes_at segs m a bs -> bkept L A m L' A' m' q ->
  In (q, k) (blocks L A) -> q <= a -> a + Z.of_nat (length bs) <= q + k -> bytes_at segs m' a bs.
Proof.
  intros L A m L' A' m' q k a bs H BK Hin H1 H2. apply (bytes_kb2 m); [exact H|].
  intros i Hi. destruct (BK k Hin) as [_ X]. replace (a + i) with (q + (a + i - q)) by ring. apply X. lia.
Qed.

Lemma rp_bkept : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q,
  MR L1 A1 m1 md1 ->
  relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 -> ~ F' q ->
  (forall k i, In (q, k) (blocks L1 A1) -> 0 <= i < k -> ~ E' (q + i)) ->
  bkept L1 A1 m1 L2 A2 m2 q.
Proof.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q M1 RP HF HE k Hin.
  destruct RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  apply rig_blocks_in in Hin as (p & Ep & Hp).
  pose proof (rig_ub_nonneg A1 p k (mr_wf Bm MR rig_laws L1 A1 m1 md1 M1) Hp) as Hk.
  subst q.
  destruct (Z.eq_dec k 0) as [->|Hk'].
  - destruct (Z2 p Hp) as [H2 E2]. split; [apply rig_blocks_in; exists p; split; [exact E2 | exact H2]|].
    intros i Hi. lia.
  - assert (H2 : In (p, k) (user_blocks A2)) by (apply SV2; [exact Hp | lia | exact HF]).
    pose proof (AD2 p k Hp H2 HF) as E2.
    split; [apply rig_blocks_in; exists p; split; [exact E2 | exact H2]|].
    intros i Hi. split.
    + apply (BY2 p k i Hp H2 HF Hi). apply HE with k; [apply rig_blocks_in; exists p; auto | exact Hi].
    + intros _. rewrite <- E2. apply rig_present_writable.
      exact (proj1 (mr_blocks Bm MR rig_laws L2 A2 m2 md2 p k i M2 H2 Hi)).
Qed.

Lemma rp_gkept : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 a,
  MR L1 A1 m1 md1 ->
  relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  (img_plain Bm a \/ alloc_ceiling <= a < 2 ^ 64) -> ~ E' a -> ~ scratch_k Bm K' R1 a ->
  kb2 m1 m2 a.
Proof using AX.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 a M1 RP Ha NE NS.
  destruct RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  assert (NO1 : ~ owned Bm L1 A1 a).
  { destruct Ha as [Ha|Ha]; [exact (rig_plain_unowned L1 A1 m1 md1 a M1 Ha)|].
    intros Ho. destruct (rig_owned_low L1 A1 m1 md1 a M1 Ho). lia. }
  assert (NO2 : ~ owned Bm L2 A2 a).
  { destruct Ha as [Ha|Ha]; [exact (rig_plain_unowned L2 A2 m2 md2 a M2 Ha)|].
    intros Ho. destruct (rig_owned_low L2 A2 m2 md2 a M2 Ho). lia. }
  assert (Ha' : alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) by (destruct Ha as [Ha|Ha]; [right; exact (proj1 Ha) | left; exact Ha]).
  destruct (FR2 a Ha' NO1 NO2 NS NE) as [E W]. split; [exact E | tauto].
Qed.

Lemma cp_bkept : forall L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p n q,
  MR L1 A1 m1 md1 ->
  call_post Bm MR L1 A1 R1 m1 md1 (fun a => ptr_addr L1 p <= a < ptr_addr L1 p + n) L2 A2 R2 m2 md2 ->
  (forall q k, In (q, k) (user_blocks A1) -> q <> p -> In (q, k) (user_blocks A2)) ->
  q <> ptr_addr L1 p ->
  bkept L1 A1 m1 L2 A2 m2 q.
Proof.
  intros L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p n q M1 CP KEEP Hq k Hin.
  destruct CP as (M2 & W2 & B2 & LE2 & AD2 & RPr & VM2 & FR2 & BY2 & SW2).
  apply rig_blocks_in in Hin as (p0 & Ep & Hp). subst q.
  assert (Hne : p0 <> p) by (intros ->; exact (Hq eq_refl)).
  pose proof (KEEP p0 k Hp Hne) as H2. pose proof (AD2 p0 k Hp H2) as E2.
  split; [apply rig_blocks_in; exists p0; split; [exact E2 | exact H2]|].
  intros i Hi. split; [exact (BY2 p0 k i Hp H2 Hi)|].
  intros _. rewrite <- E2. apply rig_present_writable.
  exact (proj1 (mr_blocks Bm MR rig_laws L2 A2 m2 md2 p0 k i M2 H2 Hi)).
Qed.

Lemma cp_gkept : forall L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p n a,
  MR L1 A1 m1 md1 -> In (p, n) (user_blocks A1) ->
  call_post Bm MR L1 A1 R1 m1 md1 (fun a => ptr_addr L1 p <= a < ptr_addr L1 p + n) L2 A2 R2 m2 md2 ->
  (img_plain Bm a \/ alloc_ceiling <= a < 2 ^ 64) -> ~ scratch Bm R1 a ->
  kb2 m1 m2 a.
Proof using AX.
  intros L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p n a M1 HIN CP Ha NS.
  destruct CP as (M2 & W2 & B2 & LE2 & AD2 & RPr & VM2 & FR2 & BY2 & SW2).
  assert (NO1 : ~ owned Bm L1 A1 a).
  { destruct Ha as [Ha|Ha]; [exact (rig_plain_unowned L1 A1 m1 md1 a M1 Ha)|].
    intros Ho. destruct (rig_owned_low L1 A1 m1 md1 a M1 Ho). lia. }
  assert (NO2 : ~ owned Bm L2 A2 a).
  { destruct Ha as [Ha|Ha]; [exact (rig_plain_unowned L2 A2 m2 md2 a M2 Ha)|].
    intros Ho. destruct (rig_owned_low L2 A2 m2 md2 a M2 Ho). lia. }
  assert (NE : ~ (ptr_addr L1 p <= a < ptr_addr L1 p + n)).
  { intros X. pose proof (mr_blocks Bm MR rig_laws L1 A1 m1 md1 p n (a - ptr_addr L1 p) M1 HIN ltac:(lia)) as (_ & _ & Hc & _).
    destruct Ha as [Ha|Ha]; [|lia].
    apply (ax_blocks_img AX L1 A1 m1 md1 p n (a - ptr_addr L1 p) M1 HIN ltac:(lia)).
    replace (ptr_addr L1 p + (a - ptr_addr L1 p)) with a by ring. exact (proj1 Ha). }
  assert (Ha' : alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) by (destruct Ha as [Ha|Ha]; [right; exact (proj1 Ha) | left; exact Ha]).
  destruct (FR2 a Ha' NO1 NO2 NS NE) as [E W]. split; [exact E | tauto].
Qed.

Lemma mu_kb2 : forall W m1 m2 a, munch W m1 m2 -> wmono segs m1 m2 -> 0 <= a < 2 ^ 64 -> outside W a -> kb2 m1 m2 a.
Proof.
  intros W m1 m2 a MU WM Ha O. split; [exact (munch_mbyte segs W m1 m2 a MU Ha O)|].
  intros X. apply WM. exact X.
Qed.

Lemma mu_bkept : forall L A W m1 m2 md q, MR L A m1 md -> munch W m1 m2 -> wmono segs m1 m2 ->
  (forall k i, In (q, k) (blocks L A) -> 0 <= i < k -> outside W (q + i)) -> bkept L A m1 L A m2 q.
Proof.
  intros L A W m1 m2 md q M1 MU WM HO k Hin. split; [exact Hin|].
  intros i Hi. destruct (rig_blk L A m1 md q k i M1 Hin Hi) as (_ & H4 & Hc & _). pose proof alloc_ceiling_lt.
  apply (mu_kb2 W); [exact MU | exact WM | lia | exact (HO k i Hin Hi)].
Qed.

Definition with_keys (e : rentry) (ks : list (Z * list byte * list byte)) : rentry :=
  RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e) (re_hp e) (re_kh e) (re_pad2 e)
     ks (re_U e) (re_junk e).

Lemma with_keys_self : forall e, with_keys e (re_keys e) = e.
Proof. intros []. reflexivity. Qed.

Lemma map_fst_ext : forall {B} (g : Z * list byte -> B) (ks ks' : list (Z * list byte * list byte)),
  map fst ks' = map fst ks -> map (fun k => g (fst k)) ks' = map (fun k => g (fst k)) ks.
Proof. intros B g ks ks' H. rewrite <- (map_map fst g ks'), <- (map_map fst g ks), H. reflexivity. Qed.

Lemma map_fst_keys : forall (ks ks' : list (Z * list byte * list byte)), map fst ks' = map fst ks ->
  map key_addr ks' = map key_addr ks /\ map key_text ks' = map key_text ks /\ length ks' = length ks /\
  key_ptrs ks' = key_ptrs ks /\ keys_texts ks' = keys_texts ks.
Proof.
  intros ks ks' H.
  assert (A1 : map key_addr ks' = map key_addr ks) by exact (map_fst_ext fst ks ks' H).
  assert (A2 : map key_text ks' = map key_text ks) by exact (map_fst_ext snd ks ks' H).
  assert (A3 : length ks' = length ks) by (rewrite <- (length_map fst ks'), <- (length_map fst ks), H; reflexivity).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split.
  - unfold key_ptrs. f_equal. exact (map_fst_ext (fun x => le8 (Z_to_bv 64 (fst x))) ks ks' H).
  - unfold keys_texts. exact (map_fst_ext (fun x => bzs (snd x)) ks ks' H).
Qed.

Lemma map_fst_in : forall (ks ks' : list (Z * list byte * list byte)) k', map fst ks' = map fst ks -> In k' ks' ->
  exists k, In k ks /\ fst k = fst k'.
Proof.
  intros ks ks' k' H Hin. assert (X : In (fst k') (map fst ks)) by (rewrite <- H; apply in_map; exact Hin).
  apply in_map_iff in X as (k & E & Hk). exists k. auto.
Qed.

Lemma entry_bytes_wk : forall e ks, length ks = length (re_keys e) -> entry_bytes (with_keys e ks) = entry_bytes e.
Proof. intros e ks H. unfold entry_bytes, re_nheld. cbn [with_keys re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_keys re_pad2]. rewrite H. reflexivity. Qed.

Lemma entry_blocks_wk : forall e ks, map key_addr ks = map key_addr (re_keys e) -> entry_blocks (with_keys e ks) = entry_blocks e.
Proof. intros e ks H. unfold entry_blocks. cbn [with_keys re_cap re_buf re_hp re_keys]. rewrite H. reflexivity. Qed.

Lemma length_key_ptrs : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof. induction ks as [|k ks IH]; [reflexivity|]. unfold key_ptrs in *. cbn [map concat length]. rewrite length_app, length_le8, IH. lia. Qed.

Definition entry_okk (L : layout) (A : astate) (m : word -> option byte) (e : rentry) : Prop :=
  exists ks, map fst ks = map fst (re_keys e) /\ entry_ok Bm L A m (with_keys e ks).

Lemma entry_okk_of : forall L A m e, entry_ok Bm L A m e -> entry_okk L A m e.
Proof. intros L A m e H. exists (re_keys e). split; [reflexivity|]. rewrite with_keys_self. exact H. Qed.

Lemma slack_at : forall L A m md q n, MR L A m md -> In (q, n) (blocks L A) ->
  exists sl, bytes_at segs m (q + n) sl /\ Z.of_nat (length sl) = (- (q + n)) mod 8.
Proof using BSP.
  intros L A m md q n HM Hin.
  pose proof Hin as Hin'. apply rig_blocks_in in Hin' as (p & Ep & Hp).
  pose proof (rig_ub_nonneg A p n (mr_wf Bm MR rig_laws L A m md HM) Hp) as Hn.
  pose proof (mr_blocks_range Bm MR rig_laws L A m md p n HM Hp) as (H4 & Hc). rewrite Ep in H4, Hc.
  pose proof alloc_ceiling_lt as HL.
  pose proof (Z.mod_pos_bound (- (q + n)) 8 ltac:(lia)) as Hr.
  destruct (present_rw_cells segs m (q + n) (Z.to_nat ((- (q + n)) mod 8))) as [junk H]; [lia | rewrite Z2Nat.id by lia; lia | |].
  { intros i Hi. rewrite Z2Nat.id in Hi by lia. apply (BSP L A m md q n (q + n + i) HM Hin).
    Z.div_mod_to_equations. lia. }
  exists junk. destruct H as [[Hwf Hb] _]. cbn in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. split; [exact Hb|]. rewrite Hl. lia.
Qed.

Lemma reslack : forall L A m md (ks : list (Z * list byte * list byte)), MR L A m md ->
  Forall (fun k => In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L A)) ks ->
  exists ks', map fst ks' = map fst ks /\
    Forall (fun k => bytes_at segs m (key_addr k + (Z.of_nat (length (key_text k)) + 1)) (key_slack k) /\
       (- (key_addr k + Z.of_nat (length (key_text k)) + 1)) mod 8 <= Z.of_nat (length (key_slack k))) ks'.
Proof using BSP.
  intros L A m md ks HM. induction ks as [|k ks IH]; intros HF.
  - exists []. split; [reflexivity | constructor].
  - pose proof (Forall_inv HF) as Hk. pose proof (Forall_inv_tail HF) as HF'.
    destruct (IH HF') as (ks' & E & F').
    destruct (slack_at L A m md _ _ HM Hk) as (sl & Hb & Hl).
    exists ((fst k, sl) :: ks'). split; [cbn [map]; rewrite E; reflexivity|].
    constructor; [|exact F']. unfold key_addr, key_text, key_slack in *. cbn [fst snd]. split; [exact Hb|].
    rewrite Hl. replace (- (fst (fst k) + Z.of_nat (length (snd (fst k))) + 1))
      with (- (fst (fst k) + (Z.of_nat (length (snd (fst k))) + 1))) by ring. lia.
Qed.

Lemma entry_okk_kept : forall L A m L' A' m' md' e,
  entry_okk L A m e -> MR L' A' m' md' ->
  (forall q, In q (entry_blocks e) -> bkept L A m L' A' m' q) ->
  entry_okk L' A' m' e.
Proof using BSP.
  intros L A m L' A' m' md' e (ks & Eks & OK) M' BK.
  destruct (map_fst_keys (re_keys e) ks Eks) as (EA & ET & EL & EP & EX).
  rewrite <- (entry_blocks_wk e ks EA) in BK.
  unfold entry_ok in OK.
  destruct OK as (Heof & Hskip & Hp1 & Hp2 & Hfd & Hcap & HU & Hused & HUz & Hbuf & Hnh & Hhp & NDa & NDt & Hkeys).
  cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_junk re_hp re_kh re_keys with_keys] in *.
  unfold re_nheld in Hnh, Hhp. cbn [re_keys with_keys] in Hnh, Hhp.
  assert (KB : Forall (fun k => In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L' A')) ks).
  { apply Forall_forall. intros k Hk. pose proof (proj1 (Forall_forall _ _) Hkeys k Hk) as (H1 & _).
    refine (proj1 (BK (key_addr k) _ _ H1)).
    unfold entry_blocks. cbn [with_keys re_cap re_buf re_hp re_keys].
    apply in_or_app; right; apply in_or_app; right; apply in_map; exact Hk. }
  destruct (reslack L' A' m' md' ks M' KB) as (ks' & E' & F').
  destruct (map_fst_keys ks ks' E') as (EA' & ET' & EL' & EP' & EX').
  exists ks'. split; [rewrite E'; exact Eks|].
  unfold entry_ok, re_nheld. cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_junk re_hp re_kh re_keys with_keys].
  rewrite EL', EP', EA', ET'.
  do 9 (split; [assumption|]).
  split.
  { destruct Hbuf as [Hb|(H0 & Hin & Hf & Hj & Hrw)]; [left; exact Hb|right].
    assert (Hq : In (re_buf e) (entry_blocks (with_keys e ks))).
    { unfold entry_blocks. cbn [with_keys re_cap re_buf re_hp re_keys].
      destruct (re_cap e =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|]. left. reflexivity. }
    pose proof (BK _ Hq) as Hb. destruct (Hb _ Hin) as [Hin' _].
    split; [exact H0|]. split; [exact Hin'|]. split; [exact Hf|]. split; [exact Hj|].
    eapply rw_in_block; [exact Hrw | exact Hb | exact Hin | lia | cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia]. }
  split; [exact Hnh|].
  split.
  { destruct Hhp as [Hh|(Hin & Hf & H8 & H8' & Hb0)]; [left; destruct Hh as [Hh0 Hh1]; split; [exact Hh0|]; subst ks; destruct ks'; [reflexivity | discriminate]|right].
    assert (Hq : In (re_hp e) (entry_blocks (with_keys e ks))).
    { unfold entry_blocks. cbn [with_keys re_cap re_buf re_hp re_keys].
      destruct Hf as (Hf0 & _). destruct (re_hp e =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|].
      apply in_or_app; right; left; reflexivity. }
    pose proof (BK _ Hq) as Hb. destruct (Hb _ Hin) as [Hin' _].
    split; [exact Hin'|]. split; [exact Hf|]. split; [exact H8|]. split; [exact H8'|].
    eapply bytes_in_block; [exact Hb0 | exact Hb | exact Hin | lia | rewrite length_key_ptrs; lia]. }
  split; [exact NDa|]. split; [exact NDt|].
  apply Forall_forall. intros k' Hk'.
  destruct (map_fst_in ks ks' k' E' Hk') as (k & Hk & Ek).
  pose proof (proj1 (Forall_forall _ _) Hkeys k Hk) as (H1 & H2 & H3 & H4 & H5 & H6).
  pose proof (proj1 (Forall_forall _ _) F' k' Hk') as (S1 & S2).
  assert (EK1 : key_addr k' = key_addr k) by (unfold key_addr; rewrite Ek; reflexivity).
  assert (EK2 : key_text k' = key_text k) by (unfold key_text; rewrite Ek; reflexivity).
  rewrite EK1, EK2 in *.
  assert (Hq : In (key_addr k) (entry_blocks (with_keys e ks))).
  { unfold entry_blocks. cbn [with_keys re_cap re_buf re_hp re_keys].
    apply in_or_app; right; apply in_or_app; right; apply in_map; exact Hk. }
  pose proof (BK _ Hq) as Hb. destruct (Hb _ H1) as [H1' _].
  split; [exact H1'|]. split; [exact H2|].
  split.
  { replace (key_text k ++ Z_to_bv 8 0 :: key_slack k') with ((key_text k ++ [Z_to_bv 8 0]) ++ key_slack k')
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split.
    - replace (key_text k ++ Z_to_bv 8 0 :: key_slack k) with ((key_text k ++ [Z_to_bv 8 0]) ++ key_slack k) in H3
        by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app in H3. destruct H3 as [H3 _].
      eapply bytes_in_block; [exact H3 | exact Hb | exact H1 | lia | rewrite length_app; cbn [length]; lia].
    - rewrite length_app. cbn [length]. replace (key_addr k + Z.of_nat (length (key_text k) + 1))
        with (key_addr k + (Z.of_nat (length (key_text k)) + 1)) by lia. exact S1. }
  split; [exact H4|]. split; [exact H5|]. exact S2.
Qed.

Lemma list_at_kept : forall L A m L' A' m' LA l b,
  list_at Bm L A m LA l b -> (forall i, 0 <= i < 16 -> kb2 m m' (LA + i)) ->
  (forall q, In q (list_blocks l) -> bkept L A m L' A' m' q) ->
  list_at Bm L' A' m' LA l b.
Proof.
  intros L A m L' A' m' LA l b (Hc & Hn & Hv & ND1 & ND2 & Hr) KG BK.
  split; [apply (rw_kb2 m); [exact Hc | intros i Hi; cbn in Hi; apply KG; lia]|].
  split; [exact Hn|].
  split.
  { destruct Hv as [Hv|(H0 & Hin & Hf & Hj & Hrw)]; [left; exact Hv|right].
    assert (Hq : In (hl_v l) (list_blocks l)).
    { unfold list_blocks. destruct (hl_cap l =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|]. left. reflexivity. }
    pose proof (BK _ Hq) as Hb. destruct (Hb _ Hin) as [Hin' _].
    split; [exact H0|]. split; [exact Hin'|]. split; [exact Hf|]. split; [exact Hj|].
    eapply rw_in_block; [exact Hrw | exact Hb | exact Hin | lia | cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia]. }
  split; [exact ND1|]. split; [exact ND2|].
  apply Forall_forall. intros r Hr0. pose proof (proj1 (Forall_forall _ _) Hr r Hr0) as (H1 & H2 & H3 & H4 & H5).
  assert (Hq : In (fst r) (list_blocks l)) by (unfold list_blocks; apply in_or_app; right; apply in_map; exact Hr0).
  pose proof (BK _ Hq) as Hb. destruct (Hb _ H1) as [H1' _].
  split; [exact H1'|]. split; [exact H2|].
  split; [eapply rw_in_block; [exact H3 | exact Hb | exact H1 | lia | cbn [cells_size csize]; lia]|].
  split; assumption.
Qed.

Lemma src_at_kept : forall L A m L' A' m' HA h,
  src_at Bm L A m HA h -> (forall i, 0 <= i < 96 -> kb2 m m' (HA + i)) ->
  (forall q, In q (hs_blocks h) -> bkept L A m L' A' m' q) ->
  src_at Bm L' A' m' HA h.
Proof.
  intros L A m L' A' m' HA h
    (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18) KG BK.
  assert (BKp : forall q, In q (list_blocks (hs_pending h)) -> bkept L A m L' A' m' q)
    by (intros q Hq; apply BK; unfold hs_blocks; apply in_or_app; left; exact Hq).
  assert (BKe : forall q, In q (list_blocks (hs_expected h)) -> bkept L A m L' A' m' q)
    by (intros q Hq; apply BK; unfold hs_blocks; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hq).
  assert (BKh : forall q, In q (list_blocks (hs_held h)) -> bkept L A m L' A' m' q)
    by (intros q Hq; apply BK; unfold hs_blocks; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hq).
  assert (BKq : bkept L A m L' A' m' (hs_partial h))
    by (apply BK; unfold hs_blocks; apply in_or_app; right; left; reflexivity).
  split; [apply (rw_kb2 m); [exact S1 | intros i Hi; cbn in Hi; apply KG; lia]|].
  split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|].
  split; [apply (list_at_kept L A m); [exact S6 | intros i Hi; replace (HA + 16 + i) with (HA + (16 + i)) by ring; apply KG; lia | exact BKp]|].
  split; [apply (rw_kb2 m); [exact S7 | intros i Hi; cbn in Hi; replace (HA + 32 + i) with (HA + (32 + i)) by ring; apply KG; lia]|].
  split; [exact S8|]. split; [exact S9|]. split; [exact S10|].
  split; [exact (proj1 (BKq _ S11))|]. split; [exact S12|]. split; [exact S13|].
  split; [eapply rw_in_block; [exact S14 | exact BKq | exact S11 | lia | cbn [cells_size csize]; lia]|].
  split; [exact S15|].
  split; [apply (list_at_kept L A m); [exact S16 | intros i Hi; replace (HA + 64 + i) with (HA + (64 + i)) by ring; apply KG; lia | exact BKe]|].
  split; [apply (list_at_kept L A m); [exact S17 | intros i Hi; replace (HA + 80 + i) with (HA + (80 + i)) by ring; apply KG; lia | exact BKh]|].
  exact S18.
Qed.

Lemma rig_run : forall (fxc : YK11.FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  ro_agree segs mem -> m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs Q (MS (Regs6ss.mkR_of regs) (@fp_regs fxc) pc (@fp_csr fxc) None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall s0 R' m', Q s0 -> mem_rel rsegs m' (ms_mem s0) -> ro_same rsegs mem m' -> Regs6ss.xregs_eqv (ms_regs s0) R' ->
     SR segs (mkCfg {| ms_regs := R'; ms_fregs := ms_fregs s0; ms_pc_val := ms_pc_val s0;
                       ms_svc_pending := ms_svc_pending s0; ms_resv := ms_resv s0; ms_fcsr := ms_fcsr s0;
                       ms_mem := m'; ms_rom := ms_rom s0 |} md) P) ->
  SR segs (mkCfg (@YK11.mkst fxc regs pc mem (seg_rom segs)) md) P.
Proof using SEGS.
  intros fxc regs pc mem md Q P RA Hh Hl HE K.
  apply (evt_SR_canon segs (@YK11.mkst fxc regs pc mem (seg_rom segs))
           (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s)) md P); [ | exact Hh | exact Hl | ].
  - rewrite SEGS. change (RegisterBridge.canonical_register_state (@YK11.mkst fxc regs pc mem (seg_rom rsegs)))
      with (MS (Regs6ss.mkR_of regs) (@fp_regs fxc) pc (@fp_csr fxc) None mem (seg_rom rsegs)).
    apply (evt_normalize rsegs); [vm_compute; reflexivity | rewrite <- SEGS; exact RA | exact HE].
  - intros ms' (can & (s0 & HQ & HR & HO) & HEQ).
    destruct ms' as [r f pv sv rv c mm o], can as [cr cf cp csv crv cc cmm co], s0 as [zr zf zp zsv zrv zc zmm zo].
    destruct HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
    destruct HEQ as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
    subst.
    exact (K _ r mm HQ R8 HO E1).
Qed.

(* The states and capacities of a run do not depend on its addresses; a drain's held keys' addresses keep pace with
   its held keys. *)
Lemma gsh_seen : forall H ka l j ha ks j' ha' ks',
  snd (fst (seen_tr H ka l j ha ks)) = snd (fst (seen_tr H ka l j' ha' ks')) /\
  (length ks = length H -> length (snd (snd (seen_tr H ka l j ha ks))) = length (seen_arr H l)).
Proof.
  intros H ka l j ha ks j' ha' ks'. unfold seen_tr, seen_arr.
  destruct (gesture l) as [[g x]|]; [destruct g; destruct (index_of x H)|]; cbn [fst snd];
    (split; [reflexivity | intros E]); rewrite ?length_app, ?rigl_len_swap; cbn [length]; lia.
Qed.

Lemma gsh_lines : forall ls live mx no cap H ka j o ha ks j' o' ha' ks',
  snd (fst (lines_run live mx no cap H ka ls j o ha ks)) = snd (fst (lines_run live mx no cap H ka ls j' o' ha' ks')) /\
  (length ks = length H ->
   length (snd (snd (lines_run live mx no cap H ka ls j o ha ks))) =
   length (snd (fst (snd (fst (lines_run live mx no cap H ka ls j o ha ks)))))).
Proof.
  induction ls as [|l r IH]; intros live mx no cap H ka j o ha ks j' o' ha' ks'; cbn [lines_run fst snd].
  - split; [reflexivity | intros E; exact E].
  - match goal with |- context [seen_tr H ka l ?j1 ha ks] => match goal with |- context [seen_tr H ka l ?j2 ha' ks'] =>
      destruct (gsh_seen H ka l j1 ha ks j2 ha' ks') as [S1 S2] end end.
    rewrite <- S1. split.
    + apply (proj1 (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    + intros E. apply (proj2 (IH _ _ _ _ _ _ _ _ _ _ 0%nat adr0 adr0 [])). apply S2. exact E.
Qed.

Lemma gsh_pushes : forall ls n cap j v rs j' v' rs',
  snd (fst (pushes_run n cap ls j v rs)) = snd (fst (pushes_run n cap ls j' v' rs')).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs j' v' rs'; cbn [pushes_run fst snd]; [reflexivity | apply IH].
Qed.

Lemma gsh_grow : forall c u j b j' b', fst (snd (grow_tr c u j b)) = fst (snd (grow_tr c u j' b')).
Proof. intros c u j b j' b'. unfold grow_tr. destruct (c - u <? 4096); reflexivity. Qed.

Lemma gsh_drain : forall f live mx s j a j' a',
  fst (snd (drain_run f live mx s j a)) = fst (snd (drain_run f live mx s j' a')) /\
  (length (da_keys a) = length (ds_H s) ->
   length (da_keys (snd (snd (drain_run f live mx s j a)))) = length (ds_H (fst (snd (drain_run f live mx s j a))))).
Proof.
  induction f as [|f IH]; intros live mx s j a j' a'; cbn [drain_run]; [split; [reflexivity | intros E; exact E]|].
  rewrite (gsh_grow (ds_cap s) (Z.of_nat (length (ds_u s))) j' (da_buf a') j (da_buf a)).
  destruct (ds_eintr s).
  - cbn [fst snd]. split; [apply (proj1 (IH _ _ _ _ _ _ _)) | intros E; apply (proj2 (IH _ _ _ _ _ 0%nat dadr0)); exact E].
  - destruct (ds_pend s) as [|r0 rs]; [cbn [fst snd]; split; [reflexivity | intros E; exact E]|].
    match goal with |- context [if (?x <=? 0) then _ else _] => destruct (x <=? 0) end;
      [cbn [fst snd]; split; [reflexivity | intros E; exact E]|].
    match goal with |- context [chunk ?u ?sk ?d] => destruct (chunk u sk d) as [[u' sk'] rl] end.
    match goal with |- context [snd (fst (pushes_run ?n ?c ?ls ?j1 (da_ev a) ?r1))] =>
      match goal with |- context [snd (fst (pushes_run n c ls ?j2 (da_ev a') ?r2))] =>
        rewrite (gsh_pushes ls n c j2 (da_ev a') r2 j1 (da_ev a) r1) end end.
    match goal with |- context [lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?J1 (da_out a) (da_hp a) (da_keys a)] =>
      match goal with |- context [lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?J2 (da_out a') (da_hp a') (da_keys a')] =>
        pose proof (gsh_lines rl live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) J1 (da_out a) (da_hp a) (da_keys a)
                      J2 (da_out a') (da_hp a') (da_keys a')) as [LS LL];
        rewrite <- LS; revert LL;
        destruct (lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl J1 (da_out a) (da_hp a) (da_keys a))
          as [[t1 [[oc' H'] ka']] [[o' ha'] ks']];
        destruct (lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl J2 (da_out a') (da_hp a') (da_keys a'))
          as [[t2 [[oc2 H2] ka2]] [[o2 ha2] ks2]]
      end end.
    cbn [fst snd]. intros LL. split.
    + apply (proj1 (IH _ _ _ _ _ _ _)).
    + intros E. apply (proj2 (IH _ _ _ _ _ 0%nat dadr0)). exact (LL E).
Qed.

Lemma gsh_after : forall lv mx no cap e h j a, length (da_keys a) = length (re_keys e) ->
  length (da_keys (after_drain_adr lv mx no cap e h j a)) = length (ds_H (after_drain lv mx no cap e h)).
Proof.
  intros lv mx no cap e h j a E. unfold after_drain_adr, after_drain.
  destruct (re_eof e =? 0); [|unfold drain_init; cbn [ds_H]; unfold keys_texts; rewrite length_map; exact E].
  unfold drain_adr, drain_fin, drain_go.
  rewrite (proj1 (gsh_drain _ lv mx (drain_init no cap e h) 0%nat dadr0 j a)).
  apply (proj2 (gsh_drain _ lv mx (drain_init no cap e h) j a 0%nat dadr0)).
  unfold drain_init. cbn [ds_H]. unfold keys_texts. rewrite length_map. exact E.
Qed.

Lemma gsh_geia : forall f pre n (Ha : list (list Z * adrF)),
  map fst (fst (geia_loop f pre n Ha)) = fst (gei_loop f pre n (map fst Ha)) /\
  map fst (snd (geia_loop f pre n Ha)) = snd (gei_loop f pre n (map fst Ha)).
Proof.
  induction f as [|f IH]; intros pre n Ha; cbn [geia_loop gei_loop]; [split; reflexivity|].
  rewrite length_map. destruct (Nat.ltb n (length Ha)) eqn:Hl; [|split; reflexivity].
  replace (nth n (map fst Ha) []) with (fst (nth n Ha ([], adr0)))
    by (rewrite <- (map_nth fst Ha ([], adr0) n); reflexivity).
  destruct (has_prefix pre (fst (nth n Ha ([], adr0)))).
  - replace (swap_remove [] n (map fst Ha)) with (map fst (swap_remove ([], adr0) n Ha))
      by (rewrite (rig_swap_map fst ([], adr0) n Ha) by (apply Nat.ltb_lt; exact Hl); reflexivity).
    pose proof (IH pre n (swap_remove ([], adr0) n Ha)) as [E1 E2]. revert E1 E2.
    destruct (geia_loop f pre n (swap_remove ([], adr0) n Ha)) as [Ea Ha'].
    destruct (gei_loop f pre n (map fst (swap_remove ([], adr0) n Ha))) as [Et Ht].
    cbn [fst snd map]. intros E1 E2. rewrite E1. split; [reflexivity | exact E2].
  - exact (IH pre (S n) Ha).
Qed.

Lemma gsh_combine_fst : forall {X Y} (l : list X) (l' : list Y), length l = length l' -> map fst (combine l l') = l.
Proof.
  intros X Y l. induction l as [|x l IH]; intros [|y l'] E; cbn [length] in E; try lia; [reflexivity|].
  cbn [combine map fst]. rewrite IH by lia. reflexivity.
Qed.

Lemma gsh_xks : forall pre (H : list (list Z)) (ka : list adrF), length ka = length H ->
  map fst (map (fun x => (Z.of_nat (length (fst x)), snd x)) (fst (geia pre (combine H ka)))) =
  map (fun x => Z.of_nat (length x)) (fst (gei pre H)).
Proof.
  intros pre H ka E. rewrite map_map. cbn [fst].
  rewrite <- (map_map fst (fun x => Z.of_nat (length x))). f_equal.
  unfold geia, gei. rewrite (proj1 (gsh_geia _ pre 0 _)), gsh_combine_fst by lia.
  rewrite length_combine, E, Nat.min_id. reflexivity.
Qed.

Lemma gone_shape : forall lv mx pre ps no cap nm j o nm' j' o',
  snd (fst (fst (gone_run lv mx no cap pre ps nm j o))) = snd (fst (fst (gone_run lv mx no cap pre ps nm' j' o'))) /\
  snd (fst (gone_run lv mx no cap pre ps nm j o)) = snd (fst (gone_run lv mx no cap pre ps nm' j' o')).
Proof.
  intros lv mx pre ps. induction ps as [|[e hj] r IH]; intros no cap nm j o nm' j' o'; [split; reflexivity|].
  rewrite !rig_gone_run_cons. cbv zeta. cbn [fst snd].
  assert (LD : forall nm0 j0 o0,
    length (da_keys (after_drain_adr lv mx no cap e (fst hj) j0 (drain_start nm0 o0 e (fst hj)))) =
    length (ds_H (after_drain lv mx no cap e (fst hj)))).
  { intros nm0 j0 o0. apply gsh_after. unfold drain_start. cbn [da_keys]. rewrite length_map. reflexivity. }
  rewrite (gsh_xks pre _ _ (LD nm j o)), (gsh_xks pre _ _ (LD nm' j' o')).
  match goal with |- context [fst (snd (keys_end_run lv mx ?n0 ?c0 ?x1 ?j1 ?o1))] =>
    match goal with |- context [fst (snd (keys_end_run lv mx n0 c0 ?x2 ?j2 ?o2))] =>
      progress rewrite (CF.gestures_end_b.p3b_ker_cap lv mx x1 x2 n0 c0 j1 o1 j2 o2)
        by (rewrite (gsh_xks pre _ _ (LD nm j o)), (gsh_xks pre _ _ (LD nm' j' o')); reflexivity) end end.
  split; [apply (proj1 (IH _ _ _ _ _ _ _ _)) | f_equal; apply (proj2 (IH _ _ _ _ _ _ _ _))].
Qed.

Section GONE.
Variables (fx0 : YK11.FPState) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
  (md0 : Model) (bnd : rt_R RF) (es : list rentry) (G : Z) (tail0 : list byte) (hs : list (hsrc * nat))
  (fs os : list Z) (O junk : list byte) (cl br dd ei : Z) (mx nout cap out : word).

Definition gNO : Z := bv_unsigned nout.
Definition gCAP : Z := bv_unsigned cap.
Definition gOUT : Z := bv_unsigned out.
Definition gS : Z := spZ regs0.
Definition gP : Z := gS - 160.
Definition gpre : list Z := instance_prefix (bv_signed (getr regs0 10)).
Definition gN : Z := Z.of_nat (length es).

(* The model of the run (relay_instance_gone_b_c.gone_run) from the entry's g_nout and g_capout, base 0, g_out at its
   entry block and the sources' blocks named by the entry state. *)
Definition glv : bool := send_live cl br dd 1.
Definition gmx : Z := bv_unsigned mx.
Definition gps : list (rentry * (hsrc * nat)) := combine es hs.
Definition gnm : Z -> adrF := known_at L0 A0.
Definition grun : trF * Z * list dstate * (adrF * list dadr) := gone_run glv gmx gNO gCAP gpre gps gnm 0 (gnm gOUT).
Definition gtr : trF := fst (fst (fst grun)).
Definition gss : list dstate := snd (fst grun).
Definition gs_of (i : nat) : dstate := nth i gss (drain_init gNO gCAP (nth i es no_entry) (fst (nth i hs no_hj))).
Definition gxls (ks0 : list (list Z)) : list Z := map (fun x => Z.of_nat (length x)) (fst (gei gpre ks0)).
(* The keys a source ends, with their addresses, from its held keys ks0 at ka0 after its drain; the addresses of
   the keys it keeps. *)
Definition gxks (ks0 : list (list Z)) (ka0 : list adrF) : list (Z * adrF) :=
  map (fun x => (Z.of_nat (length (fst x)), snd x)) (fst (geia gpre (combine ks0 ka0))).
Definition gkept (ks0 : list (list Z)) (ka0 : list adrF) : list adrF := map snd (snd (geia gpre (combine ks0 ka0))).

(* The rest of the run from g_nout = nom, g_capout = capm, base j and g_out at o: before source i (gpos_top), or in
   source i's key loop, its addresses a after its drain and its kept keys at kept, with the requests pfx (no
   returns), then the ends of the keys xks left (gpos_k). *)
Definition gpos_top (i : nat) (nom capm : Z) (j : nat) (o : adrF) : trF * Z * list dstate * (adrF * list dadr) :=
  gone_run glv gmx nom capm gpre (skipn i gps) gnm j o.

Definition gpos_k (i : nat) (a : dadr) (kept : list adrF) (pfx : trF) (xks : list (Z * adrF)) (nom capm : Z)
    (j : nat) (o : adrF) : trF * Z * list dstate * (adrF * list dadr) :=
  let k := keys_end_run glv gmx nom capm xks (j + nretF pfx) o in
  let r := gone_run glv gmx (nom + fold_right (fun xl acc => xl + 5 + acc) 0 (map fst xks)) (fst (snd k))
             gpre (skipn (S i) gps) gnm (j + nretF pfx + nretF (fst k)) (snd (snd k)) in
  (pfx ++ fst k ++ fst (fst (fst r)), snd (fst (fst r)), gs_of i :: snd (fst r),
   (fst (snd r), DA (snd (snd k)) (da_buf a) (da_hp a) kept (da_pend a) (da_ev a) (da_erecs a) :: snd (snd r))).

(* Source j's blocks at the addresses fa resolved by qs, once its run is over. *)
Definition done_links (L : layout) (A : astate) (qs : list sptr) (j : nat) (fa : dadr) (e' : rentry) (h' : hsrc)
    : Prop :=
  entry_links L A qs fa e' /\ (re_eof (nth j es no_entry) = 0 -> src_links L A qs gnm fa h').

(* The requests dn are done, returning qd, and the run's rest is P from base nret dn with g_out at oa: the whole run
   is dn then P, with i sources' states and addresses before P's. g_out and the finished sources' blocks are at
   their addresses resolved by qd and any later returns. *)
Definition gpos (P : nat -> adrF -> trF * Z * list dstate * (adrF * list dadr)) (dn : trF) (i : nat) (L : layout)
    (A : astate) (qd : list sptr) (es_c : list rentry) (hs_c : list hsrc) (live : bool) (OUTc CAPc : Z) : Prop :=
  exists oa ssd dsd,
    length ssd = i /\ length dsd = i /\
    grun = (dn ++ fst (fst (fst (P (nretF dn) oa))), snd (fst (fst (P (nretF dn) oa))),
            ssd ++ snd (fst (P (nretF dn) oa)), (fst (snd (P (nretF dn) oa)), dsd ++ snd (snd (P (nretF dn) oa)))) /\
    (live = true -> forall post, live_at L A (resolveF (qd ++ post) oa) OUTc CAPc) /\
    (live = false -> oa = gnm gOUT /\ (0 < gCAP -> live_at L A (sptr_of L0 A0 gOUT) gOUT gCAP)) /\
    (forall j, (j < i)%nat -> forall post,
       done_links L A (qd ++ post) j (nth j dsd dadr0) (nth j es_c no_entry) (nth j hs_c (fst (nth j hs no_hj)))).

Definition Eall (a : Z) : Prop :=
  send_writes true gOUT gCAP a \/ G_LOCK + 4 <= a < G_LOCK + 8 \/ G <= a < G + SRC_TABLE \/ drained_area es hs a \/
  (exists q m, In q (concat (map entry_blocks es) ++ drained_blocks es hs) /\ In (q, m) (blocks L0 A0) /\ q <= a < q + m).

Definition Fcur (T : Z) (q : Z) : Prop :=
  (send_live cl br dd T = true /\ q = gOUT) \/ In q (concat (map entry_blocks es)) \/ In q (drained_blocks es hs).

Definition seg_of (kss : list (list (list Z))) (j : nat) : list Z :=
  gone_segment gpre (entry_lines (nth j es no_entry) (nth j hs no_hj)) (nth j kss []).

Definition gHA (j : nat) : Z := G_S + SRC_SIZE * Z.of_nat (snd (nth j hs no_hj)).

Definition pl_of (j : nat) : Z :=
  if re_eof (nth j es no_entry) =? 0 then Z.of_nat (length (pending_stream (fst (nth j hs no_hj)))) else 0.

Definition gbound (i : nat) : Z :=
  fold_right Z.add 0 (map (fun j => pl_of j + 6001 + 6005 * (re_nheld (nth j es no_entry) + pl_of j)) (seq 0 i)).

Definition saved_cells : list cell :=
  [C8 (getr regs0 27); C8 (getr regs0 26); C8 (getr regs0 25); C8 (getr regs0 24); C8 (getr regs0 23);
   C8 (getr regs0 22); C8 (getr regs0 21); C8 (getr regs0 20); C8 (getr regs0 19); C8 (getr regs0 18);
   C8 (getr regs0 9); C8 (getr regs0 8); C8 (getr regs0 1)].

(* Source j's fields that its drain's state fixes (relay_instance_gone_b_c: s = nth j ss ...). *)
Definition dsrel (j : nat) (e' : rentry) (h' : hsrc) (ks : list (list Z)) : Prop :=
  let e := nth j es no_entry in
  let h := fst (nth j hs no_hj) in
  let s := gs_of j in
  ks = ds_H s /\ re_cap e' = ds_cap s /\ bzs (re_U e') = ds_u s /\ re_skip e' = (if ds_skip s then 1 else 0) /\
  ent_ka e' = ds_ka s /\
  (re_eof e = 0 -> hl_cap (hs_expected h') = ds_ecap s /\
     hl_cap (hs_expected h') <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h')))).

Definition done0 (j : nat) (e' : rentry) (h' : hsrc) (ks : list (list Z)) : Prop :=
  let e := nth j es no_entry in
  let hj := nth j hs no_hj in
  let Ls := entry_lines e hj in
  re_fd e' = re_fd e /\
  re_eof e' = (if re_eof e =? 0 then (if hs_closed (fst hj) =? 1 then 1 else 0) else 1) /\
  NoDup ks /\ same_set ks (upds (keys_texts (re_keys e)) Ls) /\
  (re_eof e = 0 ->
     let h := fst hj in
     hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\
     hs_eintr h' = 0 /\ hl_recs (hs_pending h') = [] /\
     hl_cap (hs_pending h') = hl_cap (hs_pending h) /\ hl_v (hs_pending h') = hl_v (hs_pending h) /\ hs_off h' = 0 /\
     hs_state h' = feed (hs_state h) (bzs (pending_stream h)) /\
     map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) Ls /\
     firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h')) = hl_recs (hs_expected h) /\
     hs_held h' = hs_held h /\
     hs_partial h' = hs_partial h /\
     re_skip e' = hs_overlong h' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h'))) /\
  (re_eof e = 1 ->
     re_skip e' = re_skip e /\ re_U e' = re_U e /\ re_buf e' = re_buf e /\
     re_used e' = re_used e /\ re_cap e' = re_cap e) /\
  dsrel j e' h' ks.

Definition done_rel (j : nat) (e' : rentry) (h' : hsrc) (ks : list (list Z)) : Prop :=
  done0 j e' h' ks /\ keys_texts (re_keys e') = snd (gei gpre ks).

(* A pending source's blocks: still the entry's, at the pointers the entry state names. *)
Definition pend_links (L : layout) (A : astate) (e : rentry) (h : hsrc) : Prop :=
  entry_links L A [] (drain_start gnm adr0 e h) e /\
  (re_eof e = 0 -> src_links L A [] gnm (drain_start gnm adr0 e h) h).

Definition pend_rel (j : nat) (L : layout) (A : astate) (qd : list sptr) (e' : rentry) (h' : hsrc) : Prop :=
  e' = nth j es no_entry /\ h' = fst (nth j hs no_hj) /\ pend_links L A e' h'.

Definition srcblk (p : rentry * hsrc) : list Z := if re_eof (fst p) =? 0 then hs_blocks (snd p) else [].

(* Each block is a block from the start that no entry or drained source held, a current entry's or source's block,
   or the output buffer. *)
Definition hbk (L : layout) (A : astate) (es_c : list rentry) (hs_c : list hsrc) (OUTc : Z) : Prop :=
  forall q m, In (q, m) (blocks L A) ->
    (In (q, m) (blocks L0 A0) /\ q <> gOUT /\ ~ In q (concat (map entry_blocks es)) /\ ~ In q (drained_blocks es hs)) \/
    In q (concat (map entry_blocks es_c)) \/ In q (concat (map srcblk (combine es hs_c))) \/ q = OUTc.

Definition GI (i : nat) (cur : layout -> astate -> list sptr -> rentry -> hsrc -> Prop) (part : list Z)
    (base : Z -> Z -> nat -> adrF -> trF * Z * list dstate * (adrF * list dadr))
    (bound : Z) (regs : bvmap 5 word) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (k : trF)
    (qd : list sptr) (es_c : list rentry) (hs_c : list hsrc) (kss : list (list (list Z))) (LB : list byte)
    (OUTc CAPc : Z) (junkc : list byte) : Prop :=
  let T := Z.of_nat (length LB) in
  let live := send_live cl br dd T in
  let off := send_off cl br T in
  getr regs 2 = Z_to_bv 64 gP /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
  getr regs 8 = getr regs0 10 /\ getr regs 22 = Z_to_bv 64 RIG_S6 /\
  chain RELAY_INSTANCE_GONE_K Eall (Fcur T) L0 A0 regs0 mem0 md0 L A mem md /\
  st_init_done A = true /\
  (length qd = nretF k /\ (forall ext, runF RF (qd ++ ext) bnd k = runF RF qd bnd k) /\ rt_ok RF A (runF RF qd bnd k)) /\
  gpos (base (gNO + T) (if live then CAPc else gCAP)) k i L A qd es_c hs_c live OUTc CAPc /\
  hbk L A es_c hs_c OUTc /\
  ro_agree segs mem /\
  rw_cells segs mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] /\
  rw_cells segs mem G_NSRC [C4 (Z_to_bv 64 gN); C4 (Z_to_bv 64 16)] /\
  rw_cells segs mem G_SRC [C8 (Z_to_bv 64 G)] /\ In (G, SRC_TABLE) (blocks L A) /\
  rw_cells segs mem G_CLIENT [C4 (Z_to_bv 64 cl)] /\
  rw_cells segs mem G_BROKEN [C1 (Z_to_bv 8 (if off then br else dd))] /\
  rw_cells segs mem G_DEAD [C1 (Z_to_bv 8 dd)] /\
  rw_cells segs mem G_EINTR [C1 (Z_to_bv 8 (if off then ei else 0))] /\
  (exists ev, rw_cells segs mem (errno_addr Bm) [C4 ev]) /\
  (forall j, (j < 4)%nat ->
     rw_cells segs mem (G_S + SRC_SIZE * Z.of_nat j) [C4 (Z_to_bv 64 (nth j fs 0)); C4 (Z_to_bv 64 (nth j os 0))]) /\
  rw_cells segs mem gP [C8 (Z_to_bv 64 G_LOCK)] /\ (exists jb, rw_cells segs mem (gP + 8) [CB 48 jb]) /\
  rw_cells segs mem (gP + 56) saved_cells /\
  length es_c = length es /\ (exists tl, table_at Bm mem G es_c tl) /\ Forall (entry_okk L A mem) es_c /\
  length hs_c = length es /\ length kss = i /\ (i <= length es)%nat /\
  (forall j, (j < length es)%nat -> re_eof (nth j es no_entry) = 0 ->
     src_at Bm L A mem (gHA j) (nth j hs_c (fst (nth j hs no_hj)))) /\
  (forall j, (j < i)%nat -> done_rel j (nth j es_c no_entry) (nth j hs_c (fst (nth j hs no_hj))) (nth j kss [])) /\
  ((i < length es)%nat -> cur L A qd (nth i es_c no_entry) (nth i hs_c (fst (nth i hs no_hj)))) /\
  (forall j, (i < j < length es)%nat ->
     pend_rel j L A qd (nth j es_c no_entry) (nth j hs_c (fst (nth j hs no_hj)))) /\
  NoDup (G :: OUTc :: concat (map entry_blocks es_c) ++ concat (map srcblk (combine es hs_c))) /\
  (forall q m, In (q, m) (blocks L0 A0) -> q <> gOUT -> ~ In q (concat (map entry_blocks es)) ->
     ~ In q (drained_blocks es hs) -> In (q, m) (blocks L A)) /\
  (forall q m, In (q, m) (blocks L0 A0) -> 0 < m -> ~ Fcur T q ->
     ~ In q (concat (map entry_blocks es_c) ++ concat (map srcblk (combine es hs_c))) /\ (live = true -> q <> OUTc)) /\
  bzs LB = concat (map (seg_of kss) (seq 0 i)) ++ part /\
  T <= bound /\
  (live = false -> rw_cells segs mem G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] /\ OUTc = gOUT /\ CAPc = gCAP /\
     (0 < gCAP -> In (gOUT, gCAP) (blocks L A) /\ bytes_at segs mem gOUT (O ++ junk))) /\
  (live = true -> gNO + T <= CAPc /\ In (OUTc, CAPc) (blocks L A) /\ fresh_block Bm OUTc CAPc /\
     bytes_at segs mem OUTc (O ++ LB ++ junkc) /\ Z.of_nat (length junkc) = CAPc - gNO - T /\
     rw_cells segs mem G_OUTV [C8 mx; C8 (Z_to_bv 64 (gNO + T)); C8 (Z_to_bv 64 CAPc); C8 (Z_to_bv 64 OUTc)]).

Definition gone_Q (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' (OUT' CAP' : Z) (junk' LB : list byte)
         (es' : list rentry) (hs' : list hsrc) (kss : list (list (list Z))) (tail' : list byte),
    let segsz := map (fun i => gone_segment gpre (entry_lines (nth i es no_entry) (nth i hs no_hj)) (nth i kss []))
                     (seq 0 (length es)) in
    let TOT := Z.of_nat (length (concat segsz)) in
    let live := send_live cl br dd TOT in
    let off := send_off cl br TOT in
    c' = mkCfg (@YK11.mkst fx' regs' (getr regs0 1) mem' (seg_rom segs)) md' /\ frm_zero (@fp_csr fx') /\
    relay_post Bm API RELAY_INSTANCE_GONE_K
      (fun a => send_writes true gOUT gCAP a \/ G_LOCK + 4 <= a < G_LOCK + 8 \/
                G <= a < G + SRC_TABLE \/ drained_area es hs a \/
                (exists q m, In q (concat (map entry_blocks es) ++ drained_blocks es hs) /\
                             In (q, m) (blocks L0 A0) /\ q <= a < q + m))
      (fun q => (live = true /\ q = gOUT) \/ In q (concat (map entry_blocks es)) \/ In q (drained_blocks es hs))
      L0 A0 regs0 mem0 md0 L' A' regs' mem' md' /\
    st_init_done A' = true /\
    (exists qs, length qs = nretF gtr /\ rt_ok RF A' (runF RF qs bnd gtr) /\
       (live = true -> live_at L' A' (resolveF qs (gone_out glv gmx gNO gCAP gpre es hs gnm 0 (gnm gOUT))) OUT' CAP') /\
       (forall i, (i < length es)%nat ->
          entry_links L' A' qs (nth i (gone_adrs glv gmx gNO gCAP gpre es hs gnm 0 (gnm gOUT)) dadr0)
            (nth i es' no_entry) /\
          (re_eof (nth i es no_entry) = 0 ->
             src_links L' A' qs gnm (nth i (gone_adrs glv gmx gNO gCAP gpre es hs gnm 0 (gnm gOUT)) dadr0)
               (nth i hs' (fst (nth i hs no_hj)))))) /\
    ro_agree segs mem' /\
    rw_cells segs mem' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
    rw_cells segs mem' G_NSRC [C4 (Z_to_bv 64 gN); C4 (Z_to_bv 64 16)] /\
    rw_cells segs mem' G_SRC [C8 (Z_to_bv 64 G)] /\ In (G, SRC_TABLE) (blocks L' A') /\
    length es' = length es /\ table_at Bm mem' G es' tail' /\
    Forall (entry_ok Bm L' A' mem') es' /\
    length kss = length es /\ length hs' = length es /\
    (forall i, (i < length es)%nat ->
       let e := nth i es no_entry in
       let e' := nth i es' no_entry in
       let ks := nth i kss [] in
       let hj := nth i hs no_hj in
       let Ls := entry_lines e hj in
       let s := nth i (gone_states glv gmx gNO gCAP gpre es hs) (drain_init gNO gCAP e (fst hj)) in
       re_fd e' = re_fd e /\
       re_eof e' = (if re_eof e =? 0 then (if hs_closed (fst hj) =? 1 then 1 else 0) else 1) /\
       NoDup ks /\ same_set ks (upds (keys_texts (re_keys e)) Ls) /\
       keys_texts (re_keys e') = snd (gei gpre ks) /\
       ks = ds_H s /\ re_cap e' = ds_cap s /\ bzs (re_U e') = ds_u s /\
       re_skip e' = (if ds_skip s then 1 else 0) /\ ent_ka e' = ds_ka s /\
       (re_eof e = 0 ->
          let h := fst hj in
          let h' := nth i hs' h in
          src_at Bm L' A' mem' (G_S + SRC_SIZE * Z.of_nat (snd hj)) h' /\
          hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\
          hs_eintr h' = 0 /\ hl_recs (hs_pending h') = [] /\
          hl_cap (hs_pending h') = hl_cap (hs_pending h) /\ hl_v (hs_pending h') = hl_v (hs_pending h) /\ hs_off h' = 0 /\
          hs_state h' = feed (hs_state h) (bzs (pending_stream h)) /\
          map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) Ls /\
          firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h')) = hl_recs (hs_expected h) /\
          hs_held h' = hs_held h /\
          hs_partial h' = hs_partial h /\
          re_skip e' = hs_overlong h' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) /\
          hl_cap (hs_expected h') = ds_ecap s /\
          hl_cap (hs_expected h') <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h')))) /\
       (re_eof e = 1 ->
          re_skip e' = re_skip e /\ re_U e' = re_U e /\ re_buf e' = re_buf e /\
          re_used e' = re_used e /\ re_cap e' = re_cap e)) /\
    bzs LB = concat segsz /\
    rw_cells segs mem' G_CLIENT [C4 (Z_to_bv 64 cl)] /\
    rw_cells segs mem' G_BROKEN [C1 (Z_to_bv 8 (if off then br else dd))] /\
    rw_cells segs mem' G_DEAD [C1 (Z_to_bv 8 dd)] /\
    rw_cells segs mem' G_EINTR [C1 (Z_to_bv 8 (if off then ei else 0))] /\
    (exists ev', rw_cells segs mem' (errno_addr Bm) [C4 ev']) /\
    (forall i, (i < 4)%nat ->
       rw_cells segs mem' (G_S + SRC_SIZE * Z.of_nat i) [C4 (Z_to_bv 64 (nth i fs 0)); C4 (Z_to_bv 64 (nth i os 0))]) /\
    NoDup (G :: OUT' :: concat (map entry_blocks es') ++
           concat (map (fun p => if re_eof (fst p) =? 0 then hs_blocks (snd p) else []) (combine es hs'))) /\
    (forall q m, In (q, m) (blocks L0 A0) -> q <> gOUT -> ~ In q (concat (map entry_blocks es)) ->
       ~ In q (drained_blocks es hs) -> In (q, m) (blocks L' A')) /\
    (forall q m, In (q, m) (blocks L0 A0) -> 0 < m -> q <> gOUT -> ~ In q (concat (map entry_blocks es)) ->
       ~ In q (drained_blocks es hs) ->
       q <> OUT' /\ ~ In q (concat (map entry_blocks es')) /\
       ~ In q (concat (map (fun p => if re_eof (fst p) =? 0 then hs_blocks (snd p) else []) (combine es hs')))) /\
    (forall q m, In (q, m) (blocks L' A') ->
       (In (q, m) (blocks L0 A0) /\ q <> gOUT /\ ~ In q (concat (map entry_blocks es)) /\
        ~ In q (drained_blocks es hs)) \/
       In q (concat (map entry_blocks es')) \/
       In q (concat (map (fun p => if re_eof (fst p) =? 0 then hs_blocks (snd p) else []) (combine es hs'))) \/
       q = OUT') /\
    (live = false -> rw_cells segs mem' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] /\ OUT' = gOUT /\ CAP' = gCAP /\
       (0 < gCAP -> In (gOUT, gCAP) (blocks L' A') /\ bytes_at segs mem' gOUT (O ++ junk))) /\
    (live = true ->
       gNO + TOT <= CAP' /\ CAP' = gone_cap glv gmx gNO gCAP gpre es hs /\ In (OUT', CAP') (blocks L' A') /\
       fresh_block Bm OUT' CAP' /\
       bytes_at segs mem' OUT' (O ++ LB ++ junk') /\ Z.of_nat (length junk') = CAP' - gNO - TOT /\
       rw_cells segs mem' G_OUTV
         [C8 mx; C8 (Z_to_bv 64 (gNO + TOT)); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')]).

Definition lines_of (i : nat) : list (list Z) := entry_lines (nth i es no_entry) (nth i hs no_hj).

(* In source i's key loop: the old texts' facts; the held keys H in array order at the addresses snd Ha, the keys
   left to end being geia's rest on Ha; source i's blocks at their addresses (keys at snd Ha, the others at a). *)
Definition inner_cur (i : nat) (ks0 : list (list Z)) (n : nat) (H Ed : list (list Z)) (ka0 : list adrF) (a : dadr)
    (Ha : list (list Z * adrF)) (L : layout) (A : astate) (qd : list sptr) (e' : rentry) (h' : hsrc) : Prop :=
  done0 i e' h' ks0 /\ keys_texts (re_keys e') = H /\ (n <= length H)%nat /\
  (forall j, (j < n)%nat -> has_prefix gpre (nth j H []) = false) /\
  gei gpre ks0 = (Ed ++ fst (gei_loop (length H - n) gpre n H), snd (gei_loop (length H - n) gpre n H)) /\
  map fst Ha = H /\ length ka0 = length ks0 /\
  (exists Eda, map fst Eda = Ed /\
     geia gpre (combine ks0 ka0) =
       (Eda ++ fst (geia_loop (length Ha - n) gpre n Ha), snd (geia_loop (length Ha - n) gpre n Ha))) /\
  (forall post, entry_links L A (qd ++ post) (DA adr0 (da_buf a) (da_hp a) (map snd Ha) [] adr0 []) e') /\
  (re_eof (nth i es no_entry) = 0 -> forall post, src_links L A (qd ++ post) gnm a h').

Definition part_of (i : nat) (Ed : list (list Z)) : list Z :=
  with_nul (lines_of i) ++ concat (map (fun x => x ++ END5Z) Ed).

Definition bound_in (i : nat) (Ed : list (list Z)) : Z :=
  gbound i + pl_of i + 6001 + 6005 * Z.of_nat (length Ed).

Definition AT_TOP (i : nat) (c : config) : Prop :=
  exists (fx : YK11.FPState) regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc,
    c = mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (if Nat.ltb i (length es) then 0x134bc else 0x13590)) mem (seg_rom segs)) md /\
    frm_zero (@fp_csr fx) /\
    ((0 < length es)%nat -> getr regs 18 = Z_to_bv 64 RIG_FMT /\ getr regs 19 = Z_to_bv 64 RIG_KEY /\ getr regs 23 = Z_to_bv 64 (Z.of_nat i)) /\
    GI i (pend_rel i) [] (gpos_top i) (gbound i) regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc.

Definition AT_C (i : nat) (c : config) : Prop :=
  exists (fx : YK11.FPState) regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc ks0 ka0 a,
    c = mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x134e0) mem (seg_rom segs)) md /\
    frm_zero (@fp_csr fx) /\ (i < length es)%nat /\
    getr regs 11 = Z_to_bv 64 G /\ getr regs 18 = Z_to_bv 64 RIG_FMT /\ getr regs 19 = Z_to_bv 64 RIG_KEY /\
    getr regs 23 = Z_to_bv 64 (Z.of_nat i) /\ getr regs 24 = Z_to_bv 64 (56 * Z.of_nat i) /\
    GI i (inner_cur i ks0 0 ks0 [] ka0 a (combine ks0 ka0)) (part_of i [])
      (gpos_k i a (gkept ks0 ka0) [] (gxks ks0 ka0)) (bound_in i [])
      regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc.

Definition AT_IN (i : nat) (ks0 : list (list Z)) (n : nat) (H Ed : list (list Z)) (c : config) : Prop :=
  exists (fx : YK11.FPState) regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc jr ka0 da0 Ha,
    c = mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (if Nat.ltb n (length H) then 0x13524 else 0x13584)) mem (seg_rom segs)) md /\
    frm_zero (@fp_csr fx) /\ (i < length es)%nat /\
    getr regs 18 = Z_to_bv 64 RIG_FMT /\ getr regs 19 = Z_to_bv 64 RIG_KEY /\ getr regs 23 = Z_to_bv 64 (Z.of_nat i) /\
    getr regs 24 = Z_to_bv 64 (G + 56 * Z.of_nat i) /\
    ((n < length H)%nat ->
       getr regs 9 = Z_to_bv 64 (Z.of_nat n) /\ getr regs 20 = Z_to_bv 64 (Z.of_nat (length gpre)) /\
       getr regs 21 = Z_to_bv 64 (key_addr (nth n (re_keys (nth i es_c no_entry)) rig_dk)) /\
       getr regs 25 = Z_to_bv 64 (8 * Z.of_nat n) /\ getr regs 26 = Z_to_bv 64 (Z.of_nat (length H)) /\
       getr regs 27 = Z_to_bv 64 (re_hp (nth i es_c no_entry))) /\
    rw_cells segs mem (gP + 8) [CB 48 (pf_bytes (gpre ++ [0]) ++ jr)] /\
    GI i (inner_cur i ks0 n H Ed ka0 da0 Ha) (part_of i Ed)
      (gpos_k i da0 (gkept ks0 ka0) [] (skipn (length Ed) (gxks ks0 ka0))) (bound_in i Ed)
      regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc.

Hypothesis PRE : call_pre_k Bm MR RELAY_INSTANCE_GONE_K L0 A0 regs0 mem0 md0.
Hypothesis TSZ : spZ regs0 <= TASK_SIZE.
Hypothesis INIT0 : st_init_done A0 = true.
Hypothesis TPE : ms_tp Bm + ERRNO_OFF = errno_addr Bm.
Hypothesis HERR : G_LOCK_HI <= errno_addr Bm.
Hypothesis RA0 : ro_agree segs mem0.
Hypothesis FRM0 : frm_zero (@fp_csr fx0).
Hypothesis GOTG : ms_got_guard Bm = GOT_GUARD.
Hypothesis GRD : ms_guard Bm = GUARD.
Hypothesis IMGR : forall a, G_RELAY_LO <= a < G_S + SRC_SIZE * SOURCES_MAX -> img_plain Bm a.
Hypothesis IMGC : forall a, G_CLIENT <= a < G_CLIENT + 4 -> img_plain Bm a.
Hypothesis IMGE : forall a, errno_addr Bm <= a < errno_addr Bm + 4 -> in_img Bm a.
Hypothesis IMG5 : forall a, END5_ADDR <= a < END5_ADDR + 5 -> img_plain Bm a.
Hypothesis IDR : - 2 ^ 31 <= bv_signed (getr regs0 10) < 2 ^ 31.
Hypothesis GL0 : rw_cells segs mem0 G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Hypothesis NS0 : rw_cells segs mem0 G_NSRC [C4 (Z_to_bv 64 gN); C4 (Z_to_bv 64 16)].
Hypothesis GS0 : rw_cells segs mem0 G_SRC [C8 (Z_to_bv 64 G)].
Hypothesis NLE : gN <= 4.
Hypothesis GB0 : In (G, SRC_TABLE) (blocks L0 A0).
Hypothesis GF0 : fresh_block Bm G SRC_TABLE.
Hypothesis TAB0 : table_at Bm mem0 G es tail0.
Hypothesis EOK0 : Forall (entry_ok Bm L0 A0 mem0) es.
Hypothesis NDF : NoDup (map re_fd es).
Hypothesis LHS : length hs = length es.
Hypothesis LFS : length fs = 4%nat.
Hypothesis LOS : length os = 4%nat.
Hypothesis SRCH : forall i, (i < 4)%nat ->
  rw_cells segs mem0 (G_S + SRC_SIZE * Z.of_nat i) [C4 (Z_to_bv 64 (nth i fs 0)); C4 (Z_to_bv 64 (nth i os 0))].
Hypothesis SRCD : forall i i', (i < 4)%nat -> (i' < 4)%nat -> i <> i' -> nth i os 0 = 1 -> nth i' os 0 = 1 ->
  nth i fs 0 <> nth i' fs 0.
Hypothesis SRCR : forall i, (i < 4)%nat -> (nth i os 0 = 0 \/ nth i os 0 = 1) /\ 0 <= nth i fs 0 < 2 ^ 31.
Hypothesis GSO : Forall (fun p => gone_src_ok Bm L0 A0 mem0 G gOUT es (fst p) (snd p)) (combine es hs).
Hypothesis ND0 : NoDup (G :: gOUT :: concat (map entry_blocks es) ++
  concat (map (fun p => if re_eof (fst p) =? 0 then hs_blocks (fst (snd p)) else []) (combine es hs))).
Hypothesis Hcl : cl = 3 \/ cl = -1.
Hypothesis Hbr : br = 0 \/ br = 1.
Hypothesis Hdd : dd = 0 \/ dd = 1.
Hypothesis Hei : ei = 0 \/ ei = 1.
Hypothesis CCL0 : rw_cells segs mem0 G_CLIENT [C4 (Z_to_bv 64 cl)].
Hypothesis CBR0 : rw_cells segs mem0 G_BROKEN [C1 (Z_to_bv 8 br)].
Hypothesis CDD0 : rw_cells segs mem0 G_DEAD [C1 (Z_to_bv 8 dd)].
Hypothesis CEI0 : rw_cells segs mem0 G_EINTR [C1 (Z_to_bv 8 ei)].
Hypothesis COUT0 : rw_cells segs mem0 G_OUTV [C8 mx; C8 nout; C8 cap; C8 out].
Hypothesis CERR0 : exists ev, rw_cells segs mem0 (errno_addr Bm) [C4 ev].
Hypothesis HOUT0 : (gCAP = 0 /\ gOUT = 0 /\ gNO = 0 /\ O = []) \/
  (0 < gCAP /\ gNO <= gCAP /\ In (gOUT, gCAP) (blocks L0 A0) /\ fresh_block Bm gOUT gCAP /\
   bytes_at segs mem0 gOUT (O ++ junk) /\ Z.of_nat (length O) = gNO /\ Z.of_nat (length junk) = gCAP - gNO).
Hypothesis RES0 : rt_ok RF A0 bnd.
Hypothesis ROOM0 : forall qs, length qs = nretF gtr -> roomF RF qs bnd gtr.

Lemma gS_range : alloc_ceiling + RELAY_INSTANCE_GONE_K <= gS < 2 ^ 63 /\ gS mod 16 = 0.
Proof.
  destruct PRE as (_ & _ & _ & _ & H1 & H2 & H3 & _). unfold gS. lia.
Qed.

Lemma len_O : Z.of_nat (length O) = gNO.
Proof. destruct HOUT0 as [(_ & _ & H1 & ->)|(_ & _ & _ & _ & _ & H & _)]; [cbn; lia | exact H]. Qed.

Lemma K_val : RELAY_INSTANCE_GONE_K = 8640.
Proof. vm_compute. reflexivity. Qed.

Lemma gone_end : forall (P : config -> Prop) i cur part base bound fxc regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc,
  GI i cur part base bound regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc ->
  (forall regs' mem',
     chain RELAY_INSTANCE_GONE_K Eall (Fcur (Z.of_nat (length LB))) L0 A0 regs0 mem0 md0 L A mem' md ->
     regs_preserved regs0 regs' -> ro_agree segs mem' ->
     rw_cells segs mem' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (gS - 96 <= a < gS) -> ~ (G_LOCK + 4 <= a < G_LOCK + 8) -> kb2 mem mem' a) ->
     P (mkCfg (@YK11.mkst fxc regs' (getr regs0 1) mem' (seg_rom segs)) md)) ->
  SR segs (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 0x13590) mem (seg_rom segs)) md) P.
Proof.
  intros P i cur part base bound fxc regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc HG K.
  destruct HG as (G2 & G3 & G4 & G8 & G22 & CH & INIT & RES & BUD & POT & RA & GL & HNS & HGS & HGB & CCL & CBR & CDD
    & CEI & CERR & SRCH' & FR0 & FRB & FRS & HLE & HTAB & HEOK & HLH & HLK & HIL & HSRC & HDONE & HCUR & HPEND & HND
    & HSUR & HSV & HLB & HT & HDEAD & HLIVE).
  pose proof gS_range as [[GSR1 GSR2] GSR3]. rewrite K_val in GSR1. pose proof alloc_ceiling_val as ACV.
  pose proof CH as (M1 & _).
  destruct (mr_model Bm MR rig_laws L A mem md M1) as (Hh & Hl & _).
  assert (ST : stk rsegs mem (gS - 96) gS).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a).
    { rewrite <- SEGS. destruct CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SW). apply SW.
      left. change (spZ regs0) with gS. rewrite K_val. lia. }
    split; [exact W|]. destruct (writable_hi_present mem a ltac:(lia) W) as [b E]. exists b. unfold mrd, wa. rewrite E. reflexivity. }
  apply (rig_run fxc regs (Z_to_bv 64 0x13590) mem md
    (pthread_mutex_unlock_post (getr regs0 1) (Z_to_bv 64 gS) (getr regs0 3) (getr regs0 4) (getr regs0 8) (getr regs0 9)
       (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23) (getr regs0 24)
       (getr regs0 25) (getr regs0 26) (getr regs0 27) (@fp_regs fxc) (@fp_csr fxc) G_LOCK (gS - 96) (normalize rsegs mem)));
    [exact RA | exact Hh | exact Hl | |].
  - unfold Regs6ss.mkR_of.
    assert (E2 : reg_get regs 2 = Z_to_bv 64 (gS - 160)) by exact G2.
    assert (E3 : reg_get regs 3 = getr regs0 3) by exact G3.
    assert (E4 : reg_get regs 4 = getr regs0 4) by exact G4.
    rewrite E2, E3, E4.
    rewrite SEGS in RA.
    apply (rig_segH UNLOCK); [ | | | | lia | unfold G_LOCK_HI; lia | lia | apply mem_inv_normalize].
    + apply rw_cells_normalize; [exact RA | rewrite <- SEGS; exact FR0 | intros i0 Hi; cbn in Hi; apply ro_addr_hi; unfold gP in *; lia].
    + replace (gS - 104) with (gP + 56) by (unfold gP; ring).
      apply rw_cells_normalize; [exact RA | rewrite <- SEGS; exact FRS | intros i0 Hi; cbn in Hi; apply ro_addr_hi; unfold gP in *; lia].
    + apply rw_cells_normalize; [exact RA | rewrite <- SEGS; exact GL | intros i0 Hi; cbn in Hi; apply rig_ro_glob; unfold G_LOCK; lia].
    + apply stk_normalize; [exact ST | lia].
  - intros s0 R' m' Q REL ROS X.
    unfold pthread_mutex_unlock_post in Q.
    destruct Q as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m'n & -> & MU & WM & MI & ST' & GL').
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *.
    rewrite (MState.unsigned_lit gS) in MU by lia.
    rewrite SEGS in RA.
    pose proof (mem_rel_normalize rsegs mem RA) as RN.
    pose proof (munch_rel rsegs _ mem _ m' m'n RN REL ROS MU) as MUr.
    pose proof (wmono_rel rsegs mem _ m' m'n RN REL ROS WM) as WMr.
    pose proof (ro_agree_same rsegs mem m' RA ROS) as RA'.
    pose proof (rw_cells_of_rel rsegs _ _ _ _ REL GL') as GLr.
    apply SR_ret.
    assert (RP : ret_pc (getr regs0 1) = getr regs0 1).
    { destruct PRE as (_ & _ & _ & HRA & _). exact (ret_pc_of_ok _ HRA). }
    change (MS R' (@fp_regs fxc) (ret_pc (getr regs0 1)) (@fp_csr fxc) None m' (seg_rom rsegs))
      with (@YK11.mkst fxc R' (ret_pc (getr regs0 1)) m' (seg_rom rsegs)).
    rewrite RP, <- SEGS.
    apply K.
    + rewrite <- SEGS in WMr.
      apply (chain_munch _ _ _ _ _ _ _ _ _ _ _ _ _ _ CH MUr WMr).
      intros x Hx OW. cbn [outside] in OW.
      destruct (Z_le_gt_dec (gS - 96) x) as [D1|D1]; [destruct (Z_lt_ge_dec x gS) as [D2|D2]|].
      * left. split; [left; change (spZ regs0) with gS; rewrite K_val; lia | lia].
      * right. left. split; [right; left; unfold G_LOCK in *; lia|]. apply IMGR. unfold G_LOCK, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. lia.
      * right. left. split; [right; left; unfold G_LOCK in *; lia|]. apply IMGR. unfold G_LOCK, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. lia.
    + intros r Hr. unfold callee_saved in Hr.
      assert (Hk : 0 < r < 32) by lia.
      rewrite (rig_reg_eqv _ _ r X Hk).
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; simp_regs; try reflexivity.
      unfold gS, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + rewrite SEGS. exact RA'.
    + rewrite SEGS. exact GLr.
    + intros a Ha N1 N2. rewrite <- SEGS in WMr. apply (mu_kb2 [(gS - 96, gS); (G_LOCK + 4, G_LOCK + 8)]); [exact MUr | exact WMr | exact Ha |].
      cbn [outside]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma glob_low : forall a, G_RELAY_LO <= a < G_S + SRC_SIZE * SOURCES_MAX -> a < 2 ^ 21.
Proof. intros a Ha. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in Ha. lia. Qed.

Lemma gS_low : 2 ^ 21 + RELAY_INSTANCE_GONE_K <= gS.
Proof.
  pose proof gS_range as [[H1 H2] H3]. pose proof alloc_ceiling_val. lia.
Qed.

Lemma blk_low : forall L A m md q k, MR L A m md -> In (q, k) (blocks L A) -> 0 <= k -> q + k <= gS - RELAY_INSTANCE_GONE_K.
Proof.
  intros L A m md q k HM Hin Hk. apply rig_blocks_in in Hin as (p & <- & Hp).
  pose proof (mr_blocks_range Bm MR rig_laws L A m md p k HM Hp). pose proof gS_range as [[H1 H2] H3]. lia.
Qed.

Lemma bkept_low : forall L A m m' md W, MR L A m md -> munch W m m' -> wmono segs m m' ->
  (forall x, 0 <= x < gS - RELAY_INSTANCE_GONE_K -> outside W x) -> forall q, bkept L A m L A m' q.
Proof.
  intros L A m m' md W HM MU WM HO q. apply (mu_bkept L A W m m' md q HM MU WM).
  intros k i Hin Hi. pose proof (blk_low L A m md q k HM Hin ltac:(lia)).
  pose proof (rig_blk L A m md q k i HM Hin Hi) as (_ & H4 & _). apply HO. lia.
Qed.

Lemma GI_stack : forall i cur part base bound regs regs' L A mem m' md k qd es_c hs_c kss LB OUTc CAPc junkc W,
  GI i cur part base bound regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc ->
  munch W mem m' -> wmono segs mem m' -> ro_agree segs m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> gS - RELAY_INSTANCE_GONE_K <= x < gP \/ gP + 8 <= x < gP + 56) ->
  getr regs' 2 = Z_to_bv 64 gP -> getr regs' 3 = getr regs0 3 -> getr regs' 4 = getr regs0 4 ->
  getr regs' 8 = getr regs0 10 -> getr regs' 22 = Z_to_bv 64 RIG_S6 ->
  GI i cur part base bound regs' L A m' md k qd es_c hs_c kss LB OUTc CAPc junkc.
Proof.
  intros i cur part base bound regs regs' L A mem m' md k qd es_c hs_c kss LB OUTc CAPc junkc W HG MU WM RA' HW
    R2 R3 R4 R8 R22.
  destruct HG as (G2 & G3 & G4 & G8 & G22 & CH & INIT & RES & BUD & POT & RA & GL & HNS & HGS & HGB & CCL & CBR & CDD
    & CEI & CERR & SRCH' & FR0 & FRB & FRS & HLE & HTAB & HEOK & HLH & HLK & HIL & HSRC & HDONE & HCUR & HPEND & HND
    & HSUR & HSV & HLB & HT & HDEAD & HLIVE).
  pose proof gS_range as [[GSR1 GSR2] GSR3]. pose proof gS_low as GSL. pose proof alloc_ceiling_val as ACV.
  pose proof K_val as KV.
  assert (HO : forall x, 0 <= x < gS - RELAY_INSTANCE_GONE_K -> outside W x).
  { intros x Hx. destruct (rig_outside_dec W x) as [O'|O']; [exact O'|]. exfalso.
    assert (Hx' : 0 <= x < 2 ^ 64) by lia.
    destruct (HW x Hx' O'); unfold gP in *; lia. }
  assert (HOF : forall x, gP <= x < gP + 8 \/ gP + 56 <= x < gS -> outside W x).
  { intros x Hx. destruct (rig_outside_dec W x) as [O'|O']; [exact O'|]. exfalso.
    assert (Hx' : 0 <= x < 2 ^ 64) by (unfold gP in *; lia).
    destruct (HW x Hx' O'); unfold gP in *; lia. }
  assert (KL : forall x, 0 <= x < gS - RELAY_INSTANCE_GONE_K -> kb2 mem m' x)
    by (intros x Hx; apply (mu_kb2 W); [exact MU | exact WM | lia | exact (HO x Hx)]).
  assert (RWL : forall a cs, rw_cells segs mem a cs -> a + Z.of_nat (cells_size cs) <= gS - RELAY_INSTANCE_GONE_K ->
                  rw_cells segs m' a cs).
  { intros a cs H Hb. apply (rw_kb2 mem); [exact H|]. intros j Hj. pose proof (rw_cells_bound _ _ _ _ H). apply KL. lia. }
  assert (BAL : forall a bs, bytes_at segs mem a bs -> a + Z.of_nat (length bs) <= gS - RELAY_INSTANCE_GONE_K ->
                  bytes_at segs m' a bs).
  { intros a bs H Hb. apply (bytes_kb2 mem); [exact H|]. intros j Hj. pose proof (bytes_at_bound _ _ _ _ H). apply KL. lia. }
  pose proof CH as (M1 & _).
  pose proof (bkept_low L A mem m' md W M1 MU WM HO) as BKL.
  assert (CH' : chain RELAY_INSTANCE_GONE_K Eall (Fcur (Z.of_nat (length LB))) L0 A0 regs0 mem0 md0 L A m' md).
  { apply (chain_munch _ _ _ _ _ _ _ _ _ _ _ _ _ _ CH MU WM). intros x Hx O'. left.
    destruct (HW x Hx O'); split; try (left; change (spZ regs0) with gS); unfold gP in *; lia. }
  pose proof CH' as (M1' & _).
  assert (GLOB : forall a cs, rw_cells segs mem a cs -> G_RELAY_LO <= a -> a + Z.of_nat (cells_size cs) <= G_S + SRC_SIZE * SOURCES_MAX ->
                   rw_cells segs m' a cs).
  { intros a cs H H1 H2. apply RWL; [exact H|]. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. lia. }
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R22|].
  split; [exact CH'|]. split; [exact INIT|]. split; [exact RES|]. split; [exact BUD|]. split; [exact POT|].
  split; [exact RA'|].
  split; [apply GLOB; [exact GL | unfold G_LOCK, G_RELAY_LO; lia | cbn; unfold G_LOCK, G_S, SRC_SIZE, SOURCES_MAX; lia]|].
  split; [apply GLOB; [exact HNS | unfold G_NSRC, G_RELAY_LO; lia | cbn; unfold G_NSRC, G_S, SRC_SIZE, SOURCES_MAX; lia]|].
  split; [apply GLOB; [exact HGS | unfold G_SRC, G_RELAY_LO; lia | cbn; unfold G_SRC, G_S, SRC_SIZE, SOURCES_MAX; lia]|].
  split; [exact HGB|].
  split; [apply RWL; [exact CCL | cbn; unfold G_CLIENT; lia]|].
  split; [apply GLOB; [exact CBR | unfold G_BROKEN, G_RELAY_LO; lia | cbn; unfold G_BROKEN, G_S, SRC_SIZE, SOURCES_MAX; lia]|].
  split; [apply GLOB; [exact CDD | unfold G_DEAD, G_RELAY_LO; lia | cbn; unfold G_DEAD, G_S, SRC_SIZE, SOURCES_MAX; lia]|].
  split; [apply GLOB; [exact CEI | unfold G_EINTR, G_RELAY_LO; lia | cbn; unfold G_EINTR, G_S, SRC_SIZE, SOURCES_MAX; lia]|].
  split.
  { destruct CERR as [ev Hev]. exists ev. apply RWL; [exact Hev|].
    pose proof (in_img_low Bm SEGS (errno_addr Bm + 3) (IMGE (errno_addr Bm + 3) ltac:(lia))). cbn. lia. }
  split.
  { intros j Hj. apply GLOB; [exact (SRCH' j Hj) | unfold G_S, G_RELAY_LO, SRC_SIZE; lia | cbn; unfold G_S, SRC_SIZE, SOURCES_MAX; lia]. }
  split.
  { apply (rw_kb2 mem); [exact FR0|]. intros j Hj. cbn in Hj. apply (mu_kb2 W); [exact MU | exact WM | unfold gP in *; lia | apply HOF; lia]. }
  split.
  { destruct (present_rw_cells segs m' (gP + 8) 48) as [jb H]; [unfold gP in *; lia | unfold gP in *; lia | |].
    - intros j Hj. destruct CH' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SW).
      apply (writable_hi_present m'); [unfold gP in *; lia|]. rewrite <- SEGS. apply SW.
      left. change (spZ regs0) with gS. unfold gP in *. lia.
    - exists jb. exact H. }
  split.
  { apply (rw_kb2 mem); [exact FRS|]. intros j Hj. unfold saved_cells in Hj. cbn in Hj. apply (mu_kb2 W); [exact MU | exact WM | unfold gP in *; lia | apply HOF; unfold gP in *; lia]. }
  split; [exact HLE|].
  split.
  { destruct HTAB as (tl & Htl & Htr). exists tl. split; [exact Htl|].
    apply (rw_in_block L A mem L A m' G SRC_TABLE); [exact Htr | apply BKL | exact HGB | lia | cbn; unfold SRC_TABLE, SRC_ENTRY; lia]. }
  split.
  { apply Forall_forall. intros e He. apply (entry_okk_kept L A mem L A m' md); [exact (proj1 (Forall_forall _ _) HEOK e He) | exact M1' |].
    intros q _. apply BKL. }
  split; [exact HLH|]. split; [exact HLK|]. split; [exact HIL|].
  split.
  { intros j Hj He. apply (src_at_kept L A mem L A m'); [exact (HSRC j Hj He) | | intros q _; apply BKL].
    intros x Hx. apply KL. unfold gHA. pose proof (snd (nth j hs no_hj)) as _.
    assert (Hjs : (snd (nth j hs no_hj) < 4)%nat).
    { pose proof (proj1 (Forall_forall _ _) GSO (nth j es no_entry, nth j hs no_hj)) as GO.
      assert (Hin : In (nth j es no_entry, nth j hs no_hj) (combine es hs)).
      { rewrite <- combine_nth by lia. apply nth_In. rewrite length_combine. lia. }
      destruct (GO Hin He) as (_ & Hl & _). exact Hl. }
    unfold G_S, SRC_SIZE in *. lia. }
  split; [exact HDONE|]. split; [exact HCUR|]. split; [exact HPEND|]. split; [exact HND|]. split; [exact HSUR|]. split; [exact HSV|].
  split; [exact HLB|]. split; [exact HT|].
  split.
  { intros HL. destruct (HDEAD HL) as (Hov & E1 & E2 & Hb). split; [apply GLOB; [exact Hov | unfold G_OUTV, G_RELAY_LO; lia | cbn; unfold G_OUTV, G_S, SRC_SIZE, SOURCES_MAX; lia]|].
    split; [exact E1|]. split; [exact E2|]. intros Hc. destruct (Hb Hc) as [Hb1 Hb2]. split; [exact Hb1|].
    apply (bytes_in_block L A mem L A m' gOUT gCAP); [exact Hb2 | apply BKL | exact Hb1 | lia |].
    destruct HOUT0 as [(C0 & _)|(_ & _ & _ & _ & _ & HlO & Hlj)]; [lia|]. rewrite length_app. lia. }
  intros HL. destruct (HLIVE HL) as (H1 & H2 & H3 & H4 & H5 & H6).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split.
  { apply (bytes_in_block L A mem L A m' OUTc CAPc); [exact H4 | apply BKL | exact H2 | lia |].
    pose proof len_O. rewrite !length_app. lia. }
  split; [exact H5|].
  apply GLOB; [exact H6 | unfold G_OUTV, G_RELAY_LO; lia | cbn; unfold G_OUTV, G_S, SRC_SIZE, SOURCES_MAX; lia].
Qed.

(* ===== region gone_start ===== *)

Lemma gst_srcblk : forall (es0 : list rentry) (hs0 : list (hsrc * nat)),
  map srcblk (combine es0 (map fst hs0)) =
  map (fun p => if re_eof (fst p) =? 0 then hs_blocks (fst (snd p)) else []) (combine es0 hs0).
Proof.
  intros es0. induction es0 as [|e es0 IH]; intros [|h hs0]; cbn [combine map]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma gst_nth_fst : forall (l : list (hsrc * nat)) j d, (j < length l)%nat ->
  nth j (map fst l) (fst (nth j l d)) = fst (nth j l d).
Proof. intros l j d Hj. rewrite (map_nth fst l (nth j l d) j). f_equal. apply nth_indep. exact Hj. Qed.

Lemma gpair4 : forall {A B C D E : Type} (x : A * B * C * (D * E)),
  x = (fst (fst (fst x)), snd (fst (fst x)), snd (fst x), (fst (snd x), snd (snd x))).
Proof. intros A B C D E [[[a b] c] [d e]]. reflexivity. Qed.

Lemma gst_live : forall a n, In (a, n) (blocks L0 A0) -> live_at L0 A0 (sptr_of L0 A0 a) a n.
Proof.
  intros a n HB. pose proof PRE as (M0 & _).
  exact (CF.gestures_end_b.p3b_live_of_blocks L0 A0 a n (NODUP L0 A0 mem0 md0 M0) HB).
Qed.

Lemma gst_f2 : forall {X Y : Type} (P : X -> Prop) (R : X -> Y -> Prop) (f : X -> Y) l,
  Forall P l -> (forall x, P x -> R x (f x)) -> Forall2 R l (map f l).
Proof. intros X Y P R f l H K. induction H as [|x l Hx _ IH]; constructor; [exact (K x Hx) | exact IH]. Qed.

Lemma gst_list : forall mem LA l b, list_at Bm L0 A0 mem LA l b ->
  (0 < hl_cap l -> live_at L0 A0 (sptr_of L0 A0 (hl_v l)) (hl_v l) (16 * hl_cap l)) /\
  Forall (fun r => live_at L0 A0 (sptr_of L0 A0 (fst r)) (fst r) (Z.of_nat (length (snd r)) + 1)) (hl_recs l).
Proof.
  intros mem LA l b (_ & _ & HV & _ & _ & HR). split.
  - intros Hc. destruct HV as [(C & _)|(_ & HB & _)]; [lia | exact (gst_live _ _ HB)].
  - eapply Forall_impl; [|exact HR]. intros r (HB & _). exact (gst_live _ _ HB).
Qed.

(* At the entry, each source's blocks are live at the pointers the entry state names. *)
Lemma gst_pend : forall j, (j < length es)%nat -> pend_links L0 A0 (nth j es no_entry) (fst (nth j hs no_hj)).
Proof.
  intros j Hj.
  assert (EO : entry_ok Bm L0 A0 mem0 (nth j es no_entry))
    by (apply (proj1 (Forall_forall _ _) EOK0); apply nth_In; exact Hj).
  destruct EO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBUF & _ & HHP & _ & _ & HK).
  split.
  - unfold entry_links, drain_start. cbn [da_buf da_hp da_keys]. unfold gnm, known_at. cbn [resolve].
    split; [|split].
    + intros Hc. destruct HBUF as [(C & _)|(_ & HB & _)]; [lia | exact (gst_live _ _ HB)].
    + intros Hh. destruct HHP as [(C & _)|(HB & _)]; [contradiction | exact (gst_live _ _ HB)].
    + apply (gst_f2 _ _ _ _ HK). intros k (HB & _). exact (gst_live _ _ HB).
  - intros He.
    assert (GO : gone_src_ok Bm L0 A0 mem0 G gOUT es (nth j es no_entry) (nth j hs no_hj)).
    { apply (proj1 (Forall_forall _ _) GSO (nth j es no_entry, nth j hs no_hj)).
      rewrite <- combine_nth by lia. apply nth_In. rewrite length_combine. lia. }
    destruct (GO He) as (SA & _).
    destruct SA as (_ & _ & _ & _ & _ & LP & _ & _ & _ & _ & HPB & _ & _ & _ & _ & LE & LH & _).
    destruct (gst_list _ _ _ _ LP) as [LP1 LP2]. destruct (gst_list _ _ _ _ LE) as [LE1 LE2].
    destruct (gst_list _ _ _ _ LH) as [LH1 LH2].
    unfold src_links, expected_links, drain_start. cbn [da_pend da_ev da_erecs]. unfold gnm, known_at. cbn [resolve].
    split; [exact LP1|]. split; [apply (gst_f2 _ _ _ _ LP2); intros r X; exact X|].
    split; [exact (gst_live _ _ HPB)|].
    split; [split; [exact LE1 | apply (gst_f2 _ _ _ _ LE2); intros r X; exact X]|].
    split; [exact LH1 | exact LH2].
Qed.

Lemma gone_start : SR segs (mkCfg (@YK11.mkst fx0 regs0 (Z_to_bv 64 RELAY_INSTANCE_GONE) mem0 (seg_rom segs)) md0) (AT_TOP 0).
Proof.
  pose proof gS_range as [[GSR1 GSR2] GSR3]. pose proof gS_low as GSL. pose proof K_val as KV.
  pose proof alloc_ceiling_val as ACV.
  pose proof PRE as (M0 & WF0 & BD0 & _ & _ & _ & _ & SW0 & _ & EW0 & _).
  destruct (mr_model Bm MR rig_laws L0 A0 mem0 md0 M0) as (Hh & Hl & _).
  pose proof RA0 as RA0'. rewrite SEGS in RA0'.
  assert (ST : stk rsegs mem0 (gS - 160) gS).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem0 a).
    { rewrite <- SEGS. apply SW0. change (spZ regs0) with gS. lia. }
    split; [exact W|]. destruct (writable_hi_present mem0 a ltac:(lia) W) as [b E]. exists b. unfold mrd, wa. rewrite E. reflexivity. }
  assert (SPE : bv_unsigned (reg_get regs0 2) = gS) by reflexivity.
  assert (OFF0 : send_off cl br (Z.of_nat (length (@nil byte))) = true)
    by (unfold send_off; destruct (cl <? 0), (br =? 1); reflexivity).
  assert (LIVE0 : send_live cl br dd (Z.of_nat (length (@nil byte))) = false)
    by (unfold send_live; rewrite OFF0; reflexivity).
  eapply (rig_run fx0 regs0 (Z_to_bv 64 RELAY_INSTANCE_GONE) mem0 md0); [exact RA0 | exact Hh | exact Hl | |].
  - unfold Regs6ss.mkR_of. change (Z_to_bv 64 RELAY_INSTANCE_GONE) with (Z_to_bv 64 0x13450).
    apply (rig_segA LOCK) with (lo := gS - 160) (N := gN).
    + rewrite SPE. apply stk_normalize; [exact ST | lia].
    + rewrite SPE. lia.
    + unfold G_LOCK_HI. lia.
    + apply mem_inv_normalize.
    + apply rw_cells_normalize; [exact RA0' | rewrite <- SEGS; exact GL0 | intros i0 Hi; cbn in Hi; apply rig_ro_glob; unfold G_LOCK; lia].
    + change RIG_NSRC with G_NSRC.
      apply rw_cells_normalize; [exact RA0' | rewrite <- SEGS; exact NS0 | intros i0 Hi; cbn in Hi; apply rig_ro_glob; unfold G_NSRC; lia].
    + split; [unfold gN; lia | exact NLE].
  - intros s0 R' m' Q REL ROS X.
    unfold rig_postA in Q.
    destruct Q as (x1 & x5 & x6 & x7 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21
      & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m'n & -> & HR & MU & WM & MI & FP & FS & GL).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *.
    rewrite SPE in X, MU, FP, FS.
    pose proof (mem_rel_normalize rsegs mem0 RA0') as RN.
    pose proof (munch_rel rsegs _ mem0 _ m' m'n RN REL ROS MU) as MUr.
    pose proof (wmono_rel rsegs mem0 _ m' m'n RN REL ROS WM) as WMr.
    pose proof (ro_agree_same rsegs mem0 m' RA0' ROS) as RA'.
    pose proof (rw_cells_of_rel rsegs _ _ _ _ REL GL) as GLr.
    pose proof (rw_cells_of_rel rsegs _ _ _ _ REL FP) as FPr.
    pose proof (rw_cells_of_rel rsegs _ _ _ _ REL FS) as FSr.
    rewrite <- SEGS in WMr, RA', GLr, FPr, FSr.
    assert (KL : forall x, 0 <= x < 2 ^ 64 -> ~ (gS - 160 <= x < gS) -> ~ (G_LOCK + 4 <= x < G_LOCK + 8) -> kb2 mem0 m' x).
    { intros x Hx N1 N2. apply (mu_kb2 [(gS - 160, gS); (G_LOCK + 4, G_LOCK + 8)]); [exact MUr | exact WMr | exact Hx |].
      cbn [outside]. split; [exact N1|]. split; [exact N2 | exact I]. }
    assert (RWK : forall a cs, rw_cells segs mem0 a cs -> 0 <= a ->
              a + Z.of_nat (cells_size cs) <= G_LOCK + 4 \/ (G_LOCK + 8 <= a /\ a + Z.of_nat (cells_size cs) <= gS - 160) ->
              rw_cells segs m' a cs).
    { intros a cs H H0 Hb. apply (rw_kb2 mem0); [exact H|]. intros j Hj. apply KL; unfold G_LOCK in *; lia. }
    assert (BK : forall q, bkept L0 A0 mem0 L0 A0 m' q).
    { intros q. apply (mu_bkept L0 A0 [(gS - 160, gS); (G_LOCK + 4, G_LOCK + 8)] mem0 m' md0 q M0 MUr WMr).
      intros k i Hin Hi. pose proof (rig_blk L0 A0 mem0 md0 q k i M0 Hin Hi) as (_ & H4 & Hc & _).
      apply rig_blocks_in in Hin as (p & Ep & Hp).
      pose proof (ax_blocks_img AX L0 A0 mem0 md0 p k i M0 Hp Hi) as NI. rewrite Ep in NI.
      cbn [outside]. split; [lia|]. split; [|exact I].
      intros Hx. apply NI.
      exact (proj1 (IMGR (q + i) ltac:(unfold G_LOCK, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))). }
    assert (SCW : forall a, scratch_k Bm RELAY_INSTANCE_GONE_K regs0 a -> writable_at segs mem0 a).
    { intros a [Ha|Ha]; [apply SW0 | apply EW0]; exact Ha. }
    pose proof (chain_refl RELAY_INSTANCE_GONE_K Eall (Fcur 0) L0 A0 regs0 mem0 md0 M0 WF0 BD0 SCW) as CH0.
    assert (CH : chain RELAY_INSTANCE_GONE_K Eall (Fcur 0) L0 A0 regs0 mem0 md0 L0 A0 m' md0).
    { apply (chain_munch _ _ _ _ _ _ _ _ _ _ _ _ _ _ CH0 MUr WMr).
      intros x Hx OW. cbn [outside] in OW.
      destruct (Z_le_gt_dec (gS - 160) x) as [D1|D1]; [destruct (Z_lt_ge_dec x gS) as [D2|D2]|].
      - left. split; [left; change (spZ regs0) with gS; lia | lia].
      - right. left. split; [right; left; unfold G_LOCK in *; lia|].
        apply IMGR. unfold G_LOCK, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. lia.
      - right. left. split; [right; left; unfold G_LOCK in *; lia|].
        apply IMGR. unfold G_LOCK, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. lia. }
    pose proof CH as (M' & _).
    apply SR_ret.
    exists fx0, R', L0, A0, m', md0, (@nil (rev sptr)), (@nil sptr), es, (map fst hs), (@nil (list (list Z))), (@nil byte), gOUT, gCAP, junk.
    split.
    { rewrite SEGS. unfold gN. destruct (length es); reflexivity. }
    split; [exact FRM0|].
    split.
    { intros Hn. destruct (HR ltac:(unfold gN; lia)) as (E18 & E19 & E23).
      rewrite (getr_of_eqv _ _ 18 X eq_refl), (getr_of_eqv _ _ 19 X eq_refl), (getr_of_eqv _ _ 23 X eq_refl).
      simp_regs. split; [exact E18|]. split; [exact E19 | exact E23]. }
    split; [rewrite (getr_of_eqv _ _ 2 X eq_refl); simp_regs; reflexivity|].
    split; [rewrite (getr_of_eqv _ _ 3 X eq_refl); simp_regs; reflexivity|].
    split; [rewrite (getr_of_eqv _ _ 4 X eq_refl); simp_regs; reflexivity|].
    split; [rewrite (getr_of_eqv _ _ 8 X eq_refl); simp_regs; reflexivity|].
    split; [rewrite (getr_of_eqv _ _ 22 X eq_refl); simp_regs; reflexivity|].
    split; [exact CH|].
    split; [exact INIT0|].
    split; [split; [reflexivity | split; [intros ext; reflexivity | exact RES0]]|].
    split.
    { rewrite LIVE0. exists (gnm gOUT), [], []. split; [reflexivity|]. split; [reflexivity|].
      split.
      { unfold gpos_top. rewrite (gpair4 grun). cbn [length Z.of_nat]. rewrite Z.add_0_r. reflexivity. }
      split; [intros HL; discriminate HL|].
      split.
      { intros _. split; [reflexivity|]. intros Hc.
        destruct HOUT0 as [(C0 & _)|(_ & _ & HB & _)]; [lia | exact (gst_live _ _ HB)]. }
      intros j Hj. lia. }
    split.
    { intros q m Hq.
      destruct (Z.eq_dec q gOUT) as [Y0|Y0]; [right; right; right; exact Y0|].
      destruct (in_dec Z.eq_dec q (concat (map entry_blocks es))) as [Y1|Y1]; [right; left; exact Y1|].
      destruct (in_dec Z.eq_dec q (drained_blocks es hs)) as [Y2|Y2].
      - right; right; left. unfold drained_blocks in Y2. rewrite <- gst_srcblk in Y2. exact Y2.
      - left. split; [exact Hq|]. split; [exact Y0|]. split; assumption. }
    split; [exact RA'|].
    split; [exact GLr|].
    split; [apply RWK; [exact NS0 | unfold G_NSRC; lia | left; cbn; unfold G_NSRC, G_LOCK; lia]|].
    split; [apply RWK; [exact GS0 | unfold G_SRC; lia | left; cbn; unfold G_SRC, G_LOCK; lia]|].
    split; [exact GB0|].
    split; [apply RWK; [exact CCL0 | unfold G_CLIENT; lia | left; cbn; unfold G_CLIENT, G_LOCK; lia]|].
    split; [rewrite OFF0; apply RWK; [exact CBR0 | unfold G_BROKEN; lia | left; cbn; unfold G_BROKEN, G_LOCK; lia]|].
    split; [apply RWK; [exact CDD0 | unfold G_DEAD; lia | left; cbn; unfold G_DEAD, G_LOCK; lia]|].
    split; [rewrite OFF0; apply RWK; [exact CEI0 | unfold G_EINTR; lia | left; cbn; unfold G_EINTR, G_LOCK; lia]|].
    split.
    { pose proof CERR0 as [ev Hev]. exists ev.
      pose proof (in_img_low Bm SEGS (errno_addr Bm + 3) (IMGE (errno_addr Bm + 3) ltac:(lia))).
      pose proof (in_img_low Bm SEGS (errno_addr Bm) (IMGE (errno_addr Bm) ltac:(lia))).
      apply RWK; [exact Hev | lia | right; cbn; unfold G_LOCK_HI, G_LOCK in *; lia]. }
    split.
    { intros j Hj. apply RWK; [exact (SRCH j Hj) | unfold G_S, SRC_SIZE; lia | right; cbn; unfold G_S, SRC_SIZE, G_LOCK in *; lia]. }
    split; [exact FPr|].
    split.
    { destruct (present_rw_cells segs m' (gP + 8) 48) as [jb H]; [unfold gP in *; lia | unfold gP in *; lia | |].
      - intros j Hj. destruct CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SW).
        apply (writable_hi_present m'); [unfold gP in *; lia|]. rewrite <- SEGS. apply SW.
        left. change (spZ regs0) with gS. unfold gP in *. lia.
      - exists jb. exact H. }
    split; [replace (gP + 56) with (gS - 104) by (unfold gP; ring); exact FSr|].
    split; [reflexivity|].
    split.
    { destruct TAB0 as (Htl & Htr). exists tail0. split; [exact Htl|].
      apply (rw_in_block L0 A0 mem0 L0 A0 m' G SRC_TABLE); [exact Htr | apply BK | exact GB0 | lia | cbn; unfold SRC_TABLE, SRC_ENTRY; lia]. }
    split.
    { apply Forall_forall. intros e He. apply (entry_okk_kept L0 A0 mem0 L0 A0 m' md0);
        [apply entry_okk_of; exact (proj1 (Forall_forall _ _) EOK0 e He) | exact M' | intros q _; apply BK]. }
    split; [rewrite length_map; exact LHS|].
    split; [reflexivity|].
    split; [lia|].
    split.
    { intros j Hj He. rewrite gst_nth_fst by lia.
      pose proof (proj1 (Forall_forall _ _) GSO (nth j es no_entry, nth j hs no_hj)) as GO.
      assert (Hin : In (nth j es no_entry, nth j hs no_hj) (combine es hs)).
      { rewrite <- combine_nth by lia. apply nth_In. rewrite length_combine. lia. }
      destruct (GO Hin He) as (HS & Hl4 & _).
      apply (src_at_kept L0 A0 mem0 L0 A0 m'); [exact HS | | intros q _; apply BK].
      assert (Hjs : (snd (nth j hs no_hj) < 4)%nat) by exact Hl4.
      intros x Hx. apply KL; unfold gHA, G_S, SRC_SIZE, G_LOCK in *; lia. }
    split; [intros j Hj; exfalso; lia|].
    split; [intros Hn; unfold pend_rel; rewrite gst_nth_fst by lia; split; [reflexivity|]; split; [reflexivity|];
      apply gst_pend; lia|].
    split; [intros j Hj; unfold pend_rel; rewrite gst_nth_fst by lia; split; [reflexivity|]; split; [reflexivity|];
      apply gst_pend; lia|].
    split; [rewrite gst_srcblk; exact ND0|].
    split; [intros q m Hq _ _ _; exact Hq|].
    split.
    { intros q m Hq Hm NF. split.
      - intros Hin. apply NF. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [right; left; exact Hin|].
        right; right. unfold drained_blocks. rewrite <- gst_srcblk. exact Hin.
      - intros HL. rewrite LIVE0 in HL. discriminate. }
    split; [reflexivity|].
    split; [unfold gbound; cbn; lia|].
    split.
    { intros _. split; [apply RWK; [exact COUT0 | unfold G_OUTV; lia | left; cbn; unfold G_OUTV, G_LOCK; lia]|].
      split; [reflexivity|]. split; [reflexivity|]. intros Hc.
      destruct HOUT0 as [(C0 & _)|(_ & _ & Hb & _ & HB & HlO & Hlj)]; [lia|].
      split; [exact Hb|].
      apply (bytes_in_block L0 A0 mem0 L0 A0 m' gOUT gCAP); [exact HB | apply BK | exact Hb | lia | rewrite length_app; lia]. }
    intros HL. rewrite LIVE0 in HL. discriminate.
Qed.

(* ===== region gone_drain ===== *)

Lemma gdr_nodup_app : forall (l1 l2 : list Z), List.NoDup l1 -> List.NoDup l2 -> (forall x, In x l1 -> ~ In x l2) ->
  List.NoDup (l1 ++ l2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 H1 H2 HD; [exact H2|].
  apply NoDup_cons_iff in H1 as [Hn H1]. cbn [app]. constructor.
  - intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hn Hin) | exact (HD a (or_introl eq_refl) Hin)].
  - apply IH; [exact H1 | exact H2 |]. intros x Hx. apply HD. right. exact Hx.
Qed.

Lemma gdr_perm_mid : forall (A B R : list Z), Permutation (A ++ B ++ R) (B ++ A ++ R).
Proof. intros A B R. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. Qed.

Lemma gdr_perm6 : forall (P1 X S1 P2 Y S2 : list Z),
  Permutation ((P1 ++ X ++ S1) ++ (P2 ++ Y ++ S2)) ((X ++ Y) ++ (P1 ++ S1 ++ P2 ++ S2)).
Proof.
  intros P1 X S1 P2 Y S2. rewrite <- !app_assoc.
  eapply perm_trans; [apply gdr_perm_mid|]. apply Permutation_app_head.
  replace (P1 ++ S1 ++ P2 ++ Y ++ S2) with ((P1 ++ S1 ++ P2) ++ Y ++ S2) by (rewrite <- !app_assoc; reflexivity).
  eapply perm_trans; [apply gdr_perm_mid|]. rewrite <- !app_assoc. apply Permutation_refl.
Qed.

Lemma gdr_list_ext : forall {X} (l l' : list X) d, length l = length l' ->
  (forall n, (n < length l)%nat -> nth n l d = nth n l' d) -> l = l'.
Proof.
  intros X l. induction l as [|a l IH]; intros [|b l'] d HL H; cbn [length] in HL; try discriminate; [reflexivity|].
  f_equal; [exact (H 0%nat ltac:(cbn; lia))|]. apply (IH l' d); [lia|].
  intros n Hn. exact (H (S n) ltac:(cbn; lia)).
Qed.

Lemma gdr_nth_rep : forall {X} (l : list X) i y j d, (i < length l)%nat ->
  nth j (firstn i l ++ y :: skipn (S i) l) d = if Nat.eqb j i then y else nth j l d.
Proof.
  intros X l. induction l as [|a l IH]; intros i y j d Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; destruct j as [|j]; cbn; try reflexivity.
  apply IH. lia.
Qed.

Lemma gdr_len_rep : forall {X} (l : list X) i (y : X), (i < length l)%nat ->
  length (firstn i l ++ y :: skipn (S i) l) = length l.
Proof. intros X l i y Hi. rewrite length_app, firstn_length_le by lia. cbn [length]. rewrite length_skipn. lia. Qed.

Lemma gdr_rep_concat : forall {X Y} (f : X -> list Y) l i y,
  concat (map f (firstn i l ++ y :: skipn (S i) l)) =
  concat (map f (firstn i l)) ++ f y ++ concat (map f (skipn (S i) l)).
Proof. intros X Y f l i y. rewrite map_app, concat_app. reflexivity. Qed.

Lemma gdr_in_rep : forall (Xs Xs' : list (list Z)) i x, length Xs' = length Xs ->
  (forall j, (j < length Xs)%nat -> j <> i -> nth j Xs' [] = nth j Xs []) ->
  In x (concat Xs') -> In x (concat Xs) \/ In x (nth i Xs' []).
Proof.
  intros Xs Xs' i x HL HN Hx. apply in_concat in Hx as (l & Hl & Hx).
  destruct (In_nth Xs' l [] Hl) as (n & Hn & En).
  destruct (Nat.eq_dec n i) as [->|Ne]; [right; rewrite En; exact Hx|].
  left. apply (rigl_in_nth_concat Xs n x). rewrite <- (HN n ltac:(lia) Ne), En. exact Hx.
Qed.

Lemma gdr_nodup_replace : forall (a b b' : Z) (Xs Ys Xs' Ys' : list (list Z)) i,
  (i < length Xs)%nat -> length Ys = length Xs -> length Xs' = length Xs -> length Ys' = length Xs ->
  (forall j, (j < length Xs)%nat -> j <> i -> nth j Xs' [] = nth j Xs [] /\ nth j Ys' [] = nth j Ys []) ->
  List.NoDup (a :: b :: concat Xs ++ concat Ys) ->
  List.NoDup (a :: b' :: nth i Xs' [] ++ nth i Ys' []) ->
  (forall x, In x (concat Xs ++ concat Ys) -> ~ In x (nth i Xs [] ++ nth i Ys []) -> x <> b ->
     ~ In x (b' :: nth i Xs' [] ++ nth i Ys' [])) ->
  List.NoDup (a :: b' :: concat Xs' ++ concat Ys').
Proof.
  intros a b b' Xs Ys Xs' Ys' i Hi HY HX' HY' HN ND ND' HF.
  assert (EX : Xs' = firstn i Xs ++ nth i Xs' [] :: skipn (S i) Xs).
  { apply (gdr_list_ext _ _ []); [rewrite gdr_len_rep by lia; lia|].
    intros n Hn. rewrite gdr_nth_rep by lia.
    destruct (Nat.eqb_spec n i) as [->|Ne]; [reflexivity | exact (proj1 (HN n ltac:(lia) Ne))]. }
  assert (EY : Ys' = firstn i Ys ++ nth i Ys' [] :: skipn (S i) Ys).
  { apply (gdr_list_ext _ _ []); [rewrite gdr_len_rep by lia; lia|].
    intros n Hn. rewrite gdr_nth_rep by lia.
    destruct (Nat.eqb_spec n i) as [->|Ne]; [reflexivity | exact (proj2 (HN n ltac:(lia) Ne))]. }
  assert (CX : concat Xs' = concat (firstn i Xs) ++ nth i Xs' [] ++ concat (skipn (S i) Xs))
    by (rewrite EX at 1; rewrite concat_app; reflexivity).
  assert (CY : concat Ys' = concat (firstn i Ys) ++ nth i Ys' [] ++ concat (skipn (S i) Ys))
    by (rewrite EY at 1; rewrite concat_app; reflexivity).
  pose proof (rigl_concat_split Xs i Hi) as SX.
  pose proof (rigl_concat_split Ys i ltac:(lia)) as SY.
  assert (PO : Permutation (concat Xs ++ concat Ys) ((nth i Xs [] ++ nth i Ys []) ++
                 (concat (firstn i Xs) ++ concat (skipn (S i) Xs) ++ concat (firstn i Ys) ++ concat (skipn (S i) Ys))))
    by (rewrite SX, SY; apply gdr_perm6).
  assert (PN : Permutation (concat Xs' ++ concat Ys') ((nth i Xs' [] ++ nth i Ys' []) ++
                 (concat (firstn i Xs) ++ concat (skipn (S i) Xs) ++ concat (firstn i Ys) ++ concat (skipn (S i) Ys))))
    by (rewrite CX, CY; apply gdr_perm6).
  apply (Permutation_NoDup (perm_skip a (perm_skip b PO))) in ND.
  apply NoDup_cons_iff in ND as [Na ND]. apply NoDup_cons_iff in ND as [Nb ND].
  apply (Permutation_NoDup (Permutation_sym (perm_skip a (perm_skip b' PN)))).
  change (List.NoDup ((a :: b' :: nth i Xs' [] ++ nth i Ys' []) ++
    (concat (firstn i Xs) ++ concat (skipn (S i) Xs) ++ concat (firstn i Ys) ++ concat (skipn (S i) Ys)))).
  apply gdr_nodup_app; [exact ND' | exact (NoDup_app_remove_l _ _ ND) |].
  intros x Hx HR.
  assert (HO : In x (concat Xs ++ concat Ys))
    by (apply (Permutation_in _ (Permutation_sym PO)); apply in_or_app; right; exact HR).
  destruct Hx as [<-|Hx].
  - apply Na. right. apply in_or_app. right. exact HR.
  - apply (HF x HO); [intros Y; exact (rig_nodup_app_disj _ _ x ND Y HR) | intros ->; apply Nb; apply in_or_app; right; exact HR | exact Hx].
Qed.

Lemma gdr_nodup_other : forall (a b : Z) (Xs Ys : list (list Z)) i j x,
  length Ys = length Xs -> j <> i ->
  List.NoDup (a :: b :: concat Xs ++ concat Ys) -> In x (nth j Xs [] ++ nth j Ys []) ->
  x <> a /\ x <> b /\ ~ In x (nth i Xs [] ++ nth i Ys []).
Proof.
  intros a b Xs Ys i j x HL Hij ND Hx.
  assert (Hc : In x (concat Xs ++ concat Ys)).
  { apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left | right]; exact (rigl_in_nth_concat _ j x Hx). }
  apply NoDup_cons_iff in ND as [Na ND]. apply NoDup_cons_iff in ND as [Nb ND].
  split; [intros ->; exact (Na (or_intror Hc))|]. split; [intros ->; exact (Nb Hc)|].
  rewrite <- concat_app in ND.
  assert (IX : forall k y, In y (nth k Xs []) -> In y (nth k (Xs ++ Ys) []) /\ (k < length Xs)%nat).
  { intros k y Hy. destruct (Nat.lt_ge_cases k (length Xs)) as [Hk|Hk].
    - rewrite app_nth1 by exact Hk. split; [exact Hy | exact Hk].
    - rewrite nth_overflow in Hy by exact Hk. destruct Hy. }
  assert (IY : forall k y, In y (nth k Ys []) -> In y (nth (length Xs + k) (Xs ++ Ys) [])).
  { intros k y Hy. rewrite app_nth2 by lia. replace (length Xs + k - length Xs)%nat with k by lia. exact Hy. }
  intros Hi. apply in_app_or in Hx as [Hx|Hx]; apply in_app_or in Hi as [Hi|Hi].
  - destruct (IX j x Hx) as [A1 _]. destruct (IX i x Hi) as [A2 _]. exact (Hij (rig_nodup_concat_disj _ j i x ND A1 A2)).
  - destruct (IX j x Hx) as [A1 B1]. pose proof (rig_nodup_concat_disj _ _ _ x ND A1 (IY i x Hi)). lia.
  - destruct (IX i x Hi) as [A2 B2]. pose proof (rig_nodup_concat_disj _ _ _ x ND (IY j x Hx) A2). lia.
  - pose proof (rig_nodup_concat_disj _ _ _ x ND (IY j x Hx) (IY i x Hi)). lia.
Qed.

Lemma gdr_nodup_map : forall {X Y} (f : X -> Y) (l : list X), (forall a b, f a = f b -> a = b) -> List.NoDup l ->
  List.NoDup (map f l).
Proof.
  intros X Y f l Hf. induction l as [|a l IH]; intros H; cbn [map]; [constructor|].
  apply NoDup_cons_iff in H as [Hn H]. constructor; [|exact (IH H)].
  intros Hin. apply in_map_iff in Hin as (b & Eb & Hb). apply Hf in Eb. subst b. exact (Hn Hb).
Qed.

Lemma gdr_bzs_inj : forall a b, bzs a = bzs b -> a = b.
Proof.
  unfold bzs. induction a as [|x a IH]; intros [|y b] H; cbn [map] in H; try discriminate; [reflexivity|].
  injection H as E1 E2. f_equal; [apply bv_eq; exact E1 | exact (IH b E2)].
Qed.

Lemma gdr_nd : forall {X} (l : list X), NoDup l <-> List.NoDup l.
Proof. intros X l. apply NoDup_ListNoDup. Qed.

Lemma gdr_nodup_kt : forall ks, NoDup (map key_text ks) -> NoDup (keys_texts ks).
Proof.
  intros ks H. apply gdr_nd. unfold keys_texts. rewrite <- (map_map key_text bzs).
  apply gdr_nodup_map; [exact gdr_bzs_inj | apply gdr_nd; exact H].
Qed.

Lemma gdr_rw_cb : forall m a n bs, rw_cells segs m a [CB n bs] <->
  length bs = n /\ bytes_at segs m a bs /\ wr_at segs m a (Z.of_nat n).
Proof.
  intros m a n bs. unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite app_nil_r, Nat.add_0_r. tauto.
Qed.

Lemma gdr_cb_mid : forall m a n (P M R : list byte), rw_cells segs m a [CB n (P ++ M ++ R)] ->
  rw_cells segs m (a + Z.of_nat (length P)) [CB (length M) M].
Proof.
  intros m a n P M R H. apply gdr_rw_cb in H as (HL & HB & (W0 & W1 & W)).
  apply bytes_at_app in HB as [_ HB]. apply bytes_at_app in HB as [HB _].
  rewrite !length_app in HL.
  apply gdr_rw_cb. split; [reflexivity|]. split; [exact HB|].
  split; [lia|]. split; [lia|]. intros x Hx.
  replace (a + Z.of_nat (length P) + x) with (a + (Z.of_nat (length P) + x)) by lia. apply W. lia.
Qed.

Lemma gdr_cb_c44 : forall m a n bs x y, rw_cells segs m a [CB n bs] -> (8 <= n)%nat ->
  firstn 8 bs = le4 (Z_to_bv 64 x) ++ le4 (Z_to_bv 64 y) ->
  rw_cells segs m a [C4 (Z_to_bv 64 x); C4 (Z_to_bv 64 y)].
Proof.
  intros m a n bs x y H Hn E. apply gdr_rw_cb in H as (HL & HB & (W0 & W1 & W)).
  rewrite <- (firstn_skipn 8 bs), E in HB. apply bytes_at_app in HB as [HB _].
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
Qed.

Lemma gdr_okk_len : forall L A m e, entry_okk L A m e -> length (entry_bytes e) = 56%nat.
Proof.
  intros L A m e (ks & Eks & OK).
  destruct (map_fst_keys (re_keys e) ks Eks) as (_ & _ & EL & _).
  rewrite <- (entry_bytes_wk e ks EL).
  destruct OK as (_ & _ & H1 & H2 & _). apply rig_entry_len; assumption.
Qed.

Lemma gdr_okk_facts : forall L A m e, entry_okk L A m e -> length (re_pad1 e) = 4%nat /\ (re_eof e = 0 \/ re_eof e = 1).
Proof. intros L A m e (ks & _ & (H1 & _ & H3 & _)). split; [exact H3 | exact H1]. Qed.

Lemma gdr_tab_mid : forall L A mem es_c tl i, (i < length es_c)%nat -> Forall (entry_okk L A mem) es_c ->
  table_at Bm mem G es_c tl -> rw_cells segs mem (G + 56 * Z.of_nat i) [CB 56 (entry_bytes (nth i es_c no_entry))].
Proof.
  intros L A mem es_c tl i Hi HF (Htl & Htr).
  assert (LEN : Forall (fun x => length (entry_bytes x) = 56%nat) es_c)
    by (eapply Forall_impl; [|exact HF]; intros x Hx; exact (gdr_okk_len _ _ _ _ Hx)).
  destruct (rig_concat_nth es_c i Hi LEN) as [CS CL].
  rewrite CS, <- !app_assoc in Htr.
  pose proof (gdr_cb_mid _ _ _ _ _ _ Htr) as X. rewrite CL in X.
  rewrite (gdr_okk_len _ _ _ _ (proj1 (Forall_forall _ _) HF _ (nth_In _ _ Hi))) in X.
  replace (G + 56 * Z.of_nat i) with (G + Z.of_nat (56 * i)) by lia. exact X.
Qed.

Lemma gdr_GI_same : forall i cur part base bound regs regs' L A mem m' md k qd es_c hs_c kss LB OUTc CAPc junkc,
  GI i cur part base bound regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc ->
  mem_rel rsegs m' (normalize rsegs mem) -> ro_same rsegs mem m' ->
  getr regs' 2 = Z_to_bv 64 gP -> getr regs' 3 = getr regs0 3 -> getr regs' 4 = getr regs0 4 ->
  getr regs' 8 = getr regs0 10 -> getr regs' 22 = Z_to_bv 64 RIG_S6 ->
  GI i cur part base bound regs' L A m' md k qd es_c hs_c kss LB OUTc CAPc junkc.
Proof.
  intros i cur part base bound regs regs' L A mem m' md k qd es_c hs_c kss LB OUTc CAPc junkc HG REL ROS R2 R3 R4 R8 R22.
  pose proof HG as HG'. destruct HG' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RA & _).
  rewrite SEGS in RA.
  pose proof (mem_rel_normalize rsegs mem RA) as RN.
  apply (GI_stack i cur part base bound regs regs' L A mem m' md k qd es_c hs_c kss LB OUTc CAPc junkc []).
  - exact HG.
  - exact (munch_rel rsegs [] mem (normalize rsegs mem) m' (normalize rsegs mem) RN REL ROS (munch_refl [] _)).
  - rewrite SEGS. exact (wmono_rel rsegs mem (normalize rsegs mem) m' (normalize rsegs mem) RN REL ROS (wmono_refl rsegs _)).
  - rewrite SEGS. exact (ro_agree_same rsegs mem m' RA ROS).
  - intros x _ Ou. exfalso. apply Ou. exact I.
  - exact R2.
  - exact R3.
  - exact R4.
  - exact R8.
  - exact R22.
Qed.

Lemma gsh_combine_snd : forall {X Y} (l : list X) (l' : list Y), length l = length l' -> map snd (combine l l') = l'.
Proof.
  intros X Y l. induction l as [|x l IH]; intros [|y l'] E; cbn [length] in E; try lia; [reflexivity|].
  cbn [combine map snd]. rewrite IH by lia. reflexivity.
Qed.

(* Links of blocks named by the entry state do not depend on the returned addresses. *)
Lemma gk_f2 : forall {X : Type} (l : list X) (g : X -> Z) (P : X -> sptr -> Prop) (qs qs' : list sptr),
  Forall2 (fun r a => P r (resolveF qs a)) l (map (fun r => gnm (g r)) l) ->
  Forall2 (fun r a => P r (resolveF qs' a)) l (map (fun r => gnm (g r)) l).
Proof.
  intros X l g P qs qs'. induction l as [|x l IH]; intros F; cbn [map] in F |- *; [constructor|].
  inversion F as [|? ? ? ? Px F']; subst. constructor; [exact Px | exact (IH F')].
Qed.

Lemma gk_entry_qs : forall L A qs qs' e o h,
  entry_links L A qs (drain_start gnm o e h) e -> entry_links L A qs' (drain_start gnm o e h) e.
Proof.
  intros L A qs qs' e o h (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|].
  exact (gk_f2 (re_keys e) key_addr (fun k p => live_at L A p (key_addr k) (Z.of_nat (length (key_text k)) + 1))
           qs qs' B3).
Qed.

Lemma gk_src_qs : forall L A qs qs' e o h,
  src_links L A qs gnm (drain_start gnm o e h) h -> src_links L A qs' gnm (drain_start gnm o e h) h.
Proof.
  intros L A qs qs' e o h (B1 & B2 & B3 & (B4 & B5) & B6 & B7).
  split; [exact B1|].
  split; [exact (gk_f2 (hl_recs (hs_pending h)) fst
                   (fun r p => live_at L A p (fst r) (Z.of_nat (length (snd r)) + 1)) qs qs' B2)|].
  split; [exact B3|].
  split; [split; [exact B4 | exact (gk_f2 (hl_recs (hs_expected h)) fst
                                    (fun r p => live_at L A p (fst r) (Z.of_nat (length (snd r)) + 1)) qs qs' B5)]|].
  split; [exact B6|].
  eapply Forall_impl; [|exact B7]. intros r X. exact X.
Qed.

(* Source i's held keys' addresses and blocks at the entry. *)
Definition gka0 (i : nat) : list adrF := map (fun k => gnm (key_addr k)) (re_keys (nth i es no_entry)).
Definition gda0 (i : nat) : dadr := drain_start gnm adr0 (nth i es no_entry) (fst (nth i hs no_hj)).

Lemma gdr_eof1 : forall i regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc,
  (i < length es)%nat -> re_eof (nth i es no_entry) = 1 ->
  GI i (pend_rel i) [] (gpos_top i) (gbound i) regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc ->
  GI i (inner_cur i (keys_texts (re_keys (nth i es no_entry))) 0 (keys_texts (re_keys (nth i es no_entry))) []
          (gka0 i) (gda0 i) (combine (keys_texts (re_keys (nth i es no_entry))) (gka0 i)))
    (part_of i []) (gpos_k i (gda0 i) (gkept (keys_texts (re_keys (nth i es no_entry))) (gka0 i)) []
                      (gxks (keys_texts (re_keys (nth i es no_entry))) (gka0 i))) (bound_in i [])
    regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc.
Proof.
  intros i regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc Hi He HG.
  destruct HG as (G2 & G3 & G4 & G8 & G22 & CH & INIT & RES & BUD & POT & RA & GL & HNS & HGS & HGB & CCL & CBR & CDD
    & CEI & CERR & SRCH' & FR0 & FRB & FRS & HLE & HTAB & HEOK & HLH & HLK & HIL & HSRC & HDONE & HCUR & HPEND & HND
    & HSUR & HSV & HLB & HT & HDEAD & HLIVE).
  destruct (HCUR Hi) as (Ee & Eh & PL). rewrite Ee, Eh in PL.
  assert (PO : part_of i [] = []) by (unfold part_of, lines_of, entry_lines; rewrite He; reflexivity).
  destruct BUD as (oa & ssd & dsd & Lssd & Ldsd & EQ & OL & OD & DL).
  unfold gpos_top, gps in EQ. rewrite (rig_skipn_combine es hs i no_entry no_hj Hi LHS), rig_gone_run_cons in EQ.
  cbv zeta in EQ. unfold after_drain, after_drain_adr in EQ. rewrite He in EQ.
  assert (GS : gs_of i = drain_init (gNO + Z.of_nat (length LB))
                 (if send_live cl br dd (Z.of_nat (length LB)) then CAPc else gCAP)
                 (nth i es no_entry) (fst (nth i hs no_hj))).
  { unfold gs_of, gss. rewrite EQ. cbn [fst snd]. rewrite app_nth2 by lia. rewrite Lssd, Nat.sub_diag. reflexivity. }
  assert (CUR : inner_cur i (keys_texts (re_keys (nth i es no_entry))) 0 (keys_texts (re_keys (nth i es no_entry))) []
                  (gka0 i) (gda0 i) (combine (keys_texts (re_keys (nth i es no_entry))) (gka0 i))
                  L A qd (nth i es_c no_entry) (nth i hs_c (fst (nth i hs no_hj)))).
  { rewrite Ee, Eh.
    assert (Hi' : (i < length es_c)%nat) by lia.
    pose proof (proj1 (Forall_forall _ _) HEOK _ (nth_In es_c no_entry Hi')) as OKK. rewrite Ee in OKK.
    destruct OKK as (ks & Eks & OK).
    destruct (map_fst_keys (re_keys (nth i es no_entry)) ks Eks) as (_ & _ & _ & _ & EX).
    pose proof OK as (_ & SK01 & _). cbn [with_keys re_skip] in SK01.
    destruct OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDt & _).
    split; [|split; [reflexivity|split; [lia|split; [intros n Hn; lia|]]]].
    - unfold done0. cbv zeta. rewrite He.
      split; [reflexivity|]. split; [reflexivity|].
      split; [rewrite <- EX; exact (gdr_nodup_kt ks NDt)|].
      split; [unfold entry_lines; rewrite He; intros y; reflexivity|].
      split; [intros X; discriminate X|].
      split; [intros _; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; reflexivity|].
      unfold dsrel. cbv zeta. rewrite GS. cbn [drain_init ds_H ds_cap ds_u ds_skip ds_ka].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [destruct SK01 as [X|X]; rewrite X; reflexivity|].
      split; [reflexivity|]. intros X. rewrite He in X. discriminate X.
    - split; [unfold gei; rewrite Nat.sub_0_r; cbn [app]; apply surjective_pairing|].
      assert (LKA : length (keys_texts (re_keys (nth i es no_entry))) = length (gka0 i))
        by (unfold keys_texts, gka0; rewrite !length_map; reflexivity).
      split; [apply gsh_combine_fst; exact LKA|].
      split; [symmetry; exact LKA|].
      split; [exists []; split; [reflexivity|]; unfold geia; rewrite Nat.sub_0_r; cbn [app]; apply surjective_pairing|].
      rewrite gsh_combine_snd by exact LKA.
      destruct PL as [PE PS].
      split; [intros post; exact (gk_entry_qs L A [] (qd ++ post) _ adr0 _ PE)|].
      intros HE post. exact (gk_src_qs L A [] (qd ++ post) _ adr0 _ (PS HE)). }
  split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G8|]. split; [exact G22|].
  split; [exact CH|]. split; [exact INIT|]. split; [exact RES|].
  split.
  { exists oa, ssd, dsd. split; [exact Lssd|]. split; [exact Ldsd|].
    split; [rewrite EQ; unfold gpos_k, gda0, gka0, gkept, gxks; rewrite GS; reflexivity|].
    split; [exact OL|]. split; [exact OD | exact DL]. }
  split; [exact POT|]. split; [exact RA|]. split; [exact GL|]. split; [exact HNS|]. split; [exact HGS|].
  split; [exact HGB|]. split; [exact CCL|]. split; [exact CBR|]. split; [exact CDD|]. split; [exact CEI|].
  split; [exact CERR|]. split; [exact SRCH'|]. split; [exact FR0|]. split; [exact FRB|]. split; [exact FRS|].
  split; [exact HLE|]. split; [exact HTAB|]. split; [exact HEOK|]. split; [exact HLH|]. split; [exact HLK|].
  split; [exact HIL|]. split; [exact HSRC|]. split; [exact HDONE|]. split; [intros _; exact CUR|].
  split; [exact HPEND|]. split; [exact HND|]. split; [exact HSUR|]. split; [exact HSV|].
  split; [rewrite PO; exact HLB|].
  split; [unfold bound_in, pl_of; rewrite He; change (1 =? 0) with false; cbv beta iota; cbn [length]; lia|].
  split; [exact HDEAD | exact HLIVE].
Qed.

Lemma gdr_len_bzs : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.

Lemma gdr_c44_uniq : forall m HA a b c d (r1 r2 : list cell),
  rw_cells segs m HA (C4 (Z_to_bv 64 a) :: C4 (Z_to_bv 64 b) :: r1) ->
  rw_cells segs m HA (C4 (Z_to_bv 64 c) :: C4 (Z_to_bv 64 d) :: r2) ->
  a mod 2 ^ 32 = c mod 2 ^ 32 /\ b mod 2 ^ 32 = d mod 2 ^ 32.
Proof.
  intros m HA a b c d r1 r2 [[_ B1] _] [[_ B2] _].
  cbn [cells_bytes cbytes] in B1, B2.
  apply bytes_at_app in B1 as [A1 B1]. apply bytes_at_app in B1 as [A2 _].
  apply bytes_at_app in B2 as [C1 B2]. apply bytes_at_app in B2 as [C2 _].
  rewrite !length_le4 in *.
  split; apply rig_le4_inj; (eapply (rig_bytes_uniq segs m); [eassumption | eassumption | rewrite !length_le4; reflexivity]).
Qed.

Lemma gdr_splice : forall m m' a n (P M M' R : list byte),
  rw_cells segs m a [CB n (P ++ M ++ R)] ->
  rw_cells segs m' (a + Z.of_nat (length P)) [CB (length M) M'] ->
  (forall x, 0 <= x < Z.of_nat n -> ~ (Z.of_nat (length P) <= x < Z.of_nat (length P) + Z.of_nat (length M)) ->
     kb2 m m' (a + x)) ->
  rw_cells segs m' a [CB n (P ++ M' ++ R)].
Proof.
  intros m m' a n P M M' R H1 H2 K.
  apply gdr_rw_cb in H1 as (HL & HB & (W0 & W1 & W)).
  apply gdr_rw_cb in H2 as (HL2 & HB2 & (V0 & V1 & V)).
  rewrite !length_app in HL.
  apply bytes_at_app in HB as [BP HB]. apply bytes_at_app in HB as [BM BR].
  apply gdr_rw_cb. split; [rewrite !length_app; lia|]. split.
  - apply bytes_at_app. split.
    + apply (bytes_kb2 m); [exact BP|]. intros x Hx. apply K; lia.
    + apply bytes_at_app. split; [exact HB2|].
      rewrite HL2. apply (bytes_kb2 m); [exact BR|]. intros x Hx.
      replace (a + Z.of_nat (length P) + Z.of_nat (length M) + x)
        with (a + (Z.of_nat (length P) + Z.of_nat (length M) + x)) by lia.
      apply K; lia.
  - split; [lia|]. split; [lia|]. intros x Hx.
    destruct (Z_lt_le_dec x (Z.of_nat (length P))) as [D|D];
      [|destruct (Z_lt_le_dec x (Z.of_nat (length P) + Z.of_nat (length M))) as [D2|D2]].
    + exact (proj2 (K x ltac:(lia) ltac:(lia)) (W x ltac:(lia))).
    + replace (a + x) with (a + Z.of_nat (length P) + (x - Z.of_nat (length P))) by lia. apply V. lia.
    + exact (proj2 (K x ltac:(lia) ltac:(lia)) (W x ltac:(lia))).
Qed.

Lemma gdr_lblk : forall L A m LA l b q, list_at Bm L A m LA l b -> In q (list_blocks l) ->
  exists k, In (q, k) (blocks L A) /\ 0 < k.
Proof.
  intros L A m LA l b q (Hc & Hn & Hv & ND1 & ND2 & Hr) Hq.
  unfold list_blocks in Hq. apply in_app_or in Hq as [Hq|Hq].
  - destruct (hl_cap l =? 0) eqn:E0; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct Hv as [(H0 & _)|(H0 & Hin & _)]; [apply Z.eqb_neq in E0; lia|].
    exists (16 * hl_cap l). split; [exact Hin | lia].
  - apply in_map_iff in Hq as (r & <- & Hr0). pose proof (proj1 (Forall_forall _ _) Hr r Hr0) as (H1 & _).
    exists (Z.of_nat (length (snd r)) + 1). split; [exact H1 | lia].
Qed.

Lemma gdr_hblk : forall L A m HA h q, src_at Bm L A m HA h -> In q (hs_blocks h) ->
  exists k, In (q, k) (blocks L A) /\ 0 < k.
Proof.
  intros L A m HA h q (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18) Hq.
  unfold hs_blocks in Hq. apply in_app_or in Hq as [Hq|Hq]; [exact (gdr_lblk _ _ _ _ _ _ _ S6 Hq)|].
  apply in_app_or in Hq as [Hq|Hq]; [destruct Hq as [<-|[]]; exists 6000; split; [exact S11 | lia]|].
  apply in_app_or in Hq as [Hq|Hq]; [exact (gdr_lblk _ _ _ _ _ _ _ S16 Hq) | exact (gdr_lblk _ _ _ _ _ _ _ S17 Hq)].
Qed.

Lemma gdr_eblk : forall L A m e q, entry_okk L A m e -> In q (entry_blocks e) ->
  exists k, In (q, k) (blocks L A) /\ 0 < k.
Proof.
  intros L A m e q (ks & Eks & OK) Hq.
  destruct (map_fst_keys (re_keys e) ks Eks) as (EA & _).
  rewrite <- (entry_blocks_wk e ks EA) in Hq.
  destruct OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbuf & _ & Hhp & _ & _ & Hkeys).
  unfold entry_blocks in Hq. cbn [with_keys re_cap re_buf re_hp re_keys re_kh] in Hq, Hbuf, Hhp, Hkeys.
  apply in_app_or in Hq as [Hq|Hq]; [|apply in_app_or in Hq as [Hq|Hq]].
  - destruct (re_cap e =? 0) eqn:E0; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct Hbuf as [(H0 & _)|(H0 & Hin & _)]; [apply Z.eqb_neq in E0; lia|].
    exists (re_cap e). split; [exact Hin | lia].
  - destruct (re_hp e =? 0) eqn:E0; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct Hhp as [(H0 & _)|(Hin & _ & _ & H8 & _)]; [apply Z.eqb_neq in E0; lia|].
    exists (re_kh e). split; [exact Hin | lia].
  - apply in_map_iff in Hq as (kk & <- & Hk). pose proof (proj1 (Forall_forall _ _) Hkeys kk Hk) as (H1 & _).
    exists (Z.of_nat (length (key_text kk)) + 1). split; [exact H1 | lia].
Qed.

Lemma gdr_gso : forall j, (j < length es)%nat -> gone_src_ok Bm L0 A0 mem0 G gOUT es (nth j es no_entry) (nth j hs no_hj).
Proof.
  intros j Hj. refine (proj1 (Forall_forall _ _) GSO (nth j es no_entry, nth j hs no_hj) _).
  rewrite <- combine_nth by lia. apply nth_In. rewrite length_combine. lia.
Qed.

Lemma gdr_src_lt4 : forall j, (j < length es)%nat -> re_eof (nth j es no_entry) = 0 -> (snd (nth j hs no_hj) < 4)%nat.
Proof. intros j Hj He. exact (proj1 (proj2 (gdr_gso j Hj He))). Qed.

Lemma gdr_src_ne : forall j1 j2, (j1 < length es)%nat -> (j2 < length es)%nat -> j1 <> j2 ->
  re_eof (nth j1 es no_entry) = 0 -> re_eof (nth j2 es no_entry) = 0 ->
  snd (nth j1 hs no_hj) <> snd (nth j2 hs no_hj).
Proof.
  intros j1 j2 H1 H2 Hne E1 E2 Es.
  destruct (gdr_gso j1 H1 E1) as ((S1 & _ & _ & _ & F1 & _) & _ & D1 & _).
  destruct (gdr_gso j2 H2 E2) as ((S2 & _ & _ & _ & F2 & _) & _ & D2 & _).
  rewrite Es in S1.
  destruct (gdr_c44_uniq mem0 _ _ _ _ _ _ _ S1 S2) as [U _].
  rewrite !Z.mod_small in U by lia.
  apply Hne. apply (proj1 (NoDup_nth (map re_fd es) (re_fd no_entry)) (proj1 (gdr_nd _) NDF) j1 j2);
    [rewrite length_map; lia | rewrite length_map; lia|].
  rewrite !map_nth. congruence.
Qed.

Lemma gdr_in_eb : forall i q, (i < length es)%nat -> In q (entry_blocks (nth i es no_entry)) ->
  In q (concat (map entry_blocks es)).
Proof.
  intros i q Hi Hq. apply in_concat. exists (entry_blocks (nth i es no_entry)).
  split; [apply in_map; apply nth_In; exact Hi | exact Hq].
Qed.

Lemma gdr_in_db : forall i q, (i < length es)%nat -> re_eof (nth i es no_entry) = 0 ->
  In q (hs_blocks (fst (nth i hs no_hj))) -> In q (drained_blocks es hs).
Proof.
  intros i q Hi He Hq. unfold drained_blocks. apply in_concat.
  exists (if re_eof (nth i es no_entry) =? 0 then hs_blocks (fst (nth i hs no_hj)) else []).
  split; [|rewrite He; exact Hq].
  apply (in_map (fun p => if re_eof (fst p) =? 0 then hs_blocks (fst (snd p)) else []) _ (nth i es no_entry, nth i hs no_hj)).
  rewrite <- combine_nth by lia. apply nth_In. rewrite length_combine. lia.
Qed.

Definition gdr_E (lv : bool) (OUTd CAPd SA : Z) (j : nat) (bl : list Z) (L : layout) (A : astate) (a : Z) : Prop :=
  send_writes lv OUTd CAPd a \/ SA <= a < SA + SRC_ENTRY \/
  G_S + SRC_SIZE * Z.of_nat j + 12 <= a < G_S + SRC_SIZE * Z.of_nat j + SRC_SIZE \/
  (exists q m, In q bl /\ In (q, m) (blocks L A) /\ q <= a < q + m).

Lemma gdr_blk_img : forall L A m md q k x, MR L A m md -> In (q, k) (blocks L A) -> 0 <= x < k -> ~ in_img Bm (q + x).
Proof.
  intros L A m md q k x HM Hin Hx. apply rig_blocks_in in Hin as (p & <- & Hp).
  exact (ax_blocks_img AX L A m md p k x HM Hp Hx).
Qed.

Lemma gdr_sw_img : forall lv OUTd CAPd a, send_writes lv OUTd CAPd a ->
  (img_plain Bm a /\ (G_BROKEN <= a < G_BROKEN + 1 \/ G_EINTR <= a < G_EINTR + 1 \/ G_OUTV + 8 <= a < G_OUTV + 32)) \/
  (lv = true /\ OUTd <= a < OUTd + CAPd).
Proof.
  intros lv OUTd CAPd a [E|[E|[E|E]]]; [left .. | right; exact E]; (split; [apply IMGR | tauto]);
    unfold G_BROKEN, G_EINTR, G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia.
Qed.

Lemma gdr_notE_blk : forall lv OUTd CAPd SA j bl L A m md q k x,
  MR L A m md -> In (q, k) (blocks L A) -> 0 <= x < k -> (j < 4)%nat ->
  (lv = true -> 0 < CAPd -> In (OUTd, CAPd) (blocks L A) /\ q <> OUTd) ->
  ~ In q bl -> ~ (SA <= q + x < SA + SRC_ENTRY) ->
  ~ gdr_E lv OUTd CAPd SA j bl L A (q + x).
Proof.
  intros lv OUTd CAPd SA j bl L A m md q k x HM Hq Hx Hj HO Hbl HSA [E|[E|[E|(q' & m' & Hq' & Hin' & E)]]].
  - destruct (gdr_sw_img lv OUTd CAPd (q + x) E) as [(P & _)|(Elv & E')].
    + exact (gdr_blk_img L A m md q k x HM Hq Hx (proj1 P)).
    + destruct (HO Elv ltac:(lia)) as [Hin Hne].
      destruct (rig_blk_disj L A m md q k OUTd CAPd HM Hq Hin Hne); lia.
  - exact (HSA E).
  - apply (gdr_blk_img L A m md q k x HM Hq Hx).
    apply (proj1 (IMGR (q + x) ltac:(unfold G_S, SRC_SIZE, SOURCES_MAX, G_RELAY_LO in *; lia))).
  - assert (Hne : q <> q') by (intros <-; exact (Hbl Hq')).
    destruct (rig_blk_disj L A m md q k q' m' HM Hq Hin' Hne); lia.
Qed.

Lemma gdr_notE_img : forall lv OUTd CAPd SA j bl L A m md a,
  MR L A m md -> (lv = true -> 0 < CAPd -> In (OUTd, CAPd) (blocks L A)) ->
  In (G, SRC_TABLE) (blocks L A) -> G <= SA -> SA + SRC_ENTRY <= G + SRC_TABLE ->
  in_img Bm a -> gdr_E lv OUTd CAPd SA j bl L A a ->
  (G_BROKEN <= a < G_BROKEN + 1 \/ G_EINTR <= a < G_EINTR + 1 \/ G_OUTV + 8 <= a < G_OUTV + 32) \/
  (G_S + SRC_SIZE * Z.of_nat j + 12 <= a < G_S + SRC_SIZE * Z.of_nat j + SRC_SIZE).
Proof.
  intros lv OUTd CAPd SA j bl L A m md a HM HO HG H1 H2 Hin [E|[E|[E|(q & m' & _ & Hq & E)]]].
  - destruct (gdr_sw_img lv OUTd CAPd a E) as [(_ & E')|(Elv & E')]; [left; exact E'|].
    exfalso. apply (gdr_blk_img L A m md OUTd CAPd (a - OUTd) HM (HO Elv ltac:(lia)) ltac:(lia)).
    replace (OUTd + (a - OUTd)) with a by ring. exact Hin.
  - exfalso. apply (gdr_blk_img L A m md G SRC_TABLE (a - G) HM HG ltac:(unfold SRC_TABLE, SRC_ENTRY in *; lia)).
    replace (G + (a - G)) with a by ring. exact Hin.
  - right. exact E.
  - exfalso. apply (gdr_blk_img L A m md q m' (a - q) HM Hq ltac:(lia)). replace (q + (a - q)) with a by ring. exact Hin.
Qed.

Lemma gdr_E_low : forall lv OUTd CAPd SA j bl L A m md a,
  MR L A m md -> (lv = true -> 0 < CAPd -> In (OUTd, CAPd) (blocks L A)) ->
  In (G, SRC_TABLE) (blocks L A) -> G <= SA -> SA + SRC_ENTRY <= G + SRC_TABLE -> (j < 4)%nat ->
  gdr_E lv OUTd CAPd SA j bl L A a -> a < alloc_ceiling.
Proof.
  intros lv OUTd CAPd SA j bl L A m md a HM HO HG H1 H2 Hj [E|[E|[E|(q & m' & _ & Hq & E)]]];
    pose proof alloc_ceiling_val as ACV.
  - destruct (gdr_sw_img lv OUTd CAPd a E) as [(_ & E')|(Elv & E')].
    + unfold G_BROKEN, G_EINTR, G_OUTV in E'. lia.
    + pose proof (rig_blk L A m md OUTd CAPd 0 HM (HO Elv ltac:(lia)) ltac:(lia)) as (_ & _ & X & _). lia.
  - pose proof (rig_blk L A m md G SRC_TABLE 0 HM HG ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)) as (_ & _ & X & _).
    unfold SRC_TABLE, SRC_ENTRY in *. lia.
  - unfold G_S, SRC_SIZE in *. lia.
  - pose proof (rig_blk L A m md q m' 0 HM Hq ltac:(lia)) as (_ & _ & X & _). lia.
Qed.

Lemma gdr_E_Eall : forall i lv OUTd CAPd SA bl L A m md a,
  (i < length es)%nat -> re_eof (nth i es no_entry) = 0 ->
  MR L A m md -> (lv = true -> 0 < CAPd -> In (OUTd, CAPd) (blocks L A)) ->
  In (G, SRC_TABLE) (blocks L A) -> G <= SA -> SA + SRC_ENTRY <= G + SRC_TABLE ->
  in_img Bm a -> gdr_E lv OUTd CAPd SA (snd (nth i hs no_hj)) bl L A a -> Eall a.
Proof.
  intros i lv OUTd CAPd SA bl L A m md a Hi He HM HO HG H1 H2 Hin X.
  unfold Eall.
  destruct (gdr_notE_img lv OUTd CAPd SA _ bl L A m md a HM HO HG H1 H2 Hin X) as [E|E].
  - left. unfold send_writes. destruct E as [E|[E|E]]; [left | right; left | right; right; left]; exact E.
  - right. right. right. left. exists (nth i es no_entry, nth i hs no_hj).
    split; [rewrite <- combine_nth by lia; apply nth_In; rewrite length_combine; lia|].
    split; [exact He | exact E].
Qed.

Lemma gdr_rp_kb2 : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k x,
  MR L1 A1 m1 md1 -> relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  In (q, k) (blocks L1 A1) -> ~ F' q -> 0 <= x < k -> ~ E' (q + x) -> kb2 m1 m2 (q + x).
Proof.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k x M1 RP Hin HF Hx HE.
  destruct RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  apply rig_blocks_in in Hin as (p & Ep & Hp). subst q.
  assert (H2 : In (p, k) (user_blocks A2)) by (apply SV2; [exact Hp | lia | exact HF]).
  pose proof (AD2 p k Hp H2 HF) as E2.
  split; [exact (BY2 p k x Hp H2 HF Hx HE)|].
  intros _. rewrite <- E2. apply rig_present_writable.
  exact (proj1 (mr_blocks Bm MR rig_laws L2 A2 m2 md2 p k x M2 H2 Hx)).
Qed.

Lemma gm_gbound_S : forall i, gbound (S i) = gbound i + (pl_of i + 6001 + 6005 * (re_nheld (nth i es no_entry) + pl_of i)).
Proof. intros i. unfold gbound. rewrite rig_fold_seq_S. reflexivity. Qed.

Lemma gm_pl_nn : forall j, 0 <= pl_of j.
Proof. intros j. unfold pl_of. destruct (re_eof (nth j es no_entry) =? 0); lia. Qed.

Lemma gm_gb_mono : forall i j, (i <= j)%nat -> gbound i <= gbound j.
Proof.
  intros i j Hij. induction Hij as [|j Hij IH]; [lia|].
  pose proof (gm_pl_nn j) as P.
  assert (N : 0 <= re_nheld (nth j es no_entry)) by (unfold re_nheld; lia).
  rewrite gm_gbound_S. lia.
Qed.

Lemma gm_pl_lt : forall j, (j < length es)%nat -> pl_of j < 2 ^ 26.
Proof.
  intros j Hj. unfold pl_of. destruct (Z.eqb_spec (re_eof (nth j es no_entry)) 0) as [E|E]; [|lia].
  destruct (gdr_gso j Hj E) as (_ & _ & _ & _ & _ & X & _). exact X.
Qed.

Lemma gm_nh_lt : forall j, (j < length es)%nat -> re_nheld (nth j es no_entry) < 2 ^ 26.
Proof.
  intros j Hj. pose proof (proj1 (Forall_forall _ _) EOK0 _ (nth_In es no_entry Hj)) as OK.
  destruct OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X.
Qed.

Lemma gm_gbound_lt : forall i, (i <= length es)%nat -> gbound i <= Z.of_nat i * 2 ^ 40.
Proof.
  induction i as [|i IH]; intros Hi; [unfold gbound; cbn; lia|].
  rewrite gm_gbound_S. pose proof (IH ltac:(lia)) as X.
  pose proof (gm_pl_lt i ltac:(lia)). pose proof (gm_pl_nn i). pose proof (gm_nh_lt i ltac:(lia)).
  assert (0 <= re_nheld (nth i es no_entry)) by (unfold re_nheld; lia). lia.
Qed.

Lemma gm_gNO_lt : 0 <= gNO < 2 ^ 47.
Proof.
  pose proof alloc_ceiling_val as ACV. pose proof (bv_unsigned_in_range 64 nout) as RN.
  change (bv_unsigned nout) with gNO in RN. assert (0 <= gNO) by lia.
  destruct HOUT0 as [(_ & _ & E & _)|(C0 & NC & B & _)]; [lia|].
  destruct PRE as (M0 & _).
  pose proof (rig_blk L0 A0 mem0 md0 gOUT gCAP 0 M0 B ltac:(lia)) as (_ & X1 & X2 & _). lia.
Qed.

(* gesture_end's premise 2 * (NO + LEN) < 2 ^ 63, from g_nout <= gNO + T and T + LEN within the run's bound. *)
Lemma gm_mg : forall NO T LEN, 0 <= NO <= gNO + T -> 0 <= LEN -> 0 <= T -> T + LEN <= gbound (length es) ->
  2 * (NO + LEN) < 2 ^ 63.
Proof.
  intros NO T LEN H1 H2 H3 H4. pose proof gm_gNO_lt. pose proof (gm_gbound_lt (length es) ltac:(lia)).
  pose proof NLE as N4. unfold gN in N4. lia.
Qed.

Lemma gm_fcur_mono : forall T T' q, 0 <= T -> 0 <= T' - T -> Fcur T q -> Fcur T' q.
Proof.
  intros T T' q H1 H2 [(HL & E)|X]; [left|right; exact X].
  split; [|exact E].
  destruct (rig_live_step cl br dd T (T' - T) Hcl Hbr Hdd H1 H2) as [Y _].
  replace T' with (T + (T' - T)) by ring. exact (proj2 (proj2 (Y HL))).
Qed.

Lemma gm_key_in : forall (l : list rentry) i n, (i < length l)%nat -> (n < length (re_keys (nth i l no_entry)))%nat ->
  In (key_addr (nth n (re_keys (nth i l no_entry)) rig_dk)) (concat (map entry_blocks l)).
Proof.
  intros l i n Hi Hn. apply in_concat. exists (entry_blocks (nth i l no_entry)).
  split; [apply in_map; apply nth_In; exact Hi|].
  unfold entry_blocks. apply in_or_app. right. apply in_or_app. right. apply in_map. apply nth_In. exact Hn.
Qed.

Lemma gm_nd3 : forall (a b q : Z) R, NoDup (a :: b :: R) -> In q R -> q <> a /\ q <> b.
Proof.
  intros a b q R ND Hq. apply gdr_nd in ND. apply List.NoDup_cons_iff in ND as [Na ND].
  apply List.NoDup_cons_iff in ND as [Nb _].
  split; intros ->; [apply Na; right | apply Nb]; exact Hq.
Qed.

Lemma gm_nd_ab : forall (a b : Z) R, NoDup (a :: b :: R) -> a <> b.
Proof.
  intros a b R ND. apply gdr_nd in ND. apply List.NoDup_cons_iff in ND as [Na _].
  intros ->. apply Na. left. reflexivity.
Qed.

Lemma gm_nd_out : forall (a b b' : Z) R, NoDup (a :: b :: R) -> b' <> a -> ~ In b' R -> NoDup (a :: b' :: R).
Proof.
  intros a b b' R ND N1 N2. apply gdr_nd in ND. apply gdr_nd.
  apply List.NoDup_cons_iff in ND as [Na ND]. apply List.NoDup_cons_iff in ND as [_ ND].
  constructor.
  - intros [E|E]; [exact (N1 E) | apply Na; right; exact E].
  - constructor; [exact N2 | exact ND].
Qed.

Lemma gm_in_srcblk : forall hs_c j q, length hs_c = length es -> (j < length es)%nat -> re_eof (nth j es no_entry) = 0 ->
  In q (hs_blocks (nth j hs_c (fst (nth j hs no_hj)))) -> In q (concat (map srcblk (combine es hs_c))).
Proof.
  intros hs_c j q HL Hj He Hq. apply in_concat.
  exists (srcblk (nth j es no_entry, nth j hs_c (fst (nth j hs no_hj)))). split.
  - apply in_map. rewrite <- combine_nth by lia. apply nth_In. rewrite length_combine. lia.
  - unfold srcblk. cbn [fst snd]. rewrite He. exact Hq.
Qed.

Lemma gm_R_pos : forall L A m es_c hs_c q, length hs_c = length es -> Forall (entry_okk L A m) es_c ->
  (forall j, (j < length es)%nat -> re_eof (nth j es no_entry) = 0 ->
     src_at Bm L A m (gHA j) (nth j hs_c (fst (nth j hs no_hj)))) ->
  In q (concat (map entry_blocks es_c) ++ concat (map srcblk (combine es hs_c))) ->
  exists k, In (q, k) (blocks L A) /\ 0 < k.
Proof.
  intros L A m es_c hs_c q HL HE HS Hq. apply in_app_or in Hq as [Hq|Hq].
  - apply in_concat in Hq as (l & Hl & Hq). apply in_map_iff in Hl as (e & <- & He).
    exact (gdr_eblk L A m e q (proj1 (Forall_forall _ _) HE e He) Hq).
  - apply in_concat in Hq as (l & Hl & Hq). apply in_map_iff in Hl as (p & <- & Hp).
    apply (In_nth _ _ (no_entry, fst no_hj)) in Hp as (j & Hj & Ep).
    rewrite length_combine in Hj. rewrite combine_nth in Ep by lia. subst p.
    unfold srcblk in Hq. cbn [fst snd] in Hq.
    destruct (re_eof (nth j es no_entry) =? 0) eqn:E0; [|destruct Hq].
    apply Z.eqb_eq in E0.
    pose proof (HS j ltac:(lia) E0) as S.
    rewrite (nth_indep hs_c (fst no_hj) (fst (nth j hs no_hj))) in Hq by lia.
    exact (gdr_hblk L A m _ _ q S Hq).
Qed.

Lemma gm_keep : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k,
  MR L1 A1 m1 md1 -> relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  In (q, k) (blocks L1 A1) -> (0 < k -> ~ F' q) -> In (q, k) (blocks L2 A2).
Proof.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k M1 RP Hin HF.
  destruct RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & _).
  apply rig_blocks_in in Hin as (p & Ep & Hp). subst q.
  pose proof (rig_ub_nonneg A1 p k (mr_wf Bm MR rig_laws L1 A1 m1 md1 M1) Hp) as Hk.
  destruct (Z.eq_dec k 0) as [->|Hk'].
  - destruct (Z2 p Hp) as [H2 E2]. apply rig_blocks_in. exists p. split; [exact E2 | exact H2].
  - assert (H2 : In (p, k) (user_blocks A2)) by (apply SV2; [exact Hp | lia | apply HF; lia]).
    apply rig_blocks_in. exists p. split; [exact (AD2 p k Hp H2 (HF ltac:(lia))) | exact H2].
Qed.

Lemma gm_sw_blk : forall lv O' C' L A m md q k x, MR L A m md -> In (q, k) (blocks L A) -> 0 <= x < k ->
  (0 < C' -> In (O', C') (blocks L A)) -> (lv = true -> q <> O') -> ~ send_writes lv O' C' (q + x).
Proof.
  intros lv O' C' L A m md q k x HM Hq Hx HO HN E.
  destruct (gdr_sw_img lv O' C' (q + x) E) as [(P & _)|(Elv & E')].
  - exact (gdr_blk_img L A m md q k x HM Hq Hx (proj1 P)).
  - destruct (rig_blk_disj L A m md q k O' C' HM Hq (HO ltac:(lia)) (HN Elv)); lia.
Qed.

Lemma gm_live_nz : forall T, send_live cl br dd T = true -> T <> 0.
Proof. intros T X E. subst T. unfold send_live, send_off in X. destruct (cl <? 0), (br =? 1); cbn in X; discriminate X. Qed.

Lemma gm_bzs_end5 : map bz END5 = END5Z.
Proof. reflexivity. Qed.

Definition gm_box (P : Prop) : Prop := P.
Ltac gm_hide H := let T := type of H in change (gm_box T) in H.

Lemma gdr_nth_eb : forall l i, nth i (map entry_blocks l) [] = entry_blocks (nth i l no_entry).
Proof.
  intros l i. destruct (Nat.lt_ge_cases i (length l)) as [Hl|Hl].
  - rewrite (nth_indep _ [] (entry_blocks no_entry)) by (rewrite length_map; exact Hl). apply map_nth.
  - rewrite !nth_overflow by (rewrite ?length_map; exact Hl). reflexivity.
Qed.

Lemma gdr_nth_sb : forall hs_c j, length hs_c = length es -> (j < length es)%nat ->
  nth j (map srcblk (combine es hs_c)) [] = srcblk (nth j es no_entry, nth j hs_c (fst no_hj)).
Proof.
  intros hs_c j HL Hj.
  rewrite (nth_indep _ [] (srcblk (no_entry, fst no_hj))) by (rewrite length_map, length_combine; lia).
  rewrite map_nth. rewrite combine_nth by lia. reflexivity.
Qed.

Lemma gdr_sb0 : forall e h, re_eof e = 0 -> srcblk (e, h) = hs_blocks h.
Proof. intros e h E. unfold srcblk. cbn [fst snd]. rewrite E. reflexivity. Qed.

Lemma gdr_el0 : forall e hj, re_eof e = 0 ->
  entry_lines e hj = lines (hs_state (fst hj)) (bzs (pending_stream (fst hj))).
Proof. intros e hj E. unfold entry_lines. rewrite E. reflexivity. Qed.

Lemma gdr_forall_rep : forall {X} (P : X -> Prop) (l : list X) i y d, (i < length l)%nat -> P y ->
  (forall j, (j < length l)%nat -> j <> i -> P (nth j l d)) -> Forall P (firstn i l ++ y :: skipn (S i) l).
Proof.
  intros X P l i y d Hi Py HP. apply Forall_forall. intros x Hx.
  apply (In_nth _ _ d) in Hx as (j & Hj & <-). rewrite gdr_len_rep in Hj by exact Hi.
  rewrite gdr_nth_rep by exact Hi. destruct (Nat.eqb_spec j i) as [->|Ne]; [exact Py | exact (HP j Hj Ne)].
Qed.

Lemma gdr_oth : forall m j (h : hsrc) r1, (j < 4)%nat ->
  (forall i', (i' < 4)%nat ->
     rw_cells segs m (G_S + SRC_SIZE * Z.of_nat i') [C4 (Z_to_bv 64 (nth i' fs 0)); C4 (Z_to_bv 64 (nth i' os 0))]) ->
  rw_cells segs m (G_S + SRC_SIZE * Z.of_nat j) (C4 (Z_to_bv 64 (hs_fd h)) :: C4 (Z_to_bv 64 (hs_open h)) :: r1) ->
  hs_open h = 1 -> 0 <= hs_fd h < 2 ^ 31 -> others_at Bm m j (hs_fd h) fs os.
Proof.
  intros m j h r1 Hj HS HH Ho Hf.
  destruct (gdr_c44_uniq m _ _ _ _ _ [] r1 (HS j Hj) HH) as [U1 U2].
  destruct (SRCR j Hj) as [Oj Fj].
  rewrite Ho in U2. rewrite !Z.mod_small in U1 by lia.
  assert (Ej : nth j os 0 = 1) by (rewrite !Z.mod_small in U2 by (destruct Oj; lia); exact U2).
  split; [exact LFS|]. split; [exact LOS|].
  intros i' Hi' Ne. split; [exact (HS i' Hi')|].
  destruct (SRCR i' Hi') as [[O0|O1] F']; (split; [|exact F']); [left; exact O0|right].
  pose proof (SRCD j i' Hj Hi' (fun E => Ne (eq_sym E)) Ej O1). lia.
Qed.

Lemma gdr_tot : forall L A m HA h, src_at Bm L A m HA h ->
  Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h))))) <=
  Z.of_nat (length (pending_stream h)) + 6000.
Proof.
  intros L A m HA h S. pose proof (rig_with_nul_len (hs_state h) (bzs (pending_stream h))) as X.
  destruct S as (_ & _ & _ & _ & _ & _ & _ & _ & (N0 & N1) & _).
  assert (W : Z.of_nat (length (ls_w (hs_state h))) <= 6000).
  { unfold hs_state. cbn [ls_w]. rewrite gdr_len_bzs. unfold hs_W.
    pose proof (firstn_le_length (Z.to_nat (hs_npartial h)) (hs_pjunk h)) as F.
    apply Nat2Z.inj_le in F. rewrite Z2Nat.id in F by exact N0. lia. }
  rewrite gdr_len_bzs in X. apply Nat2Z.inj_le in X. rewrite Nat2Z.inj_add in X. lia.
Qed.

Lemma gdr_wk_init : forall NO CAP e ks h, keys_texts ks = keys_texts (re_keys e) ->
  drain_init NO CAP (with_keys e ks) h = drain_init NO CAP e h.
Proof. intros NO CAP e ks h E. unfold drain_init, ent_ka. cbn [with_keys re_cap re_U re_skip re_keys re_hp re_kh]. rewrite E. reflexivity. Qed.

Lemma gdr_wk_tr : forall lv m0 NO CAP e ks h j a, keys_texts ks = keys_texts (re_keys e) ->
  drain_tr lv m0 NO CAP (with_keys e ks) h j a = drain_tr lv m0 NO CAP e h j a.
Proof. intros lv m0 NO CAP e ks h j a E. unfold drain_tr, drain_go. rewrite gdr_wk_init by exact E. reflexivity. Qed.

Lemma gdr_wk_fin : forall lv m0 NO CAP e ks h, keys_texts ks = keys_texts (re_keys e) ->
  drain_fin lv m0 NO CAP (with_keys e ks) h = drain_fin lv m0 NO CAP e h.
Proof. intros lv m0 NO CAP e ks h E. unfold drain_fin, drain_go. rewrite gdr_wk_init by exact E. reflexivity. Qed.

Lemma gdr_wk_adr : forall lv m0 NO CAP e ks h j a, keys_texts ks = keys_texts (re_keys e) ->
  drain_adr lv m0 NO CAP (with_keys e ks) h j a = drain_adr lv m0 NO CAP e h j a.
Proof. intros lv m0 NO CAP e ks h j a E. unfold drain_adr, drain_go. rewrite gdr_wk_init by exact E. reflexivity. Qed.

Lemma gdr_sn : forall a b, set_no 0 a = set_no 0 b ->
  ds_cap a = ds_cap b /\ ds_u a = ds_u b /\ ds_skip a = ds_skip b /\ ds_H a = ds_H b /\ ds_ka a = ds_ka b /\
  ds_ecap a = ds_ecap b.
Proof.
  intros a b E. split; [exact (f_equal ds_cap E)|]. split; [exact (f_equal ds_u E)|].
  split; [exact (f_equal ds_skip E)|]. split; [exact (f_equal ds_H E)|]. split; [exact (f_equal ds_ka E)|].
  exact (f_equal ds_ecap E).
Qed.

(* drain's call with its own liveness lvd, g_nout NOa and g_capout capm against the model's step from nom, capm. *)
Lemma gdr_bridge : forall lvd NOa nom capm e h TOT,
  dr_inv (drain_init nom capm e h) -> dr_rest (drain_init nom capm e h) = bzs (pending_stream h) ->
  TOT = Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h))))) ->
  (0 < TOT -> lvd = glv) -> (TOT = 0 -> lvd = false) -> (glv = true -> NOa = nom) ->
  (forall j a, drain_tr lvd (bv_unsigned mx) NOa capm e h j a = drain_tr glv (bv_unsigned mx) nom capm e h j a /\
               drain_adr lvd (bv_unsigned mx) NOa capm e h j a = drain_adr glv (bv_unsigned mx) nom capm e h j a) /\
  set_no 0 (drain_fin lvd (bv_unsigned mx) NOa capm e h) = set_no 0 (drain_fin glv (bv_unsigned mx) nom capm e h) /\
  ds_no (drain_fin glv (bv_unsigned mx) nom capm e h) = nom + TOT /\
  (lvd = true -> ds_ocap (drain_fin lvd (bv_unsigned mx) NOa capm e h) = ds_ocap (drain_fin glv (bv_unsigned mx) nom capm e h)) /\
  (lvd = false -> ds_ocap (drain_fin glv (bv_unsigned mx) nom capm e h) = capm).
Proof.
  intros lvd NOa nom capm e h TOT IV ER ET LP LZ LN.
  assert (TN : 0 <= TOT) by (rewrite ET; lia).
  assert (FA : forall j a,
             drain_tr false (bv_unsigned mx) NOa capm e h j a = drain_tr false (bv_unsigned mx) nom capm e h j a /\
             drain_adr false (bv_unsigned mx) NOa capm e h j a = drain_adr false (bv_unsigned mx) nom capm e h j a).
  { intros j a. destruct (rig_drain_false (bv_unsigned mx) nom NOa capm e h j a) as (F1 & _ & F3 & _).
    split; assumption. }
  pose proof (rig_drain_false (bv_unsigned mx) nom NOa capm e h 0 dadr0) as (_ & F2 & _ & F4).
  revert LP LN. destruct glv; intros LP LN.
  - pose proof (rig_drain_model true (bv_unsigned mx) nom capm e h IV ER) as [M1 M2].
    rewrite <- ET in M1.
    destruct (Z.eq_dec TOT 0) as [T0|TP].
    + rewrite (LZ T0), (LN eq_refl).
      assert (LS : lines (hs_state h) (bzs (pending_stream h)) = []) by (apply rig_wn_nil; lia).
      pose proof (M2 LS false) as EG.
      split; [intros j a; unfold drain_tr, drain_adr; rewrite (EG j a); split; reflexivity|].
      assert (EF : drain_fin false (bv_unsigned mx) nom capm e h = drain_fin true (bv_unsigned mx) nom capm e h)
        by (unfold drain_fin; rewrite (EG 0%nat dadr0); reflexivity).
      split; [rewrite EF; reflexivity|]. split; [exact M1|].
      split; [intros X; discriminate X|]. intros _. rewrite <- EF.
      exact (proj2 (proj2 (proj2 (rig_drain_false (bv_unsigned mx) nom nom capm e h 0 dadr0)))).
    + rewrite (LP ltac:(lia)), (LN eq_refl).
      split; [intros j a; split; reflexivity|]. split; [reflexivity|]. split; [exact M1|].
      split; [intros _; reflexivity | intros X; discriminate X].
  - pose proof (rig_drain_model false (bv_unsigned mx) nom capm e h IV ER) as [M1 _].
    rewrite <- ET in M1.
    assert (LF : lvd = false) by (destruct (Z.eq_dec TOT 0) as [T0|TP]; [exact (LZ T0) | exact (LP ltac:(lia))]).
    rewrite LF. split; [exact FA|]. split; [exact F2|]. split; [exact M1|].
    split; [intros X; discriminate X | intros _; exact F4].
Qed.

Lemma gdr_in_rep2 : forall (Xs Xs' : list (list Z)) i x, length Xs' = length Xs ->
  (forall j, (j < length Xs)%nat -> j <> i -> nth j Xs' [] = nth j Xs []) ->
  In x (concat Xs) -> ~ In x (nth i Xs []) -> In x (concat Xs').
Proof.
  intros Xs Xs' i x HL HE Hx Hn. apply in_concat in Hx as (l0 & Hl0 & Hx).
  destruct (In_nth Xs l0 [] Hl0) as (j & Hj & Ej).
  destruct (Nat.eq_dec j i) as [->|Ne]; [subst l0; contradiction|].
  apply in_concat. exists l0. split; [|exact Hx]. rewrite <- Ej, <- (HE j Hj Ne). apply nth_In. lia.
Qed.

(* Lane p3g: drain's run inside gone's numbering (base j + k, gone's addresses, list qs) against its own run (base k,
   its addresses, list qc): same resource state, room and returns, and output addresses that resolve alike. *)
Local Abbreviation gd_rn qs b j t := (run_from (rt_R RF) sptr (SP 0 0) (rt_malloc RF) (rt_free RF) (rt_realloc RF) qs b j t).
Local Abbreviation gd_rm qs b j t :=
  (room_from (rt_R RF) sptr (SP 0 0) (rt_malloc RF) (rt_free RF) (rt_realloc RF) (rt_room RF) qs b j t).

Definition gd_R (qs qc : list sptr) (a a' : adrF) : Prop := resolveF qs a = resolveF qc a'.

Lemma gd_f2_nth : forall {X Y : Type} (R : X -> Y -> Prop) l l' d d' n, Forall2 R l l' -> R d d' ->
  R (nth n l d) (nth n l' d').
Proof.
  intros X Y R l l' d d' n F Rd. revert n. induction F as [|x y l l' Rxy F IH]; intros [|n]; cbn [nth]; auto.
Qed.

Lemma gd_f2_last : forall {X Y : Type} (R : X -> Y -> Prop) l l' d d', Forall2 R l l' -> R d d' ->
  R (last l d) (last l' d').
Proof.
  intros X Y R l l' d d' F Rd. induction F as [|x y l l' Rxy F IH]; [exact Rd|].
  revert IH. destruct F; intros IH; [exact Rxy | exact IH].
Qed.

Lemma gd_f2_set : forall {X Y : Type} (R : X -> Y -> Prop) n l l' y y', Forall2 R l l' -> R y y' ->
  Forall2 R (set_nth n y l) (set_nth n y' l').
Proof.
  intros X Y R n l l' y y' F Ry. revert n. induction F as [|x x' l l' Rx F IH]; intros [|n]; cbn [set_nth];
    constructor; auto.
Qed.

Lemma gd_f2_firstn : forall {X Y : Type} (R : X -> Y -> Prop) n l l', Forall2 R l l' ->
  Forall2 R (firstn n l) (firstn n l').
Proof.
  intros X Y R n l l' F. revert n. induction F as [|x x' l l' Rx F IH]; intros [|n]; cbn [firstn]; constructor; auto.
Qed.

Lemma gd_f2_skipn : forall {X Y : Type} (R : X -> Y -> Prop) n l l', Forall2 R l l' ->
  Forall2 R (skipn n l) (skipn n l').
Proof.
  intros X Y R n l l' F. revert n. induction F as [|x x' l l' Rx F IH]; intros [|n]; cbn [skipn].
  - constructor.
  - constructor.
  - constructor; [exact Rx | exact F].
  - exact (IH n).
Qed.

Lemma gd_f2_swap : forall {X Y : Type} (R : X -> Y -> Prop) d d' n l l', Forall2 R l l' -> R d d' ->
  Forall2 R (swap_remove d n l) (swap_remove d' n l').
Proof.
  intros X Y R d d' n l l' F Rd. unfold swap_remove. rewrite (Forall2_length F).
  apply gd_f2_firstn, gd_f2_set; [exact F | exact (gd_f2_last R l l' d d' F Rd)].
Qed.

Lemma gd_grow_sim : forall cap used (qs qc : list sptr) (j k : nat) (b b' : adrF) (bb : rt_R RF),
  (forall i, (k <= i < k + nretF (fst (grow_tr cap used k b')))%nat -> nth (j + i) qs (SP 0 0) = nth i qc (SP 0 0)) ->
  (cap <> 0 -> gd_R qs qc b b') ->
  gd_rn qs bb (j + k) (fst (grow_tr cap used (j + k) b)) = gd_rn qc bb k (fst (grow_tr cap used k b')) /\
  (gd_rm qs bb (j + k) (fst (grow_tr cap used (j + k) b)) <-> gd_rm qc bb k (fst (grow_tr cap used k b'))) /\
  nretF (fst (grow_tr cap used (j + k) b)) = nretF (fst (grow_tr cap used k b')) /\
  (fst (snd (grow_tr cap used k b')) <> 0 ->
     gd_R qs qc (snd (snd (grow_tr cap used (j + k) b))) (snd (snd (grow_tr cap used k b')))).
Proof.
  intros cp used qs qc j k b b' bb. unfold grow_tr. cbv zeta.
  destruct (cp - used <? 4096); [destruct (cp =? 0) eqn:Ec|]; intros HN HR; cbn [fst snd run_from room_from] in HN |- *.
  - assert (HK : nth (j + k) qs (SP 0 0) = nth k qc (SP 0 0)) by (apply HN; cbn; lia).
    split; [reflexivity|]. split; [tauto|]. split; [reflexivity|]. intros _. exact HK.
  - assert (HK : nth (j + k) qs (SP 0 0) = nth k qc (SP 0 0)) by (apply HN; cbn; lia).
    pose proof (HR (proj1 (Z.eqb_neq _ _) Ec)) as X. unfold gd_R in X. rewrite HK, X.
    split; [reflexivity|]. split; [tauto|]. split; [reflexivity|]. intros _. exact HK.
  - split; [reflexivity|]. split; [tauto|]. split; [reflexivity|]. exact HR.
Qed.

Lemma gd_seen_sim : forall H ka l (qs qc : list sptr) (j k : nat) (ha ha' : adrF) (ks ks' : list adrF) (bb : rt_R RF),
  (forall i, (k <= i < k + nretF (fst (fst (seen_tr H ka l k ha' ks'))))%nat ->
     nth (j + i) qs (SP 0 0) = nth i qc (SP 0 0)) ->
  (ka <> 0 -> gd_R qs qc ha ha') -> Forall2 (gd_R qs qc) ks ks' ->
  gd_rn qs bb (j + k) (fst (fst (seen_tr H ka l (j + k) ha ks))) = gd_rn qc bb k (fst (fst (seen_tr H ka l k ha' ks'))) /\
  (gd_rm qs bb (j + k) (fst (fst (seen_tr H ka l (j + k) ha ks))) <->
     gd_rm qc bb k (fst (fst (seen_tr H ka l k ha' ks')))) /\
  nretF (fst (fst (seen_tr H ka l (j + k) ha ks))) = nretF (fst (fst (seen_tr H ka l k ha' ks'))) /\
  (snd (fst (seen_tr H ka l k ha' ks')) <> 0 ->
     gd_R qs qc (fst (snd (seen_tr H ka l (j + k) ha ks))) (fst (snd (seen_tr H ka l k ha' ks')))) /\
  Forall2 (gd_R qs qc) (snd (snd (seen_tr H ka l (j + k) ha ks))) (snd (snd (seen_tr H ka l k ha' ks'))).
Proof.
  intros H ka l qs qc j k ha ha' ks ks' bb. unfold seen_tr. cbv zeta.
  destruct (gesture l) as [[[|] x]|]; [destruct (index_of x H) as [n|] .. |]; intros HN HR HF;
    cbn [fst snd run_from room_from] in HN |- *.
  - split; [reflexivity|]. split; [tauto|]. split; [reflexivity|]. split; [exact HR | exact HF].
  - assert (HK0 : nth (j + k) qs (SP 0 0) = nth k qc (SP 0 0)) by (apply HN; destruct (ka =? 0); cbn; lia).
    assert (HK1 : nth (j + S k) qs (SP 0 0) = nth (S k) qc (SP 0 0)) by (apply HN; destruct (ka =? 0); cbn; lia).
    assert (HF' : Forall2 (gd_R qs qc) (ks ++ [Ret (S (j + k))]) (ks' ++ [Ret (S k)])).
    { apply Forall2_app; [exact HF|]. constructor; [|constructor].
      unfold gd_R. cbn [resolve]. replace (S (j + k)) with (j + S k)%nat by lia. exact HK1. }
    destruct (ka =? 0) eqn:Ek; cbn [run_from room_from].
    + split; [reflexivity|]. split; [tauto|]. split; [reflexivity|]. split; [intros _; exact HK0 | exact HF'].
    + pose proof (HR (proj1 (Z.eqb_neq _ _) Ek)) as X. unfold gd_R in X. rewrite HK0, X.
      split; [reflexivity|]. split; [tauto|]. split; [reflexivity|]. split; [intros _; exact HK0 | exact HF'].
  - pose proof (gd_f2_nth (gd_R qs qc) ks ks' adr0 adr0 n HF ltac:(unfold gd_R; reflexivity)) as X.
    unfold gd_R in X. rewrite X.
    split; [reflexivity|]. split; [tauto|]. split; [reflexivity|]. split; [exact HR|].
    exact (gd_f2_swap (gd_R qs qc) adr0 adr0 n ks ks' HF ltac:(unfold gd_R; reflexivity)).
  - split; [reflexivity|]. split; [tauto|]. split; [reflexivity|]. split; [exact HR | exact HF].
  - split; [reflexivity|]. split; [tauto|]. split; [reflexivity|]. split; [exact HR | exact HF].
Qed.

Lemma gd_lpush_nret : forall (v : adrF) n cap len, nretF (list_push_tra v n cap len) = S (if n =? cap then 1 else 0).
Proof. intros v n cp len. unfold list_push_tra. destruct (n =? cp); [destruct (cp =? 0)|]; reflexivity. Qed.

Lemma gd_lpush_sim : forall (v v' : adrF) n cap len (qs qc : list sptr) (j k : nat) (bb : rt_R RF),
  (forall i, (k <= i < k + nretF (list_push_tra v' n cap len))%nat -> nth (j + i) qs (SP 0 0) = nth i qc (SP 0 0)) ->
  (cap <> 0 -> gd_R qs qc v v') ->
  gd_rn qs bb (j + k) (list_push_tra v n cap len) = gd_rn qc bb k (list_push_tra v' n cap len) /\
  (gd_rm qs bb (j + k) (list_push_tra v n cap len) <-> gd_rm qc bb k (list_push_tra v' n cap len)) /\
  nretF (list_push_tra v n cap len) = nretF (list_push_tra v' n cap len).
Proof.
  intros v v' n cp len qs qc j k bb. unfold list_push_tra.
  destruct (n =? cp); [destruct (cp =? 0) eqn:Ec|]; intros HN HR; cbn [app run_from room_from] in HN |- *.
  - split; [reflexivity|]. split; [tauto | reflexivity].
  - assert (HK : nth (j + k) qs (SP 0 0) = nth k qc (SP 0 0)) by (apply HN; cbn; lia).
    pose proof (HR (proj1 (Z.eqb_neq _ _) Ec)) as X. unfold gd_R in X. rewrite HK, X.
    split; [reflexivity|]. split; [tauto | reflexivity].
  - split; [reflexivity|]. split; [tauto | reflexivity].
Qed.

Lemma gd_push_sim : forall ls n cap (qs qc : list sptr) (j k : nat) (v v' : adrF) (rs rs' : list adrF) (bb : rt_R RF),
  (forall i, (k <= i < k + nretF (fst (fst (pushes_run n cap ls k v' rs'))))%nat ->
     nth (j + i) qs (SP 0 0) = nth i qc (SP 0 0)) ->
  (cap <> 0 -> gd_R qs qc v v') -> Forall2 (gd_R qs qc) rs rs' ->
  gd_rn qs bb (j + k) (fst (fst (pushes_run n cap ls (j + k) v rs))) =
    gd_rn qc bb k (fst (fst (pushes_run n cap ls k v' rs'))) /\
  (gd_rm qs bb (j + k) (fst (fst (pushes_run n cap ls (j + k) v rs))) <->
     gd_rm qc bb k (fst (fst (pushes_run n cap ls k v' rs')))) /\
  nretF (fst (fst (pushes_run n cap ls (j + k) v rs))) = nretF (fst (fst (pushes_run n cap ls k v' rs'))) /\
  (snd (fst (pushes_run n cap ls k v' rs')) <> 0 ->
     gd_R qs qc (fst (snd (pushes_run n cap ls (j + k) v rs))) (fst (snd (pushes_run n cap ls k v' rs')))) /\
  Forall2 (gd_R qs qc) (snd (snd (pushes_run n cap ls (j + k) v rs))) (snd (snd (pushes_run n cap ls k v' rs'))).
Proof.
  induction ls as [|l r IH]; intros n cp qs qc j k v v' rs rs' bb HN HR HF; cbn [pushes_run fst snd] in HN |- *;
    cbv zeta in HN |- *.
  - split; [reflexivity|]. split; [tauto|]. split; [reflexivity|]. split; [exact HR | exact HF].
  - rewrite nret_app in HN. rewrite !run_from_app, !room_from_app, !nret_app.
    pose proof (gd_lpush_nret v' n cp (Z.of_nat (length l))) as NP.
    destruct (gd_lpush_sim v v' n cp (Z.of_nat (length l)) qs qc j k bb) as (T1 & T2 & T3);
      [intros i Hi; apply HN; lia | exact HR |].
    rewrite T1, T3.
    rewrite <- (Nat.add_assoc j k (nretF (list_push_tra v' n cp (Z.of_nat (length l))))).
    set (m := nretF (list_push_tra v' n cp (Z.of_nat (length l)))) in *.
    assert (HKk : nth (j + k) qs (SP 0 0) = nth k qc (SP 0 0)) by (apply HN; lia).
    assert (HKp : nth (j + Nat.pred (k + m)) qs (SP 0 0) = nth (Nat.pred (k + m)) qc (SP 0 0)) by (apply HN; lia).
    destruct (IH (n + 1) (push_cap n cp) qs qc j (k + m)%nat (if n =? cp then Ret (j + k) else v)
                (if n =? cp then Ret k else v') (rs ++ [Ret (Nat.pred (j + (k + m)))]) (rs' ++ [Ret (Nat.pred (k + m))])
                (gd_rn qc bb k (list_push_tra v' n cp (Z.of_nat (length l)))))
      as (S1 & S2 & S3 & S4 & S5).
    + intros i Hi. apply HN. lia.
    + intros Hc. unfold push_cap in Hc. revert Hc. destruct (n =? cp); intros Hc; [exact HKk | exact (HR Hc)].
    + apply Forall2_app; [exact HF|]. constructor; [|constructor].
      unfold gd_R. cbn [resolve]. replace (Nat.pred (j + (k + m))) with (j + Nat.pred (k + m))%nat by lia. exact HKp.
    + split; [exact S1|]. split; [clear - T2 S2; tauto|]. split; [rewrite S3; reflexivity|].
      split; [exact S4 | exact S5].
Qed.

Lemma gd_lines_sim : forall ls live mx no cap H ka (qs qc : list sptr) (j k : nat) (o o' ha ha' : adrF)
    (ks ks' : list adrF) (bb : rt_R RF),
  (forall i, (k <= i < k + nretF (fst (fst (lines_run live mx no cap H ka ls k o' ha' ks'))))%nat ->
     nth (j + i) qs (SP 0 0) = nth i qc (SP 0 0)) ->
  (cap <> 0 -> gd_R qs qc o o') -> (ka <> 0 -> gd_R qs qc ha ha') -> Forall2 (gd_R qs qc) ks ks' ->
  gd_rn qs bb (j + k) (fst (fst (lines_run live mx no cap H ka ls (j + k) o ha ks))) =
    gd_rn qc bb k (fst (fst (lines_run live mx no cap H ka ls k o' ha' ks'))) /\
  (gd_rm qs bb (j + k) (fst (fst (lines_run live mx no cap H ka ls (j + k) o ha ks))) <->
     gd_rm qc bb k (fst (fst (lines_run live mx no cap H ka ls k o' ha' ks')))) /\
  nretF (fst (fst (lines_run live mx no cap H ka ls (j + k) o ha ks))) =
    nretF (fst (fst (lines_run live mx no cap H ka ls k o' ha' ks'))) /\
  (fst (fst (snd (fst (lines_run live mx no cap H ka ls k o' ha' ks')))) <> 0 ->
     gd_R qs qc (fst (fst (snd (lines_run live mx no cap H ka ls (j + k) o ha ks))))
       (fst (fst (snd (lines_run live mx no cap H ka ls k o' ha' ks'))))) /\
  (snd (snd (fst (lines_run live mx no cap H ka ls k o' ha' ks'))) <> 0 ->
     gd_R qs qc (snd (fst (snd (lines_run live mx no cap H ka ls (j + k) o ha ks))))
       (snd (fst (snd (lines_run live mx no cap H ka ls k o' ha' ks'))))) /\
  Forall2 (gd_R qs qc) (snd (snd (lines_run live mx no cap H ka ls (j + k) o ha ks)))
    (snd (snd (lines_run live mx no cap H ka ls k o' ha' ks'))).
Proof.
  induction ls as [|l r IH]; intros live mxx no cp H ka qs qc j k o o' ha ha' ks ks' bb HN HO HH HF;
    cbn [lines_run fst snd] in HN |- *; cbv zeta in HN |- *.
  - split; [reflexivity|]. split; [tauto|]. split; [reflexivity|]. split; [exact HO|]. split; [exact HH | exact HF].
  - rewrite !nret_app in HN. rewrite !run_from_app, !room_from_app, !nret_app.
    pose proof (CF.gestures_end_b.p3b_snd_shape live mxx no cp (Z.of_nat (length l) + 1) (j + k) o k o') as E1.
    destruct (CF.gestures_end_b.p3b_snd_sim RF live mxx no cp (Z.of_nat (length l) + 1) qs qc j k o o' bb)
      as (A1 & A2 & A3); [intros i Hi; apply HN; lia | exact HO |].
    rewrite A1, E1.
    rewrite <- (Nat.add_assoc j k (nretF (send_line_tr live mxx no cp (Z.of_nat (length l) + 1) k o'))).
    set (m1 := nretF (send_line_tr live mxx no cp (Z.of_nat (length l) + 1) k o')) in *.
    destruct (gd_seen_sim H ka l qs qc j (k + m1) ha ha' ks ks'
                (gd_rn qc bb k (send_line_tr live mxx no cp (Z.of_nat (length l) + 1) k o')))
      as (B1 & B2 & B3 & B4 & B5); [intros i Hi; apply HN; lia | exact HH | exact HF |].
    rewrite B1, B3, (proj1 (gsh_seen H ka l (j + (k + m1)) ha ks (k + m1) ha' ks')).
    rewrite <- (Nat.add_assoc j (k + m1) (nretF (fst (fst (seen_tr H ka l (k + m1) ha' ks'))))).
    set (m2 := nretF (fst (fst (seen_tr H ka l (k + m1) ha' ks')))) in *.
    destruct (IH live mxx (no + (Z.of_nat (length l) + 1)) (send_line_cap live mxx no cp (Z.of_nat (length l) + 1))
                (seen_arr H l) (snd (fst (seen_tr H ka l (k + m1) ha' ks'))) qs qc j (k + m1 + m2)%nat
                (send_line_out live mxx no cp (Z.of_nat (length l) + 1) (j + k) o)
                (send_line_out live mxx no cp (Z.of_nat (length l) + 1) k o')
                (fst (snd (seen_tr H ka l (j + (k + m1)) ha ks))) (fst (snd (seen_tr H ka l (k + m1) ha' ks')))
                (snd (snd (seen_tr H ka l (j + (k + m1)) ha ks))) (snd (snd (seen_tr H ka l (k + m1) ha' ks')))
                (gd_rn qc (gd_rn qc bb k (send_line_tr live mxx no cp (Z.of_nat (length l) + 1) k o')) (k + m1)
                   (fst (fst (seen_tr H ka l (k + m1) ha' ks')))))
      as (S1 & S2 & S3 & S4 & S5 & S6); [intros i Hi; apply HN; lia | exact A3 | exact B4 | exact B5 |].
    split; [exact S1|]. split; [clear - A2 B2 S2; tauto|]. split; [rewrite S3; reflexivity|].
    split; [exact S4|]. split; [exact S5 | exact S6].
Qed.

Definition gd_dsim (qs qc : list sptr) (s : dstate) (a a' : dadr) : Prop :=
  (ds_ocap s <> 0 -> gd_R qs qc (da_out a) (da_out a')) /\
  (ds_cap s <> 0 -> gd_R qs qc (da_buf a) (da_buf a')) /\
  (ds_ka s <> 0 -> gd_R qs qc (da_hp a) (da_hp a')) /\
  Forall2 (gd_R qs qc) (da_keys a) (da_keys a') /\ Forall2 (gd_R qs qc) (da_pend a) (da_pend a') /\
  (ds_ecap s <> 0 -> gd_R qs qc (da_ev a) (da_ev a')) /\ Forall2 (gd_R qs qc) (da_erecs a) (da_erecs a').

Lemma gd_td0 : forall (w : bool) (p : adrF) n, nretF (if w then list_drop_tra p n else []) = 0%nat.
Proof. intros [|] p n; reflexivity. Qed.

Lemma gd_td_sim : forall (w : bool) (p p' : adrF) n (qs qc : list sptr) (J J' : nat) (bb : rt_R RF),
  gd_R qs qc p p' ->
  gd_rn qs bb J (if w then list_drop_tra p n else []) = gd_rn qc bb J' (if w then list_drop_tra p' n else []) /\
  (gd_rm qs bb J (if w then list_drop_tra p n else []) <-> gd_rm qc bb J' (if w then list_drop_tra p' n else [])).
Proof.
  intros [|] p p' n qs qc J J' bb HP; unfold list_drop_tra; cbn [run_from room_from].
  - unfold gd_R in HP. rewrite HP. split; [reflexivity | tauto].
  - split; [reflexivity | tauto].
Qed.

Lemma gd_drain_sim : forall f live mx (qs qc : list sptr) (j : nat) s k a a' (bb : rt_R RF),
  (forall i, (k <= i < k + nretF (fst (drain_run f live mx s k a')))%nat -> nth (j + i) qs (SP 0 0) = nth i qc (SP 0 0)) ->
  gd_dsim qs qc s a a' ->
  gd_rn qs bb (j + k) (fst (drain_run f live mx s (j + k) a)) = gd_rn qc bb k (fst (drain_run f live mx s k a')) /\
  (gd_rm qs bb (j + k) (fst (drain_run f live mx s (j + k) a)) <-> gd_rm qc bb k (fst (drain_run f live mx s k a'))) /\
  nretF (fst (drain_run f live mx s (j + k) a)) = nretF (fst (drain_run f live mx s k a')) /\
  gd_dsim qs qc (fst (snd (drain_run f live mx s k a'))) (snd (snd (drain_run f live mx s (j + k) a)))
    (snd (snd (drain_run f live mx s k a'))).
Proof.
  induction f as [|f IH]; intros live mxx qs qc j s k a a' bb.
  { intros HN HD. cbn [drain_run fst snd run_from room_from]. split; [reflexivity|]. split; [tauto|].
    split; [reflexivity | exact HD]. }
  destruct s as [c u sk H ka ei0 pd off rf en ec no oc].
  cbn [drain_run ds_cap ds_u ds_skip ds_H ds_ka ds_eintr ds_pend ds_off ds_ref ds_en ds_ecap ds_no ds_ocap
       da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
  cbv zeta.
  rewrite (gsh_grow c (Z.of_nat (length u)) (j + k) (da_buf a) k (da_buf a')).
  destruct ei0; [| destruct pd as [|r0 rs]; [| match goal with |- context [Z.min ?x ?y <=? 0] =>
                                                 destruct (Z.min x y <=? 0) end]];
    cbn [fst snd].
  - (* EINTR round *)
    intros HN HD. destruct HD as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
    cbn [ds_cap ds_ka ds_ecap ds_ocap] in D1, D2, D3, D6.
    rewrite !nret_app in HN. rewrite !run_from_app, !room_from_app, !nret_app.
    destruct (gd_grow_sim c (Z.of_nat (length u)) qs qc j k (da_buf a) (da_buf a') bb) as (G1 & G2 & G3 & G4);
      [intros i Hi; apply HN; lia | exact D2 |].
    rewrite G1, G3.
    rewrite <- (Nat.add_assoc j k (nretF (fst (grow_tr c (Z.of_nat (length u)) k (da_buf a'))))).
    set (m0 := nretF (fst (grow_tr c (Z.of_nat (length u)) k (da_buf a')))) in *.
    destruct (IH live mxx qs qc j
                (DS (fst (snd (grow_tr c (Z.of_nat (length u)) k (da_buf a')))) u sk H ka false pd off rf en ec no oc)
                (k + m0)%nat
                (DA (da_out a) (snd (snd (grow_tr c (Z.of_nat (length u)) (j + k) (da_buf a)))) (da_hp a) (da_keys a)
                    (da_pend a) (da_ev a) (da_erecs a))
                (DA (da_out a') (snd (snd (grow_tr c (Z.of_nat (length u)) k (da_buf a')))) (da_hp a') (da_keys a')
                    (da_pend a') (da_ev a') (da_erecs a'))
                (gd_rn qc bb k (fst (grow_tr c (Z.of_nat (length u)) k (da_buf a')))))
      as (S1 & S2 & S3 & S4).
    + intros i Hi. apply HN. lia.
    + unfold gd_dsim. cbn [ds_cap ds_ka ds_ecap ds_ocap da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
      split; [exact D1|]. split; [exact G4|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|].
      split; [exact D6 | exact D7].
    + split; [exact S1|]. split; [clear - G2 S2; tauto|]. split; [rewrite S3; reflexivity | exact S4].
  - (* no pending text *)
    intros HN HD. destruct HD as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
    cbn [ds_cap ds_ka ds_ecap ds_ocap] in D1, D2, D3, D6.
    destruct (gd_grow_sim c (Z.of_nat (length u)) qs qc j k (da_buf a) (da_buf a') bb) as (G1 & G2 & G3 & G4);
      [exact HN | exact D2 |].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
    unfold gd_dsim. cbn [ds_cap ds_ka ds_ecap ds_ocap da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
    split; [exact D1|]. split; [exact G4|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|].
    split; [exact D6 | exact D7].
  - (* nothing to read *)
    intros HN HD. destruct HD as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
    cbn [ds_cap ds_ka ds_ecap ds_ocap] in D1, D2, D3, D6.
    destruct (gd_grow_sim c (Z.of_nat (length u)) qs qc j k (da_buf a) (da_buf a') bb) as (G1 & G2 & G3 & G4);
      [exact HN | exact D2 |].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
    unfold gd_dsim. cbn [ds_cap ds_ka ds_ecap ds_ocap da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
    split; [exact D1|]. split; [exact G4|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|].
    split; [exact D6 | exact D7].
  - (* a data round *)
    match goal with |- context [chunk u sk ?d] => destruct (chunk u sk d) as [[u' sk'] rl] eqn:ECH end.
    cbn [fst snd].
    match goal with |- context [snd (fst (pushes_run en ec ?LS ?J (da_ev a) (da_erecs a)))] =>
      match goal with |- context [pushes_run en ec LS ?J' (da_ev a') (da_erecs a')] =>
        rewrite (gsh_pushes LS en ec J (da_ev a) (da_erecs a) J' (da_ev a') (da_erecs a')) end end.
    match goal with |- context [lines_run live mxx no oc H ka rl ?J (da_out a) (da_hp a) (da_keys a)] =>
      match goal with |- context [lines_run live mxx no oc H ka rl ?J' (da_out a') (da_hp a') (da_keys a')] =>
        pose proof (proj1 (gsh_lines rl live mxx no oc H ka J (da_out a) (da_hp a) (da_keys a) J' (da_out a') (da_hp a')
                             (da_keys a'))) as GL end end.
    match goal with |- context [lines_run live mxx no oc H ka rl ?J (da_out a) (da_hp a) (da_keys a)] =>
      destruct (lines_run live mxx no oc H ka rl J (da_out a) (da_hp a) (da_keys a))
        as [[tg [[ocg Hg] kag]] [[og hag] ksg]] eqn:ELg end.
    match goal with |- context [lines_run live mxx no oc H ka rl ?J (da_out a') (da_hp a') (da_keys a')] =>
      destruct (lines_run live mxx no oc H ka rl J (da_out a') (da_hp a') (da_keys a'))
        as [[tc [[occ Hc] kac]] [[oc' hac] ksc]] eqn:ELc end.
    try rewrite ELg in GL. try rewrite ELc in GL. cbn [fst snd] in GL. injection GL as <- <- <-.
    cbn [fst snd].
    intros HN HD. destruct HD as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
    cbn [ds_cap ds_ka ds_ecap ds_ocap] in D1, D2, D3, D6.
    rewrite !nret_app in HN. rewrite !run_from_app, !room_from_app, !nret_app.
    destruct (gd_grow_sim c (Z.of_nat (length u)) qs qc j k (da_buf a) (da_buf a') bb) as (G1 & G2 & G3 & G4);
      [intros i Hi; apply HN; lia | exact D2 |].
    rewrite G1. rewrite G3 in ELg |- *.
    rewrite <- (Nat.add_assoc j k (nretF (fst (grow_tr c (Z.of_nat (length u)) k (da_buf a'))))) in ELg |- *.
    set (m0 := nretF (fst (grow_tr c (Z.of_nat (length u)) k (da_buf a')))) in *.
    match goal with |- context [pushes_run en ec ?LS (j + (k + m0)) (da_ev a) (da_erecs a)] =>
      destruct (gd_push_sim LS en ec qs qc j (k + m0) (da_ev a) (da_ev a') (da_erecs a) (da_erecs a')
                  (gd_rn qc bb k (fst (grow_tr c (Z.of_nat (length u)) k (da_buf a')))))
        as (P1 & P2 & P3 & P4 & P5); [intros i Hi; apply HN; lia | exact D6 | exact D7 |];
      rewrite P1; rewrite P3 in ELg |- *;
      set (m1 := nretF (fst (fst (pushes_run en ec LS (k + m0) (da_ev a') (da_erecs a'))))) in *
    end.
    rewrite !gd_td0 in HN. rewrite !gd_td0 in ELg. rewrite !gd_td0 in ELc. rewrite !gd_td0.
    rewrite <- (Nat.add_assoc j (k + m0) m1) in ELg |- *.
    rewrite (Nat.add_0_r (j + (k + m0 + m1))) in ELg |- *.
    rewrite (Nat.add_0_r (k + m0 + m1)) in HN, ELc |- *.
    pose proof (gd_f2_nth (gd_R qs qc) (da_pend a) (da_pend a') adr0 adr0 0 D5 ltac:(unfold gd_R; reflexivity)) as X0.
    match goal with |- context [gd_rn qs ?B ?J0 (if ?w then list_drop_tra _ ?n else [])] =>
      destruct (gd_td_sim w (nth 0 (da_pend a) adr0) (nth 0 (da_pend a') adr0) n qs qc J0
                  (k + m0 + m1) B X0) as (TD1 & TD2); rewrite TD1
    end.
    match goal with |- context [gd_rn qc ?B3 (k + m0 + m1) tc] =>
      pose proof (gd_lines_sim rl live mxx no oc H ka qs qc j (k + m0 + m1) (da_out a) (da_out a') (da_hp a) (da_hp a')
                    (da_keys a) (da_keys a') B3) as LS
    end.
    rewrite ELg, ELc in LS. cbn [fst snd] in LS.
    destruct LS as (L1 & L2 & L3 & L4 & L5 & L6); [intros i Hi; apply HN; lia | exact D1 | exact D3 | exact D4 |].
    rewrite L1, L3.
    rewrite <- (Nat.add_assoc j (k + m0 + m1) (nretF tc)).
    match goal with |- context [drain_run f live mxx ?s2 (j + (k + m0 + m1 + nretF tc)) ?ag] =>
      match goal with |- context [drain_run f live mxx s2 (k + m0 + m1 + nretF tc) ?ac] =>
        match goal with |- context [gd_rn qc ?B4 (k + m0 + m1 + nretF tc) (fst (drain_run f live mxx s2 _ ac))] =>
          destruct (IH live mxx qs qc j s2 (k + m0 + m1 + nretF tc)%nat ag ac B4) as (S1 & S2 & S3 & S4)
        end end end.
    + intros i Hi. apply HN. lia.
    + unfold gd_dsim. cbn [ds_cap ds_ka ds_ecap ds_ocap da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
      split; [exact L4|]. split; [exact G4|]. split; [exact L5|]. split; [exact L6|].
      split; [match goal with |- Forall2 _ (if ?w then _ else _) _ => destruct w end;
              [apply gd_f2_skipn; exact D5 | exact D5]|].
      split; [exact P4 | exact P5].
    + split; [exact S1|]. split; [clear - G2 P2 TD2 L2 S2; tauto|].
      split; [rewrite S3; reflexivity | exact S4].
Qed.

Lemma gd_lines_out_false : forall ls mxx no cp H ka j o ha ks,
  fst (fst (snd (lines_run false mxx no cp H ka ls j o ha ks))) = o.
Proof.
  induction ls as [|l r IH]; intros mxx no cp H ka j o ha ks; cbn [lines_run fst snd]; [reflexivity|].
  cbv zeta. rewrite IH. reflexivity.
Qed.

(* A drain whose sends are off leaves g_out's address as it was. *)
Lemma gd_out_false : forall f mxx s j a, da_out (snd (snd (drain_run f false mxx s j a))) = da_out a.
Proof.
  induction f as [|f IH]; intros mxx s j a; [reflexivity|].
  destruct s as [c u sk H ka ei0 pd off rf en ec no oc].
  cbn [drain_run ds_cap ds_u ds_skip ds_H ds_ka ds_eintr ds_pend ds_off ds_ref ds_en ds_ecap ds_no ds_ocap]. cbv zeta.
  destruct ei0; [cbn [fst snd]; rewrite IH; reflexivity|].
  destruct pd as [|r0 rs]; [reflexivity|].
  match goal with |- context [Z.min ?x ?y <=? 0] => destruct (Z.min x y <=? 0) end; [reflexivity|].
  match goal with |- context [chunk u sk ?d] => destruct (chunk u sk d) as [[u' sk'] rl] end.
  match goal with |- context [lines_run false mxx no oc H ka rl ?J ?o ?h ?k] =>
    pose proof (gd_lines_out_false rl mxx no oc H ka J o h k) as LO;
    destruct (lines_run false mxx no oc H ka rl J o h k) as [[t1 [[oc1 H1] ka1]] [[o1 ha1] ks1]] eqn:EL end.
  try rewrite EL in LO. cbn [fst snd] in LO |- *. rewrite IH. cbn [da_out]. exact LO.
Qed.

Lemma gd_ds_wk : forall nm o e ks h, map key_addr ks = map key_addr (re_keys e) ->
  drain_start nm o (with_keys e ks) h = drain_start nm o e h.
Proof.
  intros nm o e ks h E. unfold drain_start. cbn [with_keys re_buf re_hp re_keys].
  rewrite <- (map_map key_addr nm ks), <- (map_map key_addr nm (re_keys e)), E. reflexivity.
Qed.

Lemma gd_hn : forall (qd qdr ext : list sptr) n, length qdr = n ->
  forall i, (0 <= i < 0 + n)%nat -> nth (length qd + i) (qd ++ qdr ++ ext) (SP 0 0) = nth i qdr (SP 0 0).
Proof.
  intros qd qdr ext n E i Hi. rewrite app_nth2 by lia. replace (length qd + i - length qd)%nat with i by lia.
  apply app_nth1. lia.
Qed.

Lemma gd_name1 : forall L A qs qc a n, NoDup (map fst (blocks L A)) -> live_at L A (resolveF [] (gnm a)) a n ->
  gd_R qs qc (gnm a) (known_at L A a).
Proof. intros L A qs qc a n ND LA. exact (eq_sym (CF.gestures_end_b.p3b_sptr_of_eq L A _ a n ND LA)). Qed.

Lemma gd_names : forall {X : Type} L A (l : list X) (g : X -> Z) (n : X -> Z) qs qc, NoDup (map fst (blocks L A)) ->
  Forall2 (fun r a => live_at L A (resolveF [] a) (g r) (n r)) l (map (fun r => gnm (g r)) l) ->
  Forall2 (gd_R qs qc) (map (fun r => gnm (g r)) l) (map (fun r => known_at L A (g r)) l).
Proof.
  intros X L A l g n qs qc ND. induction l as [|x l IH]; intros F; cbn [map] in F |- *; [constructor|].
  inversion F as [|x0 y0 l0 l0' Hx Fl]; subst.
  constructor; [exact (gd_name1 L A qs qc (g x) (n x) ND Hx) | exact (IH Fl)].
Qed.

Lemma gd_f2_tr : forall {X : Type} (P : X -> sptr -> Prop) (l : list X) (l1 l2 : list adrF) qs qc,
  Forall2 (fun x a => P x (resolveF qc a)) l l2 -> Forall2 (gd_R qs qc) l1 l2 ->
  Forall2 (fun x a => P x (resolveF qs a)) l l1.
Proof.
  intros X P l l1 l2 qs qc F. revert l1. induction F as [|x y l l2 Pxy F IH]; intros l1 GG.
  - inversion GG. constructor.
  - inversion GG as [|a b l1' l2' Rab GG']; subst.
    constructor; [unfold gd_R in Rab; rewrite Rab; exact Pxy | exact (IH _ GG')].
Qed.

(* At a pending source's drain, gone's addresses and the drain's own name the same blocks. *)
Lemma gd_dsim0 : forall L A qs qc oa OUTx NOm CAPm e h, NoDup (map fst (blocks L A)) ->
  pend_links L A e h -> re_eof e = 0 -> 0 <= re_cap e -> 0 <= hl_cap (hs_expected h) ->
  (CAPm <> 0 -> gd_R qs qc oa (known_at L A OUTx)) ->
  gd_dsim qs qc (drain_init NOm CAPm e h) (drain_start gnm oa e h) (drain_start (known_at L A) (known_at L A OUTx) e h).
Proof.
  intros L A qs qc oa OUTx NOm CAPm e h ND [(B1 & B2 & B3) SL] He C0 E0 HO.
  destruct (SL He) as (S1 & S2 & S3 & (S4 & S5) & S6 & S7).
  unfold gd_dsim, drain_init, drain_start, ent_ka.
  cbn [ds_cap ds_ka ds_ecap ds_ocap da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
  split; [exact HO|].
  split; [intros X; exact (gd_name1 L A qs qc (re_buf e) (re_cap e) ND (B1 ltac:(lia)))|].
  split; [destruct (Z.eqb_spec (re_hp e) 0) as [Y|Y]; intros X;
          [exfalso; exact (X eq_refl) | exact (gd_name1 L A qs qc (re_hp e) (re_kh e) ND (B2 Y))]|].
  split; [exact (gd_names L A (re_keys e) key_addr (fun k => Z.of_nat (length (key_text k)) + 1) qs qc ND B3)|].
  split; [exact (gd_names L A (hl_recs (hs_pending h)) fst (fun r => Z.of_nat (length (snd r)) + 1) qs qc ND S2)|].
  split; [intros X; exact (gd_name1 L A qs qc (hl_v (hs_expected h)) (16 * hl_cap (hs_expected h)) ND
                             (S4 ltac:(lia)))|].
  exact (gd_names L A (hl_recs (hs_expected h)) fst (fun r => Z.of_nat (length (snd r)) + 1) qs qc ND S5).
Qed.

(* gone's run after the drain, from the done run k (qd) and the drain's own run trc (qdr). *)
Lemma gd_run_post : forall (qd qdr : list sptr) (k td trc : trF) (b : rt_R RF),
  length qd = nretF k -> (forall ext, runF RF (qd ++ ext) b k = runF RF qd b k) ->
  (forall post, gd_rn (qd ++ qdr ++ post) (runF RF qd b k) (nretF k) td = gd_rn qdr (runF RF qd b k) 0 trc) ->
  length qdr = nretF trc -> nretF td = nretF trc ->
  length (qd ++ qdr) = nretF (k ++ td) /\
  (forall ext, runF RF ((qd ++ qdr) ++ ext) b (k ++ td) = runF RF (qd ++ qdr) b (k ++ td)) /\
  runF RF (qd ++ qdr) b (k ++ td) = runF RF qdr (runF RF qd b k) trc.
Proof.
  intros qd qdr k td trc b LQ EXT SIM LQd EN.
  assert (R : forall ext, runF RF ((qd ++ qdr) ++ ext) b (k ++ td) = runF RF qdr (runF RF qd b k) trc).
  { intros ext. unfold runF at 1, run_tr at 1. rewrite run_from_app, <- app_assoc.
    pose proof (EXT (qdr ++ ext)) as E1. unfold runF, run_tr in E1. rewrite E1, Nat.add_0_l. exact (SIM ext). }
  split; [rewrite length_app, nret_app; lia|].
  split; [intros ext; rewrite R; rewrite <- (app_nil_r (qd ++ qdr)); rewrite R; reflexivity|].
  rewrite <- (app_nil_r (qd ++ qdr)). exact (R []).
Qed.

(* Room for the drain's own run from gone's room premise. *)
Lemma gd_room_pre : forall (qd qdr fill : list sptr) (k td rest trc : trF) (b : rt_R RF),
  (forall ext, runF RF (qd ++ ext) b k = runF RF qd b k) ->
  roomF RF (qd ++ qdr ++ fill) b (k ++ td ++ rest) ->
  (gd_rm (qd ++ qdr ++ fill) (runF RF qd b k) (nretF k) td <-> gd_rm qdr (runF RF qd b k) 0 trc) ->
  roomF RF qdr (runF RF qd b k) trc.
Proof.
  intros qd qdr fill k td rest trc b EXT RR S2. unfold roomF, room_run in RR |- *.
  apply room_from_app in RR as [_ RR]. apply room_from_app in RR as [RR _].
  pose proof (EXT (qdr ++ fill)) as E1. unfold runF, run_tr in E1. rewrite E1, Nat.add_0_l in RR.
  exact (proj1 S2 RR).
Qed.

Lemma gk_f2_in : forall {X Y : Type} (R R' : X -> Y -> Prop) l l', Forall2 R l l' ->
  (forall x y, In x l -> R x y -> R' x y) -> Forall2 R' l l'.
Proof.
  intros X Y R R' l l' F. induction F as [|x y l l' Rxy F IH]; intros K; constructor.
  - apply K; [left; reflexivity | exact Rxy].
  - apply IH. intros x' y' Hx' R1. apply K; [right; exact Hx' | exact R1].
Qed.

(* A source's links survive a step that keeps each of its blocks live. *)
Lemma gk_entry_mono : forall L A L' A' qs fa e,
  (forall p a n, In a (entry_blocks e) -> live_at L A p a n -> live_at L' A' p a n) ->
  entry_links L A qs fa e -> entry_links L' A' qs fa e.
Proof.
  intros L A L' A' qs fa e K (B1 & B2 & B3). split; [|split].
  - intros Hc. apply K; [|exact (B1 Hc)]. unfold entry_blocks. apply in_or_app; left.
    destruct (Z.eqb_spec (re_cap e) 0); [lia | left; reflexivity].
  - intros Hh. apply K; [|exact (B2 Hh)]. unfold entry_blocks. apply in_or_app; right; apply in_or_app; left.
    destruct (Z.eqb_spec (re_hp e) 0); [contradiction | left; reflexivity].
  - apply (gk_f2_in _ _ _ _ B3). intros k a Hk X. cbv beta in X |- *. apply K; [|exact X].
    unfold entry_blocks. apply in_or_app; right; apply in_or_app; right. apply in_map. exact Hk.
Qed.

Lemma gk_lb_v : forall l, 0 < hl_cap l -> In (hl_v l) (list_blocks l).
Proof.
  intros l Hc. unfold list_blocks. apply in_or_app; left. destruct (Z.eqb_spec (hl_cap l) 0); [lia | left; reflexivity].
Qed.

Lemma gk_lb_r : forall l r, In r (hl_recs l) -> In (fst r) (list_blocks l).
Proof. intros l r Hr. unfold list_blocks. apply in_or_app; right. apply in_map. exact Hr. Qed.

Lemma gk_src_mono : forall L A L' A' qs nm fa h,
  (forall p a n, In a (hs_blocks h) -> live_at L A p a n -> live_at L' A' p a n) ->
  src_links L A qs nm fa h -> src_links L' A' qs nm fa h.
Proof.
  intros L A L' A' qs nm fa h K (B1 & B2 & B3 & (B4 & B5) & B6 & B7).
  assert (KP : forall p a n, In a (list_blocks (hs_pending h)) -> live_at L A p a n -> live_at L' A' p a n)
    by (intros p a n Ha; apply K; unfold hs_blocks; apply in_or_app; left; exact Ha).
  assert (KQ : forall p n, live_at L A p (hs_partial h) n -> live_at L' A' p (hs_partial h) n)
    by (intros p n; apply K; unfold hs_blocks; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
  assert (KE : forall p a n, In a (list_blocks (hs_expected h)) -> live_at L A p a n -> live_at L' A' p a n)
    by (intros p a n Ha; apply K; unfold hs_blocks; apply in_or_app; right; apply in_or_app; right;
        apply in_or_app; left; exact Ha).
  assert (KH : forall p a n, In a (list_blocks (hs_held h)) -> live_at L A p a n -> live_at L' A' p a n)
    by (intros p a n Ha; apply K; unfold hs_blocks; apply in_or_app; right; apply in_or_app; right;
        apply in_or_app; right; exact Ha).
  split; [intros Hc; exact (KP _ _ _ (gk_lb_v _ Hc) (B1 Hc))|].
  split; [apply (gk_f2_in _ _ _ _ B2); intros r a Hr X; exact (KP _ _ _ (gk_lb_r _ _ Hr) X)|].
  split; [exact (KQ _ _ B3)|].
  split; [split; [intros Hc; exact (KE _ _ _ (gk_lb_v _ Hc) (B4 Hc)) |
                  apply (gk_f2_in _ _ _ _ B5); intros r a Hr X; exact (KE _ _ _ (gk_lb_r _ _ Hr) X)]|].
  split; [intros Hc; exact (KH _ _ _ (gk_lb_v _ Hc) (B6 Hc))|].
  rewrite Forall_forall in B7 |- *. intros r Hr. exact (KH _ _ _ (gk_lb_r _ _ Hr) (B7 r Hr)).
Qed.

(* A live block of a positive-size block that a callee neither frees nor writes past stays live. *)
Lemma gd_live_keep : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p a n k0,
  relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 -> NoDup (map fst (blocks L1 A1)) ->
  In (a, k0) (blocks L1 A1) -> 0 < k0 -> ~ F' a -> live_at L1 A1 p a n -> live_at L2 A2 p a n.
Proof.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p a n k0 RP ND Hb Hk HF LA.
  assert (IB : In (a, n) (blocks L1 A1)) by (destruct LA as [H1 E1]; apply rig_blocks_in; exists p; split; assumption).
  pose proof (rig_nodup_fst (blocks L1 A1) a n k0 (proj1 (gdr_nd _) ND) IB Hb) as ->.
  exact (CF.gestures_end_b.p3b_live_rp Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p a k0 RP LA Hk HF).
Qed.

(* The source's own links after the drain, at gone's addresses fa (resolved by qs), from the drain's post at its
   addresses fa' (resolved by qc). *)
Lemma gd_entry_post : forall L' A' qs qc fa fa' e2 s,
  entry_links L' A' qc fa' e2 -> gd_dsim qs qc s fa fa' -> re_cap e2 = ds_cap s -> ent_ka e2 = ds_ka s ->
  (re_hp e2 <> 0 -> 8 <= re_kh e2) ->
  entry_links L' A' qs (DA adr0 (da_buf fa) (da_hp fa) (da_keys fa) [] adr0 []) e2.
Proof.
  intros L' A' qs qc fa fa' e2 s (B1 & B2 & B3) (D1 & D2 & D3 & D4 & D5 & D6 & D7) EC EK KH.
  unfold entry_links. cbn [da_buf da_hp da_keys]. split; [|split].
  - intros Hc. pose proof (D2 ltac:(lia)) as X. unfold gd_R in X. rewrite X. exact (B1 Hc).
  - intros Hh. assert (KA : ds_ka s <> 0).
    { rewrite <- EK. unfold ent_ka. destruct (Z.eqb_spec (re_hp e2) 0) as [Y|Y]; [contradiction | specialize (KH Hh); lia]. }
    pose proof (D3 KA) as X. unfold gd_R in X. rewrite X. exact (B2 Hh).
  - exact (gd_f2_tr (fun k p => live_at L' A' p (key_addr k) (Z.of_nat (length (key_text k)) + 1)) _ _ _ qs qc B3 D4).
Qed.

Lemma gd_src_post : forall L A L' A' qs qc fa fa' h2 s,
  src_links L' A' qc (known_at L A) fa' h2 -> gd_dsim qs qc s fa fa' -> hl_cap (hs_expected h2) = ds_ecap s ->
  (0 < hl_cap (hs_pending h2) -> sptr_of L A (hl_v (hs_pending h2)) = sptr_of L0 A0 (hl_v (hs_pending h2))) ->
  sptr_of L A (hs_partial h2) = sptr_of L0 A0 (hs_partial h2) ->
  (0 < hl_cap (hs_held h2) -> sptr_of L A (hl_v (hs_held h2)) = sptr_of L0 A0 (hl_v (hs_held h2))) ->
  Forall (fun r => sptr_of L A (fst r) = sptr_of L0 A0 (fst r)) (hl_recs (hs_held h2)) ->
  src_links L' A' qs gnm fa h2.
Proof.
  intros L A L' A' qs qc fa fa' h2 s (S1 & S2 & S3 & (S4 & S5) & S6 & S7) (D1 & D2 & D3 & D4 & D5 & D6 & D7) EE
    N1 N2 N3 N4.
  unfold src_links, expected_links. unfold gnm, known_at in *. cbn [resolve] in *.
  split; [intros Hc; rewrite <- (N1 Hc); exact (S1 Hc)|].
  split; [exact (gd_f2_tr (fun r p => live_at L' A' p (fst r) (Z.of_nat (length (snd r)) + 1)) _ _ _ qs qc S2 D5)|].
  split; [rewrite <- N2; exact S3|].
  split; [split|].
  - intros Hc. pose proof (D6 ltac:(lia)) as X. unfold gd_R in X. rewrite X. exact (S4 Hc).
  - exact (gd_f2_tr (fun r p => live_at L' A' p (fst r) (Z.of_nat (length (snd r)) + 1)) _ _ _ qs qc S5 D7).
  - split; [intros Hc; rewrite <- (N3 Hc); exact (S6 Hc)|].
    rewrite Forall_forall in S7, N4 |- *. intros r Hr. rewrite <- (N4 r Hr). exact (S7 r Hr).
Qed.

Lemma gd_combine_snd : forall {X Y} (l : list X) (l' : list Y), length l = length l' -> map snd (combine l l') = l'.
Proof.
  intros X Y l. induction l as [|x l IH]; intros [|y l'] E; cbn [length] in E; try lia; [reflexivity|].
  cbn [combine map snd]. rewrite IH by lia. reflexivity.
Qed.

(* Rewrites used in gdr_call in place of conversion steps (change, cbv or cbn in a hypothesis, reflexivity against a
   drain term). The kernel checks such a step again where the term is used, and on gone's run it then unfolds the
   drain's run: the Qed of gdr_call did not finish in 40 minutes. *)
Lemma gd_p1 : forall {X1 X2 X3 X4 X5 : Type} (a : X1) (b : X2) (c : X3) (d : X4) (e : X5),
  fst (fst (fst (a, b, c, (d, e)))) = a.
Proof. reflexivity. Qed.

Lemma gd_nth0 : forall {X : Type} (x : X) l d, nth 0 (x :: l) d = x.
Proof. reflexivity. Qed.

Lemma gd_p3 : forall {X1 X2 X3 X4 X5 : Type} (a : X1) (b : X2) (c : X3) (d : X4) (e : X5),
  snd (fst (a, b, c, (d, e))) = c.
Proof. reflexivity. Qed.

Lemma gd_adr_out_false : forall mxx NO CAP e h j a, da_out (drain_adr false mxx NO CAP e h j a) = da_out a.
Proof.
  intros mxx NO CAP e h j a.
  exact (gd_out_false (S (S (length (pending_stream h)))) mxx (drain_init NO CAP e h) j a).
Qed.

Lemma gd_if00 : forall {X : Type} (x y : X), (if 0 =? 0 then x else y) = x.
Proof. reflexivity. Qed.

Lemma gdr_call : forall (fx : YK11.FPState) i regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc,
  (i < length es)%nat -> re_eof (nth i es no_entry) = 0 ->
  GI i (pend_rel i) [] (gpos_top i) (gbound i) regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc ->
  getr regs 1 = Z_to_bv 64 0x134dc -> getr regs 10 = Z_to_bv 64 (G + 56 * Z.of_nat i) ->
  SR segs (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 RIG_DRAIN) mem (seg_rom segs)) md)
    (fun c => exists regs' L' A' mem' md' k' qd' es_c' hs_c' LB' OUTc' CAPc' junkc' ks0 ka0 a,
       c = mkCfg (@YK11.mkst fx regs' (getr regs 1) mem' (seg_rom segs)) md' /\ regs_preserved regs regs' /\
       GI i (inner_cur i ks0 0 ks0 [] ka0 a (combine ks0 ka0)) (part_of i [])
         (gpos_k i a (gkept ks0 ka0) [] (gxks ks0 ka0)) (bound_in i [])
         regs' L' A' mem' md' k' qd' es_c' hs_c' kss LB' OUTc' CAPc' junkc').
Proof.
  intros fx i regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc Hi He HG R1 R10.
  pose proof HG as HG0. unfold GI in HG0. cbv zeta in HG0.
  destruct HG0 as (G2 & G3 & G4 & G8 & G22 & CH & INIT & RES & BUD & POT & RA & GL & HNS & HGS & HGB & CCL & CBR & CDD
    & CEI & CERR & SRCH' & FR0 & FRB & FRS & HLE & HTAB & HEOK & HLH & HLK & HIL & HSRC & HDONE & HCUR & HPEND & HND
    & HSUR & HSV & HLB & HT & HDEAD & HLIVE).
  destruct RES as (LQ & EXT & RES).
  clear HG. gm_hide HDEAD. gm_hide HLIVE. gm_hide HCUR.
  pose proof len_O as LO. pose proof gm_fcur_mono as FCM.
  gm_hide Hcl. gm_hide Hbr. gm_hide Hdd. gm_hide Hei. gm_hide HOUT0.
  pose proof gS_range as [[GSR1 GSR2] GSR3]. pose proof alloc_ceiling_val as ACV. pose proof K_val as KV.
  rewrite KV in GSR1.
  pose proof CH as (M1 & W1 & B1 & _).
  pose proof (NODUP L A mem md M1) as NDA.
  pose proof PRE as (_ & W0 & _ & _ & _ & _ & _ & _ & TP0 & _).
  assert (Hi4 : (i < 4)%nat) by (pose proof NLE as N4; unfold gN in N4; lia).
  destruct (HCUR Hi) as (Ee & Eh & PLK). rewrite Ee, Eh in PLK.
  assert (Hic : (i < length es_c)%nat) by lia.
  pose proof (proj1 (Forall_forall _ _) HEOK _ (nth_In es_c no_entry Hic)) as OKK. rewrite Ee in OKK.
  pose proof (gdr_okk_len _ _ _ _ OKK) as EL56.
  destruct OKK as (ks & Eks & OK).
  destruct (map_fst_keys (re_keys (nth i es no_entry)) ks Eks) as (EKA & EKT & EKL & EKP & EKX).
  pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NH26 & _).
  assert (EB1 : entry_blocks (with_keys (nth i es no_entry) ks) = entry_blocks (nth i es no_entry))
    by exact (entry_blocks_wk _ _ EKA).
  assert (EY1 : entry_bytes (with_keys (nth i es no_entry) ks) = entry_bytes (nth i es no_entry))
    by exact (entry_bytes_wk _ _ EKL).
  assert (NH1 : re_nheld (with_keys (nth i es no_entry) ks) = re_nheld (nth i es no_entry))
    by (unfold re_nheld; cbn [re_keys with_keys]; rewrite EKL; reflexivity).
  destruct HTAB as (tl & HTAB).
  pose proof (gdr_tab_mid L A mem es_c tl i Hic HEOK HTAB) as ENT. rewrite Ee in ENT.
  destruct (gdr_gso i Hi He) as (_ & J4 & HFD & HSK & HSU & PL26 & EC26 & NP26).
  pose proof (HSRC i Hi He) as SRC. rewrite Eh in SRC.
  pose proof SRC as (SRC1 & _ & _ & SOP & SFD & _).
  pose proof (rig_blk L A mem md G SRC_TABLE 0 M1 HGB ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)) as (_ & GG1 & GG2 & _).
  pose proof (rig_nodup_pick G OUTc (map entry_blocks es_c) (map srcblk (combine es hs_c)) i
                ltac:(rewrite length_map; lia) ltac:(rewrite !length_map, length_combine; lia) (proj1 (gdr_nd _) HND)) as NDi.
  rewrite gdr_nth_eb, (gdr_nth_sb hs_c i HLH Hi), Ee in NDi.
  rewrite (nth_indep hs_c (fst no_hj) (fst (nth i hs no_hj))) in NDi by lia. rewrite Eh, (gdr_sb0 _ _ He) in NDi.
  assert (H2' : bv_unsigned (getr regs 2) = gP) by (rewrite G2; apply MState.unsigned_lit; unfold gP; lia).
  assert (SPR : spZ regs = gP)
    by (unfold spZ; transitivity (bv_unsigned (Z_to_bv 64 gP)); [f_equal; exact G2 | apply MState.unsigned_lit; unfold gP; lia]).
  assert (PAR : exists (nout' cap' out' : word) (Op jp : list byte),
    rw_cells segs mem G_OUTV [C8 mx; C8 nout'; C8 cap'; C8 out'] /\
    bv_unsigned out' = OUTc /\ bv_unsigned cap' = CAPc /\
    (send_live cl br dd (Z.of_nat (length LB)) = true -> bv_unsigned nout' = gNO + Z.of_nat (length LB) /\ Op = O ++ LB /\
       nout' = Z_to_bv 64 (gNO + Z.of_nat (length LB)) /\ cap' = Z_to_bv 64 CAPc /\ out' = Z_to_bv 64 OUTc /\ jp = junkc) /\
    (send_live cl br dd (Z.of_nat (length LB)) = false -> bv_unsigned nout' = gNO /\ Op = O /\ OUTc = gOUT /\ CAPc = gCAP /\
       nout' = nout /\ cap' = cap /\ out' = out /\ jp = junk) /\
    ((bv_unsigned cap' = 0 /\ bv_unsigned out' = 0 /\ bv_unsigned nout' = 0 /\ Op = []) \/
     (0 < bv_unsigned cap' /\ bv_unsigned nout' <= bv_unsigned cap' /\ In (bv_unsigned out', bv_unsigned cap') (blocks L A) /\
      fresh_block Bm (bv_unsigned out') (bv_unsigned cap') /\ bytes_at segs mem (bv_unsigned out') (Op ++ jp) /\
      Z.of_nat (length Op) = bv_unsigned nout' /\ Z.of_nat (length jp) = bv_unsigned cap' - bv_unsigned nout'))).
  { destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV.
    - destruct (HLIVE eq_refl) as (H1 & H2 & H3 & H4 & H5 & H6).
      pose proof (gm_live_nz _ LV) as TNZ.
      pose proof (rig_blk L A mem md OUTc CAPc 0 M1 H2 ltac:(lia)) as (_ & HO1 & HO2 & _).
      exists (Z_to_bv 64 (gNO + Z.of_nat (length LB))), (Z_to_bv 64 CAPc), (Z_to_bv 64 OUTc), (O ++ LB), junkc.
      rewrite !MState.unsigned_lit by lia.
      split; [exact H6|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; repeat split; reflexivity|]. split; [intros X; discriminate X|].
      right. split; [lia|]. split; [lia|]. split; [exact H2|]. split; [exact H3|].
      split; [rewrite <- app_assoc; exact H4|]. split; [rewrite length_app; lia | lia].
    - destruct (HDEAD eq_refl) as (H1 & E1 & E2 & H3).
      exists nout, cap, out, O, junk.
      split; [exact H1|]. split; [rewrite E1; reflexivity|]. split; [rewrite E2; reflexivity|].
      split; [intros X; discriminate X|].
      split; [intros _; repeat split; first [reflexivity | assumption]|].
      destruct HOUT0 as [X|(Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7)]; [left; exact X|right].
      destruct (H3 Y1) as [Z1 Z2].
      split; [exact Y1|]. split; [exact Y2|]. split; [exact Z1|]. split; [exact Y4|]. split; [exact Z2|].
      split; assumption. }
  destruct PAR as (nout' & cap' & out' & Op & jp & COUT & EOUT & ECAP & PL1 & PL0 & PH).
  rewrite EOUT, ECAP in PH. gm_hide PL1. gm_hide PL0. gm_hide PH.
  assert (NOnn : 0 <= bv_unsigned nout') by (destruct PH as [(_ & _ & X & _)|(_ & _ & _ & _ & _ & X & _)]; lia).
  assert (OB : 0 < CAPc -> In (OUTc, CAPc) (blocks L A))
    by (intros X; destruct PH as [(Y & _)|(_ & _ & Y & _)]; [lia | exact Y]).
  gm_hide OB.
  pose proof (gdr_tot _ _ _ _ _ SRC) as TOTB.
  destruct (rig_live_step cl br dd (Z.of_nat (length LB))
    (Z.of_nat (length (with_nul (lines (hs_state (fst (nth i hs no_hj))) (bzs (pending_stream (fst (nth i hs no_hj))))))))
    Hcl Hbr Hdd ltac:(lia) ltac:(lia)) as [LS1 LS0]. gm_hide LS1. gm_hide LS0.
  destruct (rig_off_step cl br dd ei (Z.of_nat (length LB))
    (Z.of_nat (length (with_nul (lines (hs_state (fst (nth i hs no_hj))) (bzs (pending_stream (fst (nth i hs no_hj))))))))
    Hcl Hbr Hdd ltac:(lia) ltac:(lia)) as (OS1 & OS2 & OS3 & OS4). gm_hide OS3. gm_hide OS4.
  remember (Z.of_nat (length (with_nul (lines (hs_state (fst (nth i hs no_hj)))
              (bzs (pending_stream (fst (nth i hs no_hj)))))))) as TOT eqn:ETOT.
  assert (LVM : send_live cl br dd (Z.of_nat (length LB)) = true ->
                send_live cl br dd (Z.of_nat (length LB) + TOT) = true)
    by (intros X; exact (proj2 (proj2 (LS1 X)))).
  gm_hide LVM.
  assert (LDV : send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT = true ->
                send_live cl br dd (Z.of_nat (length LB) + TOT) = true).
  { intros X. destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV;
      [exact (proj2 (proj2 (LS1 eq_refl))) | rewrite <- (proj1 (LS0 eq_refl)); exact X]. }
  gm_hide LDV.
  assert (LVD : send_live cl br dd (Z.of_nat (length LB) + TOT) = true ->
                send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT = false ->
                send_live cl br dd (Z.of_nat (length LB)) = true /\ TOT = 0).
  { intros X Y. destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV.
    - destruct (LS1 eq_refl) as (_ & Z1 & _). rewrite Z1 in Y. split; [reflexivity|].
      destruct (Z.eqb_spec TOT 0); [assumption | discriminate Y].
    - rewrite (proj1 (LS0 eq_refl)) in Y. rewrite X in Y. discriminate Y. }
  gm_hide LVD.
  assert (CPM : CAPc = (if send_live cl br dd (Z.of_nat (length LB)) then CAPc else gCAP)).
  { destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV; [reflexivity|].
    destruct (PL0 eq_refl) as (_ & _ & _ & X & _). exact X. }
  assert (NOM : glv = true -> bv_unsigned nout' = gNO + Z.of_nat (length LB)).
  { intros GLV. destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV; [exact (proj1 (PL1 eq_refl))|].
    destruct (Z.eq_dec (Z.of_nat (length LB)) 0) as [T0|TP].
    - rewrite (proj1 (PL0 eq_refl)), T0. lia.
    - rewrite (rig_live_pos cl br dd (Z.of_nat (length LB)) ltac:(lia)) in LV. unfold glv in GLV. rewrite GLV in LV.
      discriminate LV. }
  assert (LVP : 0 < TOT -> send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT = glv)
    by (intros X; exact (rig_live1 cl br dd _ TOT Hcl Hbr Hdd X)).
  assert (LVZ : TOT = 0 -> send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT = false)
    by (intros X; rewrite X; apply rig_live_0).
  assert (NOEQ : send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT = true ->
                 bv_unsigned nout' = gNO + Z.of_nat (length LB) /\ Op = O ++ LB).
  { intros LVt. destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV;
      [destruct (PL1 eq_refl) as (X1 & X2 & _); split; assumption|].
    rewrite (proj1 (LS0 eq_refl)) in LVt.
    pose proof (proj2 (LS0 eq_refl) LVt) as T0'.
    assert (E0 : LB = []) by (apply length_zero_iff_nil; lia).
    destruct (PL0 eq_refl) as (E1 & E2 & _). rewrite E0, E1, E2, app_nil_r. split; [cbn; lia | reflexivity]. }
  gm_hide NOEQ.
  assert (DI : dr_inv (drain_init (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry) (fst (nth i hs no_hj))) /\
               dr_rest (drain_init (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry) (fst (nth i hs no_hj))) =
               bzs (pending_stream (fst (nth i hs no_hj)))).
  { pose proof OK as (_ & SK01 & _ & _ & _ & UC & UL & UL6 & UZ & _).
    cbn [with_keys re_skip re_cap re_U re_used] in SK01, UC, UL, UL6, UZ.
    pose proof SRC as (_ & _ & _ & _ & _ & LAP & _ & PD & _).
    destruct LAP as (_ & _ & _ & _ & _ & LF).
    apply rig_dinit; [exact SK01 | exact HSK | exact HSU | lia | exact UZ | lia | exact PD |].
    eapply Forall_impl; [|exact LF]. intros r (_ & _ & _ & _ & X). exact (X eq_refl). }
  destruct BUD as (oa & ssd & dsd & Lssd & Ldsd & EQ & OLV & ODD & DLK).
  unfold gpos_top, gps, gmx in EQ. rewrite <- CPM in EQ.
  rewrite (rig_skipn_combine es hs i no_entry no_hj Hi LHS), rig_gone_run_cons in EQ.
  cbv zeta in EQ. unfold after_drain, after_drain_adr in EQ. rewrite He, !gd_if00 in EQ.
  destruct (gdr_bridge (send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT)
              (bv_unsigned nout') (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry) (fst (nth i hs no_hj)) TOT
              (proj1 DI) (proj2 DI) ETOT LVP LVZ NOM) as (BTA & BS & BNO & BOC1 & BOC0).
  (* gone's drain at base nret k from oa against the drain's own run at base 0 *)
  pose proof OK as (_ & _ & _ & _ & _ & HC3 & _). cbn [with_keys re_cap] in HC3.
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & EXC & _) & _).
  assert (C0 : 0 <= re_cap (nth i es no_entry)) by lia.
  assert (E0 : 0 <= hl_cap (hs_expected (fst (nth i hs no_hj)))) by (destruct EXC as [(X & _)|(X & _)]; lia).
  assert (HOA : forall qs2 post, CAPc <> 0 -> gd_R (qd ++ post) qs2 oa (known_at L A OUTc)).
  { intros qs2 post Hc. unfold gd_R, known_at. cbn [resolve].
    pose proof OLV as OLV'. pose proof ODD as ODD'. revert OLV' ODD'.
    destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV; intros OLV' ODD'.
    - exact (eq_sym (CF.gestures_end_b.p3b_sptr_of_eq L A _ OUTc CAPc NDA (OLV' eq_refl post))).
    - destruct (ODD' eq_refl) as (EO & OL). destruct (HDEAD eq_refl) as (_ & E1 & E2 & _).
      rewrite EO. unfold gnm, known_at. cbn [resolve]. rewrite E1. rewrite E2 in Hc.
      assert (GC : 0 < gCAP) by (pose proof (bv_unsigned_in_range 64 cap) as X; unfold gCAP in *; lia).
      exact (eq_sym (CF.gestures_end_b.p3b_sptr_of_eq L A _ gOUT gCAP NDA (OL GC))). }
  assert (SIM : forall qdr post,
    length qdr = nretF (drain_tr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry)
                          (fst (nth i hs no_hj)) 0
                          (drain_start (known_at L A) (known_at L A OUTc) (nth i es no_entry) (fst (nth i hs no_hj)))) ->
    gd_rn (qd ++ qdr ++ post) (runF RF qd bnd k) (nretF k)
      (drain_tr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry) (fst (nth i hs no_hj)) (nretF k)
         (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj)))) =
    gd_rn qdr (runF RF qd bnd k) 0
      (drain_tr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry) (fst (nth i hs no_hj)) 0
         (drain_start (known_at L A) (known_at L A OUTc) (nth i es no_entry) (fst (nth i hs no_hj)))) /\
    (gd_rm (qd ++ qdr ++ post) (runF RF qd bnd k) (nretF k)
       (drain_tr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry) (fst (nth i hs no_hj)) (nretF k)
          (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj)))) <->
     gd_rm qdr (runF RF qd bnd k) 0
       (drain_tr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry) (fst (nth i hs no_hj)) 0
          (drain_start (known_at L A) (known_at L A OUTc) (nth i es no_entry) (fst (nth i hs no_hj))))) /\
    nretF (drain_tr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry) (fst (nth i hs no_hj))
             (nretF k) (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj)))) =
    nretF (drain_tr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry) (fst (nth i hs no_hj)) 0
             (drain_start (known_at L A) (known_at L A OUTc) (nth i es no_entry) (fst (nth i hs no_hj)))) /\
    gd_dsim (qd ++ qdr ++ post) qdr
      (drain_fin glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry) (fst (nth i hs no_hj)))
      (drain_adr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry) (fst (nth i hs no_hj))
         (nretF k) (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj))))
      (drain_adr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry) (fst (nth i hs no_hj)) 0
         (drain_start (known_at L A) (known_at L A OUTc) (nth i es no_entry) (fst (nth i hs no_hj))))).
  { intros qdr post Lq.
    pose proof (gd_drain_sim (S (S (length (pending_stream (fst (nth i hs no_hj)))))) glv (bv_unsigned mx)
                  (qd ++ qdr ++ post) qdr (length qd)
                  (drain_init (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry) (fst (nth i hs no_hj))) 0
                  (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj)))
                  (drain_start (known_at L A) (known_at L A OUTc) (nth i es no_entry) (fst (nth i hs no_hj)))
                  (runF RF qd bnd k)) as X.
    rewrite Nat.add_0_r in X. rewrite LQ in X.
    unfold drain_tr, drain_fin, drain_adr, drain_go in Lq |- *.
    rewrite (proj1 (gsh_drain _ glv (bv_unsigned mx) _ 0 dadr0 0
                     (drain_start (known_at L A) (known_at L A OUTc) (nth i es no_entry) (fst (nth i hs no_hj))))).
    apply X.
    - rewrite <- LQ. apply gd_hn. exact Lq.
    - apply (gd_dsim0 L A _ _ oa OUTc _ CAPc _ _ NDA PLK He C0 E0). exact (HOA qdr (qdr ++ post)). }
  assert (ROOMd : forall qs,
    length qs = nretF (drain_tr (send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT)
                         (bv_unsigned mx) (bv_unsigned nout') CAPc (with_keys (nth i es no_entry) ks) (fst (nth i hs no_hj)) 0
                         (drain_start (known_at L A) (known_at L A OUTc) (with_keys (nth i es no_entry) ks)
                            (fst (nth i hs no_hj)))) ->
    roomF RF qs (runF RF qd bnd k)
      (drain_tr (send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT)
         (bv_unsigned mx) (bv_unsigned nout') CAPc (with_keys (nth i es no_entry) ks) (fst (nth i hs no_hj)) 0
         (drain_start (known_at L A) (known_at L A OUTc) (with_keys (nth i es no_entry) ks) (fst (nth i hs no_hj))))).
  { intros qdr Lq.
    rewrite (gd_ds_wk _ _ _ _ _ EKA), (gdr_wk_tr _ _ _ _ _ _ _ _ _ EKX), (proj1 (BTA 0%nat _)) in Lq |- *.
    destruct (SIM qdr [] Lq) as (_ & _ & S3 & _).
    assert (NGE : (length qd + length qdr <= nretF gtr)%nat).
    { unfold gtr. rewrite EQ, !gd_p1, !nret_app, LQ, Lq, <- S3. apply Nat.add_le_mono_l, Nat.le_add_r. }
    set (fill := repeat (SP 0 0) (nretF gtr - length qd - length qdr)).
    assert (LF : length fill = (nretF gtr - length qd - length qdr)%nat) by (unfold fill; apply repeat_length).
    clearbody fill.
    destruct (SIM qdr fill Lq) as (_ & S2 & _ & _).
    eapply gd_room_pre; [exact EXT | | exact S2].
    pose proof (ROOM0 (qd ++ qdr ++ fill)) as RR.
    unfold gtr in RR at 2. rewrite EQ, !gd_p1 in RR. apply RR.
    rewrite !length_app, LF. lia. }
  assert (GS : gs_of i = drain_fin glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc
                           (nth i es no_entry) (fst (nth i hs no_hj))).
  { unfold gs_of, gss. rewrite EQ, !gd_p3. rewrite app_nth2 by lia. rewrite Lssd, Nat.sub_diag.
    exact (gd_nth0 _ _ _). }
  gm_hide DI.
  assert (CPK : call_pre_k Bm MR DRAIN_K L A regs mem md).
  { destruct CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SW).
    split; [exact M1|]. split; [exact W1|]. split; [exact B1|].
    split; [assert (R1' : YK11.getr regs 1 = Z_to_bv 64 0x134dc) by exact R1; rewrite R1'; apply bv_eq; vm_compute;
            reflexivity|].
    rewrite SPR. unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK.
    split; [unfold gP; replace (gS - 160) with (gS + (-10) * 16) by ring; rewrite Z.mod_add by lia; exact GSR3|].
    split; [unfold gP; lia|]. split; [unfold gP; lia|].
    split; [intros a Ha; apply SW; left; change (spZ regs0) with gS; rewrite KV; unfold gP in Ha; lia|].
    split; [exact (eq_trans G4 TP0)|].
    split; [intros a Ha; apply SW; right; exact Ha|].
    intros X. rewrite INIT in X. discriminate X. }
  pose proof (DRAIN fx L A regs mem md (runF RF qd bnd k) (with_keys (nth i es no_entry) ks) (fst (nth i hs no_hj))
    (snd (nth i hs no_hj)) fs os G Op jp cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd
    (if send_off cl br (Z.of_nat (length LB)) then ei else 0) mx nout' cap' out') as DR.
  cbv zeta in DR.
  assert (H10 : bv_unsigned (getr regs 10) = G + 56 * Z.of_nat i)
    by (rewrite R10; apply MState.unsigned_lit; unfold SRC_TABLE, SRC_ENTRY in *; lia).
  rewrite H10, EOUT, ECAP, EB1, EY1, NH1, <- ETOT in DR.
  specialize (DR SEGS CPK INIT TPE HERR RA IMGR IMGC IMGE J4).
  specialize (DR ltac:(split; [exact HGB|]; split; [exact GF0|]; split; [lia|]; split; [unfold SRC_TABLE, SRC_ENTRY; lia|];
                       replace (G + 56 * Z.of_nat i - G) with (Z.of_nat i * SRC_ENTRY) by (unfold SRC_ENTRY; ring);
                       apply Z.mod_mul; unfold SRC_ENTRY; lia)).
  specialize (DR ENT OK SRC ltac:(cbn [re_fd with_keys]; rewrite <- HFD; exact (gdr_oth mem _ _ _ J4 SRCH' SRC1 SOP SFD))
    HFD HSK HSU
    (proj2 (gdr_nd _) NDi) PL26 EC26 NP26).
  specialize (DR Hcl OS3 Hdd (OS4 Hei) CCL CBR CDD CEI COUT CERR PH RES ROOMd).
  eapply SR_mono; [exact DR|]. clear DR.
  intros c' (L' & A' & R2 & m2 & md' & e2 & h2 & OUT' & CAP' & junk' & LB2 & -> & RP & INIT' & RES'
    & RA2 & ENT2 & EOK2 & SRC2 & OTH2 & FD2 & EOF2 & CAP2 & DCAP & DU & DSK & DH & DKA & DEC & HKH2 & DECB
    & HFD2 & HCL2 & HEI2 & PND2 & OFF2 & PV2 & PC2 & PP2 & ST2
    & EXP2 & EXF2 & HLD2 & SK2 & SU2 & NDK2 & SS2 & ND2 & GB2 & KEEP2 & BACK2 & FRS2 & CCL2 & CBR2 & CDD2 & CEI2
    & CERR2 & LBE & DEAD2 & LIVE2).
  rewrite (gdr_wk_fin _ _ _ _ _ _ _ EKX) in DCAP, DU, DSK, DH, DKA, DEC, LIVE2.
  destruct RES' as (qdr & LQd & RES' & OLK & ELK & SLK).
  rewrite (gd_ds_wk _ _ _ _ _ EKA), (gdr_wk_tr _ _ _ _ _ _ _ _ _ EKX), (proj1 (BTA 0%nat _)) in LQd, RES'.
  rewrite (gd_ds_wk _ _ _ _ _ EKA), (gdr_wk_adr _ _ _ _ _ _ _ _ _ EKX) in OLK, ELK, SLK.
  destruct (gdr_sn _ _ BS) as (SC & SU' & SS' & SH & SK' & SE).
  destruct (SIM qdr [] LQd) as (_ & _ & NEQ & _).
  destruct (gd_run_post qd qdr k _ _ bnd LQ EXT (fun post => proj1 (SIM qdr post LQd)) LQd NEQ) as (RP1 & RP2 & RP3).
  rewrite <- RP3 in RES'.
  gm_hide DECB.
  rewrite OS1 in CBR2. rewrite OS2 in CEI2. gm_hide DEAD2. gm_hide LIVE2.
  change (re_keys (with_keys (nth i es no_entry) ks)) with ks in SS2. rewrite EKX in SS2.
  pose proof RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  assert (HO : send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT = true ->
               0 < CAPc -> In (OUTc, CAPc) (blocks L A)) by (intros _ Y; exact (OB Y)).
  assert (SAlo : G <= G + 56 * Z.of_nat i) by lia.
  assert (SAhi : G + 56 * Z.of_nat i + SRC_ENTRY <= G + SRC_TABLE) by (unfold SRC_TABLE, SRC_ENTRY; lia).
  assert (NSC : forall a, (a < gP - DRAIN_K \/ gP <= a) -> ~ (errno_addr Bm <= a < errno_addr Bm + 4) ->
            ~ scratch_k Bm DRAIN_K regs a).
  { intros a H1 H3 [X|X]; [rewrite SPR in X; lia | exact (H3 X)]. }
  assert (GKa : forall a, (img_plain Bm a /\ ~ (G_BROKEN <= a < G_BROKEN + 1 \/ G_EINTR <= a < G_EINTR + 1 \/
                            G_OUTV + 8 <= a < G_OUTV + 32) /\
                           ~ (G_S + SRC_SIZE * Z.of_nat (snd (nth i hs no_hj)) + 12 <= a <
                              G_S + SRC_SIZE * Z.of_nat (snd (nth i hs no_hj)) + SRC_SIZE)) \/ gP <= a < 2 ^ 63 ->
            kb2 mem m2 a).
  { intros a [(P & NB & NH)|S].
    - pose proof (in_img_low Bm SEGS a (proj1 P)) as LOW.
      apply (rp_gkept _ _ _ L A regs mem md L' A' R2 m2 md' a M1 RP); [left; exact P | |].
      + intros X. destruct (gdr_notE_img _ _ _ _ _ _ L A mem md a M1 HO HGB SAlo SAhi (proj1 P) X) as [Y|Y];
          [exact (NB Y) | exact (NH Y)].
      + apply NSC; [left; unfold gP, DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK;
                    clear - LOW GSR1 ACV; lia |].
        destruct P as (_ & _ & _ & P4). exact P4.
    - pose proof (in_img_low Bm SEGS (errno_addr Bm) (IMGE (errno_addr Bm) ltac:(lia))) as LOW.
      apply (rp_gkept _ _ _ L A regs mem md L' A' R2 m2 md' a M1 RP); [right; unfold gP in S; lia | |].
      + intros X. pose proof (gdr_E_low _ _ _ _ _ _ L A mem md a M1 HO HGB SAlo SAhi J4 X). unfold gP in S. lia.
      + apply NSC; [right; exact (proj1 S) | unfold gP in S; lia]. }
  assert (GKc : forall a cs, rw_cells segs mem a cs ->
            (forall j, 0 <= j < Z.of_nat (cells_size cs) ->
               (img_plain Bm (a + j) /\ ~ (G_BROKEN <= a + j < G_BROKEN + 1 \/ G_EINTR <= a + j < G_EINTR + 1 \/
                                            G_OUTV + 8 <= a + j < G_OUTV + 32) /\
                ~ (G_S + SRC_SIZE * Z.of_nat (snd (nth i hs no_hj)) + 12 <= a + j <
                   G_S + SRC_SIZE * Z.of_nat (snd (nth i hs no_hj)) + SRC_SIZE)) \/ gP <= a + j < 2 ^ 63) ->
            rw_cells segs m2 a cs).
  { intros a cs Hc Hj. apply (rw_kb2 mem); [exact Hc|]. intros j Hj'. exact (GKa (a + j) (Hj j Hj')). }
  assert (GLOB : forall a, G_RELAY_LO <= a < G_S + SRC_SIZE * SOURCES_MAX ->
            ~ (G_BROKEN <= a < G_BROKEN + 1 \/ G_EINTR <= a < G_EINTR + 1 \/ G_OUTV + 8 <= a < G_OUTV + 32) ->
            ~ (G_S + SRC_SIZE * Z.of_nat (snd (nth i hs no_hj)) + 12 <= a <
               G_S + SRC_SIZE * Z.of_nat (snd (nth i hs no_hj)) + SRC_SIZE) ->
            (img_plain Bm a /\ ~ (G_BROKEN <= a < G_BROKEN + 1 \/ G_EINTR <= a < G_EINTR + 1 \/
                                   G_OUTV + 8 <= a < G_OUTV + 32) /\
             ~ (G_S + SRC_SIZE * Z.of_nat (snd (nth i hs no_hj)) + 12 <= a <
                G_S + SRC_SIZE * Z.of_nat (snd (nth i hs no_hj)) + SRC_SIZE)) \/ gP <= a < 2 ^ 63)
    by (intros a X1 X2 X3; left; split; [exact (IMGR a X1) | split; [exact X2 | exact X3]]).
  assert (BK : forall q, (send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT = true ->
                          q <> OUTc) ->
            ~ In q (entry_blocks (nth i es no_entry) ++ hs_blocks (fst (nth i hs no_hj))) -> q <> G ->
            bkept L A mem L' A' m2 q).
  { intros q Hq1 Hq2 Hq3. apply (rp_bkept _ _ _ L A regs mem md L' A' R2 m2 md' q M1 RP).
    - intros [(X & Y)|X]; [exact (Hq1 X Y) | exact (Hq2 X)].
    - intros k0 x Hin Hx. apply (gdr_notE_blk _ _ _ _ _ _ L A mem md q k0 x M1 Hin Hx J4); [| exact Hq2 |].
      + intros X Y. split; [exact (OB Y) | exact (Hq1 X)].
      + destruct (rig_blk_disj L A mem md q k0 G SRC_TABLE M1 Hin HGB Hq3) as [D|D];
          clear - D Hx Hi4; unfold SRC_TABLE, SRC_ENTRY in *; lia. }
  assert (NDR : forall q, In q (concat (map entry_blocks es_c) ++ concat (map srcblk (combine es hs_c))) ->
                  q <> G /\ q <> OUTc) by (intros q Hq; exact (gm_nd3 _ _ _ _ HND Hq)).
  assert (QN0 : forall q m, In (q, m) (blocks L0 A0) -> 0 < m -> ~ Fcur (Z.of_nat (length LB) + TOT) q ->
            send_live cl br dd (Z.of_nat (length LB) + TOT) = true -> q <> OUTc).
  { intros q m Hq Hm HF LVt.
    assert (HF0 : ~ Fcur (Z.of_nat (length LB)) q)
      by (intros X; apply HF; exact (FCM (Z.of_nat (length LB)) (Z.of_nat (length LB) + TOT) q ltac:(lia) ltac:(lia) X)).
    destruct (HSV q m Hq Hm HF0) as [_ X].
    destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV; [exact (X eq_refl)|].
    destruct (PL0 eq_refl) as (_ & _ & E3 & _). rewrite E3. intros E. apply HF. left. split; [exact LVt | exact E]. }
  assert (NFB : forall q, ~ Fcur (Z.of_nat (length LB) + TOT) q ->
            ~ In q (entry_blocks (nth i es no_entry) ++ hs_blocks (fst (nth i hs no_hj)))).
  { intros q HF X. apply HF. right. apply in_app_or in X as [X|X]; [left; exact (gdr_in_eb i q Hi X)|].
    right. exact (gdr_in_db i q Hi He X). }
  assert (CH0 : chain RELAY_INSTANCE_GONE_K Eall (Fcur (Z.of_nat (length LB) + TOT)) L0 A0 regs0 mem0 md0 L A mem md).
  { eapply chain_mono; [exact CH | intros a X; exact X |].
    intros q X. exact (FCM (Z.of_nat (length LB)) (Z.of_nat (length LB) + TOT) q ltac:(lia) ltac:(lia) X). }
  assert (CH' : chain RELAY_INSTANCE_GONE_K Eall (Fcur (Z.of_nat (length LB) + TOT)) L0 A0 regs0 mem0 md0 L' A' m2 md').
  { eapply chain_callee; [exact W0 | exact CH0 | exact RP | | | |].
    - intros a [X|X]; [left | right; exact X]. rewrite SPR in X. change (spZ regs0) with gS. rewrite KV.
      unfold gP, DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in *. lia.
    - intros a [X|X] Y; [|exfalso; apply Y; right; exact X].
      change (spZ regs0) with gS in X. rewrite KV in X. lia.
    - intros a X. split.
      + exact (gdr_E_low _ _ _ _ _ _ L A mem md a M1 HO HGB SAlo SAhi J4 X).
      + intros Hin. exact (gdr_E_Eall i _ _ _ _ _ L A mem md a Hi He M1 HO HGB SAlo SAhi Hin X).
    - intros p n0 H0 H1 Hn0 HF.
      destruct (chain_in _ _ _ _ _ _ _ _ _ _ _ _ p n0 W0 CH0 H0 HF) as [_ EA].
      assert (QB : In (ptr_addr L0 p, n0) (blocks L A)) by (apply rig_blocks_in; exists p; split; [exact EA | exact H1]).
      assert (QB0 : In (ptr_addr L0 p, n0) (blocks L0 A0)) by (apply rig_blocks_in; exists p; split; [reflexivity | exact H0]).
      assert (QN : send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT = true ->
                   ptr_addr L0 p <> OUTc) by (intros X; exact (QN0 _ _ QB0 Hn0 HF (LDV X))).
      pose proof (NFB _ HF) as Nbl.
      split; [intros [(X & Y)|X]; [exact (QN X Y) | exact (Nbl X)]|].
      intros x Hx NE X.
      assert (NSA : ~ (G + 56 * Z.of_nat i <= ptr_addr L0 p + x < G + 56 * Z.of_nat i + SRC_ENTRY)).
      { intros Y. destruct (Z.eq_dec (ptr_addr L0 p) G) as [Eq|Nq].
        - apply NE. unfold Eall. right. right. left. rewrite Eq in Y |- *. clear - Y Hi4. unfold SRC_TABLE, SRC_ENTRY in *. lia.
        - destruct (rig_blk_disj L A mem md _ n0 G SRC_TABLE M1 QB HGB Nq) as [D|D];
            clear - D Y Hx Hi4; unfold SRC_TABLE, SRC_ENTRY in *; lia. }
      exact (gdr_notE_blk _ _ _ _ _ _ L A mem md _ n0 x M1 QB Hx J4 (fun X Y => conj (OB Y) (QN X)) Nbl NSA X). }
  assert (LT : Z.of_nat (length (LB ++ LB2)) = Z.of_nat (length LB) + TOT)
    by (pose proof (f_equal (@length Z) LBE) as LL; rewrite gdr_len_bzs in LL; rewrite length_app, LL, ETOT; lia).
  assert (LR : length (firstn i hs_c ++ h2 :: skipn (S i) hs_c) = length es) by (rewrite gdr_len_rep by lia; exact HLH).
  assert (XEQ : forall j, (j < length (map entry_blocks es_c))%nat -> j <> i ->
            nth j (map entry_blocks (firstn i es_c ++ e2 :: skipn (S i) es_c)) [] = nth j (map entry_blocks es_c) []).
  { intros j Hj Ne. rewrite !gdr_nth_eb, gdr_nth_rep by lia. rewrite (proj2 (Nat.eqb_neq j i) Ne). reflexivity. }
  assert (YEQ : forall j, (j < length (map entry_blocks es_c))%nat -> j <> i ->
            nth j (map srcblk (combine es (firstn i hs_c ++ h2 :: skipn (S i) hs_c))) [] =
            nth j (map srcblk (combine es hs_c)) []).
  { intros j Hj Ne. rewrite length_map in Hj.
    rewrite (gdr_nth_sb _ j LR ltac:(lia)), (gdr_nth_sb hs_c j HLH ltac:(lia)).
    rewrite gdr_nth_rep by lia. rewrite (proj2 (Nat.eqb_neq j i) Ne). reflexivity. }
  rewrite (proj2 (BTA 0%nat _)) in OLK, ELK, SLK.
  assert (NDO : forall j' x, (j' < length es)%nat -> j' <> i ->
            In x (entry_blocks (nth j' es_c no_entry) ++ srcblk (nth j' es no_entry, nth j' hs_c (fst no_hj))) ->
            x <> G /\ x <> OUTc /\ ~ In x (entry_blocks (nth i es no_entry) ++ hs_blocks (fst (nth i hs no_hj)))).
  { intros j' x Hj' Ne Hx.
    rewrite <- gdr_nth_eb, <- (gdr_nth_sb hs_c j' HLH Hj') in Hx.
    destruct (gdr_nodup_other G OUTc (map entry_blocks es_c) (map srcblk (combine es hs_c)) i j' x
                ltac:(rewrite !length_map, length_combine; lia) Ne (proj1 (gdr_nd _) HND) Hx) as (X1 & X2 & X3).
    rewrite gdr_nth_eb, (gdr_nth_sb hs_c i HLH Hi), Ee in X3.
    rewrite (nth_indep hs_c (fst no_hj) (fst (nth i hs no_hj))) in X3 by lia. rewrite Eh, (gdr_sb0 _ _ He) in X3.
    split; [exact X1|]. split; [exact X2 | exact X3]. }
  (* a block of another source, live before the drain, stays live *)
  assert (LKO : forall j a p n, (j < length es)%nat -> j <> i ->
            In a (entry_blocks (nth j es_c no_entry) ++ srcblk (nth j es no_entry, nth j hs_c (fst no_hj))) ->
            (exists k0, In (a, k0) (blocks L A) /\ 0 < k0) -> live_at L A p a n -> live_at L' A' p a n).
  { intros j a p n Hj Ne Ha (k0 & Hk & Pk) LA. destruct (NDO j a Hj Ne Ha) as (_ & X2 & X3).
    apply (gd_live_keep _ _ _ L A regs mem md L' A' R2 m2 md' p a n k0 RP NDA Hk Pk); [|exact LA].
    intros [(_ & Y)|Y]; [exact (X2 Y) | exact (X3 Y)]. }
  (* the names of the source's blocks that the drain keeps *)
  pose proof PLK as (_ & PSL). destruct (PSL He) as (PS1 & _ & PS3 & _ & PS5 & PS6).
  assert (N1 : 0 < hl_cap (hs_pending h2) -> sptr_of L A (hl_v (hs_pending h2)) = sptr_of L0 A0 (hl_v (hs_pending h2))).
  { intros Hc. rewrite PC2 in Hc. rewrite PV2. exact (CF.gestures_end_b.p3b_sptr_of_eq L A _ _ _ NDA (PS1 Hc)). }
  assert (N2 : sptr_of L A (hs_partial h2) = sptr_of L0 A0 (hs_partial h2)).
  { rewrite PP2. exact (CF.gestures_end_b.p3b_sptr_of_eq L A _ _ _ NDA PS3). }
  assert (N3 : 0 < hl_cap (hs_held h2) -> sptr_of L A (hl_v (hs_held h2)) = sptr_of L0 A0 (hl_v (hs_held h2))).
  { rewrite HLD2. intros Hc. exact (CF.gestures_end_b.p3b_sptr_of_eq L A _ _ _ NDA (PS5 Hc)). }
  assert (N4 : Forall (fun r => sptr_of L A (fst r) = sptr_of L0 A0 (fst r)) (hl_recs (hs_held h2))).
  { rewrite HLD2. eapply Forall_impl; [|exact PS6]. intros r X. exact (CF.gestures_end_b.p3b_sptr_of_eq L A _ _ _ NDA X). }
  assert (KH : re_hp e2 <> 0 -> 8 <= re_kh e2).
  { intros Hh. pose proof EOK2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPC & _).
    destruct HPC as [(X & _)|(_ & _ & _ & X & _)]; [contradiction | exact X]. }
  assert (LKA : length (da_keys (drain_adr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry)
                                  (fst (nth i hs no_hj)) (nretF k)
                                  (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj))))) =
                length (ds_H (drain_fin glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry)
                                (fst (nth i hs no_hj))))).
  { pose proof (gsh_after glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry) (fst (nth i hs no_hj))
                  (nretF k) (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj)))) as X.
    unfold after_drain_adr, after_drain in X. rewrite He in X. change (0 =? 0) with true in X. cbv beta iota in X.
    apply X. unfold drain_start. cbn [da_keys]. apply length_map. }
  assert (LKS : length (keys_texts (re_keys e2)) =
                length (da_keys (drain_adr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry)
                                  (fst (nth i hs no_hj)) (nretF k)
                                  (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj))))))
    by (rewrite DH, SH; symmetry; exact LKA).
  (* with sends off in the drain, g_out keeps its address *)
  assert (DOUT : send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT = false ->
                 da_out (drain_adr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry)
                           (fst (nth i hs no_hj)) (nretF k)
                           (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj)))) = oa).
  { intros LDf. rewrite <- (proj2 (BTA (nretF k) (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj))))).
    rewrite LDf, gd_adr_out_false. reflexivity. }
  assert (CUR : inner_cur i (keys_texts (re_keys e2)) 0 (keys_texts (re_keys e2)) []
                  (da_keys (drain_adr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry)
                              (fst (nth i hs no_hj)) (nretF k)
                              (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj)))))
                  (drain_adr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry)
                     (fst (nth i hs no_hj)) (nretF k) (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj))))
                  (combine (keys_texts (re_keys e2))
                     (da_keys (drain_adr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry)
                                 (fst (nth i hs no_hj)) (nretF k)
                                 (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj))))))
                  L' A' (qd ++ qdr) e2 h2).
  { unfold inner_cur.
    split.
    { unfold done0. cbv zeta. rewrite He.
      split; [exact FD2|].
      split; [rewrite EOF2; change (re_eof (with_keys (nth i es no_entry) ks)) with (re_eof (nth i es no_entry));
              rewrite He; reflexivity|].
      split; [exact NDK2|].
      split; [rewrite gdr_el0 by exact He; exact SS2|].
      split.
      { intros _. rewrite gdr_el0 by exact He.
        split; [exact HFD2|]. split; [exact HCL2|]. split; [exact HEI2|]. split; [exact PND2|].
        split; [exact PC2|]. split; [exact PV2|]. split; [exact OFF2|].
        split; [exact ST2|]. split; [exact EXP2|]. split; [exact EXF2|]. split; [exact HLD2|]. split; [exact PP2|].
        split; [exact SK2 | exact SU2]. }
      split; [intros X; discriminate X|].
      unfold dsrel. cbv zeta. rewrite GS.
      split; [rewrite DH; exact SH|].
      split; [rewrite DCAP; exact SC|].
      split; [rewrite DU; exact SU'|].
      split; [rewrite DSK, SS'; reflexivity|].
      split; [rewrite DKA; exact SK'|].
      intros _. split; [rewrite DEC; exact SE | exact DECB]. }
    split; [reflexivity|]. split; [lia|]. split; [intros n Hn; lia|].
    split; [unfold gei; rewrite Nat.sub_0_r; cbn [app]; apply surjective_pairing|].
    split; [exact (gsh_combine_fst _ _ LKS)|].
    split; [symmetry; exact LKS|].
    split; [exists []; split; [reflexivity|]; unfold geia; rewrite Nat.sub_0_r; cbn [app]; apply surjective_pairing|].
    split.
    - intros post. rewrite (gd_combine_snd _ _ LKS), <- app_assoc.
      destruct (SIM qdr post LQd) as (_ & _ & _ & DS).
      exact (gd_entry_post L' A' (qd ++ qdr ++ post) qdr _ _ e2 _ ELK DS (eq_trans DCAP SC) (eq_trans DKA SK') KH).
    - intros _ post. rewrite <- app_assoc. destruct (SIM qdr post LQd) as (_ & _ & _ & DS).
      exact (gd_src_post L A L' A' (qd ++ qdr ++ post) qdr _ _ h2 _ SLK DS (eq_trans DEC SE) N1 N2 N3 N4). }
  exists R2, L', A', m2, md',
    (k ++ drain_tr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry) (fst (nth i hs no_hj))
            (nretF k) (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj)))),
    (qd ++ qdr),
    (firstn i es_c ++ e2 :: skipn (S i) es_c),
    (firstn i hs_c ++ h2 :: skipn (S i) hs_c), (LB ++ LB2), OUT',
    (if send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT then CAP' else CAPc),
    (if send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT then junk' else junkc),
    (keys_texts (re_keys e2)),
    (da_keys (drain_adr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry)
                (fst (nth i hs no_hj)) (nretF k) (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj))))),
    (drain_adr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry)
       (fst (nth i hs no_hj)) (nretF k) (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj)))).
  split; [reflexivity|]. split; [exact RPr|].
  unfold GI. cbv zeta. rewrite LT.
  split; [exact (eq_trans (RPr 2 ltac:(unfold callee_saved; lia)) G2)|].
  split; [exact (eq_trans (RPr 3 ltac:(unfold callee_saved; lia)) G3)|].
  split; [exact (eq_trans (RPr 4 ltac:(unfold callee_saved; lia)) G4)|].
  split; [exact (eq_trans (RPr 8 ltac:(unfold callee_saved; lia)) G8)|].
  split; [exact (eq_trans (RPr 22 ltac:(unfold callee_saved; lia)) G22)|].
  split; [exact CH'|]. split; [exact INIT'|].
  split; [split; [exact RP1|]; split; [exact RP2 | exact RES']|].
  split.
  { assert (NOM' : gNO + (Z.of_nat (length LB) + TOT) =
                   ds_no (drain_fin glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc
                            (nth i es no_entry) (fst (nth i hs no_hj)))) by (rewrite BNO; ring).
    assert (CAPM' : (if send_live cl br dd (Z.of_nat (length LB) + TOT) then
                      (if send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT then CAP'
                       else CAPc) else gCAP) =
                    ds_ocap (drain_fin glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc
                               (nth i es no_entry) (fst (nth i hs no_hj)))).
    { destruct (send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT) eqn:LD.
      - rewrite (LDV eq_refl). destruct (LIVE2 eq_refl) as (_ & LAc & _). rewrite LAc. exact (BOC1 eq_refl).
      - rewrite (BOC0 eq_refl). destruct (send_live cl br dd (Z.of_nat (length LB) + TOT)) eqn:LV'; [reflexivity|].
        assert (LV0 : send_live cl br dd (Z.of_nat (length LB)) = false)
          by (destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:X; [discriminate (LVM eq_refl) | reflexivity]).
        destruct (PL0 LV0) as (_ & _ & _ & X & _). rewrite X. reflexivity. }
    unfold gpos.
    exists (da_out (drain_adr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry)
                      (fst (nth i hs no_hj)) (nretF k) (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj))))),
      ssd, dsd.
    split; [exact Lssd|]. split; [exact Ldsd|].
    split.
    { rewrite EQ, NOM', CAPM', DH, SH.
      unfold gpos_k. cbv beta zeta. rewrite GS.
      generalize (drain_tr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry)
                    (fst (nth i hs no_hj)) (nretF k) (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj))))
        as tdg.
      generalize (drain_adr glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry)
                    (fst (nth i hs no_hj)) (nretF k) (drain_start gnm oa (nth i es no_entry) (fst (nth i hs no_hj))))
        as fag.
      generalize (drain_fin glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry)
                    (fst (nth i hs no_hj))) as fsg.
      intros fsg fag tdg.
      unfold gxks, gkept, gmx, gps. cbn [fst snd app].
      rewrite !nret_app. change (nretF []) with 0%nat.
      rewrite !Nat.add_0_r, <- !app_assoc. reflexivity. }
    split.
    { intros LVt post. rewrite <- app_assoc.
      destruct (send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT) eqn:LD.
      - destruct (LIVE2 eq_refl) as (LA1 & LA2 & _).
        assert (TP : 0 < TOT)
          by (destruct (Z.eq_dec TOT 0) as [T0|T0]; [exfalso; pose proof (LVZ T0); congruence | lia]).
        assert (OC : ds_ocap (drain_fin glv (bv_unsigned mx) (gNO + Z.of_nat (length LB)) CAPc (nth i es no_entry)
                                (fst (nth i hs no_hj))) <> 0) by (rewrite <- (BOC1 eq_refl), <- LA2; lia).
        destruct (SIM qdr post LQd) as (_ & _ & _ & (D1 & _)).
        pose proof (D1 OC) as X. unfold gd_R in X. rewrite X. exact (OLK eq_refl).
      - destruct (LVD LVt eq_refl) as [LV0 T0].
        rewrite (DOUT eq_refl).
        destruct (DEAD2 eq_refl) as (_ & _ & EO'). rewrite EO'.
        destruct (HLIVE LV0) as (H1 & H2 & _).
        pose proof (gm_live_nz _ LV0) as TNZ.
        assert (CP0 : 0 < CAPc) by (pose proof (bv_unsigned_in_range 64 nout) as X; unfold gNO in H1; lia).
        apply (gd_live_keep _ _ _ L A regs mem md L' A' R2 m2 md' _ OUTc CAPc CAPc RP NDA H2 CP0);
          [|exact (OLV LV0 (qdr ++ post))].
        intros [(X & _)|X]; [congruence | exact (proj2 (gm_nd3 _ _ _ _ (proj2 (gdr_nd _) NDi) X) eq_refl)]. }
    split.
    { intros LVf.
      assert (LD : send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT = false)
        by (destruct (send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT) eqn:X;
            [rewrite (LDV eq_refl) in LVf; discriminate LVf | reflexivity]).
      assert (LV0 : send_live cl br dd (Z.of_nat (length LB)) = false)
        by (destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:X;
            [rewrite (LVM eq_refl) in LVf; discriminate LVf | reflexivity]).
      rewrite (DOUT LD). destruct (ODD LV0) as (EO & OL). split; [exact EO|].
      intros Hc. destruct (HDEAD LV0) as (_ & E1 & E2 & H3).
      apply (gd_live_keep _ _ _ L A regs mem md L' A' R2 m2 md' _ gOUT gCAP gCAP RP NDA (proj1 (H3 Hc)) Hc);
        [|exact (OL Hc)].
      intros [(X & _)|X]; [congruence|]. rewrite <- E1 in X.
      exact (proj2 (gm_nd3 _ _ _ _ (proj2 (gdr_nd _) NDi) X) eq_refl). }
    intros j Hj post. rewrite !gdr_nth_rep by lia. rewrite (proj2 (Nat.eqb_neq j i) ltac:(lia)). cbv beta iota.
    rewrite <- app_assoc.
    assert (Hj' : (j < length es)%nat) by lia. assert (Ne : j <> i) by lia.
    assert (Hjc : (j < length es_c)%nat) by lia.
    destruct (DLK j Hj (qdr ++ post)) as (DE & DS).
    split.
    - apply (gk_entry_mono L A L' A'); [|exact DE]. intros p a n Ha LA.
      apply (LKO j a p n Hj' Ne (in_or_app _ _ _ (or_introl Ha))); [|exact LA].
      exact (gdr_eblk L A mem _ a (proj1 (Forall_forall _ _) HEOK _ (nth_In es_c no_entry Hjc)) Ha).
    - intros He'. apply (gk_src_mono L A L' A'); [|exact (DS He')]. intros p a n Ha LA.
      apply (LKO j a p n Hj' Ne); [| exact (gdr_hblk L A mem _ _ a (HSRC j Hj' He') Ha) | exact LA].
      apply in_or_app. right.
      rewrite (gdr_sb0 _ _ He'), (nth_indep hs_c (fst no_hj) (fst (nth j hs no_hj))) by lia. exact Ha. }
  split.
  { intros q m Hq.
    destruct (BACK2 q m Hq) as [(Hq0 & NO1 & NE1 & NH1')|[X|X]].
    - destruct (POT q m Hq0) as [Y|[Y|[Y|Y]]].
      + left. exact Y.
      + right; left. apply (gdr_in_rep2 (map entry_blocks es_c) _ i q);
          [rewrite !length_map, gdr_len_rep by lia; reflexivity | exact XEQ | exact Y |].
        rewrite gdr_nth_eb, Ee. exact NE1.
      + right; right; left. apply (gdr_in_rep2 (map srcblk (combine es hs_c)) _ i q);
          [rewrite !length_map, !length_combine, gdr_len_rep by lia; reflexivity | | exact Y |].
        * intros j Hj Ne. rewrite !length_map, length_combine in Hj. apply (YEQ j ltac:(rewrite length_map; lia) Ne).
        * rewrite (gdr_nth_sb hs_c i HLH Hi), (nth_indep hs_c (fst no_hj) (fst (nth i hs no_hj))) by lia.
          rewrite Eh, (gdr_sb0 _ _ He). exact NH1'.
      + exfalso. exact (NO1 Y).
    - apply in_app_or in X as [X|X].
      + right; left. apply (rigl_in_nth_concat _ i). rewrite gdr_nth_eb, gdr_nth_rep by lia. rewrite Nat.eqb_refl. exact X.
      + right; right; left. apply (rigl_in_nth_concat _ i). rewrite (gdr_nth_sb _ i LR Hi), gdr_nth_rep by lia.
        rewrite Nat.eqb_refl, (gdr_sb0 _ _ He). exact X.
    - right; right; right. exact X. }
  split; [exact RA2|].
  split; [apply (GKc _ _ GL); intros j Hj; cbn in Hj; apply GLOB; pose proof J4;
          unfold G_LOCK, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, G_BROKEN, G_EINTR, G_OUTV; lia|].
  split; [apply (GKc _ _ HNS); intros j Hj; cbn in Hj; apply GLOB; pose proof J4;
          unfold G_NSRC, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, G_BROKEN, G_EINTR, G_OUTV; lia|].
  split; [apply (GKc _ _ HGS); intros j Hj; cbn in Hj; apply GLOB; pose proof J4;
          unfold G_SRC, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, G_BROKEN, G_EINTR, G_OUTV; lia|].
  split; [exact GB2|].
  split; [exact CCL2|]. split; [exact CBR2|]. split; [exact CDD2|]. split; [exact CEI2|]. split; [exact CERR2|].
  split.
  { intros j Hj. apply (GKc _ _ (SRCH' j Hj)). intros x Hx. cbn in Hx. apply GLOB; pose proof J4;
      unfold G_S, SRC_SIZE, SOURCES_MAX, G_RELAY_LO, G_BROKEN, G_EINTR, G_OUTV; lia. }
  split; [apply (GKc _ _ FR0); intros j Hj; cbn in Hj; right; unfold gP in *; lia|].
  split; [destruct FRB as (jb & Hjb); exists jb; apply (GKc _ _ Hjb); intros j Hj; cbn in Hj; right; unfold gP in *; lia|].
  split; [apply (GKc _ _ FRS); intros j Hj; unfold saved_cells in Hj; cbn in Hj; right; unfold gP in *; lia|].
  split; [rewrite gdr_len_rep by lia; exact HLE|].
  split.
  { exists tl. destruct HTAB as [Htl Htr]. split; [rewrite gdr_len_rep by lia; exact Htl|].
    assert (HL56 : Forall (fun e => length (entry_bytes e) = 56%nat) es_c).
    { apply Forall_forall. intros x Hx. exact (gdr_okk_len _ _ _ _ (proj1 (Forall_forall _ _) HEOK x Hx)). }
    destruct (rig_concat_nth es_c i Hic HL56) as [EC LP].
    rewrite gdr_rep_concat. rewrite EC, <- !app_assoc in Htr. rewrite <- !app_assoc.
    rewrite Ee in Htr.
    apply (gdr_splice mem m2 G 896 _ (entry_bytes (nth i es no_entry)) (entry_bytes e2) _ Htr).
    - rewrite LP, EL56. replace (G + Z.of_nat (56 * i)) with (G + 56 * Z.of_nat i) by lia.
      exact ENT2.
    - intros x Hx Hn. rewrite LP, EL56 in Hn.
      apply (gdr_rp_kb2 _ _ _ L A regs mem md L' A' R2 m2 md' G SRC_TABLE x M1 RP HGB).
      + intros [(X & Y)|X]; [exact (gm_nd_ab _ _ _ HND Y) |].
        exact (proj1 (gm_nd3 _ _ _ _ (proj2 (gdr_nd _) NDi) X) eq_refl).
      + unfold SRC_TABLE, SRC_ENTRY. lia.
      + apply (gdr_notE_blk _ _ _ _ _ _ L A mem md G SRC_TABLE x M1 HGB ltac:(unfold SRC_TABLE, SRC_ENTRY; lia) J4).
        * intros X Y. split; [exact (OB Y) | exact (gm_nd_ab _ _ _ HND)].
        * intros X. apply in_app_or in X as [X|X].
          -- exact (proj1 (gm_nd3 _ _ _ _ (proj2 (gdr_nd _) NDi) (in_or_app _ _ _ (or_introl X))) eq_refl).
          -- exact (proj1 (gm_nd3 _ _ _ _ (proj2 (gdr_nd _) NDi) (in_or_app _ _ _ (or_intror X))) eq_refl).
        * clear - Hn Hx. unfold SRC_ENTRY. lia. }
  split.
  { apply (gdr_forall_rep _ es_c i e2 no_entry Hic (entry_okk_of _ _ _ _ EOK2)).
    intros j' Hj' Ne.
    apply (entry_okk_kept L A mem L' A' m2 md'); [exact (proj1 (Forall_forall _ _) HEOK _ (nth_In _ _ Hj')) | exact M2 |].
    intros q Hq. destruct (NDO j' q ltac:(lia) Ne ltac:(apply in_or_app; left; exact Hq)) as (X1 & X2 & X3).
    apply BK; [intros _; exact X2 | exact X3 | exact X1]. }
  split; [rewrite gdr_len_rep by lia; exact HLH|]. split; [exact HLK|]. split; [exact HIL|].
  split.
  { intros j' Hj' He'. rewrite gdr_nth_rep by lia. destruct (Nat.eqb_spec j' i) as [->|Ne]; [exact SRC2|].
    pose proof (gdr_src_lt4 j' Hj' He') as J4'. pose proof (gdr_src_ne j' i Hj' Hi Ne He' He) as SNE.
    apply (src_at_kept L A mem L' A' m2); [exact (HSRC j' Hj' He') | |].
    - intros x Hx. apply GKa. apply GLOB; unfold gHA, G_S, SRC_SIZE, SOURCES_MAX, G_RELAY_LO, G_BROKEN, G_EINTR, G_OUTV;
        clear - Hx J4 J4' SNE; lia.
    - intros q Hq.
      assert (Hq' : In q (entry_blocks (nth j' es_c no_entry) ++ srcblk (nth j' es no_entry, nth j' hs_c (fst no_hj)))).
      { apply in_or_app. right. rewrite (gdr_sb0 _ _ He').
        rewrite (nth_indep hs_c (fst no_hj) (fst (nth j' hs no_hj))) by lia. exact Hq. }
      destruct (NDO j' q Hj' Ne Hq') as (X1 & X2 & X3).
      apply BK; [intros _; exact X2 | exact X3 | exact X1]. }
  split.
  { intros j' Hj'. rewrite !gdr_nth_rep by lia. rewrite (proj2 (Nat.eqb_neq j' i) ltac:(lia)). exact (HDONE j' Hj'). }
  split.
  { intros _. rewrite !gdr_nth_rep by lia. rewrite Nat.eqb_refl. exact CUR. }
  split.
  { intros j' Hj'. rewrite !gdr_nth_rep by lia. rewrite (proj2 (Nat.eqb_neq j' i) ltac:(lia)). cbv beta iota.
    assert (Ne : j' <> i) by lia. assert (Hj'' : (j' < length es)%nat) by lia.
    assert (Hjc : (j' < length es_c)%nat) by lia.
    destruct (HPEND j' Hj') as (P1 & P2 & PE & PS).
    split; [exact P1|]. split; [exact P2|]. split.
    - apply (gk_entry_mono L A L' A'); [|exact PE]. intros p a n Ha LA.
      apply (LKO j' a p n Hj'' Ne (in_or_app _ _ _ (or_introl Ha))); [|exact LA].
      exact (gdr_eblk L A mem _ a (proj1 (Forall_forall _ _) HEOK _ (nth_In es_c no_entry Hjc)) Ha).
    - intros He'. assert (He2 : re_eof (nth j' es no_entry) = 0) by (rewrite <- P1; exact He').
      apply (gk_src_mono L A L' A'); [|exact (PS He')]. intros p a n Ha LA.
      apply (LKO j' a p n Hj'' Ne); [| exact (gdr_hblk L A mem _ _ a (HSRC j' Hj'' He2) Ha) | exact LA].
      apply in_or_app. right.
      rewrite (gdr_sb0 _ _ He2), (nth_indep hs_c (fst no_hj) (fst (nth j' hs no_hj))) by lia. exact Ha. }
  split.
  { apply gdr_nd.
    apply (gdr_nodup_replace G OUTc OUT' (map entry_blocks es_c) (map srcblk (combine es hs_c)) _ _ i).
    - rewrite length_map. lia.
    - rewrite !length_map, length_combine. lia.
    - rewrite !length_map. rewrite gdr_len_rep by lia. reflexivity.
    - rewrite !length_map, !length_combine. rewrite gdr_len_rep by lia. lia.
    - intros j Hj Ne. split; [exact (XEQ j Hj Ne) | exact (YEQ j Hj Ne)].
    - exact (proj1 (gdr_nd _) HND).
    - rewrite gdr_nth_eb, (gdr_nth_sb _ i LR Hi), !gdr_nth_rep by lia.
      rewrite Nat.eqb_refl. rewrite (gdr_sb0 _ _ He). exact (proj1 (gdr_nd _) ND2).
    - intros x Hx Hn Hb.
      rewrite gdr_nth_eb, (gdr_nth_sb hs_c i HLH Hi), Ee in Hn.
      rewrite (nth_indep hs_c (fst no_hj) (fst (nth i hs no_hj))) in Hn by lia. rewrite Eh, (gdr_sb0 _ _ He) in Hn.
      rewrite gdr_nth_eb, (gdr_nth_sb _ i LR Hi), !gdr_nth_rep by lia.
      rewrite Nat.eqb_refl, (gdr_sb0 _ _ He).
      destruct (gm_R_pos L A mem es_c hs_c x HLH HEOK HSRC Hx) as (k0 & Hk0 & Pk0).
      destruct (FRS2 x k0 Hk0 Pk0 Hb Hn) as (Y1 & Y2 & Y3).
      intros [Y|Y]; [exact (Y1 (eq_sym Y))|]. apply in_app_or in Y as [Y|Y]; [exact (Y2 Y) | exact (Y3 Y)]. }
  split.
  { intros q m Hq0 H1 H3 H4. pose proof (HSUR q m Hq0 H1 H3 H4) as Hq.
    apply (gm_keep _ _ _ L A regs mem md L' A' R2 m2 md' q m M1 RP Hq).
    assert (HF : ~ Fcur (Z.of_nat (length LB) + TOT) q)
      by (intros [(_ & E)|[E|E]]; [exact (H1 E) | exact (H3 E) | exact (H4 E)]).
    intros Hm [(X & Y)|X]; [exact (QN0 q m Hq0 Hm HF (LDV X) Y) | exact (NFB q HF X)]. }
  split.
  { intros q m Hq0 Hm HF.
    destruct (HSV q m Hq0 Hm (fun X => HF (FCM (Z.of_nat (length LB)) (Z.of_nat (length LB) + TOT) q
                                          ltac:(lia) ltac:(lia) X))) as [X1 X2].
    pose proof (NFB q HF) as Nbl.
    assert (KEY : (send_live cl br dd (Z.of_nat (length LB) + TOT) = true -> q <> OUT') /\ ~ In q (entry_blocks e2) /\
                  ~ In q (hs_blocks h2)).
    { destruct (Z.eq_dec q OUTc) as [Eq|Nq].
      - assert (LV0 : send_live cl br dd (Z.of_nat (length LB)) = false)
          by (destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:X; [exfalso; exact (X2 eq_refl Eq) | reflexivity]).
        destruct (PL0 LV0) as (_ & _ & E3 & _).
        assert (LVf : send_live cl br dd (Z.of_nat (length LB) + TOT) = false)
          by (destruct (send_live cl br dd (Z.of_nat (length LB) + TOT)) eqn:X;
              [exfalso; apply HF; left; split; [exact X | congruence] | reflexivity]).
        assert (LD : send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT = false)
          by (destruct (send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT) eqn:X;
              [rewrite (LDV eq_refl) in LVf; discriminate LVf | reflexivity]).
        destruct (DEAD2 LD) as (_ & _ & EO').
        pose proof (proj1 (gdr_nd _) ND2) as ND2'. apply List.NoDup_cons_iff in ND2' as [_ ND2'].
        apply List.NoDup_cons_iff in ND2' as [NO' _].
        rewrite EO', <- Eq in NO'. split; [intros LVt; rewrite LVf in LVt; discriminate LVt|].
        split; intros Y; apply NO'; apply in_or_app; [left | right]; exact Y.
      - assert (QA : In (q, m) (blocks L A)).
        { apply HSUR; [exact Hq0 | | intros E; apply HF; right; left; exact E | intros E; apply HF; right; right; exact E].
          intros E. destruct (send_live cl br dd (Z.of_nat (length LB) + TOT)) eqn:LV'.
          - apply HF. left. split; [exact LV' | exact E].
          - assert (LV0 : send_live cl br dd (Z.of_nat (length LB)) = false)
              by (destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:X; [discriminate (LVM eq_refl) | reflexivity]).
            destruct (PL0 LV0) as (_ & _ & E3 & _). apply Nq. congruence. }
        destruct (FRS2 q m QA Hm Nq Nbl) as (F1 & F2 & F3). split; [intros _; exact F1|]. split; assumption. }
    destruct KEY as (K1 & K2 & K3).
    split.
    - intros Y. apply in_app_or in Y as [Y|Y].
      + destruct (gdr_in_rep (map entry_blocks es_c) (map entry_blocks (firstn i es_c ++ e2 :: skipn (S i) es_c)) i q
                    ltac:(rewrite !length_map, gdr_len_rep by lia; reflexivity)
                    XEQ Y) as [Z1|Z1]; [exact (X1 (in_or_app _ _ _ (or_introl Z1)))|].
        rewrite gdr_nth_eb, gdr_nth_rep in Z1 by lia. rewrite Nat.eqb_refl in Z1. exact (K2 Z1).
      + destruct (gdr_in_rep (map srcblk (combine es hs_c)) (map srcblk (combine es (firstn i hs_c ++ h2 :: skipn (S i) hs_c)))
                    i q
                    ltac:(rewrite !length_map, !length_combine, gdr_len_rep by lia; reflexivity)
                    ltac:(intros j Hj Ne; rewrite !length_map, length_combine in Hj;
                          apply (YEQ j ltac:(rewrite length_map; lia) Ne)) Y) as [Z1|Z1];
          [exact (X1 (in_or_app _ _ _ (or_intror Z1)))|].
        rewrite (gdr_nth_sb _ i LR Hi), gdr_nth_rep in Z1 by lia.
        rewrite Nat.eqb_refl, (gdr_sb0 _ _ He) in Z1. exact (K3 Z1).
    - exact K1. }
  split.
  { unfold bzs in HLB, LBE |- *. rewrite map_app, HLB, LBE. unfold part_of. cbn [map concat]. rewrite !app_nil_r.
    unfold lines_of. rewrite gdr_el0 by exact He. reflexivity. }
  split.
  { assert (PLi : pl_of i = Z.of_nat (length (pending_stream (fst (nth i hs no_hj)))))
      by (unfold pl_of; rewrite He; reflexivity).
    unfold bound_in. rewrite PLi. cbn [length]. clear - HT TOTB. lia. }
  split.
  { intros LVf.
    assert (LD : send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT = false)
      by (destruct (send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT) eqn:X;
          [rewrite (LDV eq_refl) in LVf; discriminate LVf | reflexivity]).
    assert (LV0 : send_live cl br dd (Z.of_nat (length LB)) = false)
      by (destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:X;
          [rewrite (LVM eq_refl) in LVf; discriminate LVf | reflexivity]).
    rewrite LD. cbv iota.
    destruct (PL0 LV0) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    destruct (DEAD2 LD) as (EOV & EBK & EO').
    rewrite E5, E6, E7 in EOV. rewrite E2, E8 in EBK.
    split; [exact EOV|]. split; [rewrite EO'; exact E3|]. split; [exact E4|].
    intros Hc. rewrite <- E3, <- E4. apply EBK. rewrite E4. exact Hc. }
  intros LVt.
  destruct (send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd TOT) eqn:LD; cbv iota.
  - destruct (LIVE2 eq_refl) as (LA1 & _ & LA2 & LA3 & LA4 & LA5 & LA6).
    destruct (NOEQ eq_refl) as (EN & EO).
    rewrite EN in LA1, LA5, LA6. rewrite EO in LA4.
    split; [lia|]. split; [exact LA2|]. split; [exact LA3|].
    split; [rewrite <- !app_assoc in LA4; rewrite <- !app_assoc; exact LA4|]. split; [lia|].
    replace (gNO + (Z.of_nat (length LB) + TOT)) with (gNO + Z.of_nat (length LB) + TOT) by ring. exact LA6.
  - destruct (LVD LVt eq_refl) as [LV0 T0].
    destruct (PL1 LV0) as (E1 & E2 & E3 & E4 & E5 & E6).
    destruct (DEAD2 eq_refl) as (EOV & EBK & EO').
    destruct (HLIVE LV0) as (H1 & H2 & H3 & H4 & H5 & H6).
    pose proof (gm_live_nz _ LV0) as TNZ.
    assert (EL2 : LB2 = []).
    { apply length_zero_iff_nil. pose proof (f_equal (@length Z) LBE) as LL. rewrite gdr_len_bzs in LL.
      rewrite LL. rewrite ETOT in T0. lia. }
    rewrite EL2, app_nil_r, EO'. rewrite T0, Z.add_0_r.
    destruct (EBK ltac:(lia)) as [BB1 BB2]. rewrite E2, E6 in BB2.
    split; [exact H1|]. split; [exact BB1|]. split; [exact H3|].
    split; [rewrite <- app_assoc in BB2; exact BB2|]. split; [exact H5|].
    rewrite E3, E4, E5 in EOV. exact EOV.
Qed.

Lemma gone_drain : forall i c, (i < length es)%nat -> AT_TOP i c -> SR segs c (AT_C i).
Proof.
  intros i c Hi (fx & regs & L & A & mem & md & k & qd & es_c & hs_c & kss & LB & OUTc & CAPc & junkc & -> & FRM & RGS & HG).
  destruct (RGS ltac:(lia)) as (R18 & R19 & R23). clear RGS.
  replace (Nat.ltb i (length es)) with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  pose proof HG as HG0.
  destruct HG0 as (G2 & G3 & G4 & G8 & G22 & CH & _ & _ & _ & _ & RA & _ & _ & HGS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & HLE & HTAB & HEOK & _ & _ & _ & _ & _ & HCUR & _).
  pose proof CH as (M1 & _).
  destruct (mr_model Bm MR rig_laws L A mem md M1) as (Hh & Hl & _).
  destruct (HCUR Hi) as (Ee & Eh & _).
  assert (Hi' : (i < length es_c)%nat) by lia.
  destruct HTAB as (tl & HTAB).
  pose proof (gdr_tab_mid L A mem es_c tl i Hi' HEOK HTAB) as ENT.
  pose proof (proj1 (Forall_forall _ _) HEOK _ (nth_In es_c no_entry Hi')) as OKK.
  rewrite Ee in ENT, OKK.
  destruct (gdr_okk_facts _ _ _ _ OKK) as (Hp1 & EOF01).
  assert (FE : rw_cells segs mem (G + 56 * Z.of_nat i)
                 [C4 (Z_to_bv 64 (re_fd (nth i es no_entry))); C4 (Z_to_bv 64 (re_eof (nth i es no_entry)))]).
  { apply (gdr_cb_c44 mem _ 56 (entry_bytes (nth i es no_entry))); [exact ENT | lia | exact (proj2 (rig_entry_split _ Hp1))]. }
  pose proof gS_range as [[GSR1 GSR2] GSR3]. rewrite K_val in GSR1.
  pose proof alloc_ceiling_val as ACV.
  pose proof NLE as NLE'. unfold gN in NLE'.
  pose proof GF0 as (GF1 & GF2 & GF3).
  eapply rig_run; [exact RA | exact Hh | exact Hl | |].
  - unfold Regs6ss.mkR_of.
    assert (E2 : reg_get regs 2 = Z_to_bv 64 gP) by exact G2.
    assert (E18 : reg_get regs 18 = Z_to_bv 64 RIG_FMT) by exact R18.
    assert (E19 : reg_get regs 19 = Z_to_bv 64 RIG_KEY) by exact R19.
    assert (E22 : reg_get regs 22 = Z_to_bv 64 RIG_S6) by exact G22.
    assert (E23 : reg_get regs 23 = Z_to_bv 64 (Z.of_nat i)) by exact R23.
    rewrite E2, E18, E19, E22, E23.
    rewrite SEGS in RA, FE, HGS.
    apply rig_segB with (fd := re_fd (nth i es no_entry)) (eof := re_eof (nth i es no_entry)).
    + apply rw_cells_normalize; [exact RA | exact HGS |]. intros x Hx. cbn in Hx. apply rig_ro_glob. clear -Hx. unfold RIG_GSRC. lia.
    + apply rw_cells_normalize; [exact RA | exact FE |]. intros x Hx. cbn in Hx.
      apply (ro_addr_out Bm SEGS); [unfold SRC_TABLE, SRC_ENTRY in *; lia |].
      replace (G + 56 * Z.of_nat i + x) with (G + (56 * Z.of_nat i + x)) by ring.
      apply GF3. unfold SRC_TABLE, SRC_ENTRY. lia.
    + lia.
    + exact EOF01.
    + unfold gP. lia.
  - intros s0 R' m' HQ REL ROS X.
    destruct HQ as (x10' & x12' & [(Heof & ->) | (Heof & ->)]);
      cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in X |- *.
    + assert (R'1 : getr R' 1 = Z_to_bv 64 0x134dc) by (rewrite (getr_of_eqv _ _ 1 X eq_refl); reflexivity).
      assert (R'2 : getr R' 2 = Z_to_bv 64 gP) by (rewrite (getr_of_eqv _ _ 2 X eq_refl); reflexivity).
      assert (R'3 : getr R' 3 = getr regs0 3) by (rewrite (getr_of_eqv _ _ 3 X eq_refl); exact G3).
      assert (R'4 : getr R' 4 = getr regs0 4) by (rewrite (getr_of_eqv _ _ 4 X eq_refl); exact G4).
      assert (R'8 : getr R' 8 = getr regs0 10) by (rewrite (getr_of_eqv _ _ 8 X eq_refl); exact G8).
      assert (R'10 : getr R' 10 = Z_to_bv 64 (G + 56 * Z.of_nat i)) by (rewrite (getr_of_eqv _ _ 10 X eq_refl); reflexivity).
      assert (R'18 : getr R' 18 = Z_to_bv 64 RIG_FMT) by (rewrite (getr_of_eqv _ _ 18 X eq_refl); reflexivity).
      assert (R'19 : getr R' 19 = Z_to_bv 64 RIG_KEY) by (rewrite (getr_of_eqv _ _ 19 X eq_refl); reflexivity).
      assert (R'22 : getr R' 22 = Z_to_bv 64 RIG_S6) by (rewrite (getr_of_eqv _ _ 22 X eq_refl); reflexivity).
      assert (R'23 : getr R' 23 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (getr_of_eqv _ _ 23 X eq_refl); reflexivity).
      assert (R'24 : getr R' 24 = Z_to_bv 64 (56 * Z.of_nat i)) by (rewrite (getr_of_eqv _ _ 24 X eq_refl); reflexivity).
      pose proof (gdr_GI_same _ _ _ _ _ regs R' L A mem m' md k qd es_c hs_c kss LB OUTc CAPc junkc HG REL ROS
                    R'2 R'3 R'4 R'8 R'22) as HG'.
      rewrite <- SEGS.
      change (SR segs (mkCfg (@YK11.mkst fx R' (Z_to_bv 64 RIG_DRAIN) m' (seg_rom segs)) md) (AT_C i)).
      eapply SR_bind; [exact (gdr_call fx i R' L A m' md k qd es_c hs_c kss LB OUTc CAPc junkc Hi Heof HG' R'1 R'10)|].
      intros c1 (regs2 & L2 & A2 & mem2 & md2 & k2 & qd2 & es_c2 & hs_c2 & LB2 & OUTc2 & CAPc2 & junkc2 & ks0 & ka0 & da0
        & -> & RP2 & HG2).
      rewrite R'1.
      pose proof HG2 as HG2c.
      destruct HG2c as (H2_2 & H2_3 & H2_4 & H2_8 & H2_22 & CH2 & _ & _ & _ & _ & RA2 & _ & _ & HGS2 & _).
      pose proof CH2 as (M2 & _).
      destruct (mr_model Bm MR rig_laws L2 A2 mem2 md2 M2) as (Hh2 & Hl2 & _).
      eapply rig_run; [exact RA2 | exact Hh2 | exact Hl2 | |].
      * unfold Regs6ss.mkR_of.
        assert (E22 : reg_get regs2 22 = Z_to_bv 64 RIG_S6) by exact H2_22.
        rewrite E22. rewrite SEGS in RA2, HGS2.
        apply rig_segB2.
        apply rw_cells_normalize; [exact RA2 | exact HGS2 |]. intros x Hx. cbn in Hx. apply rig_ro_glob. clear -Hx. unfold RIG_GSRC. lia.
      * intros s1 R'' m'' HQ2 REL2 ROS2 X2. cbv beta in HQ2. subst s1.
        cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in X2 |- *.
        rewrite <- SEGS. apply SR_ret. unfold AT_C.
        exists fx, R'', L2, A2, m'', md2, k2, qd2, es_c2, hs_c2, kss, LB2, OUTc2, CAPc2, junkc2, ks0, ka0, da0.
        split; [reflexivity|]. split; [exact FRM|]. split; [exact Hi|].
        split; [rewrite (getr_of_eqv _ _ 11 X2 eq_refl); reflexivity|].
        split; [rewrite (getr_of_eqv _ _ 18 X2 eq_refl); exact (eq_trans (RP2 18 ltac:(unfold callee_saved; lia)) R'18)|].
        split; [rewrite (getr_of_eqv _ _ 19 X2 eq_refl); exact (eq_trans (RP2 19 ltac:(unfold callee_saved; lia)) R'19)|].
        split; [rewrite (getr_of_eqv _ _ 23 X2 eq_refl); exact (eq_trans (RP2 23 ltac:(unfold callee_saved; lia)) R'23)|].
        split; [rewrite (getr_of_eqv _ _ 24 X2 eq_refl); exact (eq_trans (RP2 24 ltac:(unfold callee_saved; lia)) R'24)|].
        apply (gdr_GI_same _ _ _ _ _ regs2 R'' L2 A2 mem2 m'' md2); [exact HG2 | exact REL2 | exact ROS2 | | | | |].
        -- rewrite (getr_of_eqv _ _ 2 X2 eq_refl). exact H2_2.
        -- rewrite (getr_of_eqv _ _ 3 X2 eq_refl). exact H2_3.
        -- rewrite (getr_of_eqv _ _ 4 X2 eq_refl). exact H2_4.
        -- rewrite (getr_of_eqv _ _ 8 X2 eq_refl). exact H2_8.
        -- rewrite (getr_of_eqv _ _ 22 X2 eq_refl). reflexivity.
    + rewrite <- SEGS. apply SR_ret. unfold AT_C.
      exists fx, R', L, A, m', md, k, qd, es_c, hs_c, kss, LB, OUTc, CAPc, junkc, (keys_texts (re_keys (nth i es no_entry))),
        (gka0 i), (gda0 i).
      split; [reflexivity|]. split; [exact FRM|]. split; [exact Hi|].
      split; [rewrite (getr_of_eqv _ _ 11 X eq_refl); reflexivity|].
      split; [rewrite (getr_of_eqv _ _ 18 X eq_refl); reflexivity|].
      split; [rewrite (getr_of_eqv _ _ 19 X eq_refl); reflexivity|].
      split; [rewrite (getr_of_eqv _ _ 23 X eq_refl); reflexivity|].
      split; [rewrite (getr_of_eqv _ _ 24 X eq_refl); reflexivity|].
      apply (gdr_GI_same _ _ _ _ _ regs R' L A mem m' md); [exact (gdr_eof1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi Heof HG) | exact REL | exact ROS | | | | |].
      * rewrite (getr_of_eqv _ _ 2 X eq_refl). reflexivity.
      * rewrite (getr_of_eqv _ _ 3 X eq_refl). exact G3.
      * rewrite (getr_of_eqv _ _ 4 X eq_refl). exact G4.
      * rewrite (getr_of_eqv _ _ 8 X eq_refl). exact G8.
      * rewrite (getr_of_eqv _ _ 22 X eq_refl). reflexivity.
Qed.

(* ===== region gone_C ===== *)

Lemma gc_run : forall (fxc : YK11.FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  ro_agree segs mem -> m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs Q (MS (Regs6ss.mkR_of regs) (@fp_regs fxc) pc (@fp_csr fxc) None (MemNorm.normalize_cj rsegs mem)
                      (seg_rom rsegs)) ->
  (forall s0 R' m', Q s0 -> MemNorm.mem_rel_cj rsegs m' (ms_mem s0) -> MemNorm.cj_same rsegs mem m' ->
     Regs6ss.xregs_eqv (ms_regs s0) R' ->
     SR segs (mkCfg {| ms_regs := R'; ms_fregs := ms_fregs s0; ms_pc_val := ms_pc_val s0;
                       ms_svc_pending := ms_svc_pending s0; ms_resv := ms_resv s0; ms_fcsr := ms_fcsr s0;
                       ms_mem := m'; ms_rom := ms_rom s0 |} md) P) ->
  SR segs (mkCfg (@YK11.mkst fxc regs pc mem (seg_rom segs)) md) P.
Proof.
  intros fxc regs pc mem md Q P RA Hh Hl HE K.
  apply (evt_SR_canon segs (@YK11.mkst fxc regs pc mem (seg_rom segs))
           (fun s => exists s0, Q s0 /\ MemNorm.ms_rel_cj rsegs s s0 /\ MemNorm.cj_same rsegs mem (ms_mem s)) md P);
    [ | exact Hh | exact Hl | ].
  - rewrite SEGS. change (RegisterBridge.canonical_register_state (@YK11.mkst fxc regs pc mem (seg_rom rsegs)))
      with (MS (Regs6ss.mkR_of regs) (@fp_regs fxc) pc (@fp_csr fxc) None mem (seg_rom rsegs)).
    apply (MemNorm.evt_normalize_cj rsegs); [vm_compute; reflexivity | rewrite <- SEGS; exact RA | exact HE].
  - intros ms' (can & (s0 & HQ & HR & HO) & HEQ).
    destruct ms' as [r f pv sv rv c mm o], can as [cr cf cp csv crv cc cmm co], s0 as [zr zf zp zsv zrv zc zmm zo].
    destruct HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
    destruct HEQ as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
    subst.
    exact (K _ r mm HQ R8 HO E1).
Qed.

Lemma gc_stk_cj : forall m lo hi, 2 ^ 20 <= lo -> hi <= TASK_SIZE ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> stk rsegs (MemNorm.normalize_cj rsegs m) lo hi.
Proof.
  intros m lo hi Hlo Hhi HW. unfold TASK_SIZE in Hhi. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (writable_hi_present m a ltac:(lia) (HW a Ha)) as [bb E].
  assert (NE : MemNorm.normalize_cj rsegs m (wa a) = m (wa a)).
  { unfold MemNorm.normalize_cj. rewrite (MemNorm.cj_drop_false_intro rsegs (wa a)); [reflexivity | |].
    - unfold wa. apply ro_addr_hi. lia.
    - right. unfold wa. rewrite MState.unsigned_lit by lia. unfold TASK_SIZE. lia. }
  unfold wview, mrd. rewrite NE. unfold wa. rewrite E. split; [discriminate | exists bb; reflexivity].
Qed.

Lemma gc_rw_rel : forall m m0 a cs, MemNorm.mem_rel_cj rsegs m m0 -> rw_cells rsegs m0 a cs -> rw_cells rsegs m a cs.
Proof.
  intros m m0 a cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (MemNorm.bytes_at_rel_cj rsegs m m0 a _ HR Hb).
  - exact (MemNorm.wr_at_rel_cj rsegs m m0 a _ HR Hw).
Qed.

Lemma gc_rw_cj : forall m a cs, ro_agree rsegs m -> rw_cells rsegs m a cs ->
  a + Z.of_nat (cells_size cs) <= TASK_SIZE ->
  (forall j, 0 <= j < Z.of_nat (cells_size cs) -> ro_addr rsegs (Z_to_bv 64 (a + j)) = false) ->
  rw_cells rsegs (MemNorm.normalize_cj rsegs m) a cs.
Proof.
  intros m a cs RO [[Hwf Hb] Hw] Hlt Hro. split; [split; [exact Hwf|]|].
  - apply (MemNorm.bytes_at_normalize_cj_low rsegs m a _ RO); [rewrite cells_bytes_length by exact Hwf; exact Hlt | exact Hb].
  - apply (MemNorm.wr_at_norm_cj rsegs m _ a _ (MemNorm.mem_rel_cj_normalize rsegs m RO) Hw).
    intros j Hj. destruct Hw as (W1 & W2 & _).
    apply (MemNorm.cj_drop_false_intro rsegs); [exact (Hro j Hj) | right].
    unfold wa. rewrite MState.unsigned_lit by (unfold TASK_SIZE in Hlt; lia). unfold TASK_SIZE in *. lia.
Qed.

Lemma gc_rw_sub : forall m A n bs pre cs post, rw_cells segs m A [CB n bs] ->
  bs = pre ++ cells_bytes cs ++ post -> cells_wf cs ->
  rw_cells segs m (A + Z.of_nat (length pre)) cs.
Proof.
  intros m A n bs pre cs post [[Hwf Hb] Hw] E Hcw.
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in Hwf, Hb, Hw.
  rewrite app_nil_r in Hb. destruct Hwf as [Hl _]. subst bs.
  rewrite !length_app, (cells_bytes_length cs Hcw) in Hl.
  apply bytes_at_app in Hb as [_ Hb]. apply bytes_at_app in Hb as [Hb _].
  destruct Hw as (W1 & W2 & W3).
  split; [split; [exact Hcw | exact Hb]|].
  split; [lia|]. split; [lia|].
  intros j Hj. replace (A + Z.of_nat (length pre) + j) with (A + (Z.of_nat (length pre) + j)) by ring.
  apply W3. lia.
Qed.

Lemma gc_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma gc_le_byte_bv : forall v k, 0 <= v < 2 ^ 64 ->
  Z_to_bv 8 (le_byte v 8 k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
  intros v k Hv. unfold le_byte. change (8 * Z.of_nat 8) with 64.
  rewrite (Z.mod_small v (2 ^ 64)) by lia.
  apply Mem.Z_to_bv8_mod. change 256 with (2 ^ 8). apply Z.mod_mod. lia.
Qed.

Lemma gc_word_le8 : forall m a v, word_mem segs m a v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  bytes_at segs m a (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v Hw Hv Ha Hb. split; [exact Ha|]. rewrite length_le8. split; [lia|].
  intros j Hj. unfold le8, word_to_le_bytes. rewrite gc_nth_le_bytes by exact Hj.
  rewrite MState.unsigned_lit by lia. rewrite <- gc_le_byte_bv by exact Hv. exact (Hw j Hj).
Qed.

Lemma gc_blk_ro : forall L A m md q k j, MR L A m md -> In (q, k) (blocks L A) -> 0 <= j < k ->
  ro_addr rsegs (Z_to_bv 64 (q + j)) = false.
Proof.
  intros L A m md q k j HM Hin Hj.
  pose proof (rig_blk L A m md q k j HM Hin Hj) as (_ & H4 & H5 & _).
  pose proof alloc_ceiling_lt as HL.
  apply rig_blocks_in in Hin as (p & Ep & Hp).
  apply (ro_addr_out Bm SEGS); [lia|]. rewrite <- Ep.
  exact (ax_blocks_img AX L A m md p k j HM Hp Hj).
Qed.

Lemma gc_entry : forall L A mem md es_c tl i, MR L A mem md -> (i < length es_c)%nat ->
  In (G, SRC_TABLE) (blocks L A) -> table_at Bm mem G es_c tl -> Forall (entry_okk L A mem) es_c ->
  rw_cells segs mem (G + 56 * Z.of_nat i + 40)
    [C8 (Z_to_bv 64 (re_hp (nth i es_c no_entry))); C4 (Z_to_bv 64 (re_nheld (nth i es_c no_entry)))] /\
  0 <= re_nheld (nth i es_c no_entry) < 2 ^ 26 /\
  (0 < re_nheld (nth i es_c no_entry) ->
     4096 <= re_hp (nth i es_c no_entry) /\ re_hp (nth i es_c no_entry) + 8 <= gS - RELAY_INSTANCE_GONE_K /\
     bytes_at segs mem (re_hp (nth i es_c no_entry))
       (le8 (Z_to_bv 64 (key_addr (nth 0 (re_keys (nth i es_c no_entry)) rig_dk))))).
Proof.
  intros L A mem md es_c tl i HM Hic HGB (Htl & TBC) HEOK.
  assert (EL56 : Forall (fun e0 => length (entry_bytes e0) = 56%nat) es_c).
  { apply Forall_forall. intros e0 He0. destruct (proj1 (Forall_forall _ _) HEOK e0 He0) as (ksx & _ & OK0).
    unfold entry_ok in OK0. destruct OK0 as (_ & _ & P1 & P2 & _). exact (rig_entry_len e0 P1 P2). }
  destruct (rig_concat_nth es_c i Hic EL56) as [CE CL].
  destruct (proj1 (Forall_forall _ _) HEOK (nth i es_c no_entry) (nth_In es_c no_entry Hic)) as (ks & Eks & OK).
  set (e := nth i es_c no_entry) in *. clearbody e.
  destruct (map_fst_keys (re_keys e) ks Eks) as (EKA & EKT & EKL & EKP & EKX).
  unfold entry_ok in OK.
  destruct OK as (_ & _ & Hp1 & Hp2 & _ & _ & _ & _ & _ & _ & Hnh & Hhp & _).
  cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_junk re_hp re_kh re_keys with_keys]
    in Hp1, Hp2, Hnh, Hhp.
  unfold re_nheld in Hnh, Hhp. cbn [re_keys with_keys] in Hnh, Hhp.
  rewrite EKL in Hnh, Hhp. rewrite EKP in Hhp.
  assert (ELe : length (entry_bytes e) = 56%nat) by exact (rig_entry_len e Hp1 Hp2).
  destruct (rig_entry_split e Hp1) as [ES _].
  assert (EQ : concat (map entry_bytes es_c) ++ tl =
     (concat (map entry_bytes (firstn i es_c)) ++ firstn 40 (entry_bytes e)) ++
     cells_bytes [C8 (Z_to_bv 64 (re_hp e)); C4 (Z_to_bv 64 (re_nheld e))] ++
     (re_pad2 e ++ concat (map entry_bytes (skipn (S i) es_c)) ++ tl)).
  { rewrite CE. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    transitivity (concat (map entry_bytes (firstn i es_c)) ++
      (firstn 40 (entry_bytes e) ++ le8 (Z_to_bv 64 (re_hp e)) ++ le4 (Z_to_bv 64 (re_nheld e)) ++ re_pad2 e) ++
      concat (map entry_bytes (skipn (S i) es_c)) ++ tl).
    - rewrite <- ES. rewrite <- !app_assoc. reflexivity.
    - rewrite <- !app_assoc. reflexivity. }
  pose proof (gc_rw_sub mem G 896 _ _ _ _ TBC EQ ltac:(cbn; tauto)) as EC0.
  assert (LP : G + Z.of_nat (length (concat (map entry_bytes (firstn i es_c)) ++ firstn 40 (entry_bytes e))) =
               G + 56 * Z.of_nat i + 40).
  { rewrite length_app, CL, firstn_length, ELe. replace (Nat.min 40 56) with 40%nat by reflexivity. lia. }
  rewrite LP in EC0.
  split; [exact EC0|].
  split; [unfold re_nheld; lia|].
  intros NZ. unfold re_nheld in NZ.
  destruct Hhp as [(_ & Hk0)|(Hin & _ & H8 & H8' & Hb0)].
  - subst ks. cbn [length] in EKL. lia.
  - pose proof (blk_low L A mem md (re_hp e) (re_kh e) HM Hin ltac:(lia)) as HBL.
    pose proof (rig_blk L A mem md (re_hp e) (re_kh e) 0 HM Hin ltac:(lia)) as (_ & H4 & _).
    split; [lia|]. split; [lia|].
    pose proof (rig_key_ptrs_slot segs mem (re_hp e) (re_keys e) 0 Hb0 ltac:(lia)) as HS.
    replace (re_hp e + 8 * Z.of_nat 0) with (re_hp e) in HS by lia. exact HS.
Qed.

Lemma gone_C : forall i c, AT_C i c -> SR segs c (fun c' => exists ks0, AT_IN i ks0 0 ks0 [] c').
Proof.
  intros i c (fx & regs & L & A & mem & md & k & qd & es_c & hs_c & kss & LB & OUTc & CAPc & junkc & ks0 & ka0 & da0 & -> & FZ & Hi
    & R11 & R18 & R19 & R23 & R24 & HG).
  pose proof HG as (G2 & G3 & G4 & G8 & G22 & CH & _ & _ & _ & _ & RA & _ & _ & _ & HGB & _ & _ & _ & _ & _ & _ & _
    & FRB & _ & HLE & HTAB & HEOK & _ & _ & _ & _ & _ & HCUR & _).
  pose proof gS_range as [[GSR1 GSR2] GSR3]. pose proof gS_low as GSL. pose proof alloc_ceiling_val as ACV.
  pose proof K_val as KV.
  assert (TS : gS <= TASK_SIZE) by exact TSZ.
  pose proof CH as (M1 & _).
  destruct (mr_model Bm MR rig_laws L A mem md M1) as (Hh & Hl & _).
  assert (RAr : ro_agree rsegs mem) by (rewrite <- SEGS; exact RA).
  assert (I4 : (i < 4)%nat) by (pose proof NLE as N4; unfold gN in N4; lia).
  assert (Hic : (i < length es_c)%nat) by lia.
  destruct HTAB as (tl & HTAB).
  destruct (gc_entry L A mem md es_c tl i M1 Hic HGB HTAB HEOK) as (EC & NHR & HK).
  destruct (HCUR Hi) as (_ & KT & _).
  assert (LK : length ks0 = length (re_keys (nth i es_c no_entry)))
    by (rewrite <- KT; unfold keys_texts; rewrite length_map; reflexivity).
  assert (NE : re_nheld (nth i es_c no_entry) = Z.of_nat (length ks0)) by (unfold re_nheld; rewrite LK; reflexivity).
  destruct FRB as (jb & FRB).
  pose proof (blk_low L A mem md G SRC_TABLE M1 HGB ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)) as GBL.
  unfold SRC_TABLE, SRC_ENTRY in GBL.
  pose proof (rig_blk L A mem md G SRC_TABLE 0 M1 HGB ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)) as (_ & G4096 & _).
  destruct (ax_statics AX L A mem md M1) as (GW & (g & Hg & GW2) & _).
  rewrite GOTG, GRD in GW. rewrite GRD in GW2.
  pose proof (gc_word_le8 mem GOT_GUARD GUARD GW ltac:(unfold GUARD; lia) ltac:(unfold GOT_GUARD; lia)
    ltac:(unfold GOT_GUARD; lia)) as GGb.
  pose proof (gc_word_le8 mem GUARD g GW2 Hg ltac:(unfold GUARD; lia) ltac:(unfold GUARD; lia)) as GWb.
  rewrite SEGS in GGb, GWb, EC, FRB, HK.
  apply (gc_run fx regs (Z_to_bv 64 0x134e0) mem md
    (rig_postC (getr regs0 3) (getr regs0 4) (getr regs0 10) gP (Z.of_nat i) (G + 56 * Z.of_nat i)
       (re_nheld (nth i es_c no_entry)) (re_hp (nth i es_c no_entry))
       (key_addr (nth 0 (re_keys (nth i es_c no_entry)) rig_dk)) (gS - RELAY_INSTANCE_GONE_K)
       (rig_pre (bv_signed (getr regs0 10))) jb (MemNorm.normalize_cj rsegs mem)));
    [exact RA | exact Hh | exact Hl | |].
  - unfold Regs6ss.mkR_of.
    assert (E2 : reg_get regs 2 = Z_to_bv 64 gP) by exact G2.
    assert (E3 : reg_get regs 3 = getr regs0 3) by exact G3.
    assert (E4 : reg_get regs 4 = getr regs0 4) by exact G4.
    assert (E8 : reg_get regs 8 = getr regs0 10) by exact G8.
    assert (E11 : reg_get regs 11 = Z_to_bv 64 G) by exact R11.
    assert (E18 : reg_get regs 18 = Z_to_bv 64 RIG_FMT) by exact R18.
    assert (E19 : reg_get regs 19 = Z_to_bv 64 RIG_KEY) by exact R19.
    assert (E22 : reg_get regs 22 = Z_to_bv 64 RIG_S6) by exact G22.
    assert (E23 : reg_get regs 23 = Z_to_bv 64 (Z.of_nat i)) by exact R23.
    assert (E24 : reg_get regs 24 = Z_to_bv 64 (56 * Z.of_nat i)) by exact R24.
    rewrite E2, E3, E4, E8, E11, E18, E19, E22, E23, E24.
    eapply (rig_segC SNP SLEN) with (canary := Z_to_bv 64 g).
    + apply gc_stk_cj; [lia | unfold gP; lia |]. intros a Ha.
      destruct CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SW).
      rewrite <- SEGS. apply SW. left. change (spZ regs0) with gS. unfold gP in Ha. lia.
    + unfold SNPRINTF_K, gP. lia.
    + unfold IMG_END. lia.
    + lia.
    + unfold gP. lia.
    + exact FZ.
    + exact (MemNorm.mem_inv_cj_inv rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)).
    + exact (MemNorm.mem_inv_cj_task rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)).
    + apply gc_rw_cj; [exact RAr | exact FRB | cbn [cells_size csize]; unfold gP; lia |].
      intros j Hj. cbn [cells_size csize] in Hj. apply ro_addr_hi. unfold gP. lia.
    + apply (MemNorm.bytes_at_normalize_cj_low rsegs mem _ _ RAr); [rewrite length_le8; unfold GOT_GUARD; lia | exact GGb].
    + apply (MemNorm.bytes_at_normalize_cj_low rsegs mem _ _ RAr); [rewrite length_le8; unfold GUARD; lia | exact GWb].
    + exact IDR.
    + lia.
    + lia.
    + lia.
    + apply gc_rw_cj; [exact RAr | exact EC | cbn [cells_size csize]; lia |].
      intros j Hj. cbn [cells_size csize] in Hj.
      replace (G + 56 * Z.of_nat i + 40 + j) with (G + (56 * Z.of_nat i + 40 + j)) by ring.
      apply (gc_blk_ro L A mem md G SRC_TABLE); [exact M1 | exact HGB | unfold SRC_TABLE, SRC_ENTRY; lia].
    + exact NHR.
    + intros NZ. destruct (HK NZ) as (H1 & H2 & H3). split; [lia|]. split; [exact H2|].
      apply (MemNorm.bytes_at_normalize_cj_low rsegs mem _ _ RAr); [rewrite length_le8; lia | exact H3].
  - intros s0 R' m' HQ REL ROS X.
    unfold rig_postC in HQ.
    destruct HQ as (x1' & x5' & x6' & x7' & x9' & x10' & x11' & x12' & x13' & x14' & x15' & x16' & x17' & x20' & x21'
      & x25' & x26' & x27' & x28' & x29' & x30' & x31' & Ft & fc' & m'n & -> & FRM2 & HNZ & MU & WM & MI & CB2).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in REL, X |- *.
    pose proof (MemNorm.mem_rel_cj_normalize rsegs mem RAr) as RN.
    pose proof (MemNorm.munch_rel_cj rsegs _ mem _ m' m'n RN REL ROS MU) as MUr.
    pose proof (MemNorm.wmono_rel_cj rsegs mem _ m' m'n RN REL ROS WM) as WMr.
    pose proof (MemNorm.ro_agree_same_cj rsegs mem m' RAr ROS) as RA'.
    pose proof (gc_rw_rel m' m'n _ _ REL CB2) as CBr.
    rewrite <- SEGS in WMr, RA', CBr.
    apply SR_ret. exists ks0. unfold AT_IN.
    exists (YK11.mkFP Ft fc'), R', L, A, m', md, k, qd, es_c, hs_c, kss, LB, OUTc, CAPc, junkc,
      (skipn (length (rig_pre (bv_signed (getr regs0 10))) + 1) jb), ka0, da0, (combine ks0 ka0).
    split; [rewrite NE, SEGS; destruct (length ks0); reflexivity|].
    split; [exact FRM2|].
    split; [exact Hi|].
    split; [rewrite (getr_of_eqv _ _ 18 X eq_refl); simp_regs; reflexivity|].
    split; [rewrite (getr_of_eqv _ _ 19 X eq_refl); simp_regs; reflexivity|].
    split; [rewrite (getr_of_eqv _ _ 23 X eq_refl); simp_regs; reflexivity|].
    split; [rewrite (getr_of_eqv _ _ 24 X eq_refl); simp_regs; reflexivity|].
    split.
    { intros HL0. assert (NZ : re_nheld (nth i es_c no_entry) <> 0) by lia.
      destruct (HNZ NZ) as (H9 & H20 & H21 & H25 & H26 & H27).
      split; [rewrite (getr_of_eqv _ _ 9 X eq_refl); simp_regs; exact H9|].
      split; [rewrite (getr_of_eqv _ _ 20 X eq_refl); simp_regs; exact H20|].
      split; [rewrite (getr_of_eqv _ _ 21 X eq_refl); simp_regs; exact H21|].
      split; [rewrite (getr_of_eqv _ _ 25 X eq_refl); simp_regs; exact H25|].
      split; [rewrite (getr_of_eqv _ _ 26 X eq_refl); simp_regs; rewrite H26, NE; reflexivity|].
      rewrite (getr_of_eqv _ _ 27 X eq_refl); simp_regs; exact H27. }
    split; [exact CBr|].
    apply (GI_stack i _ _ _ _ regs R' L A mem m' md k qd es_c hs_c kss LB OUTc CAPc junkc _ HG MUr WMr RA').
    + intros x Hx NO. cbn [outside] in NO. unfold gP in *.
      destruct (Z_lt_ge_dec x (gS - RELAY_INSTANCE_GONE_K)) as [D1|D1];
        [exfalso; apply NO; split; [lia|]; split; [lia | exact I]|].
      destruct (Z_lt_ge_dec x (gS - 160)) as [D2|D2]; [left; lia|].
      destruct (Z_lt_ge_dec x (gS - 160 + 8)) as [D3|D3]; [exfalso; apply NO; split; [lia|]; split; [lia | exact I]|].
      destruct (Z_lt_ge_dec x (gS - 160 + 56)) as [D4|D4]; [right; lia|].
      exfalso; apply NO; split; [lia|]; split; [lia | exact I].
    + rewrite (getr_of_eqv _ _ 2 X eq_refl); simp_regs; reflexivity.
    + rewrite (getr_of_eqv _ _ 3 X eq_refl); simp_regs; reflexivity.
    + rewrite (getr_of_eqv _ _ 4 X eq_refl); simp_regs; reflexivity.
    + rewrite (getr_of_eqv _ _ 8 X eq_refl); simp_regs; reflexivity.
    + rewrite (getr_of_eqv _ _ 22 X eq_refl); simp_regs; reflexivity.
Qed.

(* ===== region gone_skip ===== *)

Lemma gsk_GI_cur : forall i cur cur' part base bound regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc,
  GI i cur part base bound regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc ->
  ((i < length es)%nat -> cur L A qd (nth i es_c no_entry) (nth i hs_c (fst (nth i hs no_hj))) ->
     cur' L A qd (nth i es_c no_entry) (nth i hs_c (fst (nth i hs no_hj)))) ->
  GI i cur' part base bound regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc.
Proof.
  intros i cur cur' part base bound regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc HG HC.
  unfold GI in HG |- *. cbv zeta in HG |- *.
  destruct HG as (G2 & G3 & G4 & G8 & G22 & CH & INIT & RES & BUD & POT & RA & GL & HNS & HGS & HGB & CCL & CBR & CDD
    & CEI & CERR & SRCH' & FR0 & FRB & FRS & HLE & HTAB & HEOK & HLH & HLK & HIL & HSRC & HDONE & HCUR & HREST).
  do 32 (split; [assumption|]).
  split; [intros Hi; exact (HC Hi (HCUR Hi))|].
  exact HREST.
Qed.

Lemma gsk_cur_step : forall i ks0 n H Ed ka0 a Ha L A qd e h, (n < length H)%nat ->
  has_prefix gpre (nth n H []) = false ->
  inner_cur i ks0 n H Ed ka0 a Ha L A qd e h -> inner_cur i ks0 (S n) H Ed ka0 a Ha L A qd e h.
Proof.
  intros i ks0 n H Ed ka0 a Ha L A qd e h Hn Hp (D0 & HK & Hle & Hpf & Hg & HHa & Hka & (Eda & HEda & Hga) & HL1 & HL2).
  split; [exact D0|]. split; [exact HK|]. split; [lia|].
  split.
  { intros j Hj. destruct (Nat.eq_dec j n) as [->|Hne]; [exact Hp | apply Hpf; lia]. }
  split.
  { rewrite Hg. replace (length H - n)%nat with (S (length H - S n)) by lia.
    rewrite (rig_gei_skip _ gpre n H Hn Hp). reflexivity. }
  split; [exact HHa|]. split; [exact Hka|].
  split; [|split; [exact HL1 | exact HL2]].
  exists Eda. split; [exact HEda|]. rewrite Hga.
  assert (HnA : (n < length Ha)%nat) by (rewrite <- HHa, length_map in Hn; exact Hn).
  assert (HpA : has_prefix gpre (fst (nth n Ha ([], adr0))) = false).
  { rewrite <- Hp, <- HHa. f_equal. rewrite <- (map_nth fst Ha ([], adr0) n). reflexivity. }
  replace (length Ha - n)%nat with (S (length Ha - S n)) by lia.
  cbn [geia_loop]. rewrite (proj2 (Nat.ltb_lt _ _) HnA), HpA. reflexivity.
Qed.

Lemma gsk_key : forall L A mem e' n, entry_okk L A mem e' -> (n < length (re_keys e'))%nat ->
  bytes_at segs mem (key_addr (nth n (re_keys e') rig_dk)) (key_text (nth n (re_keys e') rig_dk) ++ [Z_to_bv 8 0]) /\
  ~ In (Z_to_bv 8 0) (key_text (nth n (re_keys e') rig_dk)) /\
  re_nheld e' < 2 ^ 26 /\ In (re_hp e', re_kh e') (blocks L A) /\ 8 * re_nheld e' <= re_kh e' /\ 8 <= re_kh e' /\
  bytes_at segs mem (re_hp e') (key_ptrs (re_keys e')).
Proof.
  intros L A mem e' n (ks & Eks & OK) Hn.
  destruct (map_fst_keys (re_keys e') ks Eks) as (EA & ET & EL & EP & EX).
  unfold entry_ok in OK.
  destruct OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnh & Hhp & _ & _ & Hkeys).
  cbn [re_hp re_kh re_keys with_keys] in Hhp, Hkeys. unfold re_nheld in Hnh, Hhp |- *.
  cbn [re_keys with_keys] in Hnh, Hhp.
  assert (Hnk : (n < length ks)%nat) by lia.
  pose proof (proj1 (Forall_forall _ _) Hkeys (nth n ks rig_dk) (nth_In _ _ Hnk)) as (H1 & H2 & H3 & H4 & H5 & H6).
  assert (F1 : nth n (map fst ks) (fst rig_dk) = nth n (map fst (re_keys e')) (fst rig_dk)) by (rewrite Eks; reflexivity).
  rewrite !map_nth in F1.
  assert (KA : key_addr (nth n ks rig_dk) = key_addr (nth n (re_keys e') rig_dk)) by (unfold key_addr; rewrite F1; reflexivity).
  assert (KT : key_text (nth n ks rig_dk) = key_text (nth n (re_keys e') rig_dk)) by (unfold key_text; rewrite F1; reflexivity).
  rewrite KA, KT in H3. rewrite KT in H4.
  split.
  { replace (key_text (nth n (re_keys e') rig_dk) ++ Z_to_bv 8 0 :: key_slack (nth n ks rig_dk))
      with ((key_text (nth n (re_keys e') rig_dk) ++ [Z_to_bv 8 0]) ++ key_slack (nth n ks rig_dk)) in H3
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in H3. exact (proj1 H3). }
  split; [exact H4|]. split; [lia|].
  destruct Hhp as [(_ & E0)|(Hin & _ & H8 & H8' & Hb)]; [subst ks; cbn in Hnk; lia|].
  split; [exact Hin|]. split; [lia|]. split; [exact H8'|]. rewrite <- EP. exact Hb.
Qed.

Lemma gone_skip : forall i ks0 n H Ed c, (n < length H)%nat -> has_prefix gpre (nth n H []) = false ->
  AT_IN i ks0 n H Ed c -> SR segs c (AT_IN i ks0 (S n) H Ed).
Proof.
  intros i ks0 n H Ed c Hn Hp HA.
  destruct HA as (fx & regs & L & A & mem & md & k & qd & es_c & hs_c & kss & LB & OUTc & CAPc & junkc & jr & ka0 & da0 & Ha &
    -> & FRM & Hi & R18 & R19 & R23 & R24 & HR & PB & HG).
  destruct (HR Hn) as (R9 & R20 & R21 & R25 & R26 & R27). clear HR.
  replace (Nat.ltb n (length H)) with true by (symmetry; apply Nat.ltb_lt; exact Hn).
  pose proof HG as HG0. unfold GI in HG0. cbv zeta in HG0.
  destruct HG0 as (G2 & G3 & G4 & G8 & G22 & CH & _ & _ & _ & _ & RA & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & HLE & _ & HEOK & _ & _ & _ & _ & _ & HCUR & _).
  destruct (HCUR Hi) as (_ & HK & _ & _ & _).
  assert (LK : length (re_keys (nth i es_c no_entry)) = length H)
    by (rewrite <- HK; unfold keys_texts; rewrite length_map; reflexivity).
  assert (OKK : entry_okk L A mem (nth i es_c no_entry)) by (apply (proj1 (Forall_forall _ _) HEOK); apply nth_In; lia).
  destruct (gsk_key L A mem (nth i es_c no_entry) n OKK ltac:(lia)) as (KB & KZ & NH & HPB & HP8 & HK8 & KP).
  unfold re_nheld in NH, HP8. rewrite LK in NH, HP8.
  pose proof CH as (M1 & _).
  destruct (mr_model Bm MR rig_laws L A mem md M1) as (Hh & Hl & _).
  pose proof (blk_low L A mem md _ _ M1 HPB ltac:(lia)) as HPL.
  pose proof (rig_blk L A mem md _ _ 0 M1 HPB ltac:(lia)) as (_ & HP4 & _ & _).
  pose proof gS_range as [[GSR1 GSR2] GSR3]. pose proof alloc_ceiling_val as ACV. pose proof K_val as KV.
  assert (NHk : nth n H [] = bzs (key_text (nth n (re_keys (nth i es_c no_entry)) rig_dk))).
  { rewrite <- HK. unfold keys_texts. exact (map_nth (fun k => bzs (key_text k)) (re_keys (nth i es_c no_entry)) rig_dk n). }
  assert (HPF : has_prefix gpre (map (fun b : byte => bv_unsigned b) (key_text (nth n (re_keys (nth i es_c no_entry)) rig_dk)))
                = false) by (rewrite NHk in Hp; exact Hp).
  assert (LP : 1 <= Z.of_nat (length gpre) < 48).
  { unfold gpre, instance_prefix, K_GESTURE. rewrite !length_app. cbn [length].
    pose proof (rigc_dec_len (bv_signed (getr regs0 10))). lia. }
  eapply (rig_run fx regs (Z_to_bv 64 0x13524) mem md); [exact RA | exact Hh | exact Hl | |].
  - unfold Regs6ss.mkR_of.
    assert (E2 : reg_get regs 2 = Z_to_bv 64 gP) by exact G2.
    assert (E9 : reg_get regs 9 = Z_to_bv 64 (Z.of_nat n)) by exact R9.
    assert (E20 : reg_get regs 20 = Z_to_bv 64 (Z.of_nat (length gpre))) by exact R20.
    assert (E21 : reg_get regs 21 = Z_to_bv 64 (key_addr (nth n (re_keys (nth i es_c no_entry)) rig_dk))) by exact R21.
    assert (E25 : reg_get regs 25 = Z_to_bv 64 (8 * Z.of_nat n)) by exact R25.
    assert (E26 : reg_get regs 26 = Z_to_bv 64 (Z.of_nat (length H))) by exact R26.
    assert (E27 : reg_get regs 27 = Z_to_bv 64 (re_hp (nth i es_c no_entry))) by exact R27.
    rewrite E2, E9, E20, E21, E25, E26, E27.
    rewrite SEGS in RA, KB, KP.
    pose proof PB as [[_ PBb] _]. cbn [cells_bytes cbytes] in PBb. rewrite app_nil_r in PBb.
    apply bytes_at_app in PBb. destruct PBb as [PBb _]. rewrite SEGS in PBb.
    apply (rig_segE SNCMP) with (m := normalize rsegs mem) (P := gP) (n := Z.of_nat n) (nh := Z.of_nat (length H))
      (hp := re_hp (nth i es_c no_entry)) (ka := key_addr (nth n (re_keys (nth i es_c no_entry)) rig_dk))
      (knext := key_addr (nth (S n) (re_keys (nth i es_c no_entry)) rig_dk)) (T := gpre)
      (x := key_text (nth n (re_keys (nth i es_c no_entry)) rig_dk)).
    + apply mem_inv_normalize.
    + exact (bytes_at_normalize rsegs mem _ _ RA KB).
    + exact KZ.
    + exact (bytes_at_normalize rsegs mem _ _ RA PBb).
    + exact (rigc_pre_nz (bv_signed (getr regs0 10))).
    + exact LP.
    + lia.
    + lia.
    + lia.
    + lia.
    + unfold gP. lia.
    + intros Hlt. apply (bytes_at_normalize rsegs mem _ _ RA).
      replace (re_hp (nth i es_c no_entry) + 8 * (Z.of_nat n + 1))
        with (re_hp (nth i es_c no_entry) + 8 * Z.of_nat (S n)) by lia.
      apply rig_key_ptrs_slot; [exact KP | lia].
  - intros s0 R' m' HQ REL ROS X.
    unfold rig_postE in HQ.
    destruct HQ as (x1 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m''
      & MU & WM & MI & HB).
    destruct HB as [(HF & _)|[(_ & Hlt & ->)|(_ & Heq & ->)]].
    { exfalso. assert (Hc : false = true) by (rewrite <- HPF; exact HF). discriminate Hc. }
    all: cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *.
    all: pose proof RA as RAr; rewrite SEGS in RAr.
    all: pose proof (mem_rel_normalize rsegs mem RAr) as RN.
    all: pose proof (munch_rel rsegs [] mem _ m' _ RN REL ROS MU) as MUr.
    all: pose proof (wmono_rel rsegs mem _ m' _ RN REL ROS WM) as WMr.
    all: pose proof (ro_agree_same rsegs mem m' RAr ROS) as RA'.
    all: rewrite <- SEGS in WMr, RA'.
    all: assert (HG' : GI i (inner_cur i ks0 n H Ed ka0 da0 Ha) (part_of i Ed) (gpos_k i da0 (gkept ks0 ka0) [] (skipn (length Ed) (gxks ks0 ka0))) (bound_in i Ed)
                         R' L A m' md k qd es_c hs_c kss LB OUTc CAPc junkc)
      by (apply (GI_stack _ _ _ _ _ regs R' L A mem m' md k qd es_c hs_c kss LB OUTc CAPc junkc [] HG MUr WMr RA');
          [intros x _ Ox; exfalso; apply Ox; exact I | ..];
          repeat rewrite (getr_of_eqv _ _ _ X) by reflexivity; simp_regs; first [reflexivity | assumption]).
    all: assert (HG'' : GI i (inner_cur i ks0 (S n) H Ed ka0 da0 Ha) (part_of i Ed) (gpos_k i da0 (gkept ks0 ka0) [] (skipn (length Ed) (gxks ks0 ka0))) (bound_in i Ed)
                          R' L A m' md k qd es_c hs_c kss LB OUTc CAPc junkc)
      by (apply (gsk_GI_cur _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG'); intros _ Hc; exact (gsk_cur_step _ _ _ _ _ _ _ _ _ _ _ _ _ Hn Hp Hc)).
    all: assert (PB' : rw_cells segs m' (gP + 8) [CB 48 (pf_bytes (gpre ++ [0]) ++ jr)])
      by (apply (rw_kb2 mem); [exact PB | intros j Hj; cbn in Hj; apply (mu_kb2 []);
            [exact MUr | exact WMr | unfold gP; lia | exact I]]).
    all: apply SR_ret.
    all: exists fx, R', L, A, m', md, k, qd, es_c, hs_c, kss, LB, OUTc, CAPc, junkc, jr, ka0, da0, Ha.
    + replace (Nat.ltb (S n) (length H)) with true by (symmetry; apply Nat.ltb_lt; lia).
      split; [rewrite SEGS; reflexivity|]. split; [exact FRM|]. split; [exact Hi|].
      repeat rewrite (getr_of_eqv _ _ _ X) by reflexivity. simp_regs.
      split; [exact R18|]. split; [exact R19|]. split; [exact R23|]. split; [exact R24|].
      split.
      { intros _. split; [f_equal; lia|]. split; [reflexivity|]. split; [reflexivity|].
        split; [f_equal; lia|]. split; reflexivity. }
      split; [exact PB'|]. exact HG''.
    + replace (Nat.ltb (S n) (length H)) with false by (symmetry; apply Nat.ltb_ge; lia).
      split; [rewrite SEGS; reflexivity|]. split; [exact FRM|]. split; [exact Hi|].
      repeat rewrite (getr_of_eqv _ _ _ X) by reflexivity. simp_regs.
      split; [exact R18|]. split; [exact R19|]. split; [exact R23|]. split; [exact R24|].
      split; [intros Hc; lia|].
      split; [exact PB'|]. exact HG''.
Qed.

(* ===== region gone_match ===== *)

Lemma gd_nodup : forall (l : list (list Z)), NoDup l -> List.NoDup l.
Proof.
  intros l H. induction H as [|x l Hx Hl IH]; constructor; [|exact IH].
  intros Hin. apply Hx. clear -Hin. induction l as [|y l IHl]; [destruct Hin|].
  destruct Hin as [<-|Hin]; [left | right; apply IHl; exact Hin].
Qed.

Lemma gd_gei_len : forall pre ks E H', gei pre ks = (E, H') -> (length E <= length ks)%nat.
Proof.
  intros pre ks E H' HG.
  pose proof (gei_loop_ok (length ks) pre 0 ks ltac:(lia) ltac:(intros j Hj; lia)) as GO.
  unfold gei in HG. rewrite HG in GO. cbv beta iota in GO. destruct GO as (GP & _ & _).
  apply Permutation_length in GP. rewrite length_app in GP. lia.
Qed.

Lemma gd_lines_len : forall j, Z.of_nat (length (lines_of j)) <= pl_of j.
Proof.
  intros j. unfold lines_of, entry_lines, pl_of.
  destruct (re_eof (nth j es no_entry) =? 0); [|cbn [length]; lia].
  pose proof (rig_lines_len (hs_state (fst (nth j hs no_hj))) (bzs (pending_stream (fst (nth j hs no_hj))))) as HL.
  unfold bzs in *. rewrite length_map in HL. lia.
Qed.

Lemma gd_ed_len : forall j e' h' ks0 Ed H, done0 j e' h' ks0 -> gei gpre ks0 = (Ed, H) ->
  Z.of_nat (length Ed) <= re_nheld (nth j es no_entry) + pl_of j.
Proof.
  intros j e' h' ks0 Ed H D HG.
  unfold done0 in D. cbv zeta in D. destruct D as (_ & _ & ND & SS & _).
  pose proof (gd_gei_len gpre ks0 Ed H HG) as L1.
  pose proof (rig_nodup_incl_len ks0 _ (gd_nodup ks0 ND) (fun y Hy => proj1 (SS y) Hy)) as L2.
  pose proof (rig_upds_len (keys_texts (re_keys (nth j es no_entry))) (entry_lines (nth j es no_entry) (nth j hs no_hj))) as L3.
  pose proof (gd_lines_len j) as L4. unfold lines_of in L4.
  assert (LKT : length (keys_texts (re_keys (nth j es no_entry))) = length (re_keys (nth j es no_entry)))
    by (unfold keys_texts; apply length_map).
  unfold re_nheld. lia.
Qed.

Lemma gm_sep : forall q k lo hi, 0 < k -> lo < hi ->
  (forall j, 0 <= j < k -> ~ in_img Bm (q + j)) -> (forall a, lo <= a < hi -> in_img Bm a) ->
  q + k <= lo \/ hi <= q.
Proof.
  intros q k lo hi Hk Hlh HQ HI.
  destruct (Z_le_gt_dec (q + k) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec hi q) as [D2|D2]; [right; exact D2|]. exfalso.
  destruct (Z_le_gt_dec lo q) as [D3|D3].
  - apply (HQ 0); [lia|]. rewrite Z.add_0_r. apply HI. lia.
  - apply (HQ (lo - q)); [lia|]. replace (q + (lo - q)) with lo by ring. apply HI. lia.
Qed.

Lemma gm_blk_noimg : forall L A m md q k j, MR L A m md -> In (q, k) (blocks L A) -> 0 <= j < k -> ~ in_img Bm (q + j).
Proof using AX.
  intros L A m md q k j HM Hin Hj. apply rig_blocks_in in Hin as (p & <- & Hp).
  exact (ax_blocks_img AX L A m md p k j HM Hp Hj).
Qed.

Lemma gm_keyf : forall L A m e n, entry_okk L A m e -> (n < length (re_keys e))%nat ->
  let kn := nth n (re_keys e) rig_dk in
  In (key_addr kn, Z.of_nat (length (key_text kn)) + 1) (blocks L A) /\
  fresh_block Bm (key_addr kn) (Z.of_nat (length (key_text kn)) + 1) /\
  (exists sl, bytes_at segs m (key_addr kn) (key_text kn ++ Z_to_bv 8 0 :: sl) /\
     (- (key_addr kn + Z.of_nat (length (key_text kn)) + 1)) mod 8 <= Z.of_nat (length sl)) /\
  ~ In (Z_to_bv 8 0) (key_text kn) /\ 14 <= Z.of_nat (length (key_text kn)) <= 6000 /\
  In (re_hp e, re_kh e) (blocks L A) /\ fresh_block Bm (re_hp e) (re_kh e) /\ 8 * re_nheld e <= re_kh e /\
  bytes_at segs m (re_hp e) (key_ptrs (re_keys e)) /\ re_nheld e < 2 ^ 26 /\
  NoDup (map key_addr (re_keys e)) /\ length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat.
Proof.
  intros L A m e n (ks & Eks & OK) Hn. cbv zeta.
  destruct (map_fst_keys (re_keys e) ks Eks) as (EA & ET & EL & EP & EX).
  unfold entry_ok in OK.
  destruct OK as (Heof & Hskip & Hp1 & Hp2 & Hfd & Hcap & HU & Hused & HUz & Hbuf & Hnh & Hhp & NDa & NDt & Hkeys).
  cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_junk re_hp re_kh re_keys with_keys] in *.
  unfold re_nheld in Hnh, Hhp |- *. cbn [re_keys with_keys] in Hnh, Hhp.
  assert (Hn' : (n < length ks)%nat) by lia.
  assert (FA : key_addr (nth n ks rig_dk) = key_addr (nth n (re_keys e) rig_dk)).
  { rewrite <- (map_nth key_addr ks rig_dk n), <- (map_nth key_addr (re_keys e) rig_dk n), EA. reflexivity. }
  assert (FT : key_text (nth n ks rig_dk) = key_text (nth n (re_keys e) rig_dk)).
  { rewrite <- (map_nth key_text ks rig_dk n), <- (map_nth key_text (re_keys e) rig_dk n), ET. reflexivity. }
  pose proof (proj1 (Forall_forall _ _) Hkeys _ (nth_In ks rig_dk Hn')) as (K1 & K2 & K3 & K4 & K5 & K6).
  rewrite FA, FT in *.
  split; [exact K1|]. split; [exact K2|]. split; [exists (key_slack (nth n ks rig_dk)); split; assumption|].
  split; [exact K4|]. split; [exact K5|].
  destruct Hhp as [(_ & Hk0)|(H1 & H2 & H3 & H4 & H5)]; [subst ks; cbn in Hn'; lia|].
  rewrite EP in H5. rewrite EL in H3, Hnh. rewrite EA in NDa.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H5|]. split; [exact Hnh|].
  split; [exact NDa|]. split; assumption.
Qed.

Lemma gm_rw_eqv : forall sg m A cs cs', rw_cells sg m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  rw_cells sg m A cs'.
Proof.
  intros sg m A cs cs' [[W B] (H0 & H1 & H)] W' E.
  assert (S : cells_size cs' = cells_size cs) by (rewrite <- !cells_bytes_length by assumption; rewrite E; reflexivity).
  split; [split; [exact W' | rewrite E; exact B]|]. rewrite S. split; [exact H0|]. split; [exact H1|]. exact H.
Qed.

Lemma gm_eb_wk : forall e ks, length (re_pad1 e) = 4%nat ->
  entry_bytes (with_keys e ks) = firstn 40 (entry_bytes e) ++ le8 (Z_to_bv 64 (re_hp e)) ++
    le4 (Z_to_bv 64 (Z.of_nat (length ks))) ++ re_pad2 e.
Proof.
  intros e ks H1.
  assert (F : forall e', length (re_pad1 e') = 4%nat -> firstn 40 (entry_bytes e') =
     le4 (Z_to_bv 64 (re_fd e')) ++ le4 (Z_to_bv 64 (re_eof e')) ++ le4 (Z_to_bv 64 (re_skip e')) ++
     re_pad1 e' ++ le8 (Z_to_bv 64 (re_buf e')) ++ le8 (Z_to_bv 64 (re_used e')) ++ le8 (Z_to_bv 64 (re_cap e'))).
  { intros e' He'. unfold entry_bytes.
    replace (le4 (Z_to_bv 64 (re_fd e')) ++ le4 (Z_to_bv 64 (re_eof e')) ++ le4 (Z_to_bv 64 (re_skip e')) ++ re_pad1 e' ++
      le8 (Z_to_bv 64 (re_buf e')) ++ le8 (Z_to_bv 64 (re_used e')) ++ le8 (Z_to_bv 64 (re_cap e')) ++
      le8 (Z_to_bv 64 (re_hp e')) ++ le4 (Z_to_bv 64 (re_nheld e')) ++ re_pad2 e')
    with ((le4 (Z_to_bv 64 (re_fd e')) ++ le4 (Z_to_bv 64 (re_eof e')) ++ le4 (Z_to_bv 64 (re_skip e')) ++ re_pad1 e' ++
      le8 (Z_to_bv 64 (re_buf e')) ++ le8 (Z_to_bv 64 (re_used e')) ++ le8 (Z_to_bv 64 (re_cap e'))) ++
      (le8 (Z_to_bv 64 (re_hp e')) ++ le4 (Z_to_bv 64 (re_nheld e')) ++ re_pad2 e')) by (rewrite <- !app_assoc; reflexivity).
    apply rigl_firstn_app_exact. rewrite !length_app, !length_le4, !length_le8, He'. reflexivity. }
  rewrite (F e H1).
  pose proof (proj1 (rig_entry_split (with_keys e ks) H1)) as E. rewrite E.
  rewrite (F (with_keys e ks) H1). reflexivity.
Qed.

Lemma gm_firstn_set : forall {X} i (y : X) l, firstn i (set_nth i y l) = firstn i l.
Proof. intros X i. induction i as [|i IH]; intros y [|a l]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma gm_skipn_set : forall {X} i (y : X) l, skipn (S i) (set_nth i y l) = skipn (S i) l.
Proof. intros X i. induction i as [|i IH]; intros y [|a l]; cbn; try reflexivity. apply IH. Qed.

Lemma gm_in_skipn : forall {X} k (l : list X) x, In x (skipn k l) -> In x l.
Proof. intros X k l x H. rewrite <- (firstn_skipn k l). apply in_or_app. right. exact H. Qed.

Lemma gm_tab : forall m es_c tl i, table_at Bm m G es_c tl -> (i < length es_c)%nat ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es_c ->
  let e := nth i es_c no_entry in
  let Sf := re_pad2 e ++ concat (map entry_bytes (skipn (S i) es_c)) ++ tl in
  rw_cells segs m G [CB (56 * i + 40) (concat (map entry_bytes (firstn i es_c)) ++ firstn 40 (entry_bytes e))] /\
  rw_cells segs m (G + 56 * Z.of_nat i + 40) [C8 (Z_to_bv 64 (re_hp e)); C4 (Z_to_bv 64 (re_nheld e))] /\
  rw_cells segs m (G + 56 * Z.of_nat i + 52) [CB (length Sf) Sf].
Proof.
  intros m es_c tl i [Htl Hc] Hi HP. cbv zeta. set (e := nth i es_c no_entry).
  assert (HL : Forall (fun e => length (entry_bytes e) = 56%nat) es_c).
  { apply Forall_forall. intros x Hx. destruct (proj1 (Forall_forall _ _) HP x Hx) as [A1 A2]. exact (rig_entry_len x A1 A2). }
  destruct (rig_concat_nth es_c i Hi HL) as [EC LP]. fold e in EC.
  destruct (proj1 (Forall_forall _ _) HP e (nth_In _ _ Hi)) as [P1 P2].
  pose proof (proj1 (rig_entry_split e P1)) as EE.
  assert (L40 : length (firstn 40 (entry_bytes e)) = 40%nat) by (rewrite firstn_length, (rig_entry_len e P1 P2); reflexivity).
  rewrite SEGS in Hc |- *.
  set (Pf := concat (map entry_bytes (firstn i es_c))) in EC, LP |- *.
  set (Sf := concat (map entry_bytes (skipn (S i) es_c))) in EC |- *.
  rewrite EC, EE in Hc.
  assert (Hc' : rw_cells rsegs m G ([CB (56 * i + 40) (Pf ++ firstn 40 (entry_bytes e))] ++
      [C8 (Z_to_bv 64 (re_hp e)); C4 (Z_to_bv 64 (re_nheld e))] ++
      [CB (length (re_pad2 e ++ Sf ++ tl)) (re_pad2 e ++ Sf ++ tl)])).
  { apply (gm_rw_eqv _ _ _ _ _ Hc).
    - cbn [cells_wf cell_wf app]. rewrite length_app, L40, LP. split; [lia|]. split; [exact I|]. split; [exact I|].
      split; [reflexivity|exact I].
    - cbn [cells_bytes cbytes app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
  destruct (rigc_cut _ _ _ _ _ Hc' eq_refl) as [C1 C23].
  destruct (rigc_cut _ _ _ [C8 _; C4 _] _ C23 eq_refl) as [C2 C3].
  cbn [cells_size csize] in C2, C3.
  split; [exact C1|]. split.
  - replace (G + 56 * Z.of_nat i + 40) with (G + Z.of_nat (56 * i + 40 + 0)) by lia. exact C2.
  - replace (G + 56 * Z.of_nat i + 52) with (G + Z.of_nat (56 * i + 40 + 0) + Z.of_nat (8 + (4 + 0))) by lia. exact C3.
Qed.

Lemma gm_tab_upd : forall m es_c tl i ks,
  Z.of_nat (length tl) = 896 - 56 * Z.of_nat (length es_c) -> (i < length es_c)%nat ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es_c ->
  let e := nth i es_c no_entry in
  let Sf := re_pad2 e ++ concat (map entry_bytes (skipn (S i) es_c)) ++ tl in
  rw_cells segs m G [CB (56 * i + 40) (concat (map entry_bytes (firstn i es_c)) ++ firstn 40 (entry_bytes e))] ->
  rw_cells segs m (G + 56 * Z.of_nat i + 40) [C8 (Z_to_bv 64 (re_hp e)); C4 (Z_to_bv 64 (Z.of_nat (length ks)))] ->
  rw_cells segs m (G + 56 * Z.of_nat i + 52) [CB (length Sf) Sf] ->
  table_at Bm m G (set_nth i (with_keys e ks) es_c) tl.
Proof.
  intros m es_c tl i ks Htl Hi HP. cbv zeta. set (e := nth i es_c no_entry). intros C1 C2 C3.
  set (e' := with_keys e ks).
  set (es' := set_nth i e' es_c).
  destruct (proj1 (Forall_forall _ _) HP e (nth_In _ _ Hi)) as [P1 P2].
  assert (HP' : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es').
  { apply Forall_forall. intros x Hx. apply rigl_in_set_nth in Hx as [Hx|Hx]; [exact (proj1 (Forall_forall _ _) HP x Hx)|].
    subst x. split; assumption. }
  assert (HL' : Forall (fun e => length (entry_bytes e) = 56%nat) es').
  { apply Forall_forall. intros x Hx. destruct (proj1 (Forall_forall _ _) HP' x Hx) as [A1 A2]. exact (rig_entry_len x A1 A2). }
  assert (HL : Forall (fun e => length (entry_bytes e) = 56%nat) es_c).
  { apply Forall_forall. intros x Hx. destruct (proj1 (Forall_forall _ _) HP x Hx) as [A1 A2]. exact (rig_entry_len x A1 A2). }
  assert (Hi' : (i < length es')%nat) by (unfold es'; rewrite rigl_set_nth_len; exact Hi).
  destruct (rig_concat_nth es' i Hi' HL') as [EC LP].
  unfold es' in EC, LP. rewrite gm_firstn_set in EC, LP. rewrite gm_skipn_set in EC.
  rewrite rigl_nth_set_nth in EC by exact Hi. rewrite Nat.eqb_refl in EC.
  unfold e' in EC. rewrite (gm_eb_wk e ks P1) in EC.
  split; [unfold es'; rewrite rigl_set_nth_len; exact Htl|].
  rewrite SEGS in C1, C2, C3 |- *.
  assert (C23 : rw_cells rsegs m (G + 56 * Z.of_nat i + 40)
                  ([C8 (Z_to_bv 64 (re_hp e)); C4 (Z_to_bv 64 (Z.of_nat (length ks)))] ++
                   [CB (length (re_pad2 e ++ concat (map entry_bytes (skipn (S i) es_c)) ++ tl))
                       (re_pad2 e ++ concat (map entry_bytes (skipn (S i) es_c)) ++ tl)])).
  { apply (rigc_join _ _ _ _ _ C2 C3). cbn [cells_size csize]. lia. }
  replace (G + 56 * Z.of_nat i + 40) with (G + Z.of_nat (cells_size [CB (56 * i + 40)
    (concat (map entry_bytes (firstn i es_c)) ++ firstn 40 (entry_bytes e))])) in C23 by (cbn [cells_size csize]; lia).
  pose proof (rigc_join _ _ _ _ _ C1 C23 eq_refl) as C.
  apply (gm_rw_eqv _ _ _ _ _ C).
  - cbn [cells_wf cell_wf]. split; [|exact I].
    rewrite length_app, (rigl_concat_len es' HL'). unfold es'. rewrite rigl_set_nth_len. lia.
  - cbn [cells_bytes cbytes app]. unfold es', e'. rewrite EC. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma gm_gei_len : forall f pre n H, (length (fst (gei_loop f pre n H)) <= length H - n)%nat.
Proof.
  induction f as [|f IH]; intros pre n H; cbn [gei_loop]; [cbn; lia|].
  destruct (Nat.ltb_spec n (length H)) as [Hn|Hn]; [|cbn; lia].
  destruct (has_prefix pre (nth n H [])).
  - pose proof (IH pre n (swap_remove [] n H)) as X.
    destruct (gei_loop f pre n (swap_remove [] n H)) as [E H'] eqn:EQ. cbn [fst] in X |- *.
    rewrite (rig_len_swap [] n H Hn) in X. cbn [length]. lia.
  - pose proof (IH pre (S n) H). lia.
Qed.

Definition gm_AT_GE (i : nat) (ks0 : list (list Z)) (n : nat) (H Ed : list (list Z)) (c : config) : Prop :=
  exists (fx : YK11.FPState) regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc jr ka0 da0 Ha,
    c = mkCfg (@YK11.mkst fx regs (Z_to_bv 64 GESTURE_END) mem (seg_rom segs)) md /\
    frm_zero (@fp_csr fx) /\ (i < length es)%nat /\
    getr regs 1 = Z_to_bv 64 0x13540 /\
    getr regs 10 = Z_to_bv 64 (key_addr (nth n (re_keys (nth i es_c no_entry)) rig_dk)) /\
    getr regs 18 = Z_to_bv 64 RIG_FMT /\ getr regs 19 = Z_to_bv 64 RIG_KEY /\ getr regs 23 = Z_to_bv 64 (Z.of_nat i) /\
    getr regs 24 = Z_to_bv 64 (G + 56 * Z.of_nat i) /\
    getr regs 9 = Z_to_bv 64 (Z.of_nat n) /\ getr regs 20 = Z_to_bv 64 (Z.of_nat (length gpre)) /\
    getr regs 25 = Z_to_bv 64 (8 * Z.of_nat n) /\
    rw_cells segs mem (gP + 8) [CB 48 (pf_bytes (gpre ++ [0]) ++ jr)] /\
    GI i (inner_cur i ks0 n H Ed ka0 da0 Ha) (part_of i Ed) (gpos_k i da0 (gkept ks0 ka0) [] (skipn (length Ed) (gxks ks0 ka0))) (bound_in i Ed)
      regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc.

Lemma gm_E : forall i ks0 n H Ed c, (n < length H)%nat -> has_prefix gpre (nth n H []) = true ->
  AT_IN i ks0 n H Ed c -> SR segs c (gm_AT_GE i ks0 n H Ed).
Proof.
  intros i ks0 n H Ed c Hn Hp HA.
  destruct HA as (fx & regs & L & A & mem & md & k & qd & es_c & hs_c & kss & LB & OUTc & CAPc & junkc & jr & ka0 & da0 & Ha &
    -> & FRM & Hi & R18 & R19 & R23 & R24 & HR & PB & HG).
  destruct (HR Hn) as (R9 & R20 & R21 & R25 & R26 & R27). clear HR.
  replace (Nat.ltb n (length H)) with true by (symmetry; apply Nat.ltb_lt; exact Hn).
  pose proof HG as HG0. unfold GI in HG0. cbv zeta in HG0.
  destruct HG0 as (G2 & G3 & G4 & G8 & G22 & CH & _ & _ & _ & _ & RA & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & HLE & _ & HEOK & _ & _ & _ & _ & _ & HCUR & _).
  destruct (HCUR Hi) as (_ & HK & _ & _ & _).
  assert (LK : length (re_keys (nth i es_c no_entry)) = length H)
    by (rewrite <- HK; unfold keys_texts; rewrite length_map; reflexivity).
  assert (OKK : entry_okk L A mem (nth i es_c no_entry)) by (apply (proj1 (Forall_forall _ _) HEOK); apply nth_In; lia).
  destruct (gsk_key L A mem (nth i es_c no_entry) n OKK ltac:(lia)) as (KB & KZ & NH & HPB & HP8 & HK8 & KP).
  unfold re_nheld in NH, HP8. rewrite LK in NH, HP8.
  pose proof CH as (M1 & _).
  destruct (mr_model Bm MR rig_laws L A mem md M1) as (Hh & Hl & _).
  pose proof (blk_low L A mem md _ _ M1 HPB ltac:(lia)) as HPL.
  pose proof (rig_blk L A mem md _ _ 0 M1 HPB ltac:(lia)) as (_ & HP4 & _ & _).
  pose proof gS_range as [[GSR1 GSR2] GSR3]. pose proof alloc_ceiling_val as ACV. pose proof K_val as KV.
  assert (NHk : nth n H [] = bzs (key_text (nth n (re_keys (nth i es_c no_entry)) rig_dk))).
  { rewrite <- HK. unfold keys_texts. exact (map_nth (fun k => bzs (key_text k)) (re_keys (nth i es_c no_entry)) rig_dk n). }
  assert (HPF : has_prefix gpre (map (fun b : byte => bv_unsigned b) (key_text (nth n (re_keys (nth i es_c no_entry)) rig_dk)))
                = true) by (rewrite NHk in Hp; exact Hp).
  assert (LP : 1 <= Z.of_nat (length gpre) < 48).
  { unfold gpre, instance_prefix, K_GESTURE. rewrite !length_app. cbn [length].
    pose proof (rigc_dec_len (bv_signed (getr regs0 10))). lia. }
  eapply (rig_run fx regs (Z_to_bv 64 0x13524) mem md); [exact RA | exact Hh | exact Hl | |].
  - unfold Regs6ss.mkR_of.
    assert (E2 : reg_get regs 2 = Z_to_bv 64 gP) by exact G2.
    assert (E9 : reg_get regs 9 = Z_to_bv 64 (Z.of_nat n)) by exact R9.
    assert (E20 : reg_get regs 20 = Z_to_bv 64 (Z.of_nat (length gpre))) by exact R20.
    assert (E21 : reg_get regs 21 = Z_to_bv 64 (key_addr (nth n (re_keys (nth i es_c no_entry)) rig_dk))) by exact R21.
    assert (E25 : reg_get regs 25 = Z_to_bv 64 (8 * Z.of_nat n)) by exact R25.
    assert (E26 : reg_get regs 26 = Z_to_bv 64 (Z.of_nat (length H))) by exact R26.
    assert (E27 : reg_get regs 27 = Z_to_bv 64 (re_hp (nth i es_c no_entry))) by exact R27.
    rewrite E2, E9, E20, E21, E25, E26, E27.
    rewrite SEGS in RA, KB, KP.
    pose proof PB as [[_ PBb] _]. cbn [cells_bytes cbytes] in PBb. rewrite app_nil_r in PBb.
    apply bytes_at_app in PBb. destruct PBb as [PBb _]. rewrite SEGS in PBb.
    apply (rig_segE SNCMP) with (m := normalize rsegs mem) (P := gP) (n := Z.of_nat n) (nh := Z.of_nat (length H))
      (hp := re_hp (nth i es_c no_entry)) (ka := key_addr (nth n (re_keys (nth i es_c no_entry)) rig_dk))
      (knext := key_addr (nth (S n) (re_keys (nth i es_c no_entry)) rig_dk)) (T := gpre)
      (x := key_text (nth n (re_keys (nth i es_c no_entry)) rig_dk)).
    + apply mem_inv_normalize.
    + exact (bytes_at_normalize rsegs mem _ _ RA KB).
    + exact KZ.
    + exact (bytes_at_normalize rsegs mem _ _ RA PBb).
    + exact (rigc_pre_nz (bv_signed (getr regs0 10))).
    + exact LP.
    + lia.
    + lia.
    + lia.
    + lia.
    + unfold gP. lia.
    + intros Hlt. apply (bytes_at_normalize rsegs mem _ _ RA).
      replace (re_hp (nth i es_c no_entry) + 8 * (Z.of_nat n + 1))
        with (re_hp (nth i es_c no_entry) + 8 * Z.of_nat (S n)) by lia.
      apply rig_key_ptrs_slot; [exact KP | lia].
  - intros s0 R' m' HQ REL ROS X.
    unfold rig_postE in HQ.
    destruct HQ as (x1 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m''
      & MU & WM & MI & HB).
    rewrite HPF in HB.
    destruct HB as [(_ & ->)|[(HF & _)|(HF & _)]]; [|discriminate HF|discriminate HF].
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *.
    pose proof RA as RAr; rewrite SEGS in RAr.
    pose proof (mem_rel_normalize rsegs mem RAr) as RN.
    pose proof (munch_rel rsegs [] mem _ m' _ RN REL ROS MU) as MUr.
    pose proof (wmono_rel rsegs mem _ m' _ RN REL ROS WM) as WMr.
    pose proof (ro_agree_same rsegs mem m' RAr ROS) as RA'.
    rewrite <- SEGS in WMr, RA'.
    assert (HG' : GI i (inner_cur i ks0 n H Ed ka0 da0 Ha) (part_of i Ed) (gpos_k i da0 (gkept ks0 ka0) [] (skipn (length Ed) (gxks ks0 ka0))) (bound_in i Ed)
                    R' L A m' md k qd es_c hs_c kss LB OUTc CAPc junkc)
      by (apply (GI_stack _ _ _ _ _ regs R' L A mem m' md k qd es_c hs_c kss LB OUTc CAPc junkc [] HG MUr WMr RA');
          [intros x _ Ox; exfalso; apply Ox; exact I | ..];
          repeat rewrite (getr_of_eqv _ _ _ X) by reflexivity; simp_regs; first [reflexivity | assumption]).
    assert (PB' : rw_cells segs m' (gP + 8) [CB 48 (pf_bytes (gpre ++ [0]) ++ jr)])
      by (apply (rw_kb2 mem); [exact PB | intros j Hj; cbn in Hj; apply (mu_kb2 []);
            [exact MUr | exact WMr | unfold gP; lia | exact I]]).
    apply SR_ret.
    exists fx, R', L, A, m', md, k, qd, es_c, hs_c, kss, LB, OUTc, CAPc, junkc, jr, ka0, da0, Ha.
    split; [rewrite SEGS; reflexivity|]. split; [exact FRM|]. split; [exact Hi|].
    repeat rewrite (getr_of_eqv _ _ _ X) by reflexivity. simp_regs.
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact R18|]. split; [exact R19|]. split; [exact R23|]. split; [exact R24|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact PB'|]. exact HG'.
Qed.

Definition gm_AT_RET (i : nat) (ks0 : list (list Z)) (n : nat) (H Ed : list (list Z)) (c : config) : Prop :=
  exists (fx : YK11.FPState) regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc jr ka0 da0 Ha,
    c = mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x13540) mem (seg_rom segs)) md /\
    frm_zero (@fp_csr fx) /\ (i < length es)%nat /\
    getr regs 18 = Z_to_bv 64 RIG_FMT /\ getr regs 19 = Z_to_bv 64 RIG_KEY /\ getr regs 23 = Z_to_bv 64 (Z.of_nat i) /\
    getr regs 24 = Z_to_bv 64 (G + 56 * Z.of_nat i) /\
    getr regs 9 = Z_to_bv 64 (Z.of_nat n) /\ getr regs 20 = Z_to_bv 64 (Z.of_nat (length gpre)) /\
    getr regs 25 = Z_to_bv 64 (8 * Z.of_nat n) /\
    rw_cells segs mem (gP + 8) [CB 48 (pf_bytes (gpre ++ [0]) ++ jr)] /\
    GI i (inner_cur i ks0 n H Ed ka0 da0 Ha) (part_of i (Ed ++ [nth n H []]))
      (gpos_k i da0 (gkept ks0 ka0) [RFree (Z.of_nat (length (nth n H [])) + 1) (snd (nth n Ha ([], adr0)))]
        (skipn (S (length Ed)) (gxks ks0 ka0))) (bound_in i (Ed ++ [nth n H []]))
      regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc.

Definition gm_AT_FREE (i : nat) (ks0 : list (list Z)) (n : nat) (H Ed : list (list Z)) (c : config) : Prop :=
  exists (fx : YK11.FPState) regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc jr ka0 da0 Ha,
    c = mkCfg (@YK11.mkst fx regs (Z_to_bv 64 RIG_FREE) mem (seg_rom segs)) md /\
    frm_zero (@fp_csr fx) /\ (i < length es)%nat /\
    getr regs 1 = Z_to_bv 64 0x13550 /\
    getr regs 10 = Z_to_bv 64 (key_addr (nth n (re_keys (nth i es_c no_entry)) rig_dk)) /\
    getr regs 18 = Z_to_bv 64 RIG_FMT /\ getr regs 19 = Z_to_bv 64 RIG_KEY /\ getr regs 23 = Z_to_bv 64 (Z.of_nat i) /\
    getr regs 24 = Z_to_bv 64 (G + 56 * Z.of_nat i) /\
    getr regs 9 = Z_to_bv 64 (Z.of_nat n) /\ getr regs 20 = Z_to_bv 64 (Z.of_nat (length gpre)) /\
    getr regs 25 = Z_to_bv 64 (8 * Z.of_nat n) /\
    rw_cells segs mem (gP + 8) [CB 48 (pf_bytes (gpre ++ [0]) ++ jr)] /\
    GI i (inner_cur i ks0 n H Ed ka0 da0 Ha) (part_of i (Ed ++ [nth n H []]))
      (gpos_k i da0 (gkept ks0 ka0) [RFree (Z.of_nat (length (nth n H [])) + 1) (snd (nth n Ha ([], adr0)))]
        (skipn (S (length Ed)) (gxks ks0 ka0))) (bound_in i (Ed ++ [nth n H []]))
      regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc.

Lemma gm_F : forall i ks0 n H Ed c, (n < length H)%nat ->
  gm_AT_RET i ks0 n H Ed c -> SR segs c (gm_AT_FREE i ks0 n H Ed).
Proof.
  intros i ks0 n H Ed c Hn HA.
  destruct HA as (fx & regs & L & A & mem & md & k & qd & es_c & hs_c & kss & LB & OUTc & CAPc & junkc & jr & ka0 & da0 & Ha &
    -> & FRM & Hi & R18 & R19 & R23 & R24 & R9 & R20 & R25 & PB & HG).
  pose proof HG as HG0. unfold GI in HG0. cbv zeta in HG0.
  destruct HG0 as (G2 & G3 & G4 & G8 & G22 & CH & _ & _ & _ & _ & RA & _ & _ & _ & HGB & _ & _ & _ & _ & _ & _ & _
    & _ & _ & HLE & HTAB & HEOK & _ & _ & _ & _ & _ & HCUR & _).
  destruct (HCUR Hi) as (_ & HK & _ & _ & _).
  assert (LK : length (re_keys (nth i es_c no_entry)) = length H)
    by (rewrite <- HK; unfold keys_texts; rewrite length_map; reflexivity).
  pose proof CH as (M1 & _).
  destruct (mr_model Bm MR rig_laws L A mem md M1) as (Hh & Hl & _).
  assert (Hic : (i < length es_c)%nat) by lia.
  destruct HTAB as (tl & HTAB).
  destruct (gc_entry L A mem md es_c tl i M1 Hic HGB HTAB HEOK) as (EC & _ & _).
  assert (OKK : entry_okk L A mem (nth i es_c no_entry)) by (apply (proj1 (Forall_forall _ _) HEOK); apply nth_In; lia).
  destruct (gsk_key L A mem (nth i es_c no_entry) n OKK ltac:(lia)) as (_ & _ & NH & HPB & HP8 & HK8 & KP).
  unfold re_nheld in NH, HP8. rewrite LK in NH, HP8.
  pose proof (blk_low L A mem md _ _ M1 HPB ltac:(lia)) as HPL.
  pose proof (rig_blk L A mem md _ _ 0 M1 HPB ltac:(lia)) as (_ & HP4 & _ & _).
  pose proof (rig_blk L A mem md G SRC_TABLE 0 M1 HGB ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)) as (_ & G4096 & _).
  pose proof gS_range as [[GSR1 GSR2] GSR3]. pose proof alloc_ceiling_val as ACV. pose proof K_val as KV.
  assert (I4 : (i < 4)%nat) by (pose proof NLE as N4; unfold gN in N4; lia).
  pose proof (rig_key_ptrs_slot segs mem _ _ n KP ltac:(lia)) as KS.
  eapply (rig_run fx regs (Z_to_bv 64 0x13540) mem md); [exact RA | exact Hh | exact Hl | |].
  - unfold Regs6ss.mkR_of.
    assert (E24 : reg_get regs 24 = Z_to_bv 64 (G + 56 * Z.of_nat i)) by exact R24.
    assert (E25 : reg_get regs 25 = Z_to_bv 64 (8 * Z.of_nat n)) by exact R25.
    rewrite E24, E25.
    assert (ROT : forall j, 0 <= j < Z.of_nat (cells_size [C8 (Z_to_bv 64 (re_hp (nth i es_c no_entry)));
                     C4 (Z_to_bv 64 (re_nheld (nth i es_c no_entry)))]) ->
                  ro_addr rsegs (Z_to_bv 64 (G + 56 * Z.of_nat i + 40 + j)) = false).
    { intros j Hj. cbn [cells_size csize] in Hj.
      replace (G + 56 * Z.of_nat i + 40 + j) with (G + (56 * Z.of_nat i + 40 + j)) by ring.
      apply (gc_blk_ro L A mem md G SRC_TABLE); [exact M1 | exact HGB | unfold SRC_TABLE, SRC_ENTRY; lia]. }
    rewrite SEGS in RA, EC, KS.
    apply (rig_segF) with (nh := re_nheld (nth i es_c no_entry)) (hp := re_hp (nth i es_c no_entry))
      (ka := key_addr (nth n (re_keys (nth i es_c no_entry)) rig_dk)).
    + exact (rw_cells_normalize rsegs mem _ _ RA EC ROT).
    + exact (bytes_at_normalize rsegs mem _ _ RA KS).
    + lia.
    + lia.
    + lia.
  - intros s0 R' m' HQ REL ROS X.
    cbv beta in HQ. subst s0.
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *.
    pose proof RA as RAr; rewrite SEGS in RAr.
    pose proof (mem_rel_normalize rsegs mem RAr) as RN.
    pose proof (munch_rel rsegs [] mem _ m' _ RN REL ROS (munch_refl [] _)) as MUr.
    pose proof (wmono_rel rsegs mem _ m' _ RN REL ROS (wmono_refl rsegs _)) as WMr.
    pose proof (ro_agree_same rsegs mem m' RAr ROS) as RA'.
    rewrite <- SEGS in WMr, RA'.
    assert (HG' : GI i (inner_cur i ks0 n H Ed ka0 da0 Ha) (part_of i (Ed ++ [nth n H []]))
                    (gpos_k i da0 (gkept ks0 ka0) [RFree (Z.of_nat (length (nth n H [])) + 1) (snd (nth n Ha ([], adr0)))]
        (skipn (S (length Ed)) (gxks ks0 ka0)))
                    (bound_in i (Ed ++ [nth n H []])) R' L A m' md k qd es_c hs_c kss LB OUTc CAPc junkc)
      by (apply (GI_stack _ _ _ _ _ regs R' L A mem m' md k qd es_c hs_c kss LB OUTc CAPc junkc [] HG MUr WMr RA');
          [intros x _ Ox; exfalso; apply Ox; exact I | ..];
          repeat rewrite (getr_of_eqv _ _ _ X) by reflexivity; simp_regs; first [reflexivity | assumption]).
    assert (PB' : rw_cells segs m' (gP + 8) [CB 48 (pf_bytes (gpre ++ [0]) ++ jr)])
      by (apply (rw_kb2 mem); [exact PB | intros j Hj; cbn in Hj; apply (mu_kb2 []);
            [exact MUr | exact WMr | unfold gP; lia | exact I]]).
    apply SR_ret.
    exists fx, R', L, A, m', md, k, qd, es_c, hs_c, kss, LB, OUTc, CAPc, junkc, jr, ka0, da0, Ha.
    split; [rewrite SEGS; reflexivity|]. split; [exact FRM|]. split; [exact Hi|].
    repeat rewrite (getr_of_eqv _ _ _ X) by reflexivity. simp_regs.
    do 9 (split; [first [reflexivity | assumption]|]).
    split; [exact PB'|]. exact HG'.
Qed.

Lemma gm_skipn_map : forall {X Y} (f : X -> Y) (A : list X) B, skipn (length A) (map f A ++ B) = B.
Proof. intros X Y f A B. induction A as [|a A IH]; [reflexivity|]. exact IH. Qed.

Lemma gm_skipn_map_S : forall {X Y} (f : X -> Y) (A : list X) b B, skipn (S (length A)) (map f A ++ b :: B) = B.
Proof. intros X Y f A b B. induction A as [|a A IH]; [reflexivity|]. exact IH. Qed.

(* The key the loop ends next heads the lengths still to end. *)
Lemma gm_xls_split : forall ks0 Ed H n, (n < length H)%nat -> has_prefix gpre (nth n H []) = true ->
  gei gpre ks0 = (Ed ++ fst (gei_loop (length H - n) gpre n H), snd (gei_loop (length H - n) gpre n H)) ->
  skipn (length Ed) (gxls ks0) = Z.of_nat (length (nth n H [])) :: skipn (S (length Ed)) (gxls ks0).
Proof.
  intros ks0 Ed H n Hn Hp Hg. unfold gxls. rewrite Hg. cbn [fst].
  replace (length H - n)%nat with (S (length H - n - 1)) by lia.
  rewrite (rig_gei_match _ gpre n H Hn Hp). cbn [fst]. rewrite map_app. cbn [map].
  rewrite gm_skipn_map, gm_skipn_map_S. reflexivity.
Qed.

Lemma gm_nd_mid : forall (b1 b2 : list (Z * Z)) x y, NoDup (map fst (b1 ++ x :: b2)) -> In y (b1 ++ b2) ->
  fst y <> fst x.
Proof.
  intros b1 b2 x y ND Hy E. apply gdr_nd in ND. rewrite map_app in ND. cbn [map] in ND.
  apply List.NoDup_remove_2 in ND. apply ND. rewrite <- map_app, <- E. apply in_map. exact Hy.
Qed.

(* gesture_end replaces the output block (OUTc, CAPc), if any, by (OUT', CAP'). *)
Lemma gm_hbk_ge : forall L A L' A' mem md es_c hs_c OUTc CAPc OUT' CAP' b1 b2 c1 c2,
  MR L A mem md ->
  blocks L' A' = c1 ++ (OUT', CAP') :: c2 -> c1 ++ c2 = b1 ++ b2 ->
  ((CAPc = 0 /\ blocks L A = b1 ++ b2) \/ (0 < CAPc /\ blocks L A = b1 ++ (OUTc, CAPc) :: b2)) ->
  (CAPc = 0 -> OUTc = 0) ->
  hbk L A es_c hs_c OUTc -> hbk L' A' es_c hs_c OUT'.
Proof.
  intros L A L' A' mem md es_c hs_c OUTc CAPc OUT' CAP' b1 b2 c1 c2 HM EBL ECB EOB C0 HB q m Hq.
  assert (KEEP : In (q, m) (b1 ++ b2) -> In (q, m) (blocks L A) /\ q <> OUTc).
  { intros Hb. destruct EOB as [(Z0 & E0)|(Z0 & E0)].
    - split; [rewrite E0; exact Hb|]. intros Eq.
      pose proof (rig_blk_lo L A mem md q m HM ltac:(rewrite E0; exact Hb)) as LO. pose proof (C0 Z0). lia.
    - split.
      + rewrite E0. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left | right; right]; exact Hb.
      + intros Eq. apply (gm_nd_mid b1 b2 (OUTc, CAPc) (q, m)); [rewrite <- E0; exact (NODUP _ _ _ _ HM) | exact Hb | exact Eq]. }
  rewrite EBL in Hq. apply in_app_or in Hq as [Hq|[Hq|Hq]].
  - destruct (KEEP ltac:(rewrite <- ECB; apply in_or_app; left; exact Hq)) as [QA QN].
    destruct (HB q m QA) as [X|[X|[X|X]]]; [left; exact X | right; left; exact X | right; right; left; exact X | contradiction].
  - injection Hq as E1 E2. right; right; right. symmetry. exact E1.
  - destruct (KEEP ltac:(rewrite <- ECB; apply in_or_app; right; exact Hq)) as [QA QN].
    destruct (HB q m QA) as [X|[X|[X|X]]]; [left; exact X | right; left; exact X | right; right; left; exact X | contradiction].
Qed.

(* ----- gone_match sub-region GE (gesture_end call) ----- *)

(* gesture_end's call with its own liveness lvg and g_nout NOa against the model's step from nom. *)
Lemma gg_ge_bridge : forall lvg NOa nom capm XL j o, lvg = glv -> (glv = true -> NOa = nom) ->
  gesture_end_tr lvg (bv_unsigned mx) NOa capm XL j o = gesture_end_tr glv gmx nom capm XL j o /\
  gesture_end_cap lvg (bv_unsigned mx) NOa capm XL = gesture_end_cap glv gmx nom capm XL /\
  gesture_end_out lvg (bv_unsigned mx) NOa capm XL j o = gesture_end_out glv gmx nom capm XL j o.
Proof.
  intros lvg NOa nom capm XL j o -> LN. unfold gmx. revert LN. destruct glv; intros LN.
  - rewrite (LN eq_refl). split; [reflexivity | split; reflexivity].
  - split; [reflexivity | split; reflexivity].
Qed.

(* The key the loop ends next, with its address, heads the keys still to end. *)
Lemma gg_xks_split : forall ks0 ka0 Ed H n Ha Eda, (n < length H)%nat -> has_prefix gpre (nth n H []) = true ->
  map fst Ha = H -> map fst Eda = Ed ->
  geia gpre (combine ks0 ka0) =
    (Eda ++ fst (geia_loop (length Ha - n) gpre n Ha), snd (geia_loop (length Ha - n) gpre n Ha)) ->
  skipn (length Ed) (gxks ks0 ka0) =
    (Z.of_nat (length (nth n H [])), snd (nth n Ha ([], adr0))) :: skipn (S (length Ed)) (gxks ks0 ka0).
Proof.
  intros ks0 ka0 Ed H n Ha Eda Hn Hp HHa HEd Hg. subst H Ed. rewrite length_map in Hn.
  assert (HP : fst (nth n Ha ([], adr0)) = nth n (map fst Ha) [])
    by (rewrite <- (map_nth fst Ha ([], adr0) n); reflexivity).
  unfold gxks. rewrite Hg. cbn [fst].
  replace (length Ha - n)%nat with (S (length Ha - n - 1)) by lia.
  cbn [geia_loop]. rewrite (proj2 (Nat.ltb_lt n (length Ha)) Hn), HP, Hp.
  destruct (geia_loop (length Ha - n - 1) gpre n (swap_remove ([], adr0) n Ha)) as [E' H'].
  cbn [fst]. rewrite map_app. cbn [map]. rewrite length_map, gm_skipn_map, gm_skipn_map_S. cbn beta.
  rewrite ?HP. reflexivity.
Qed.

(* gpos_k at the next key to end: gesture_end's requests, then the rest after the key's free. *)
Lemma gg_gpos_step : forall i a kept xl ka rest nom capm j o,
  let g := gesture_end_tr glv gmx nom capm xl j o in
  let r := gpos_k i a kept [RFree (xl + 1) ka] rest (nom + xl + 5) (gesture_end_cap glv gmx nom capm xl) (j + nretF g)
             (gesture_end_out glv gmx nom capm xl j o) in
  gpos_k i a kept [] ((xl, ka) :: rest) nom capm j o = (g ++ fst (fst (fst r)), snd (fst (fst r)), snd (fst r), snd r).
Proof.
  intros i a kept xl ka rest nom capm j o. cbv zeta. unfold gpos_k. cbv zeta.
  change (nretF (@nil (rev sptr))) with 0%nat. change (nretF [RFree (xl + 1) ka]) with 0%nat. rewrite !Nat.add_0_r.
  cbn [keys_end_run fst snd].
  rewrite nret_app, CF.gestures_end_b.p3b_nret_cons. cbn [rets]. rewrite Nat.add_0_l, Nat.add_assoc.
  replace (nom + fold_right (fun xl0 acc => xl0 + 5 + acc) 0 (map fst ((xl, ka) :: rest)))
    with (nom + xl + 5 + fold_right (fun xl0 acc => xl0 + 5 + acc) 0 (map fst rest)) by (cbn [map fst fold_right]; ring).
  rewrite <- app_assoc. reflexivity.
Qed.

(* A live block of positive size that a callee does not free stays live at the same address. *)
Lemma gg_live_rp : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p a n,
  MR L1 A1 m1 md1 -> relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 -> live_at L1 A1 p a n ->
  (exists k, In (a, k) (blocks L1 A1) /\ 0 < k) -> ~ F' a -> live_at L2 A2 p a n.
Proof.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p a n HM RP [H1 E1] (k & Hk & Hk0) HF.
  assert (En : n = k).
  { apply (rig_nodup_fst (blocks L1 A1) a); [exact (proj1 (gdr_nd _) (NODUP _ _ _ _ HM)) | | exact Hk].
    apply rig_blocks_in. exists p. split; [exact E1 | exact H1]. }
  subst k. destruct RP as (_ & _ & _ & _ & _ & AD & SV & _). rewrite <- E1 in HF.
  assert (H2 : In (p, n) (user_blocks A2)) by exact (SV p n H1 Hk0 HF).
  split; [exact H2|]. rewrite (AD p n H1 H2 HF). exact E1.
Qed.

Lemma gm_GE : forall i ks0 n H Ed c, (n < length H)%nat -> has_prefix gpre (nth n H []) = true ->
  gm_AT_GE i ks0 n H Ed c -> SR segs c (gm_AT_RET i ks0 n H Ed).
Proof.
  intros i ks0 n H Ed c Hn Hp HA.
  destruct HA as (fx & regs & L & A & mem & md & k & qd & es_c & hs_c & kss & LB & OUTc & CAPc & junkc & jr & ka0 & da0 &
    HaK & -> & FRM & Hi & R1 & R10 & R18 & R19 & R23 & R24 & R9 & R20 & R25 & PB & HG).
  pose proof HG as HG0. unfold GI in HG0. cbv zeta in HG0.
  destruct HG0 as (G2 & G3 & G4 & G8 & G22 & CH & INIT & RES & BUD & POT & RA & GL & HNS & HGS & HGB & CCL & CBR & CDD
    & CEI & CERR & SRCH' & FR0 & FRB & FRS & HLE & HTAB & HEOK & HLH & HLK & HIL & HSRC & HDONE & HCUR & HPEND & HND
    & HSUR & HSV & HLB & HT & HDEAD & HLIVE).
  clear HG. gm_hide HDEAD. gm_hide HLIVE. gm_hide HCUR.
  pose proof Hcl as Hcl'. pose proof Hbr as Hbr'. pose proof Hdd as Hdd'. pose proof Hei as Hei'.
  pose proof HOUT0 as HOUT0'. gm_hide Hcl'. gm_hide Hbr'. gm_hide Hdd'. gm_hide Hei'. gm_hide HOUT0'.
  pose proof len_O as LO. pose proof gm_fcur_mono as FCM.
  gm_hide Hcl. gm_hide Hbr. gm_hide Hdd. gm_hide Hei. gm_hide HOUT0.
  pose proof gS_range as [[GSR1 GSR2] GSR3]. pose proof alloc_ceiling_val as ACV. pose proof K_val as KV.
  rewrite KV in GSR1.
  pose proof CH as (M1 & W1 & B1 & _).
  pose proof PRE as (_ & W0 & _ & _ & _ & _ & _ & _ & TP0 & _).
  destruct (HCUR Hi) as (D0 & HK & Hle & Hpf & Hgei & HHa & HLka & (Eda & HEda & HGa) & HEL & HSL).
  assert (LK : length (re_keys (nth i es_c no_entry)) = length H)
    by (rewrite <- HK; unfold keys_texts; rewrite length_map; reflexivity).
  assert (OKK : entry_okk L A mem (nth i es_c no_entry)) by (apply (proj1 (Forall_forall _ _) HEOK); apply nth_In; lia).
  assert (NHk : nth n H [] = bzs (key_text (nth n (re_keys (nth i es_c no_entry)) rig_dk))).
  { rewrite <- HK. unfold keys_texts. exact (map_nth (fun k => bzs (key_text k)) (re_keys (nth i es_c no_entry)) rig_dk n). }
  assert (KIN : In (key_addr (nth n (re_keys (nth i es_c no_entry)) rig_dk))
                  (concat (map entry_blocks es_c) ++ concat (map srcblk (combine es hs_c))))
    by (apply in_or_app; left; apply gm_key_in; lia).
  destruct (gm_keyf L A mem (nth i es_c no_entry) n OKK ltac:(lia)) as (KB & KF & (sl & KS & KSL) & KZ & KL & _).
  remember (nth n (re_keys (nth i es_c no_entry)) rig_dk) as kn eqn:Ekn. clear Ekn.
  pose proof KF as (KF1 & KF2 & KF3).
  destruct (gm_nd3 _ _ _ _ HND KIN) as (KNG & KNO).
  pose proof (gm_nd_ab _ _ _ HND) as GNO.
  assert (H2' : bv_unsigned (getr regs 2) = gP) by (rewrite G2; apply MState.unsigned_lit; unfold gP; lia).
  assert (SPR : spZ regs = gP)
    by (unfold spZ; transitivity (bv_unsigned (Z_to_bv 64 gP)); [f_equal; exact G2 | apply MState.unsigned_lit; unfold gP; lia]).
  assert (PAR : exists (nout' cap' out' : word) (Op jp : list byte),
    rw_cells segs mem G_OUTV [C8 mx; C8 nout'; C8 cap'; C8 out'] /\
    bv_unsigned out' = OUTc /\ bv_unsigned cap' = CAPc /\
    (send_live cl br dd (Z.of_nat (length LB)) = true -> bv_unsigned nout' = gNO + Z.of_nat (length LB) /\ Op = O ++ LB) /\
    (send_live cl br dd (Z.of_nat (length LB)) = false -> bv_unsigned nout' = gNO /\ Op = O /\ OUTc = gOUT /\ CAPc = gCAP /\
       nout' = nout /\ cap' = cap /\ out' = out) /\
    ((bv_unsigned cap' = 0 /\ bv_unsigned out' = 0 /\ bv_unsigned nout' = 0 /\ Op = []) \/
     (0 < bv_unsigned cap' /\ bv_unsigned nout' <= bv_unsigned cap' /\ In (bv_unsigned out', bv_unsigned cap') (blocks L A) /\
      fresh_block Bm (bv_unsigned out') (bv_unsigned cap') /\ bytes_at segs mem (bv_unsigned out') (Op ++ jp) /\
      Z.of_nat (length Op) = bv_unsigned nout' /\ Z.of_nat (length jp) = bv_unsigned cap' - bv_unsigned nout'))).
  { destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV.
    - destruct (HLIVE eq_refl) as (H1 & H2 & H3 & H4 & H5 & H6).
      pose proof (gm_live_nz _ LV) as TNZ.
      pose proof (rig_blk L A mem md OUTc CAPc 0 M1 H2 ltac:(lia)) as (_ & HO1 & HO2 & _).
      exists (Z_to_bv 64 (gNO + Z.of_nat (length LB))), (Z_to_bv 64 CAPc), (Z_to_bv 64 OUTc), (O ++ LB), junkc.
      rewrite !MState.unsigned_lit by lia.
      split; [exact H6|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; split; reflexivity|]. split; [intros X; discriminate X|].
      right. split; [lia|]. split; [lia|]. split; [exact H2|]. split; [exact H3|].
      split; [rewrite <- app_assoc; exact H4|]. split; [rewrite length_app; lia | lia].
    - destruct (HDEAD eq_refl) as (H1 & E1 & E2 & H3).
      exists nout, cap, out, O, junk.
      split; [exact H1|]. split; [rewrite E1; reflexivity|]. split; [rewrite E2; reflexivity|].
      split; [intros X; discriminate X|].
      split; [intros _; repeat split; first [reflexivity | assumption]|].
      destruct HOUT0' as [X|(Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7)]; [left; exact X|right].
      destruct (H3 Y1) as [Z1 Z2].
      split; [exact Y1|]. split; [exact Y2|]. split; [exact Z1|]. split; [exact Y4|]. split; [exact Z2|].
      split; assumption. }
  destruct PAR as (nout' & cap' & out' & Op & jp & COUT & EOUT & ECAP & PL1 & PL0 & PH).
  rewrite EOUT, ECAP in PH. gm_hide PL1. gm_hide PL0. gm_hide PH.
  assert (NOnn : 0 <= bv_unsigned nout') by (destruct PH as [(_ & _ & X & _)|(_ & _ & _ & _ & _ & X & _)]; lia).
  assert (OB : 0 < CAPc -> In (OUTc, CAPc) (blocks L A))
    by (intros X; destruct PH as [(Y & _)|(_ & _ & Y & _)]; [lia | exact Y]).
  gm_hide OB.
  destruct (rig_live_step cl br dd (Z.of_nat (length LB)) (Z.of_nat (length (key_text kn)) + 5) Hcl' Hbr' Hdd'
    ltac:(lia) ltac:(lia)) as [LS1 LS0]. gm_hide LS1. gm_hide LS0.
  destruct (rig_off_step cl br dd ei (Z.of_nat (length LB)) (Z.of_nat (length (key_text kn)) + 5) Hcl' Hbr' Hdd'
    ltac:(lia) ltac:(lia)) as (OS1 & OS2 & OS3 & OS4). gm_hide OS3. gm_hide OS4.
  assert (EQLG : send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd
                   (Z.of_nat (length (key_text kn)) + 5) =
                 send_live cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5))).
  { destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV.
    - destruct (LS1 eq_refl) as (_ & X & Y). rewrite X, Y.
      rewrite (proj2 (Z.eqb_neq (Z.of_nat (length (key_text kn)) + 5) 0) ltac:(lia)). reflexivity.
    - exact (proj1 (LS0 eq_refl)). }
  assert (LVM : send_live cl br dd (Z.of_nat (length LB)) = true ->
                send_live cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)) = true)
    by (intros X; exact (proj2 (proj2 (LS1 X)))).
  gm_hide LVM.
  assert (CPM : CAPc = (if send_live cl br dd (Z.of_nat (length LB)) then CAPc else gCAP)).
  { destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV; [reflexivity|].
    destruct (PL0 eq_refl) as (_ & _ & _ & X & _). exact X. }
  assert (NOM : glv = true -> bv_unsigned nout' = gNO + Z.of_nat (length LB)).
  { intros GLV. destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV; [exact (proj1 (PL1 eq_refl))|].
    destruct (Z.eq_dec (Z.of_nat (length LB)) 0) as [T0|TP].
    - rewrite (proj1 (PL0 eq_refl)), T0. lia.
    - rewrite (rig_live_pos cl br dd (Z.of_nat (length LB)) ltac:(lia)) in LV. unfold glv in GLV. rewrite GLV in LV.
      discriminate LV. }
  assert (NOle : bv_unsigned nout' <= gNO + Z.of_nat (length LB)).
  { destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV;
      [rewrite (proj1 (PL1 eq_refl)) | rewrite (proj1 (PL0 eq_refl))]; lia. }
  assert (NOEQ : send_live cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)) = true ->
                 bv_unsigned nout' = gNO + Z.of_nat (length LB) /\ Op = O ++ LB).
  { intros LVt. destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV; [exact (PL1 eq_refl)|].
    pose proof (proj2 (LS0 eq_refl) LVt) as T0'.
    assert (E0 : LB = []) by (apply length_zero_iff_nil; lia).
    destruct (PL0 eq_refl) as (E1 & E2 & _). rewrite E0, E1, E2, app_nil_r. split; [cbn; lia | reflexivity]. }
  gm_hide NOEQ.
  assert (EDL : Z.of_nat (length (Ed ++ [nth n H []])) <= re_nheld (nth i es no_entry) + pl_of i).
  { pose proof (gd_ed_len i _ _ ks0 _ _ D0 Hgei) as X.
    replace (length H - n)%nat with (S (length H - n - 1)) in X by lia.
    rewrite (rig_gei_match _ gpre n H Hn Hp) in X. cbn [fst] in X.
    rewrite !length_app in X |- *. cbn [length] in X |- *. lia. }
  assert (BND : Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5) <= gbound (length es)).
  { pose proof (gm_gb_mono (S i) (length es) ltac:(lia)) as X.
    rewrite gm_gbound_S in X. unfold bound_in in HT. rewrite length_app in EDL. cbn [length] in EDL. lia. }
  assert (MG : 2 * (bv_unsigned nout' + (Z.of_nat (length (key_text kn)) + 5)) < 2 ^ 63)
    by (apply (gm_mg _ (Z.of_nat (length LB))); lia).
  assert (XLE : Z.of_nat (length (nth n H [])) = Z.of_nat (length (key_text kn)))
    by (rewrite NHk; unfold bzs; rewrite length_map; reflexivity).
  destruct BUD as (oa & ssd & dsd & Lssd & Ldsd & EQ & OL & OD & DL).
  rewrite (gg_xks_split ks0 ka0 Ed H n HaK Eda Hn Hp HHa HEda HGa) in EQ.
  rewrite gg_gpos_step in EQ. cbv zeta in EQ. cbn [fst snd] in EQ. rewrite <- CPM, XLE in EQ.
  destruct RES as (RL & RW & RS).
  assert (EGT : exists rest, gtr = k ++ gesture_end_tr glv gmx (gNO + Z.of_nat (length LB)) CAPc
                  (Z.of_nat (length (key_text kn))) (nretF k) oa ++ rest)
    by (eexists; unfold gtr; rewrite EQ; reflexivity).
  destruct EGT as (rest & EGT).
  assert (OUTR : CAPc <> 0 -> forall post, resolveF (qd ++ post) oa = sptr_of L A OUTc).
  { intros Hc post. destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV.
    - symmetry. exact (CF.gestures_end_b.p3b_sptr_of_eq L A _ OUTc CAPc (NODUP _ _ _ _ M1) (OL eq_refl post)).
    - destruct (OD eq_refl) as [Eo Lo]. destruct (HDEAD eq_refl) as (_ & EO & EC & _). rewrite Eo, EO.
      rewrite EC in Hc. symmetry.
      exact (CF.gestures_end_b.p3b_sptr_of_eq L A _ gOUT gCAP (NODUP _ _ _ _ M1)
               (Lo ltac:(assert (0 <= gCAP) by (unfold gCAP; pose proof (bv_unsigned_in_range 64 cap); lia); lia))). }
  assert (LVG : send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd
                  (Z.of_nat (length (key_text kn)) + 5) = glv)
    by (exact (rig_live1 cl br dd (Z.of_nat (length LB)) (Z.of_nat (length (key_text kn)) + 5) Hcl' Hbr' Hdd'
                 ltac:(lia))).
  destruct (gg_ge_bridge _ (bv_unsigned nout') (gNO + Z.of_nat (length LB)) CAPc (Z.of_nat (length (key_text kn)))
              0 (known_at L A OUTc) LVG NOM) as (BGT & BGC & BGO).
  assert (ROOMg : forall qs, length qs = nretF (gesture_end_tr (send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd
                               (Z.of_nat (length (key_text kn)) + 5))
               (bv_unsigned mx) (bv_unsigned nout') CAPc (Z.of_nat (length (key_text kn))) 0 (known_at L A OUTc)) ->
            roomF RF qs (runF RF qd bnd k)
              (gesture_end_tr (send_live cl (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd
                               (Z.of_nat (length (key_text kn)) + 5))
               (bv_unsigned mx) (bv_unsigned nout') CAPc (Z.of_nat (length (key_text kn))) 0 (known_at L A OUTc))).
  { rewrite BGT. intros qc Hqc.
    pose proof (CF.gestures_end_b.p3b_ge_shape glv gmx (gNO + Z.of_nat (length LB)) CAPc (Z.of_nat (length (key_text kn)))
                  (nretF k) oa 0 (known_at L A OUTc)) as SH0.
    assert (NG : nretF gtr = (nretF k + nretF (gesture_end_tr glv gmx (gNO + Z.of_nat (length LB)) CAPc
                   (Z.of_nat (length (key_text kn))) (nretF k) oa) + nretF rest)%nat) by (rewrite EGT, !nret_app; lia).
    remember (repeat (SP 0 0) (nretF gtr - length qd - length qc)) as pad eqn:Epad.
    assert (LQ : length (qd ++ qc ++ pad) = nretF gtr) by (rewrite Epad, !length_app, repeat_length; lia).
    pose proof (ROOM0 _ LQ) as RQ. rewrite EGT in RQ. unfold roomF, room_run in RQ. rewrite !room_from_app in RQ.
    destruct RQ as (_ & RQ & _).
    assert (RK : run_from (rt_R RF) sptr (SP 0 0) (rt_malloc RF) (rt_free RF) (rt_realloc RF) (qd ++ qc ++ pad) bnd 0 k =
                 runF RF qd bnd k) by exact (RW (qc ++ pad)).
    rewrite RK, Nat.add_0_l, <- RL in RQ.
    destruct (CF.gestures_end_b.p3b_ge_sim RF glv gmx (gNO + Z.of_nat (length LB)) CAPc (Z.of_nat (length (key_text kn)))
                (qd ++ qc ++ pad) qc (length qd) 0 oa (known_at L A OUTc) (runF RF qd bnd k)) as (_ & S2 & _).
    { intros i0 Hi0. rewrite app_nth2 by lia. replace (length qd + i0 - length qd)%nat with i0 by lia.
      apply app_nth1. lia. }
    { intros Hc. rewrite (OUTR Hc (qc ++ pad)). reflexivity. }
    rewrite !Nat.add_0_r in S2. exact (proj1 S2 RQ). }
  assert (CPK : call_pre_k Bm MR GESTURE_END_K L A regs mem md).
  { destruct CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SW).
    split; [exact M1|]. split; [exact W1|]. split; [exact B1|].
    split; [assert (R1' : YK11.getr regs 1 = Z_to_bv 64 0x13540) by exact R1; rewrite R1'; apply bv_eq; vm_compute;
            reflexivity|].
    rewrite SPR. unfold GESTURE_END_K, GESTURE_END_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK.
    split; [unfold gP; replace (gS - 160) with (gS + (-10) * 16) by ring; rewrite Z.mod_add by lia; exact GSR3|].
    split; [unfold gP; lia|]. split; [unfold gP; lia|].
    split; [intros a Ha; apply SW; left; change (spZ regs0) with gS; rewrite KV; unfold gP in Ha; lia|].
    split; [exact (eq_trans G4 TP0)|].
    split; [intros a Ha; apply SW; right; exact Ha|].
    intros X. rewrite INIT in X. discriminate X. }
  pose proof (blk_low L A mem md _ _ M1 KB ltac:(lia)) as KLOW. rewrite KV in KLOW.
  destruct CERR as [ev Hev].
  pose proof (GEND fx L A regs mem md (runF RF qd bnd k) (key_text kn) sl Op jp cl
    (if send_off cl br (Z.of_nat (length LB)) then br else dd) dd
    (if send_off cl br (Z.of_nat (length LB)) then ei else 0) mx nout' cap' out' ev) as GE.
  cbv zeta in GE.
  assert (H10 : bv_unsigned (getr regs 10) = key_addr kn) by (rewrite R10; apply MState.unsigned_lit; lia).
  rewrite H10, H2', EOUT, ECAP in GE.
  specialize (GE SEGS CPK INIT TPE ltac:(unfold G_RELAY_HI, G_LOCK_HI in *; lia) RA KS KZ KSL ltac:(lia)).
  specialize (GE ltac:(destruct (gm_sep (key_addr kn) (Z.of_nat (length (key_text kn)) + 1) G_RELAY_LO G_RELAY_HI
                        ltac:(lia) ltac:(unfold G_RELAY_LO, G_RELAY_HI; lia) KF3
                        (fun a Ha => proj1 (IMGR a ltac:(unfold G_RELAY_LO, G_RELAY_HI, G_S, SRC_SIZE, SOURCES_MAX in *; lia))));
                      lia)).
  specialize (GE ltac:(destruct (gm_sep (key_addr kn) (Z.of_nat (length (key_text kn)) + 1) (errno_addr Bm)
                        (errno_addr Bm + 4) ltac:(lia) ltac:(lia) KF3 IMGE); lia)).
  specialize (GE ltac:(left; unfold gP, GESTURE_END_K, GESTURE_END_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK,
                        ALLOC_STACK; lia)).
  specialize (GE (fun a Ha => IMGR a ltac:(unfold G_RELAY_LO, G_RELAY_HI, G_S, SRC_SIZE, SOURCES_MAX in *; lia))
    IMGC IMGE IMG5).
  specialize (GE ltac:(exists (key_addr kn), (Z.of_nat (length (key_text kn)) + 1); split; [exact KB|];
                        split; [exact KF|]; split; [lia|]; split; [lia | exact KNO])).
  specialize (GE Hcl' OS3 Hdd' (OS4 Hei') CCL CBR CDD CEI COUT Hev).
  specialize (GE ltac:(destruct PH as [X|(Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7)]; [left; exact X | right];
                        do 7 (split; [assumption|]);
                        destruct (rig_blk_disj L A mem md _ _ _ _ M1 KB Y3 KNO); lia)).
  specialize (GE MG RS ROOMg).
  eapply SR_mono; [exact GE|]. clear GE.
  intros c' (L' & A' & R2 & m2 & md' & OUT' & CAP' & junk' & -> & RP & INIT' & RES' & RA2 & KB2
    & CCL2 & CBR2 & CDD2 & CEI2 & DEAD2 & LIVE2).
  destruct RES' as (qg & LQG & ROK' & RLK).
  rewrite BGT in LQG, ROK'. rewrite BGO in RLK. rewrite BGC in LIVE2.
  rewrite EQLG in RP, DEAD2, LIVE2, RLK. rewrite OS1 in CBR2. rewrite OS2 in CEI2. gm_hide DEAD2. gm_hide LIVE2.
  pose proof RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  assert (NSW : forall a, (in_img Bm a /\ ~ (G_BROKEN <= a < G_BROKEN + 1 \/ G_EINTR <= a < G_EINTR + 1 \/
                                             G_OUTV + 8 <= a < G_OUTV + 32)) \/ alloc_ceiling <= a ->
            ~ send_writes (send_live cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5))) OUTc CAPc a).
  { intros a Ha X. destruct (gdr_sw_img _ _ _ a X) as [(P & E)|(Elv & E)].
    - destruct Ha as [(_ & Ha)|Ha]; [exact (Ha E)|]. clear - Ha E ACV. unfold G_BROKEN, G_EINTR, G_OUTV in E. lia.
    - assert (C0 : 0 < CAPc) by (clear - E; lia).
      pose proof (rig_blk L A mem md OUTc CAPc 0 M1 (OB C0) ltac:(clear - C0; lia)) as (_ & _ & X3 & _).
      destruct Ha as [(Hin & _)|Ha]; [|clear - X3 E Ha; lia].
      apply (gdr_blk_img L A mem md OUTc CAPc (a - OUTc) M1 (OB C0) ltac:(clear - E; lia)).
      replace (OUTc + (a - OUTc)) with a by ring. exact Hin. }
  assert (NSC : forall a, (a < gP - GESTURE_END_K \/ gP <= a) -> ~ (errno_addr Bm <= a < errno_addr Bm + 4) ->
            ~ scratch_k Bm GESTURE_END_K regs a).
  { intros a H1 H2 [X|X]; [rewrite SPR in X; lia | exact (H2 X)]. }
  assert (GKa : forall a, (img_plain Bm a /\ ~ (G_BROKEN <= a < G_BROKEN + 1 \/ G_EINTR <= a < G_EINTR + 1 \/
                                                 G_OUTV + 8 <= a < G_OUTV + 32)) \/ gP <= a < 2 ^ 63 ->
            kb2 mem m2 a).
  { intros a [(P & NB)|S].
    - pose proof (in_img_low Bm SEGS a (proj1 P)) as LOW.
      apply (rp_gkept _ _ _ L A regs mem md L' A' R2 m2 md' a M1 RP);
        [left; exact P | apply NSW; left; split; [exact (proj1 P) | exact NB] |].
      apply NSC; [left; unfold gP, GESTURE_END_K, GESTURE_END_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK,
                    ALLOC_STACK; lia |].
      destruct P as (_ & _ & _ & P4). exact P4.
    - pose proof (in_img_low Bm SEGS (errno_addr Bm) (IMGE (errno_addr Bm) ltac:(lia))) as LOW.
      apply (rp_gkept _ _ _ L A regs mem md L' A' R2 m2 md' a M1 RP);
        [right; unfold gP in S; lia | apply NSW; right; unfold gP in S; lia |].
      apply NSC; [right; exact (proj1 S) | unfold gP in S; lia]. }
  assert (GKc : forall a cs, rw_cells segs mem a cs ->
            (forall j, 0 <= j < Z.of_nat (cells_size cs) ->
               (img_plain Bm (a + j) /\ ~ (G_BROKEN <= a + j < G_BROKEN + 1 \/ G_EINTR <= a + j < G_EINTR + 1 \/
                                            G_OUTV + 8 <= a + j < G_OUTV + 32)) \/ gP <= a + j < 2 ^ 63) ->
            rw_cells segs m2 a cs).
  { intros a cs Hc Hj. apply (rw_kb2 mem); [exact Hc|]. intros j Hj'. exact (GKa (a + j) (Hj j Hj')). }
  assert (GLOB : forall a, G_RELAY_LO <= a < G_S + SRC_SIZE * SOURCES_MAX ->
            ~ (G_BROKEN <= a < G_BROKEN + 1 \/ G_EINTR <= a < G_EINTR + 1 \/ G_OUTV + 8 <= a < G_OUTV + 32) ->
            (img_plain Bm a /\ ~ (G_BROKEN <= a < G_BROKEN + 1 \/ G_EINTR <= a < G_EINTR + 1 \/
                                   G_OUTV + 8 <= a < G_OUTV + 32)) \/ gP <= a < 2 ^ 63)
    by (intros a X1 X2; left; split; [exact (IMGR a X1) | exact X2]).
  assert (BK : forall q, (send_live cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)) = true ->
                          q <> OUTc) -> bkept L A mem L' A' m2 q).
  { intros q Hq. apply (rp_bkept _ _ _ L A regs mem md L' A' R2 m2 md' q M1 RP).
    - intros (X & Y). exact (Hq X Y).
    - intros k0 i0 Hin Hi0. exact (gm_sw_blk _ _ _ L A mem md q k0 i0 M1 Hin Hi0 OB Hq). }
  assert (NDR : forall q, In q (concat (map entry_blocks es_c) ++ concat (map srcblk (combine es hs_c))) -> q <> OUTc)
    by (intros q Hq; exact (proj2 (gm_nd3 _ _ _ _ HND Hq))).
  pose proof (CF.gestures_end_b.p3b_ge_shape glv gmx (gNO + Z.of_nat (length LB)) CAPc (Z.of_nat (length (key_text kn)))
                (nretF k) oa 0 (known_at L A OUTc)) as SH.
  assert (SIMR : forall post,
    runF RF (qd ++ qg ++ post) bnd (k ++ gesture_end_tr glv gmx (gNO + Z.of_nat (length LB)) CAPc
                                            (Z.of_nat (length (key_text kn))) (nretF k) oa) =
      runF RF qg (runF RF qd bnd k)
        (gesture_end_tr glv gmx (gNO + Z.of_nat (length LB)) CAPc (Z.of_nat (length (key_text kn))) 0 (known_at L A OUTc)) /\
    (gesture_end_cap glv gmx (gNO + Z.of_nat (length LB)) CAPc (Z.of_nat (length (key_text kn))) <> 0 ->
     resolveF (qd ++ qg ++ post)
       (gesture_end_out glv gmx (gNO + Z.of_nat (length LB)) CAPc (Z.of_nat (length (key_text kn))) (nretF k) oa) =
     resolveF qg
       (gesture_end_out glv gmx (gNO + Z.of_nat (length LB)) CAPc (Z.of_nat (length (key_text kn))) 0 (known_at L A OUTc)))).
  { intros post.
    destruct (CF.gestures_end_b.p3b_ge_sim RF glv gmx (gNO + Z.of_nat (length LB)) CAPc (Z.of_nat (length (key_text kn)))
                (qd ++ qg ++ post) qg (length qd) 0 oa (known_at L A OUTc) (runF RF qd bnd k)) as (S1 & _ & S3).
    { intros i0 Hi0. rewrite app_nth2 by lia. replace (length qd + i0 - length qd)%nat with i0 by lia.
      apply app_nth1. lia. }
    { intros Hc. rewrite (OUTR Hc (qg ++ post)). reflexivity. }
    rewrite !Nat.add_0_r, RL in S1, S3. split; [|exact S3].
    assert (RFA : forall qs t1 t2 b, runF RF qs b (t1 ++ t2) =
              run_from (rt_R RF) sptr (SP 0 0) (rt_malloc RF) (rt_free RF) (rt_realloc RF) qs (runF RF qs b t1) (nretF t1) t2)
      by (intros qs t1 t2 b; unfold runF, run_tr; rewrite run_from_app; reflexivity).
    rewrite RFA, (RW (qg ++ post)). exact S1. }
  pose proof (proj1 (SIMR [])) as S0. rewrite app_nil_r in S0.
  assert (LVE : forall j pz az nz, (j < length es)%nat -> In az (entry_blocks (nth j es_c no_entry)) ->
            live_at L A pz az nz -> live_at L' A' pz az nz).
  { intros j pz az nz Hj Hz Xz. apply (gg_live_rp _ _ _ L A regs mem md L' A' R2 m2 md' pz az nz M1 RP Xz).
    - apply (gdr_eblk L A mem (nth j es_c no_entry) az); [apply (proj1 (Forall_forall _ _) HEOK); apply nth_In; lia | exact Hz].
    - intros (_ & E). refine (NDR az _ E). apply in_or_app; left. apply in_concat. exists (entry_blocks (nth j es_c no_entry)).
      split; [apply in_map, nth_In; lia | exact Hz]. }
  assert (LVS : forall j pz az nz, (j < length es)%nat -> re_eof (nth j es no_entry) = 0 ->
            In az (hs_blocks (nth j hs_c (fst (nth j hs no_hj)))) -> live_at L A pz az nz -> live_at L' A' pz az nz).
  { intros j pz az nz Hj He Hz Xz. apply (gg_live_rp _ _ _ L A regs mem md L' A' R2 m2 md' pz az nz M1 RP Xz).
    - exact (gdr_hblk L A mem (gHA j) _ az (HSRC j Hj He) Hz).
    - intros (_ & E). refine (NDR az _ E). apply in_or_app; right. exact (gm_in_srcblk hs_c j az HLH Hj He Hz). }
  assert (QN0 : forall q m, In (q, m) (blocks L0 A0) -> 0 < m ->
            ~ Fcur (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)) q ->
            send_live cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)) = true -> q <> OUTc).
  { intros q m Hq Hm HF LVt.
    assert (HF0 : ~ Fcur (Z.of_nat (length LB)) q)
      by (intros X; apply HF; exact (FCM (Z.of_nat (length LB))
            (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)) q ltac:(lia) ltac:(lia) X)).
    destruct (HSV q m Hq Hm HF0) as [_ X].
    destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV; [exact (X eq_refl)|].
    destruct (PL0 eq_refl) as (_ & _ & E3 & _). rewrite E3. intros E. apply HF. left. split; [exact LVt | exact E]. }
  assert (CH0 : chain RELAY_INSTANCE_GONE_K Eall (Fcur (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)))
                  L0 A0 regs0 mem0 md0 L A mem md).
  { eapply chain_mono; [exact CH | intros a X; exact X |].
    intros q X. exact (FCM (Z.of_nat (length LB)) (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5))
                         q ltac:(lia) ltac:(lia) X). }
  assert (CH' : chain RELAY_INSTANCE_GONE_K Eall (Fcur (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)))
                  L0 A0 regs0 mem0 md0 L' A' m2 md').
  { eapply chain_callee; [exact W0 | exact CH0 | exact RP | | | |].
    - intros a [X|X]; [left | right; exact X]. rewrite SPR in X. change (spZ regs0) with gS. rewrite KV.
      unfold gP, GESTURE_END_K, GESTURE_END_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in *. lia.
    - intros a [X|X] Y; [|exfalso; apply Y; right; exact X].
      change (spZ regs0) with gS in X. rewrite KV in X. lia.
    - intros a X. destruct (gdr_sw_img _ _ _ a X) as [(P & E)|(Elv & E)].
      + split; [unfold G_BROKEN, G_EINTR, G_OUTV in E; lia|]. intros _. left. unfold send_writes.
        destruct E as [E|[E|E]]; [left | right; left | right; right; left]; exact E.
      + assert (C0 : 0 < CAPc) by (clear - E; lia).
        pose proof (rig_blk L A mem md OUTc CAPc 0 M1 (OB C0) ltac:(clear - C0; lia)) as (_ & _ & X3 & _).
        split; [clear - X3 E; lia|]. intros Hin. exfalso.
        apply (gdr_blk_img L A mem md OUTc CAPc (a - OUTc) M1 (OB C0) ltac:(clear - E; lia)).
        replace (OUTc + (a - OUTc)) with a by ring. exact Hin.
    - intros p n0 H0 H1 Hn0 HF.
      destruct (chain_in _ _ _ _ _ _ _ _ _ _ _ _ p n0 W0 CH0 H0 HF) as [_ EA].
      assert (QB : In (ptr_addr L0 p, n0) (blocks L A)) by (apply rig_blocks_in; exists p; split; [exact EA | exact H1]).
      assert (QB0 : In (ptr_addr L0 p, n0) (blocks L0 A0)) by (apply rig_blocks_in; exists p; split; [reflexivity | exact H0]).
      pose proof (QN0 _ _ QB0 Hn0 HF) as QN.
      split; [intros (X & Y); exact (QN X Y)|].
      intros i0 Hi0 _. exact (gm_sw_blk _ _ _ L A mem md _ n0 i0 M1 QB Hi0 OB QN). }
  assert (LT : Z.of_nat (length (LB ++ key_text kn ++ END5)) =
               Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5))
    by (rewrite !length_app; change (length END5) with 5%nat; lia).
  unfold gm_AT_RET.
  exists fx, R2, L', A', m2, md',
    (k ++ gesture_end_tr glv gmx (gNO + Z.of_nat (length LB)) CAPc (Z.of_nat (length (key_text kn))) (nretF k) oa),
    (qd ++ qg), es_c, hs_c, kss, (LB ++ key_text kn ++ END5),
    (if send_live cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)) then OUT' else OUTc),
    (if send_live cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)) then CAP' else CAPc),
    (if send_live cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)) then junk' else junkc), jr,
    ka0, da0, HaK.
  split; [rewrite R1; reflexivity|]. split; [exact FRM|]. split; [exact Hi|].
  split; [exact (eq_trans (RPr 18 ltac:(unfold callee_saved; lia)) R18)|].
  split; [exact (eq_trans (RPr 19 ltac:(unfold callee_saved; lia)) R19)|].
  split; [exact (eq_trans (RPr 23 ltac:(unfold callee_saved; lia)) R23)|].
  split; [exact (eq_trans (RPr 24 ltac:(unfold callee_saved; lia)) R24)|].
  split; [exact (eq_trans (RPr 9 ltac:(unfold callee_saved; lia)) R9)|].
  split; [exact (eq_trans (RPr 20 ltac:(unfold callee_saved; lia)) R20)|].
  split; [exact (eq_trans (RPr 25 ltac:(unfold callee_saved; lia)) R25)|].
  split; [apply (GKc _ _ PB); intros j Hj; cbn in Hj; right; unfold gP in *; lia|].
  unfold GI. cbv zeta. rewrite LT.
  split; [exact (eq_trans (RPr 2 ltac:(unfold callee_saved; lia)) G2)|].
  split; [exact (eq_trans (RPr 3 ltac:(unfold callee_saved; lia)) G3)|].
  split; [exact (eq_trans (RPr 4 ltac:(unfold callee_saved; lia)) G4)|].
  split; [exact (eq_trans (RPr 8 ltac:(unfold callee_saved; lia)) G8)|].
  split; [exact (eq_trans (RPr 22 ltac:(unfold callee_saved; lia)) G22)|].
  split; [exact CH'|]. split; [exact INIT'|].
  split.
  { split; [rewrite length_app, nret_app; lia|].
    split; [intros ext; rewrite <- app_assoc, (proj1 (SIMR ext)), S0; reflexivity|].
    rewrite S0. exact ROK'. }
  split.
  { assert (CAPM' : (if send_live cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)) then
                      (if send_live cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)) then CAP'
                       else CAPc) else gCAP) =
                    gesture_end_cap glv gmx (gNO + Z.of_nat (length LB)) CAPc (Z.of_nat (length (key_text kn)))).
    { destruct (send_live cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5))) eqn:LV'.
      - destruct (LIVE2 eq_refl) as (_ & LAc & _). exact LAc.
      - assert (GLF : glv = false)
          by (unfold glv; rewrite <- (rig_live_pos cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)))
                by lia; exact LV').
        assert (LV0 : send_live cl br dd (Z.of_nat (length LB)) = false)
          by (destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:X; [discriminate (LVM eq_refl) | reflexivity]).
        destruct (PL0 LV0) as (_ & _ & _ & X & _). rewrite GLF. unfold gesture_end_cap, send_line_cap. rewrite X.
        reflexivity. }
    exists (gesture_end_out glv gmx (gNO + Z.of_nat (length LB)) CAPc (Z.of_nat (length (key_text kn))) (nretF k) oa), ssd, dsd.
    split; [exact Lssd|]. split; [exact Ldsd|].
    split.
    { rewrite EQ, CAPM', XLE, nret_app, <- !app_assoc.
      replace (gNO + (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)))
        with (gNO + Z.of_nat (length LB) + Z.of_nat (length (key_text kn)) + 5) by ring.
      reflexivity. }
    split.
    { intros LVt post. rewrite LVt. rewrite <- app_assoc.
      destruct (LIVE2 LVt) as (LA1 & LAc & _).
      rewrite (proj2 (SIMR post) ltac:(rewrite <- LAc; lia)). exact (RLK LVt). }
    split.
    { intros LVf.
      assert (LV0 : send_live cl br dd (Z.of_nat (length LB)) = false)
        by (destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:X;
            [rewrite (LVM eq_refl) in LVf; discriminate LVf | reflexivity]).
      assert (GLF : glv = false)
        by (unfold glv; rewrite <- (rig_live_pos cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)))
              by lia; exact LVf).
      destruct (OD LV0) as [O1 O2]. rewrite GLF. split; [exact O1|].
      intros Hc. apply (gg_live_rp _ _ _ L A regs mem md L' A' R2 m2 md' _ _ _ M1 RP (O2 Hc)).
      - exists gCAP. split; [|exact Hc]. destruct (O2 Hc) as [X1 X2]. apply rig_blocks_in.
        exists (sptr_of L0 A0 gOUT). split; [exact X2 | exact X1].
      - intros (X & _). rewrite LVf in X. discriminate X. }
    intros j Hj post. rewrite <- app_assoc. destruct (DL j Hj (qg ++ post)) as [D1 D2]. split.
    - apply (gk_entry_mono L A L' A'); [|exact D1]. intros pz az nz Hz Xz. exact (LVE j pz az nz ltac:(lia) Hz Xz).
    - intros HE. apply (gk_src_mono L A L' A'); [|exact (D2 HE)]. intros pz az nz Hz Xz.
      exact (LVS j pz az nz ltac:(lia) HE Hz Xz). }
  split.
  { destruct (send_live cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5))) eqn:LV'.
    - destruct (LIVE2 eq_refl) as (_ & _ & _ & _ & _ & (b1 & b2 & c1 & c2 & EBL & ECB & EOB) & _).
      apply (gm_hbk_ge L A L' A' mem md es_c hs_c OUTc CAPc OUT' CAP' b1 b2 c1 c2 M1 EBL ECB EOB); [|exact POT].
      intros C0. destruct PH as [(_ & X & _)|(Y & _)]; [exact X | lia].
    - destruct (DEAD2 eq_refl) as (EB & _). intros q m Hq. rewrite EB in Hq. exact (POT q m Hq). }
  split; [exact RA2|].
  split; [apply (GKc _ _ GL); intros j Hj; cbn in Hj; apply GLOB;
          unfold G_LOCK, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, G_BROKEN, G_EINTR, G_OUTV; lia|].
  split; [apply (GKc _ _ HNS); intros j Hj; cbn in Hj; apply GLOB;
          unfold G_NSRC, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, G_BROKEN, G_EINTR, G_OUTV; lia|].
  split; [apply (GKc _ _ HGS); intros j Hj; cbn in Hj; apply GLOB;
          unfold G_SRC, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, G_BROKEN, G_EINTR, G_OUTV; lia|].
  split; [exact (gm_keep _ _ _ L A regs mem md L' A' R2 m2 md' G SRC_TABLE M1 RP HGB (fun _ X => GNO (proj2 X)))|].
  split; [exact CCL2|]. split; [exact CBR2|]. split; [exact CDD2|]. split; [exact CEI2|].
  split.
  { destruct (send_live cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5))) eqn:LV'.
    - destruct (LIVE2 eq_refl) as (_ & _ & _ & X & _). exact X.
    - destruct (DEAD2 eq_refl) as (_ & X & _). eexists. exact X. }
  split.
  { intros j Hj. apply (GKc _ _ (SRCH' j Hj)). intros x Hx. cbn in Hx. apply GLOB;
      unfold G_S, SRC_SIZE, SOURCES_MAX, G_RELAY_LO, G_BROKEN, G_EINTR, G_OUTV; lia. }
  split; [apply (GKc _ _ FR0); intros j Hj; cbn in Hj; right; unfold gP in *; lia|].
  split; [destruct FRB as (jb & Hjb); exists jb; apply (GKc _ _ Hjb); intros j Hj; cbn in Hj; right; unfold gP in *; lia|].
  split; [apply (GKc _ _ FRS); intros j Hj; unfold saved_cells in Hj; cbn in Hj; right; unfold gP in *; lia|].
  split; [exact HLE|].
  split.
  { destruct HTAB as (tl & Htl & Htr). exists tl. split; [exact Htl|].
    apply (rw_in_block L A mem L' A' m2 G SRC_TABLE);
      [exact Htr | apply BK; intros _; exact GNO | exact HGB | lia | cbn; unfold SRC_TABLE, SRC_ENTRY; lia]. }
  split.
  { apply Forall_forall. intros e He.
    apply (entry_okk_kept L A mem L' A' m2 md'); [exact (proj1 (Forall_forall _ _) HEOK e He) | exact M2 |].
    intros q Hq. apply BK. intros _. apply NDR. apply in_or_app. left. apply in_concat.
    exists (entry_blocks e). split; [apply in_map; exact He | exact Hq]. }
  split; [exact HLH|]. split; [exact HLK|]. split; [exact HIL|].
  split.
  { intros j Hj He. pose proof (gdr_src_lt4 j Hj He) as J4.
    apply (src_at_kept L A mem L' A' m2); [exact (HSRC j Hj He) | |].
    - intros x Hx. apply GKa. apply GLOB; unfold gHA, G_S, SRC_SIZE, SOURCES_MAX, G_RELAY_LO, G_BROKEN, G_EINTR, G_OUTV; lia.
    - intros q Hq. apply BK. intros _. apply NDR. apply in_or_app. right. exact (gm_in_srcblk hs_c j q HLH Hj He Hq). }
  split; [exact HDONE|].
  split.
  { intros _. split; [exact D0|]. split; [exact HK|]. split; [exact Hle|]. split; [exact Hpf|]. split; [exact Hgei|].
    split; [exact HHa|]. split; [exact HLka|]. split; [exists Eda; split; [exact HEda | exact HGa]|]. split.
    - intros post. rewrite <- app_assoc. apply (gk_entry_mono L A L' A'); [|exact (HEL (qg ++ post))].
      intros pz az nz Hz Xz. exact (LVE i pz az nz Hi Hz Xz).
    - intros HE post. rewrite <- app_assoc. apply (gk_src_mono L A L' A'); [|exact (HSL HE (qg ++ post))].
      intros pz az nz Hz Xz. exact (LVS i pz az nz Hi HE Hz Xz). }
  split.
  { intros j Hj. destruct (HPEND j Hj) as (P1 & P2 & PE & PS). split; [exact P1|]. split; [exact P2|]. split.
    - apply (gk_entry_mono L A L' A'); [|exact PE]. intros pz az nz Hz Xz. exact (LVE j pz az nz ltac:(lia) Hz Xz).
    - intros HE. apply (gk_src_mono L A L' A'); [|exact (PS HE)]. intros pz az nz Hz Xz. rewrite P1 in HE.
      exact (LVS j pz az nz ltac:(lia) HE Hz Xz). }
  split.
  { destruct (send_live cl br dd (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5))) eqn:LV'; cbv iota;
      [|exact HND].
    destruct (LIVE2 eq_refl) as (_ & _ & _ & _ & NO' & _).
    apply (gm_nd_out G OUTc OUT' _ HND).
    - intros E. apply (NO' G SRC_TABLE HGB GNO ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)). symmetry. exact E.
    - intros Hin. destruct (gm_R_pos L A mem es_c hs_c OUT' HLH HEOK HSRC Hin) as (k0 & Hk0 & Pk0).
      exact (NO' OUT' k0 Hk0 (NDR OUT' Hin) Pk0 eq_refl). }
  split.
  { intros q m Hq0 H1 H2 H3. pose proof (HSUR q m Hq0 H1 H2 H3) as Hq.
    apply (gm_keep _ _ _ L A regs mem md L' A' R2 m2 md' q m M1 RP Hq).
    intros Hm (X & Y). refine (QN0 q m Hq0 Hm _ X Y).
    intros [(_ & E)|[E|E]]; [exact (H1 E) | exact (H2 E) | exact (H3 E)]. }
  split.
  { intros q m Hq0 Hm HF.
    destruct (HSV q m Hq0 Hm (fun X => HF (FCM (Z.of_nat (length LB))
               (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)) q ltac:(lia) ltac:(lia) X))) as [X1 _].
    split; [exact X1|]. intros LVt. rewrite LVt. cbv iota.
    destruct (LIVE2 LVt) as (_ & _ & _ & _ & NO' & _).
    assert (QA : In (q, m) (blocks L A)).
    { apply HSUR; [exact Hq0 | intros E; apply HF; left; split; [exact LVt | exact E]
                  | intros E; apply HF; right; left; exact E | intros E; apply HF; right; right; exact E]. }
    exact (NO' q m QA (QN0 q m Hq0 Hm HF LVt) Hm). }
  split.
  { unfold bzs in HLB |- *. rewrite !map_app, HLB. unfold part_of. rewrite map_app, concat_app. cbn [map concat].
    rewrite NHk. unfold bzs. rewrite gm_bzs_end5, app_nil_r, <- !app_assoc. reflexivity. }
  split; [unfold bound_in in HT |- *; rewrite length_app; cbn [length]; lia|].
  split.
  { intros LVf. rewrite LVf. cbv iota.
    assert (LV0 : send_live cl br dd (Z.of_nat (length LB)) = false)
      by (destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:X;
          [rewrite (LVM eq_refl) in LVf; discriminate LVf | reflexivity]).
    destruct (PL0 LV0) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
    destruct (DEAD2 LVf) as (EB & _ & EOV).
    rewrite E5, E6, E7 in EOV.
    split; [exact EOV|]. split; [exact E3|]. split; [exact E4|].
    intros Hc. destruct (HDEAD LV0) as (_ & _ & _ & Hb). destruct (Hb Hc) as [Hb1 Hb2]. rewrite EB.
    split; [exact Hb1|].
    apply (bytes_in_block L A mem L' A' m2 gOUT gCAP);
      [exact Hb2 | apply BK; intros X; rewrite LVf in X; discriminate X | exact Hb1 | lia |].
    destruct HOUT0' as [(C0 & _)|(_ & _ & _ & _ & _ & HlO & Hlj)]; [lia|]. rewrite length_app. lia. }
  intros LVt. rewrite LVt. cbv iota.
  destruct (LIVE2 LVt) as (LA1 & _ & LA2 & _ & _ & (b1 & b2 & c1 & c2 & EBL & _ & _) & LA7 & LA8 & LA9).
  destruct (NOEQ LVt) as (EN & EO).
  rewrite EN in LA1, LA8, LA9. rewrite EO in LA7.
  split; [lia|]. split; [rewrite EBL; apply in_or_app; right; left; reflexivity|].
  split; [exact LA2|]. split; [rewrite <- !app_assoc in LA7; rewrite <- !app_assoc; exact LA7|]. split; [lia|].
  replace (gNO + (Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)))
    with (gNO + Z.of_nat (length LB) + (Z.of_nat (length (key_text kn)) + 5)) by ring.
  exact LA9.
Qed.

(* ----- gone_match sub-region FG (free call and swap-remove) ----- *)

Lemma gm_kb2_trans : forall m1 m2 m3 a, kb2 m1 m2 a -> kb2 m2 m3 a -> kb2 m1 m3 a.
Proof. intros m1 m2 m3 a [E1 W1] [E2 W2]. split; [congruence | intros X; exact (W2 (W1 X))]. Qed.

Lemma gm_bkept_trans : forall L A m L1 A1 m1 L2 A2 m2 q,
  bkept L A m L1 A1 m1 q -> bkept L1 A1 m1 L2 A2 m2 q -> bkept L A m L2 A2 m2 q.
Proof.
  intros L A m L1 A1 m1 L2 A2 m2 q B1 B2 k0 Hin. destruct (B1 k0 Hin) as [H1 K1]. destruct (B2 k0 H1) as [H2 K2].
  split; [exact H2|]. intros j Hj. exact (gm_kb2_trans _ _ _ _ (K1 j Hj) (K2 j Hj)).
Qed.

Lemma gm_c8_of : forall m a w, bytes_at segs m a (le8 w) -> (forall j, 0 <= j < 8 -> writable_at segs m (a + j)) ->
  rw_cells segs m a [C8 w].
Proof.
  intros m a w HB W. pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_le8 in BB.
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros j Hj. apply W. lia.
Qed.

Lemma gm_c8_bytes : forall m a w, rw_cells segs m a [C8 w] -> bytes_at segs m a (le8 w).
Proof. intros m a w [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

Lemma gm_in_rm : forall (b1 b2 : list (Z * Z)) x y, In y (b1 ++ x :: b2) -> fst y <> fst x -> In y (b1 ++ b2).
Proof.
  intros b1 b2 x y H N. apply in_app_or in H as [H|[H|H]]; apply in_or_app;
    [left; exact H | subst; exfalso; exact (N eq_refl) | right; exact H].
Qed.

(* The held array after the swap-remove of slot n: slot n holds the last key, the other slots are as they were. *)
Lemma gm_kp_swap : forall m m' hp (K : list (Z * list byte * list byte)) n,
  (n < length K)%nat -> 0 <= hp -> hp + 8 * Z.of_nat (length K) <= 2 ^ 64 ->
  bytes_at segs m hp (key_ptrs K) ->
  bytes_at segs m' (hp + 8 * Z.of_nat n) (le8 (Z_to_bv 64 (key_addr (nth (length K - 1) K rig_dk)))) ->
  (forall a, hp <= a < hp + 8 * Z.of_nat (length K) -> ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8) ->
     kb2 m m' a) ->
  bytes_at segs m' hp (key_ptrs (swap_remove rig_dk n K)).
Proof.
  intros m m' hp K n Hn H0 H1 KP Hs KK.
  apply rig_key_ptrs_bytes; [exact H0 | rewrite rig_len_swap by exact Hn; lia |].
  intros j Hj. rewrite rig_len_swap in Hj by exact Hn.
  rewrite (rig_nth_swap rig_dk n K j Hn Hj).
  destruct (Nat.eqb_spec j n) as [->|Ne]; [exact Hs|].
  apply (bytes_kb2 m); [exact (rig_key_ptrs_slot segs m hp K j KP ltac:(lia))|].
  intros x Hx. rewrite length_le8 in Hx. apply KK; [lia|].
  destruct (Nat.lt_ge_cases j n); lia.
Qed.

Lemma gm_eb_swap : forall e n q, (n < length (re_keys e))%nat -> In q (entry_blocks e) ->
  q <> key_addr (nth n (re_keys e) rig_dk) -> In q (entry_blocks (with_keys e (swap_remove rig_dk n (re_keys e)))).
Proof.
  intros e n q Hn Hq Hk. unfold entry_blocks in *. cbn [with_keys re_cap re_buf re_hp re_keys].
  apply in_app_or in Hq as [Hq|Hq]; [apply in_or_app; left; exact Hq|]. apply in_or_app; right.
  apply in_app_or in Hq as [Hq|Hq]; [apply in_or_app; left; exact Hq|]. apply in_or_app; right.
  rewrite rig_swap_map by exact Hn. apply rig_swap_keep; [rewrite length_map; exact Hn | exact Hq |].
  rewrite map_nth. exact Hk.
Qed.

Lemma gm_perm_eb : forall e n, (n < length (re_keys e))%nat ->
  Permutation (entry_blocks e)
    (key_addr (nth n (re_keys e) rig_dk) :: entry_blocks (with_keys e (swap_remove rig_dk n (re_keys e)))).
Proof.
  intros e n Hn. unfold entry_blocks. cbn [with_keys re_cap re_buf re_hp re_keys].
  rewrite rig_swap_map by exact Hn. rewrite !app_assoc.
  eapply Permutation_trans; [apply Permutation_app_head; apply (rigl_swap_perm (key_addr rig_dk) n);
                             rewrite length_map; exact Hn|].
  rewrite map_nth. apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma gm_perm_set : forall (l : list rentry) i y (kq : Z), (i < length l)%nat ->
  Permutation (entry_blocks (nth i l no_entry)) (kq :: entry_blocks y) ->
  Permutation (concat (map entry_blocks l)) (kq :: concat (map entry_blocks (set_nth i y l))).
Proof.
  induction l as [|a l IH]; intros [|i] y kq Hi HP; cbn [length] in Hi; try lia.
  - cbn [set_nth map concat nth] in *. exact (Permutation_app_tail _ HP).
  - cbn [set_nth map concat nth] in *.
    eapply Permutation_trans; [apply Permutation_app_head; exact (IH i y kq ltac:(lia) HP)|].
    apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma gm_concat_set : forall (l : list rentry) i y q, (i < length l)%nat -> In q (concat (map entry_blocks l)) ->
  (In q (entry_blocks (nth i l no_entry)) -> In q (entry_blocks y)) ->
  In q (concat (map entry_blocks (set_nth i y l))).
Proof.
  intros l i y q Hi Hq Hy. apply in_concat in Hq as (b & Hb & Hqb). apply in_map_iff in Hb as (x & <- & Hx).
  apply (In_nth _ _ no_entry) in Hx as (j & Hj & <-).
  apply in_concat. destruct (Nat.eq_dec j i) as [->|Ne].
  - exists (entry_blocks y). split; [|exact (Hy Hqb)]. apply in_map.
    assert (E : nth i (set_nth i y l) no_entry = y) by (rewrite rigl_nth_set_nth by exact Hi; rewrite Nat.eqb_refl; reflexivity).
    assert (Hin : In (nth i (set_nth i y l) no_entry) (set_nth i y l))
      by (apply nth_In; rewrite rigl_set_nth_len; exact Hi).
    rewrite E in Hin. exact Hin.
  - exists (entry_blocks (nth j l no_entry)). split; [|exact Hqb]. apply in_map.
    assert (E : nth j (set_nth i y l) no_entry = nth j l no_entry)
      by (rewrite rigl_nth_set_nth by exact Hi; rewrite (proj2 (Nat.eqb_neq j i) Ne); reflexivity).
    assert (Hin : In (nth j (set_nth i y l) no_entry) (set_nth i y l))
      by (apply nth_In; rewrite rigl_set_nth_len; exact Hj).
    rewrite E in Hin. exact Hin.
Qed.

(* An entry stays well formed when the key in slot n is freed and its slot takes the last key: the other blocks are
   kept and the held array holds the swapped pointers. *)
Lemma entry_okk_swap : forall L A m L' A' m' md' e n,
  entry_okk L A m e -> MR L' A' m' md' -> List.NoDup (entry_blocks e) -> (n < length (re_keys e))%nat ->
  (forall q, In q (entry_blocks e) -> q <> key_addr (nth n (re_keys e) rig_dk) -> q <> re_hp e ->
     bkept L A m L' A' m' q) ->
  In (re_hp e, re_kh e) (blocks L' A') ->
  bytes_at segs m' (re_hp e) (key_ptrs (swap_remove rig_dk n (re_keys e))) ->
  entry_okk L' A' m' (with_keys e (swap_remove rig_dk n (re_keys e))).
Proof.
  intros L A m L' A' m' md' e n (ks & Eks & OK) M' NDE Hn BK HPB' KP'.
  destruct (map_fst_keys (re_keys e) ks Eks) as (EA & ET & EL & EP & EX).
  assert (Hn' : (n < length ks)%nat) by lia.
  assert (EKW : map fst (swap_remove rig_dk n ks) = map fst (swap_remove rig_dk n (re_keys e))).
  { rewrite !rig_swap_map by lia. rewrite Eks. reflexivity. }
  assert (KQ : key_addr (nth n ks rig_dk) = key_addr (nth n (re_keys e) rig_dk)).
  { rewrite <- (map_nth key_addr ks rig_dk n), <- (map_nth key_addr (re_keys e) rig_dk n), EA. reflexivity. }
  unfold entry_ok in OK.
  destruct OK as (Heof & Hskip & Hp1 & Hp2 & Hfd & Hcap & HU & Hused & HUz & Hbuf & Hnh & Hhp & NDa & NDt & Hkeys).
  cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_junk re_hp re_kh re_keys with_keys] in *.
  unfold re_nheld in Hnh, Hhp. cbn [re_keys with_keys] in Hnh, Hhp.
  destruct Hhp as [(_ & Hk0)|(HinH & HfH & H8 & H8' & Hb0)]; [subst ks; cbn in Hn'; lia|].
  assert (HP0 : re_hp e <> 0) by (destruct HfH as (Hf0 & _); lia).
  pose proof NDE as NDE'. unfold entry_blocks in NDE'. rewrite (proj2 (Z.eqb_neq (re_hp e) 0) HP0) in NDE'.
  assert (HPK : ~ In (re_hp e) (map key_addr (re_keys e))).
  { pose proof (List.NoDup_app_remove_l _ _ NDE') as N. cbn [app] in N. apply List.NoDup_cons_iff in N as [N _]. exact N. }
  assert (KWin : forall k, In k (swap_remove rig_dk n ks) ->
            In k ks /\ key_addr k <> key_addr (nth n (re_keys e) rig_dk) /\ key_addr k <> re_hp e).
  { intros k Hk. pose proof (rig_swap_incl rig_dk n ks k Hk) as Hk1. split; [exact Hk1|]. split.
    - intros E. rewrite <- KQ in E.
      assert (Hk' : In (key_addr k) (swap_remove (key_addr rig_dk) n (map key_addr ks))).
      { rewrite <- rig_swap_map by lia. apply in_map. exact Hk. }
      apply (rig_swap_removed (key_addr rig_dk) n (map key_addr ks) ltac:(rewrite length_map; lia) (proj1 (gdr_nd _) NDa)).
      rewrite map_nth. rewrite <- E. exact Hk'.
    - intros E. apply HPK. rewrite <- E, <- EA. apply in_map. exact Hk1. }
  assert (KB : Forall (fun k => In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L' A')) (swap_remove rig_dk n ks)).
  { apply Forall_forall. intros k Hk. destruct (KWin k Hk) as (Hk1 & Hk2 & Hk3).
    pose proof (proj1 (Forall_forall _ _) Hkeys k Hk1) as (H1 & _).
    refine (proj1 (BK (key_addr k) _ Hk2 Hk3 _ H1)).
    unfold entry_blocks. apply in_or_app; right; apply in_or_app; right. rewrite <- EA. apply in_map. exact Hk1. }
  destruct (reslack L' A' m' md' _ M' KB) as (kw' & E' & F').
  destruct (map_fst_keys _ kw' E') as (EA' & ET' & EL' & EP' & EX').
  destruct (map_fst_keys _ _ EKW) as (_ & _ & _ & EP2 & _).
  exists kw'. split; [rewrite E'; exact EKW|].
  unfold entry_ok, re_nheld.
  cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_junk re_hp re_kh re_keys with_keys].
  rewrite EL', EP', EA', ET'.
  do 9 (split; [assumption|]).
  split.
  { destruct Hbuf as [Hb|(H0 & Hin & Hf & Hj & Hrw)]; [left; exact Hb|right].
    assert (Hq : In (re_buf e) ((if re_cap e =? 0 then [] else [re_buf e]))).
    { destruct (re_cap e =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|]. left. reflexivity. }
    assert (BN : re_buf e <> key_addr (nth n (re_keys e) rig_dk) /\ re_buf e <> re_hp e).
    { split; intros E; apply (rig_nodup_app_disj _ _ (re_buf e) NDE' Hq); rewrite E;
        [right; apply in_map; apply nth_In; lia | left; reflexivity]. }
    assert (Hq' : In (re_buf e) (entry_blocks e)) by (unfold entry_blocks; apply in_or_app; left; exact Hq).
    pose proof (BK _ Hq' (proj1 BN) (proj2 BN)) as Hb. destruct (Hb _ Hin) as [Hin' _].
    split; [exact H0|]. split; [exact Hin'|]. split; [exact Hf|]. split; [exact Hj|].
    eapply rw_in_block; [exact Hrw | exact Hb | exact Hin | lia | cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia]. }
  split; [rewrite rig_len_swap by exact Hn'; lia|].
  split.
  { right. split; [exact HPB'|]. split; [exact HfH|]. split; [rewrite rig_len_swap by exact Hn'; lia|].
    split; [exact H8'|]. rewrite EP2. exact KP'. }
  split.
  { apply gdr_nd. rewrite rig_swap_map by lia. apply rig_swap_nodup; [rewrite length_map; lia | exact (proj1 (gdr_nd _) NDa)]. }
  split.
  { apply gdr_nd. rewrite rig_swap_map by lia. apply rig_swap_nodup; [rewrite length_map; lia | exact (proj1 (gdr_nd _) NDt)]. }
  apply Forall_forall. intros k' Hk'.
  destruct (map_fst_in _ kw' k' E' Hk') as (k & Hk & Ek).
  destruct (KWin k Hk) as (Hk1 & Hk2 & Hk3).
  pose proof (proj1 (Forall_forall _ _) Hkeys k Hk1) as (H1 & H2 & H3 & H4 & H5 & H6).
  pose proof (proj1 (Forall_forall _ _) F' k' Hk') as (S1 & S2).
  assert (EK1 : key_addr k' = key_addr k) by (unfold key_addr; rewrite Ek; reflexivity).
  assert (EK2 : key_text k' = key_text k) by (unfold key_text; rewrite Ek; reflexivity).
  rewrite EK1, EK2 in *.
  assert (Hq : In (key_addr k) (entry_blocks e)).
  { unfold entry_blocks. apply in_or_app; right; apply in_or_app; right. rewrite <- EA. apply in_map. exact Hk1. }
  pose proof (BK _ Hq Hk2 Hk3) as Hb. destruct (Hb _ H1) as [H1' _].
  split; [exact H1'|]. split; [exact H2|].
  split.
  { replace (key_text k ++ Z_to_bv 8 0 :: key_slack k') with ((key_text k ++ [Z_to_bv 8 0]) ++ key_slack k')
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split.
    - replace (key_text k ++ Z_to_bv 8 0 :: key_slack k) with ((key_text k ++ [Z_to_bv 8 0]) ++ key_slack k) in H3
        by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app in H3. destruct H3 as [H3 _].
      eapply bytes_in_block; [exact H3 | exact Hb | exact H1 | lia | rewrite length_app; cbn [length]; lia].
    - rewrite length_app. cbn [length]. replace (key_addr k + Z.of_nat (length (key_text k) + 1))
        with (key_addr k + (Z.of_nat (length (key_text k)) + 1)) by lia. exact S1. }
  split; [exact H4|]. split; [exact H5|]. exact S2.
Qed.

Lemma gm_ltb : forall n m, (0 < m)%nat -> (Z.of_nat n <? Z.of_nat m - 1) = Nat.ltb n (m - 1).
Proof.
  intros n m Hm. destruct (Nat.ltb_spec n (m - 1)); destruct (Z.ltb_spec (Z.of_nat n) (Z.of_nat m - 1));
    first [reflexivity | lia].
Qed.

Lemma gk_f2_nth : forall {X Y : Type} (R : X -> Y -> Prop) (dx : X) (dy : Y) l l', Forall2 R l l' ->
  forall i, (i < length l)%nat -> R (nth i l dx) (nth i l' dy).
Proof.
  intros X Y R dx dy l l' F. induction F as [|x y l l' Rxy F IH]; intros [|i] Hi; cbn [length nth] in *; try lia.
  - exact Rxy.
  - apply IH. lia.
Qed.

Lemma gk_f2_of_nth : forall {X Y : Type} (R : X -> Y -> Prop) (dx : X) (dy : Y) l l', length l = length l' ->
  (forall i, (i < length l)%nat -> R (nth i l dx) (nth i l' dy)) -> Forall2 R l l'.
Proof.
  intros X Y R dx dy l. induction l as [|x l IH]; intros [|y l'] E K; cbn [length] in E; try lia; constructor.
  - apply (K 0%nat). cbn [length]. lia.
  - apply IH; [lia|]. intros i Hi. apply (K (S i)). cbn [length]. lia.
Qed.

Lemma gk_f2_swap : forall {X Y : Type} (R : X -> Y -> Prop) (dx : X) (dy : Y) n l l',
  Forall2 R l l' -> (n < length l)%nat -> Forall2 R (swap_remove dx n l) (swap_remove dy n l').
Proof.
  intros X Y R dx dy n l l' F Hn. pose proof (Forall2_length F) as EL.
  apply (gk_f2_of_nth R dx dy).
  - rewrite !rig_len_swap by lia. lia.
  - intros i Hi. rewrite rig_len_swap in Hi by lia.
    rewrite !rig_nth_swap by lia. rewrite <- EL.
    destruct (Nat.eqb i n); apply (gk_f2_nth R dx dy l l' F); lia.
Qed.

Lemma gk_live_free : forall L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 p q a n,
  call_post Bm MR L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 ->
  (forall q' k, In (q', k) (user_blocks A1) -> q' <> p -> In (q', k) (user_blocks A2)) ->
  live_at L1 A1 q a n -> a <> ptr_addr L1 p -> live_at L2 A2 q a n.
Proof.
  intros L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 p q a n CP SURV [H1 E1] Hne.
  pose proof CP as (_ & _ & _ & _ & AD & _).
  assert (H2 : In (q, n) (user_blocks A2)) by (apply SURV; [exact H1 | intros ->; exact (Hne (eq_sym E1))]).
  split; [exact H2|]. rewrite (AD q n H1 H2). exact E1.
Qed.

Lemma gk_eb_swap_ne : forall e n a, (n < length (re_keys e))%nat -> List.NoDup (entry_blocks e) ->
  In a (entry_blocks (with_keys e (swap_remove rig_dk n (re_keys e)))) -> a <> key_addr (nth n (re_keys e) rig_dk).
Proof.
  intros e n a Hn ND Ha E. subst a. unfold entry_blocks in ND, Ha. cbn [with_keys re_cap re_buf re_hp re_keys] in Ha.
  assert (XM : In (key_addr (nth n (re_keys e) rig_dk)) (map key_addr (re_keys e))) by (apply in_map, nth_In; exact Hn).
  pose proof (NoDup_app_remove_l _ _ ND) as ND1. pose proof (NoDup_app_remove_l _ _ ND1) as ND2.
  apply in_app_or in Ha as [Ha|Ha]; [exact (rig_nodup_app_disj _ _ _ ND Ha (in_or_app _ _ _ (or_intror XM)))|].
  apply in_app_or in Ha as [Ha|Ha]; [exact (rig_nodup_app_disj _ _ _ ND1 Ha XM)|].
  rewrite rig_swap_map in Ha by exact Hn.
  apply (rig_swap_removed (key_addr rig_dk) n (map key_addr (re_keys e))); [rewrite length_map; exact Hn | exact ND2 |].
  rewrite (map_nth key_addr (re_keys e) rig_dk n). exact Ha.
Qed.

Lemma gm_FG : forall i ks0 n H Ed c, (n < length H)%nat -> has_prefix gpre (nth n H []) = true ->
  gm_AT_FREE i ks0 n H Ed c -> SR segs c (AT_IN i ks0 n (swap_remove [] n H) (Ed ++ [nth n H []])).
Proof.
  intros i ks0 n H Ed c Hn Hp HA.
  destruct HA as (fx & regs & L & A & mem & md & k & qd & es_c & hs_c & kss & LB & OUTc & CAPc & junkc & jr & ka0 & da0 & HaK &
    -> & FRM & Hi & R1 & R10 & R18 & R19 & R23 & R24 & R9 & R20 & R25 & PB & HG).
  pose proof HG as HG0. unfold GI in HG0. cbv zeta in HG0.
  destruct HG0 as (G2 & G3 & G4 & G8 & G22 & CH & INIT & RES & BUD & POT & RA & GL & HNS & HGS & HGB & CCL & CBR & CDD
    & CEI & CERR & SRCH' & FR0 & FRB & FRS & HLE & HTAB & HEOK & HLH & HLK & HIL & HSRC & HDONE & HCUR & HPEND & HND
    & HSUR & HSV & HLB & HT & HDEAD & HLIVE).
  clear HG. gm_hide HDEAD. gm_hide HLIVE. gm_hide HCUR.
  gm_hide Hcl. gm_hide Hbr. gm_hide Hdd. gm_hide Hei. gm_hide HOUT0.
  pose proof gS_range as [[GSR1 GSR2] GSR3]. pose proof alloc_ceiling_val as ACV. pose proof K_val as KV.
  rewrite KV in GSR1.
  pose proof CH as (M1 & W1 & B1 & _).
  pose proof PRE as (_ & W0 & _ & _ & _ & _ & _ & _ & TP0 & _).
  destruct (HCUR Hi) as (D0 & HK & Hle & Hpf & Hgei & HHa & Hka & (Eda & HEda & HGA) & HL1 & HL2).
  assert (LK : length (re_keys (nth i es_c no_entry)) = length H)
    by (rewrite <- HK; unfold keys_texts; rewrite length_map; reflexivity).
  assert (Hic : (i < length es_c)%nat) by lia.
  assert (I4 : (i < 4)%nat) by (pose proof NLE as N4; unfold gN in N4; lia).
  assert (OKK : entry_okk L A mem (nth i es_c no_entry)) by (apply (proj1 (Forall_forall _ _) HEOK); apply nth_In; lia).
  destruct (gm_keyf L A mem (nth i es_c no_entry) n OKK ltac:(lia))
    as (KB & KF & _ & KZ & KL & HPB & HPF & HP8 & KP & NH26 & NDA & PD1 & PD2).
  remember (nth n (re_keys (nth i es_c no_entry)) rig_dk) as kn eqn:Ekn.
  remember (key_addr (nth (length (re_keys (nth i es_c no_entry)) - 1) (re_keys (nth i es_c no_entry)) rig_dk))
    as klast eqn:Ekl.
  assert (NHE : re_nheld (nth i es_c no_entry) = Z.of_nat (length H)) by (unfold re_nheld; rewrite LK; reflexivity).
  pose proof KF as (KF1 & KF2 & KF3).
  pose proof HPF as (HPF1 & HPF2 & HPF3).
  pose proof GF0 as (GF1 & GF2 & GF3).
  assert (HP0 : re_hp (nth i es_c no_entry) <> 0) by lia.
  assert (KEB : In (key_addr kn) (entry_blocks (nth i es_c no_entry))).
  { unfold entry_blocks. apply in_or_app; right; apply in_or_app; right. rewrite Ekn. apply in_map. apply nth_In. lia. }
  assert (HPEB : In (re_hp (nth i es_c no_entry)) (entry_blocks (nth i es_c no_entry))).
  { unfold entry_blocks. apply in_or_app; right; apply in_or_app; left.
    rewrite (proj2 (Z.eqb_neq (re_hp (nth i es_c no_entry)) 0) HP0). left. reflexivity. }
  assert (INC : forall q, In q (entry_blocks (nth i es_c no_entry)) -> In q (concat (map entry_blocks es_c))).
  { intros q Hq. apply in_concat. exists (entry_blocks (nth i es_c no_entry)). split; [|exact Hq].
    apply in_map, nth_In. lia. }
  pose proof (INC _ KEB) as KIN. pose proof (INC _ HPEB) as HPIN.
  destruct (gm_nd3 _ _ _ _ HND (in_or_app _ _ _ (or_introl KIN))) as (KNG & KNO).
  destruct (gm_nd3 _ _ _ _ HND (in_or_app _ _ _ (or_introl HPIN))) as (HPG & HPO).
  pose proof (gm_nd_ab _ _ _ HND) as GNO.
  pose proof (rig_nodup_pick G OUTc (map entry_blocks es_c) (map srcblk (combine es hs_c)) i
                ltac:(rewrite length_map; lia) ltac:(rewrite !length_map, length_combine; lia) (proj1 (gdr_nd _) HND)) as NDi.
  rewrite gdr_nth_eb in NDi.
  assert (NDE : List.NoDup (entry_blocks (nth i es_c no_entry))).
  { apply List.NoDup_cons_iff in NDi as [_ NDi]. apply List.NoDup_cons_iff in NDi as [_ NDi].
    exact (List.NoDup_app_remove_r _ _ NDi). }
  assert (NDES : List.NoDup (concat (map entry_blocks es_c) ++ concat (map srcblk (combine es hs_c)))).
  { pose proof (proj1 (gdr_nd _) HND) as N. apply List.NoDup_cons_iff in N as [_ N].
    apply List.NoDup_cons_iff in N as [_ N]. exact N. }
  assert (HPK : re_hp (nth i es_c no_entry) <> key_addr kn).
  { intros E. pose proof NDE as N. unfold entry_blocks in N.
    rewrite (proj2 (Z.eqb_neq (re_hp (nth i es_c no_entry)) 0) HP0) in N.
    apply List.NoDup_app_remove_l in N. cbn [app] in N. apply List.NoDup_cons_iff in N as [N _]. apply N.
    rewrite E, Ekn. apply in_map. apply nth_In. lia. }
  assert (HGHP : re_hp (nth i es_c no_entry) + re_kh (nth i es_c no_entry) <= G \/
                 G + SRC_TABLE <= re_hp (nth i es_c no_entry))
    by exact (rig_blk_disj L A mem md _ _ _ _ M1 HPB HGB HPG).
  assert (NHk : nth n H [] = bzs (key_text kn)).
  { rewrite <- HK, Ekn. unfold keys_texts. exact (map_nth (fun k => bzs (key_text k)) _ rig_dk n). }
  assert (XLE : Z.of_nat (length (nth n H [])) = Z.of_nat (length (key_text kn)))
    by (rewrite NHk; unfold bzs; rewrite length_map; reflexivity).
  assert (H2' : bv_unsigned (getr regs 2) = gP) by (rewrite G2; apply MState.unsigned_lit; unfold gP; lia).
  assert (SPR : spZ regs = gP)
    by (unfold spZ; transitivity (bv_unsigned (Z_to_bv 64 gP)); [f_equal; exact G2 | apply MState.unsigned_lit; unfold gP; lia]).
  destruct HTAB as (tl & HTAB).
  assert (HPD : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es_c).
  { apply Forall_forall. intros x Hx. destruct (proj1 (Forall_forall _ _) HEOK x Hx) as (ks & _ & (_ & _ & X1 & X2 & _)).
    exact (conj X1 X2). }
  destruct (gm_tab mem es_c tl i HTAB Hic HPD) as (TC1 & TC2 & TC3).
  assert (HL56 : Forall (fun e => length (entry_bytes e) = 56%nat) es_c).
  { apply Forall_forall. intros x Hx. exact (gdr_okk_len _ _ _ _ (proj1 (Forall_forall _ _) HEOK x Hx)). }
  assert (LSf : Z.of_nat (length (re_pad2 (nth i es_c no_entry) ++ concat (map entry_bytes (skipn (S i) es_c)) ++ tl))
                 = 844 - 56 * Z.of_nat i).
  { rewrite !length_app, PD2.
    rewrite (rigl_concat_len (skipn (S i) es_c))
      by (apply Forall_forall; intros x Hx; exact (proj1 (Forall_forall _ _) HL56 x (gm_in_skipn _ _ _ Hx))).
    rewrite length_skipn. destruct HTAB as [Htl _]. lia. }
  (* free (held[n]) *)
  assert (HnA : (n < length HaK)%nat) by (rewrite <- HHa, length_map in Hn; exact Hn).
  assert (KLn : live_at L A (resolveF qd (snd (nth n HaK ([], adr0)))) (key_addr kn) (Z.of_nat (length (key_text kn)) + 1)).
  { pose proof (HL1 []) as (_ & _ & KLF). rewrite app_nil_r in KLF. cbn [da_keys] in KLF.
    pose proof (gk_f2_nth _ rig_dk adr0 _ _ KLF n ltac:(lia)) as X. cbv beta in X.
    rewrite Ekn. rewrite <- (map_nth snd HaK ([], adr0) n). exact X. }
  set (p := resolveF qd (snd (nth n HaK ([], adr0)))) in *.
  destruct KLn as [Hpu Ep].
  assert (RSA : forall ext, resolveF (qd ++ ext) (snd (nth n HaK ([], adr0))) = p).
  { intros ext. pose proof (HL1 ext) as (_ & _ & KLF'). cbn [da_keys] in KLF'.
    pose proof (gk_f2_nth _ rig_dk adr0 _ _ KLF' n ltac:(lia)) as X'. cbv beta in X'.
    apply (CF.gestures_end_b.p3b_live_uniq L A _ _ (key_addr kn) (Z.of_nat (length (key_text kn)) + 1)
             (Z.of_nat (length (key_text kn)) + 1) (NODUP L A mem md M1)); [|exact (conj Hpu Ep)].
    rewrite Ekn. rewrite <- (map_nth snd HaK ([], adr0) n). exact X'. }
  assert (DJE : forall j a, (j < length es)%nat -> j <> i -> In a (entry_blocks (nth j es_c no_entry)) -> a <> key_addr kn).
  { intros j a Hj Ne Ha0 E. subst a.
    destruct (gdr_nodup_other G OUTc (map entry_blocks es_c) (map srcblk (combine es hs_c)) i j (key_addr kn)
                ltac:(rewrite !length_map, length_combine; lia) Ne (proj1 (gdr_nd _) HND)
                ltac:(rewrite gdr_nth_eb; apply in_or_app; left; exact Ha0)) as (_ & _ & Y3).
    rewrite gdr_nth_eb in Y3. apply Y3. apply in_or_app; left. exact KEB. }
  assert (DJS : forall j a, (j < length es)%nat -> re_eof (nth j es no_entry) = 0 ->
              In a (hs_blocks (nth j hs_c (fst (nth j hs no_hj)))) -> a <> key_addr kn).
  { intros j a Hj He Ha0 E. subst a. exact (rig_nodup_app_disj _ _ _ NDES KIN (gm_in_srcblk hs_c j _ HLH Hj He Ha0)). }
  pose proof (FREE fx) as FR. unfold free_contract_rt in FR. rewrite FREE_PC in FR.
  eapply SR_bind.
  { apply (FR L A regs mem md p (Z.of_nat (length (key_text kn)) + 1) (runF RF qd bnd k)).
    - destruct CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SW).
      split; [exact M1|]. split; [exact W1|]. split; [exact B1|].
      split; [assert (R1' : YK11.getr regs 1 = Z_to_bv 64 0x13550) by exact R1; rewrite R1'; apply bv_eq; vm_compute;
              reflexivity|].
      rewrite SPR. unfold ALLOC_STACK.
      split; [unfold gP; replace (gS - 160) with (gS + (-10) * 16) by ring; rewrite Z.mod_add by lia; exact GSR3|].
      split; [unfold gP; lia|]. split; [unfold gP; lia|].
      split; [intros a Ha; apply SW; left; change (spZ regs0) with gS; rewrite KV; unfold gP in Ha; lia|].
      split; [exact (eq_trans G4 TP0)|].
      split; [intros a Ha; apply SW; right; exact Ha|].
      intros X. rewrite INIT in X. discriminate X.
    - exact RA.
    - exact Hpu.
    - rewrite Ep. exact R10.
    - exact (proj2 (proj2 RES)). }
  intros c3 (L3 & A3 & R3 & m3 & md3 & -> & CP3 & (b1 & b2 & EB2 & EB3) & _ & RO3 & _ & SURV & INI3 & LN3 & RS3).
  rewrite Ep in EB2.
  pose proof CP3 as (M3 & W3 & B3 & LE3 & AD3 & RPr3 & VM3 & FR3 & BY3 & SW3).
  assert (FRL : forall pz az nz, live_at L A pz az nz -> az <> key_addr kn -> live_at L3 A3 pz az nz).
  { intros pz az nz X Ne. apply (gk_live_free L A regs mem md _ L3 A3 R3 m3 md3 p pz az nz CP3 SURV X).
    rewrite Ep. exact Ne. }
  destruct (mr_model Bm MR rig_laws L3 A3 m3 md3 M3) as (Hh3 & Hl3 & _).
  assert (HGB3 : In (G, SRC_TABLE) (blocks L3 A3)).
  { rewrite EB3. apply (gm_in_rm b1 b2 (key_addr kn, Z.of_nat (length (key_text kn)) + 1)); [rewrite <- EB2; exact HGB|].
    cbn [fst]. intros E. exact (KNG (eq_sym E)). }
  assert (HPB3 : In (re_hp (nth i es_c no_entry), re_kh (nth i es_c no_entry)) (blocks L3 A3)).
  { rewrite EB3. apply (gm_in_rm b1 b2 (key_addr kn, Z.of_nat (length (key_text kn)) + 1)); [rewrite <- EB2; exact HPB|].
    cbn [fst]. exact HPK. }
  assert (E2 : getr R3 2 = Z_to_bv 64 gP) by exact (eq_trans (RPr3 2 ltac:(unfold callee_saved; lia)) G2).
  assert (E3 : getr R3 3 = getr regs0 3) by exact (eq_trans (RPr3 3 ltac:(unfold callee_saved; lia)) G3).
  assert (E4 : getr R3 4 = getr regs0 4) by exact (eq_trans (RPr3 4 ltac:(unfold callee_saved; lia)) G4).
  assert (E8 : getr R3 8 = getr regs0 10) by exact (eq_trans (RPr3 8 ltac:(unfold callee_saved; lia)) G8).
  assert (E22 : getr R3 22 = Z_to_bv 64 RIG_S6) by exact (eq_trans (RPr3 22 ltac:(unfold callee_saved; lia)) G22).
  assert (E9 : getr R3 9 = Z_to_bv 64 (Z.of_nat n)) by exact (eq_trans (RPr3 9 ltac:(unfold callee_saved; lia)) R9).
  assert (E18 : getr R3 18 = Z_to_bv 64 RIG_FMT) by exact (eq_trans (RPr3 18 ltac:(unfold callee_saved; lia)) R18).
  assert (E19 : getr R3 19 = Z_to_bv 64 RIG_KEY) by exact (eq_trans (RPr3 19 ltac:(unfold callee_saved; lia)) R19).
  assert (E20 : getr R3 20 = Z_to_bv 64 (Z.of_nat (length gpre)))
    by exact (eq_trans (RPr3 20 ltac:(unfold callee_saved; lia)) R20).
  assert (E23 : getr R3 23 = Z_to_bv 64 (Z.of_nat i)) by exact (eq_trans (RPr3 23 ltac:(unfold callee_saved; lia)) R23).
  assert (E24 : getr R3 24 = Z_to_bv 64 (G + 56 * Z.of_nat i))
    by exact (eq_trans (RPr3 24 ltac:(unfold callee_saved; lia)) R24).
  assert (E25 : getr R3 25 = Z_to_bv 64 (8 * Z.of_nat n))
    by exact (eq_trans (RPr3 25 ltac:(unfold callee_saved; lia)) R25).
  assert (BKF : forall q, q <> key_addr kn -> bkept L A mem L3 A3 m3 q)
    by (intros q Hq; apply (cp_bkept L A regs mem md L3 A3 R3 m3 md3 p _ q M1 CP3 SURV); rewrite Ep; exact Hq).
  assert (GKF : forall a, (img_plain Bm a \/ alloc_ceiling <= a < 2 ^ 64) -> ~ scratch Bm regs a -> kb2 mem m3 a)
    by (intros a Ha Hs; exact (cp_gkept L A regs mem md L3 A3 R3 m3 md3 p _ a M1 Hpu CP3 Ha Hs)).
  assert (TC2' : rw_cells segs m3 (G + 56 * Z.of_nat i + 40)
                   [C8 (Z_to_bv 64 (re_hp (nth i es_c no_entry))); C4 (Z_to_bv 64 (re_nheld (nth i es_c no_entry)))]).
  { apply (rw_in_block L A mem L3 A3 m3 G SRC_TABLE _ _ TC2 (BKF G (fun E => KNG (eq_sym E))) HGB);
      [lia | cbn [cells_size csize]; unfold SRC_TABLE, SRC_ENTRY; lia]. }
  assert (KP3 : bytes_at segs m3 (re_hp (nth i es_c no_entry)) (key_ptrs (re_keys (nth i es_c no_entry)))).
  { apply (bytes_in_block L A mem L3 A3 m3 _ _ _ _ KP (BKF _ HPK) HPB); [lia|].
    rewrite length_key_ptrs. unfold re_nheld in HP8. lia. }
  assert (KL3 : bytes_at segs m3 (re_hp (nth i es_c no_entry) + 8 * (re_nheld (nth i es_c no_entry) - 1))
                  (le8 (Z_to_bv 64 klast))).
  { rewrite Ekl. replace (re_nheld (nth i es_c no_entry) - 1) with (Z.of_nat (length (re_keys (nth i es_c no_entry)) - 1))
      by (rewrite NHE, LK; lia).
    exact (rig_key_ptrs_slot segs m3 _ _ (length (re_keys (nth i es_c no_entry)) - 1) KP3 ltac:(lia)). }
  assert (KW3 : rw_cells segs m3 (re_hp (nth i es_c no_entry) + 8 * Z.of_nat n) [C8 (Z_to_bv 64 (key_addr kn))]).
  { apply gm_c8_of; [rewrite Ekn; exact (rig_key_ptrs_slot segs m3 _ _ n KP3 ltac:(lia))|].
    intros j Hj. apply rig_present_writable.
    replace (re_hp (nth i es_c no_entry) + 8 * Z.of_nat n + j) with (re_hp (nth i es_c no_entry) + (8 * Z.of_nat n + j))
      by ring.
    exact (proj1 (rig_blk L3 A3 m3 md3 _ _ (8 * Z.of_nat n + j) M3 HPB3 ltac:(unfold re_nheld in *; lia))). }
  (* the swap: held[n] = held[nheld - 1], nheld-- *)
  rewrite (R1 : YK11.getr regs 1 = Z_to_bv 64 0x13550).
  eapply (rig_run fx R3 (Z_to_bv 64 0x13550) m3 md3); [exact RO3 | exact Hh3 | exact Hl3 | |].
  - unfold Regs6ss.mkR_of.
    assert (X9 : reg_get R3 9 = Z_to_bv 64 (Z.of_nat n)) by exact E9.
    assert (X24 : reg_get R3 24 = Z_to_bv 64 (G + 56 * Z.of_nat i)) by exact E24.
    assert (X25 : reg_get R3 25 = Z_to_bv 64 (8 * Z.of_nat n)) by exact E25.
    rewrite X9, X24, X25.
    pose proof RO3 as RO3r. rewrite SEGS in RO3r, TC2', KL3, KW3.
    apply rig_segG with (hp := re_hp (nth i es_c no_entry)) (nh := re_nheld (nth i es_c no_entry)) (klast := klast)
      (w := Z_to_bv 64 (key_addr kn)).
    + apply mem_inv_normalize.
    + apply (rw_cells_normalize rsegs m3 _ _ RO3r TC2'). intros j Hj. cbn [cells_size csize] in Hj.
      replace (G + 56 * Z.of_nat i + 40 + j) with (G + (56 * Z.of_nat i + 40 + j)) by ring.
      apply (gc_blk_ro L3 A3 m3 md3 G SRC_TABLE); [exact M3 | exact HGB3 | unfold SRC_TABLE, SRC_ENTRY; lia].
    + exact (bytes_at_normalize rsegs m3 _ _ RO3r KL3).
    + apply (rw_cells_normalize rsegs m3 _ _ RO3r KW3). intros j Hj. cbn [cells_size csize] in Hj.
      replace (re_hp (nth i es_c no_entry) + 8 * Z.of_nat n + j) with (re_hp (nth i es_c no_entry) + (8 * Z.of_nat n + j))
        by ring.
      apply (gc_blk_ro L3 A3 m3 md3 _ _ _ M3 HPB3). lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + destruct HGHP; unfold SRC_TABLE, SRC_ENTRY in *; lia.
  - intros s0 R' m' HQ REL ROS X.
    unfold rig_postG in HQ. destruct HQ as (x10' & m'n & -> & MU & WM & MI & HC' & HW').
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *.
    pose proof RO3 as RAr. rewrite SEGS in RAr.
    pose proof (mem_rel_normalize rsegs m3 RAr) as RN.
    pose proof (munch_rel rsegs _ m3 _ m' m'n RN REL ROS MU) as MUr.
    pose proof (wmono_rel rsegs m3 _ m' m'n RN REL ROS WM) as WMr.
    pose proof (ro_agree_same rsegs m3 m' RAr ROS) as RA'.
    pose proof (rw_cells_of_rel rsegs _ _ _ _ REL HC') as HCr.
    pose proof (rw_cells_of_rel rsegs _ _ _ _ REL HW') as HWr.
    rewrite <- SEGS in WMr, RA', HCr, HWr.
    assert (OUTW : forall a, (in_img Bm a \/ alloc_ceiling <= a < 2 ^ 64) ->
              outside [(G + 56 * Z.of_nat i + 48, G + 56 * Z.of_nat i + 52);
                       (re_hp (nth i es_c no_entry) + 8 * Z.of_nat n, re_hp (nth i es_c no_entry) + 8 * Z.of_nat n + 8)] a).
    { intros a Ha. cbn [outside]. split; [|split; [|exact I]]; intros Hr.
      - destruct Ha as [Ha|Ha]; [|unfold SRC_TABLE, SRC_ENTRY in *; lia].
        apply (GF3 (a - G)); [unfold SRC_TABLE, SRC_ENTRY in *; lia|]. replace (G + (a - G)) with a by ring. exact Ha.
      - destruct Ha as [Ha|Ha]; [|unfold re_nheld in *; lia].
        apply (HPF3 (a - re_hp (nth i es_c no_entry))); [unfold re_nheld in *; lia|].
        replace (re_hp (nth i es_c no_entry) + (a - re_hp (nth i es_c no_entry))) with a by ring. exact Ha. }
    assert (KM : forall a, 0 <= a < 2 ^ 64 ->
              outside [(G + 56 * Z.of_nat i + 48, G + 56 * Z.of_nat i + 52);
                       (re_hp (nth i es_c no_entry) + 8 * Z.of_nat n, re_hp (nth i es_c no_entry) + 8 * Z.of_nat n + 8)] a ->
              kb2 m3 m' a)
      by (intros a Ha O'; exact (mu_kb2 _ m3 m' a MUr WMr Ha O')).
    assert (NSC : forall a, img_plain Bm a -> ~ scratch Bm regs a).
    { intros a P [X0|X0].
      - rewrite SPR in X0. pose proof (in_img_low Bm SEGS a (proj1 P)). unfold gP, ALLOC_STACK in *. lia.
      - destruct P as (_ & _ & _ & P4). exact (P4 X0). }
    assert (NSS : forall a, gP <= a < 2 ^ 63 -> ~ scratch Bm regs a).
    { intros a Ha [X0|X0].
      - rewrite SPR in X0. lia.
      - pose proof (in_img_low Bm SEGS (errno_addr Bm + 3) (IMGE (errno_addr Bm + 3) ltac:(lia))).
        unfold gP in *. lia. }
    assert (GK2 : forall a, (img_plain Bm a \/ alloc_ceiling <= a < 2 ^ 64) -> ~ scratch Bm regs a -> kb2 mem m' a).
    { intros a Ha Hs. apply (gm_kb2_trans _ m3); [exact (GKF a Ha Hs)|].
      assert (Ha' : in_img Bm a \/ alloc_ceiling <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [left; exact (proj1 Ha) | right; exact Ha]).
      apply KM; [|exact (OUTW a Ha')].
      destruct Ha' as [Ha'|Ha']; [pose proof (in_img_low Bm SEGS a Ha')|]; lia. }
    assert (GKc : forall a cs, rw_cells segs mem a cs -> (forall j, 0 <= j < Z.of_nat (cells_size cs) -> img_plain Bm (a + j)) ->
              rw_cells segs m' a cs).
    { intros a cs Hc Hj. apply (rw_kb2 mem); [exact Hc|]. intros j Hj'.
      apply GK2; [left; exact (Hj j Hj') | apply NSC; exact (Hj j Hj')]. }
    assert (BKM : forall q, q <> G -> q <> re_hp (nth i es_c no_entry) -> bkept L3 A3 m3 L3 A3 m' q).
    { intros q Q1 Q2. apply (mu_bkept L3 A3 _ m3 m' md3 q M3 MUr WMr). intros k0 j Hin Hj. cbn [outside].
      destruct (rig_blk_disj L3 A3 m3 md3 q k0 G SRC_TABLE M3 Hin HGB3 Q1) as [D1|D1];
      destruct (rig_blk_disj L3 A3 m3 md3 q k0 _ _ M3 Hin HPB3 Q2) as [D2|D2];
      unfold SRC_TABLE, SRC_ENTRY, re_nheld in *; (split; [lia | split; [lia | exact I]]). }
    assert (BKA : forall q, q <> key_addr kn -> q <> G -> q <> re_hp (nth i es_c no_entry) -> bkept L A mem L3 A3 m' q)
      by (intros q Q1 Q2 Q3; exact (gm_bkept_trans _ _ _ _ _ _ _ _ _ _ (BKF q Q1) (BKM q Q2 Q3))).
    assert (KG : forall j, 0 <= j < SRC_TABLE -> ~ (56 * Z.of_nat i + 48 <= j < 56 * Z.of_nat i + 52) -> kb2 mem m' (G + j)).
    { intros j Hj Hn0. destruct (BKF G (fun E => KNG (eq_sym E)) SRC_TABLE HGB) as [_ KK].
      apply (gm_kb2_trans _ m3); [exact (KK j Hj)|].
      apply KM; [unfold SRC_TABLE, SRC_ENTRY in *; lia | cbn [outside]; split; [lia | split; [|exact I]]].
      destruct HGHP; unfold SRC_TABLE, SRC_ENTRY, re_nheld in *; lia. }
    assert (CHf : chain RELAY_INSTANCE_GONE_K Eall (Fcur (Z.of_nat (length LB))) L0 A0 regs0 mem0 md0 L3 A3 m3 md3).
    { eapply (chain_free _ _ _ _ _ _ _ _ L A mem md regs L3 A3 R3 m3 md3 p);
        [exact W0 | exact CH | exact CP3 | exact SURV | exact LN3 | exact Hpu | lia | | |].
      - intros a [Ha|Ha]; [left | right; exact Ha]. rewrite SPR in Ha. change (spZ regs0) with gS. rewrite KV.
        unfold gP, ALLOC_STACK in *. lia.
      - intros a [Ha|Ha] Hn0; [|exfalso; apply Hn0; right; exact Ha]. change (spZ regs0) with gS in Ha. rewrite KV in Ha.
        assert (X0 : ~ (gP - ALLOC_STACK <= a < gP)) by (intros X0; apply Hn0; left; rewrite SPR; exact X0).
        unfold gP, ALLOC_STACK in *. lia.
      - intros p0 n0 H0 H1 HF E. subst p0.
        pose proof (rig_nodup_fst _ p n0 (Z.of_nat (length (key_text kn)) + 1) (YO10.user_block_ptrs_NoDup A W1) H1 Hpu)
          as En0.
        destruct (chain_in _ _ _ _ _ _ _ _ _ _ _ _ p n0 W0 CH H0 HF) as [_ EA].
        assert (QB0 : In (ptr_addr L0 p, n0) (blocks L0 A0)) by (apply rig_blocks_in; exists p; split; [reflexivity | exact H0]).
        destruct (HSV _ _ QB0 ltac:(lia) HF) as [X1 _]. apply X1. apply in_or_app. left. rewrite <- EA, Ep. exact KIN. }
    assert (CH' : chain RELAY_INSTANCE_GONE_K Eall (Fcur (Z.of_nat (length LB))) L0 A0 regs0 mem0 md0 L3 A3 m' md3).
    { apply (chain_munch _ _ _ _ _ _ _ _ _ _ _ _ _ _ CHf MUr WMr). intros x Hx O'. right; right.
      cbn [outside] in O'.
      assert (XW : (G + 56 * Z.of_nat i + 48 <= x < G + 56 * Z.of_nat i + 52) \/
                   (re_hp (nth i es_c no_entry) + 8 * Z.of_nat n <= x < re_hp (nth i es_c no_entry) + 8 * Z.of_nat n + 8))
        by (clear - O'; lia).
      destruct XW as [XW|XW].
      - split; [exists G, SRC_TABLE; split; [exact HGB3 | unfold SRC_TABLE, SRC_ENTRY; lia]|].
        intros p0 n0 _ _ _ _. unfold Eall. right; right; left. unfold SRC_TABLE, SRC_ENTRY; lia.
      - split; [exists (re_hp (nth i es_c no_entry)), (re_kh (nth i es_c no_entry)); split; [exact HPB3 | unfold re_nheld in *; lia]|].
        intros p0 n0 H0 H3 HF Hr. exfalso.
        destruct (chain_in _ _ _ _ _ _ _ _ _ _ _ _ p0 n0 W0 CHf H0 HF) as [_ EA].
        assert (QB3 : In (ptr_addr L0 p0, n0) (blocks L3 A3)) by (apply rig_blocks_in; exists p0; split; [exact EA | exact H3]).
        assert (QE : ptr_addr L0 p0 = re_hp (nth i es_c no_entry)).
        { destruct (Z.eq_dec (ptr_addr L0 p0) (re_hp (nth i es_c no_entry))) as [E|NE]; [exact E|].
          destruct (rig_blk_disj L3 A3 m3 md3 _ _ _ _ M3 QB3 HPB3 NE); unfold re_nheld in *; lia. }
        assert (QB0 : In (re_hp (nth i es_c no_entry), n0) (blocks L0 A0))
          by (rewrite <- QE; apply rig_blocks_in; exists p0; split; [reflexivity | exact H0]).
        rewrite QE in HF.
        destruct (HSV _ _ QB0 ltac:(lia) HF) as [X1 _]. apply X1. apply in_or_app. left. exact HPIN. }
    pose proof CH' as (M' & _).
    assert (PERM : Permutation (concat (map entry_blocks es_c))
                     (key_addr kn :: concat (map entry_blocks
                        (set_nth i (with_keys (nth i es_c no_entry) (swap_remove rig_dk n (re_keys (nth i es_c no_entry))))
                           es_c)))).
    { apply (gm_perm_set es_c i _ (key_addr kn) Hic). rewrite Ekn. apply gm_perm_eb. lia. }
    assert (NTHI : nth i (set_nth i (with_keys (nth i es_c no_entry) (swap_remove rig_dk n (re_keys (nth i es_c no_entry))))
                      es_c) no_entry =
                   with_keys (nth i es_c no_entry) (swap_remove rig_dk n (re_keys (nth i es_c no_entry))))
      by (rewrite rigl_nth_set_nth by exact Hic; rewrite Nat.eqb_refl; reflexivity).
    assert (NTHJ : forall j, j <> i ->
              nth j (set_nth i (with_keys (nth i es_c no_entry) (swap_remove rig_dk n (re_keys (nth i es_c no_entry))))
                       es_c) no_entry = nth j es_c no_entry)
      by (intros j Ne; rewrite rigl_nth_set_nth by exact Hic; rewrite (proj2 (Nat.eqb_neq j i) Ne); reflexivity).
    assert (KPS : bytes_at segs m' (re_hp (nth i es_c no_entry))
                    (key_ptrs (swap_remove rig_dk n (re_keys (nth i es_c no_entry))))).
    { apply (gm_kp_swap m3 m' (re_hp (nth i es_c no_entry)) (re_keys (nth i es_c no_entry)) n ltac:(lia) ltac:(lia)
               ltac:(unfold re_nheld in *; lia) KP3).
      - rewrite <- Ekl. exact (gm_c8_bytes _ _ _ HWr).
      - intros a Ha Hs. apply KM; [unfold re_nheld in *; lia|]. cbn [outside].
        split; [destruct HGHP; unfold SRC_TABLE, SRC_ENTRY, re_nheld in *; lia | split; [lia | exact I]]. }
    assert (PC : (Z.of_nat n <? re_nheld (nth i es_c no_entry) - 1) = Nat.ltb n (length (swap_remove [] n H))).
    { rewrite rig_len_swap by exact Hn. rewrite NHE. apply gm_ltb. lia. }
    apply SR_ret. unfold AT_IN.
    exists fx, R', L3, A3, m', md3, (k ++ [RFree (Z.of_nat (length (nth n H [])) + 1) (snd (nth n HaK ([], adr0)))]), qd,
      (set_nth i (with_keys (nth i es_c no_entry) (swap_remove rig_dk n (re_keys (nth i es_c no_entry)))) es_c),
      hs_c, kss, LB, OUTc, CAPc, junkc, jr, ka0, da0, (swap_remove ([], adr0) n HaK).
    split; [rewrite SEGS, PC; reflexivity|]. split; [exact FRM|]. split; [exact Hi|].
    repeat rewrite (getr_of_eqv _ _ _ X) by reflexivity. simp_regs.
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [reflexivity|].
    split.
    { intros Hn'. rewrite rig_len_swap in Hn' by exact Hn. rewrite NTHI. cbn [with_keys re_keys re_hp].
      split; [reflexivity|]. split; [assumption|].
      split; [rewrite rig_nth_swap by lia; rewrite Nat.eqb_refl, Ekl; reflexivity|].
      split; [reflexivity|]. split; [f_equal; rewrite rig_len_swap by exact Hn; rewrite NHE; lia|]. reflexivity. }
    split.
    { apply (rw_kb2 mem); [exact PB|]. intros j Hj. cbn in Hj.
      apply GK2; [right; unfold gP in *; lia | apply NSS; unfold gP in *; lia]. }
    unfold GI. cbv zeta.
    repeat rewrite (getr_of_eqv _ _ _ X) by reflexivity. simp_regs.
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [exact CH'|]. split; [exact (INI3 INIT)|].
    split.
    { destruct RES as (RL & RW & _).
      assert (RFA : forall qs, runF RF qs bnd (k ++ [RFree (Z.of_nat (length (nth n H [])) + 1) (snd (nth n HaK ([], adr0)))]) =
                     rt_free RF (runF RF qs bnd k) (Z.of_nat (length (nth n H [])) + 1) (resolveF qs (snd (nth n HaK ([], adr0))))).
      { intros qs. unfold runF, run_tr. rewrite run_from_app. reflexivity. }
      split; [rewrite nret_app; cbn [nret rets fold_right]; lia|].
      split; [intros ext; rewrite !RFA, (RW ext), (RSA ext); reflexivity|].
      rewrite RFA, XLE. exact RS3. }
    split.
    { destruct BUD as (oa & ssd & dsd & Lssd & Ldsd & EQ & OL & OD & DL). exists oa, ssd, dsd.
      split; [exact Lssd|]. split; [exact Ldsd|].
      split.
      { rewrite EQ. unfold gpos_k.
        replace (length (Ed ++ [nth n H []])) with (S (length Ed)) by (rewrite length_app; cbn [length]; lia).
        rewrite nret_app. cbn [nret rets fold_right]. rewrite !Nat.add_0_r.
        cbv zeta. cbn [fst snd app]. rewrite <- app_assoc. reflexivity. }
      split; [intros HL post; apply (FRL _ _ _ (OL HL post)); intros E; exact (KNO (eq_sym E))|].
      split.
      { intros HL. destruct (OD HL) as [O1 O2]. split; [exact O1|]. intros Hc.
        apply (FRL _ _ _ (O2 Hc)). destruct (HDEAD HL) as (_ & EO & _). intros E. apply KNO. rewrite EO. exact (eq_sym E). }
      intros j Hj post. rewrite (NTHJ j ltac:(lia)). destruct (DL j Hj post) as [D1 D2]. split.
      - apply (gk_entry_mono L A L3 A3); [|exact D1].
        intros pz az nz Hz Xz. apply (FRL pz az nz Xz). exact (DJE j az ltac:(lia) ltac:(lia) Hz).
      - intros HE. apply (gk_src_mono L A L3 A3); [|exact (D2 HE)].
        intros pz az nz Hz Xz. apply (FRL pz az nz Xz). exact (DJS j az ltac:(lia) HE Hz). }
    split.
    { intros q m Hq. rewrite EB3 in Hq.
      assert (Hq' : In (q, m) (blocks L A))
        by (rewrite EB2; apply in_app_or in Hq as [Hq|Hq]; apply in_or_app; [left | right; right]; exact Hq).
      assert (QK : q <> key_addr kn)
        by exact (gm_nd_mid b1 b2 _ (q, m) ltac:(rewrite <- EB2; exact (NODUP _ _ _ _ M1)) Hq).
      destruct (POT q m Hq') as [Y|[Y|[Y|Y]]].
      - left. exact Y.
      - right; left. apply (gm_concat_set es_c i _ q Hic Y). intros Y'. apply gm_eb_swap; [lia | exact Y' |].
        rewrite <- Ekn. exact QK.
      - right; right; left. exact Y.
      - right; right; right. exact Y. }
    split; [exact RA'|].
    split; [apply (GKc _ _ GL); intros j Hj; cbn in Hj; apply IMGR; unfold G_LOCK, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia|].
    split; [apply (GKc _ _ HNS); intros j Hj; cbn in Hj; apply IMGR; unfold G_NSRC, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia|].
    split; [apply (GKc _ _ HGS); intros j Hj; cbn in Hj; apply IMGR; unfold G_SRC, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia|].
    split; [exact HGB3|].
    split; [apply (GKc _ _ CCL); intros j Hj; cbn in Hj; apply IMGC; lia|].
    split; [apply (GKc _ _ CBR); intros j Hj; cbn in Hj; apply IMGR; unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia|].
    split; [apply (GKc _ _ CDD); intros j Hj; cbn in Hj; apply IMGR; unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia|].
    split; [apply (GKc _ _ CEI); intros j Hj; cbn in Hj; apply IMGR; unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia|].
    split.
    { pose proof (in_img_low Bm SEGS _ (IMGE (errno_addr Bm) ltac:(lia))) as EL0.
      pose proof (in_img_low Bm SEGS _ (IMGE (errno_addr Bm + 3) ltac:(lia))) as EL3.
      rewrite SEGS. apply CF.gestures_end_b.err_cells; [lia | lia |].
      intros j Hj. rewrite <- SEGS.
      apply (proj2 (KM (errno_addr Bm + j) ltac:(lia)
                     (OUTW (errno_addr Bm + j) (or_introl (IMGE (errno_addr Bm + j) ltac:(lia)))))).
      apply SW3. right. lia. }
    split.
    { intros j Hj. apply (GKc _ _ (SRCH' j Hj)). intros x Hx. cbn in Hx. apply IMGR.
      unfold G_S, SRC_SIZE, SOURCES_MAX, G_RELAY_LO. lia. }
    split; [apply (rw_kb2 mem); [exact FR0|]; intros j Hj; cbn in Hj;
            apply GK2; [right; unfold gP in *; lia | apply NSS; unfold gP in *; lia]|].
    split; [exists (pf_bytes (gpre ++ [0]) ++ jr); apply (rw_kb2 mem); [exact PB|]; intros j Hj; cbn in Hj;
            apply GK2; [right; unfold gP in *; lia | apply NSS; unfold gP in *; lia]|].
    split; [apply (rw_kb2 mem); [exact FRS|]; intros j Hj; unfold saved_cells in Hj; cbn in Hj;
            apply GK2; [right; unfold gP in *; lia | apply NSS; unfold gP in *; lia]|].
    split; [rewrite rigl_set_nth_len; exact HLE|].
    split.
    { exists tl. destruct HTAB as [Htl _].
      apply (gm_tab_upd m' es_c tl i (swap_remove rig_dk n (re_keys (nth i es_c no_entry))) Htl Hic HPD).
      - apply (rw_kb2 mem); [exact TC1|]. intros j Hj. cbn [cells_size csize] in Hj.
        apply KG; unfold SRC_TABLE, SRC_ENTRY; lia.
      - replace (Z.of_nat (length (swap_remove rig_dk n (re_keys (nth i es_c no_entry)))))
          with (re_nheld (nth i es_c no_entry) - 1) by (rewrite rig_len_swap by lia; rewrite NHE, LK; lia).
        exact HCr.
      - apply (rw_kb2 mem); [exact TC3|]. intros j Hj. cbn [cells_size csize] in Hj.
        replace (G + 56 * Z.of_nat i + 52 + j) with (G + (56 * Z.of_nat i + 52 + j)) by ring.
        apply KG; unfold SRC_TABLE, SRC_ENTRY; lia. }
    split.
    { apply Forall_forall. intros x Hx. apply (In_nth _ _ no_entry) in Hx as (j & Hj & <-).
      rewrite rigl_set_nth_len in Hj.
      destruct (Nat.eq_dec j i) as [->|Ne].
      - rewrite NTHI. apply (entry_okk_swap L A mem L3 A3 m' md3 (nth i es_c no_entry) n OKK M' NDE ltac:(lia)).
        + intros q Hq Q1 Q2. apply BKA; [rewrite Ekn; exact Q1 | | exact Q2].
          exact (proj1 (gm_nd3 _ _ _ _ HND (in_or_app _ _ _ (or_introl (INC q Hq))))).
        + exact HPB3.
        + exact KPS.
      - rewrite (NTHJ j Ne).
        apply (entry_okk_kept L A mem L3 A3 m' md3);
          [apply (proj1 (Forall_forall _ _) HEOK); apply nth_In; lia | exact M' |].
        intros q Hq.
        destruct (gdr_nodup_other G OUTc (map entry_blocks es_c) (map srcblk (combine es hs_c)) i j q
                    ltac:(rewrite !length_map, length_combine; lia) Ne (proj1 (gdr_nd _) HND)
                    ltac:(rewrite gdr_nth_eb; apply in_or_app; left; exact Hq)) as (Y1 & Y2 & Y3).
        rewrite gdr_nth_eb in Y3.
        apply BKA; [intros E; apply Y3; apply in_or_app; left; rewrite E; exact KEB | exact Y1 |
                    intros E; apply Y3; apply in_or_app; left; rewrite E; exact HPEB]. }
    split; [exact HLH|]. split; [exact HLK|]. split; [exact HIL|].
    split.
    { intros j Hj He. apply (src_at_kept L A mem L3 A3 m'); [exact (HSRC j Hj He) | |].
      - intros x Hx. pose proof (gdr_src_lt4 j Hj He) as J4.
        assert (P : img_plain Bm (gHA j + x)) by (apply IMGR; unfold gHA, G_S, SRC_SIZE, SOURCES_MAX, G_RELAY_LO; lia).
        apply GK2; [left; exact P | exact (NSC _ P)].
      - intros q Hq. assert (Hq' : In q (concat (map srcblk (combine es hs_c)))) by exact (gm_in_srcblk hs_c j q HLH Hj He Hq).
        destruct (gm_nd3 _ _ _ _ HND (in_or_app _ _ _ (or_intror Hq'))) as (Y1 & _).
        apply BKA; [intros E; rewrite E in Hq'; exact (rig_nodup_app_disj _ _ _ NDES KIN Hq') | exact Y1 |
                    intros E; rewrite E in Hq'; exact (rig_nodup_app_disj _ _ _ NDES HPIN Hq')]. }
    split.
    { intros j Hj. rewrite (NTHJ j ltac:(lia)). exact (HDONE j Hj). }
    split.
    { intros _. rewrite NTHI. split; [exact D0|].
      split; [rewrite <- HK; unfold keys_texts; cbn [with_keys re_keys]; rewrite rig_swap_map by lia; reflexivity|].
      split; [rewrite rig_len_swap by exact Hn; lia|].
      split; [intros j Hj; rewrite rig_nth_swap by lia; rewrite (proj2 (Nat.eqb_neq j n) ltac:(lia)); exact (Hpf j Hj)|].
      split.
      { rewrite Hgei. replace (length H - n)%nat with (S (length (swap_remove [] n H) - n))
          by (rewrite rig_len_swap by exact Hn; lia).
        rewrite (rig_gei_match _ gpre n H Hn Hp). cbn [fst snd]. rewrite <- app_assoc. reflexivity. }
      split; [rewrite rig_swap_map by exact HnA; rewrite HHa; reflexivity|].
      split; [exact Hka|].
      split.
      { exists (Eda ++ [nth n HaK ([], adr0)]). split.
        - rewrite map_app, HEda. cbn [map]. replace (fst (nth n HaK ([], adr0))) with (nth n H []); [reflexivity|].
          rewrite <- HHa. rewrite <- (map_nth fst HaK ([], adr0) n). reflexivity.
        - assert (HpA : has_prefix gpre (fst (nth n HaK ([], adr0))) = true).
          { rewrite <- Hp, <- HHa. f_equal. rewrite <- (map_nth fst HaK ([], adr0) n). reflexivity. }
          rewrite HGA. rewrite rig_len_swap by exact HnA.
          replace (length HaK - n)%nat with (S (length HaK - 1 - n)) by lia.
          cbn [geia_loop]. rewrite (proj2 (Nat.ltb_lt _ _) HnA), HpA.
          destruct (geia_loop (length HaK - 1 - n) gpre n (swap_remove ([], adr0) n HaK)) as [E' H'].
          cbn [fst snd]. rewrite <- app_assoc. reflexivity. }
      split.
      { intros post. apply (gk_entry_mono L A L3 A3).
        - intros pz az nz Hz Xz. apply (FRL pz az nz Xz). rewrite Ekn. exact (gk_eb_swap_ne (nth i es_c no_entry) n az ltac:(lia) NDE Hz).
        - pose proof (HL1 post) as (EK1 & EK2 & EK3). split; [exact EK1|]. split; [exact EK2|].
          cbn [da_keys re_keys with_keys] in EK3 |- *. rewrite rig_swap_map by exact HnA.
          exact (gk_f2_swap _ rig_dk adr0 n _ _ EK3 ltac:(lia)). }
      intros HE post. apply (gk_src_mono L A L3 A3).
      - intros pz az nz Hz Xz. apply (FRL pz az nz Xz). exact (DJS i az Hi HE Hz).
      - exact (HL2 HE post). }
    split.
    { intros j Hj. rewrite (NTHJ j ltac:(lia)). destruct (HPEND j Hj) as (P1 & P2 & PE & PS).
      split; [exact P1|]. split; [exact P2|]. split.
      - apply (gk_entry_mono L A L3 A3); [|exact PE].
        intros pz az nz Hz Xz. apply (FRL pz az nz Xz). exact (DJE j az ltac:(lia) ltac:(lia) Hz).
      - intros HE. apply (gk_src_mono L A L3 A3); [|exact (PS HE)].
        intros pz az nz Hz Xz. apply (FRL pz az nz Xz). rewrite P1 in HE. exact (DJS j az ltac:(lia) HE Hz). }
    split.
    { apply gdr_nd. pose proof (proj1 (gdr_nd _) HND) as N.
      assert (P2 : Permutation (G :: OUTc :: concat (map entry_blocks es_c) ++ concat (map srcblk (combine es hs_c)))
                     ([G; OUTc] ++ [key_addr kn] ++
                      concat (map entry_blocks
                        (set_nth i (with_keys (nth i es_c no_entry) (swap_remove rig_dk n (re_keys (nth i es_c no_entry))))
                           es_c)) ++ concat (map srcblk (combine es hs_c)))).
      { cbn [app]. apply perm_skip, perm_skip. exact (Permutation_app_tail _ PERM). }
      exact (rigl_nodup_mid [G; OUTc] [key_addr kn] _ (Permutation_NoDup P2 N)). }
    split.
    { intros q m Hq0 H1 H3 H4. pose proof (HSUR q m Hq0 H1 H3 H4) as Hq. pose proof Hq as HqA.
      rewrite EB2 in Hq. rewrite EB3. apply (gm_in_rm b1 b2 _ _ Hq). cbn [fst]. intros E. subst q.
      destruct (proj1 (rig_blocks_in _ _ _ _) Hq0) as (p0 & _ & Hp0).
      pose proof (rig_ub_nonneg A0 p0 m W0 Hp0) as Mnn.
      destruct (Z.eq_dec m 0) as [M0|M0].
      - subst m. pose proof (rig_nodup_fst _ (key_addr kn) 0 (Z.of_nat (length (key_text kn)) + 1)
                               (proj1 (gdr_nd _) (NODUP _ _ _ _ M1)) HqA KB). lia.
      - assert (HF : ~ Fcur (Z.of_nat (length LB)) (key_addr kn))
          by (intros [(_ & E)|[E|E]]; [exact (H1 E) | exact (H3 E) | exact (H4 E)]).
        destruct (HSV _ _ Hq0 ltac:(lia) HF) as [X1 _]. apply X1. apply in_or_app. left. exact KIN. }
    split.
    { intros q m Hq0 Hm HF. destruct (HSV q m Hq0 Hm HF) as [X1 X2]. split; [|exact X2].
      intros Y. apply X1. apply in_app_or in Y as [Y|Y]; apply in_or_app; [left | right; exact Y].
      apply (Permutation_in q (Permutation_sym PERM)). right. exact Y. }
    split; [exact HLB|]. split; [exact HT|].
    split.
    { intros HL. destruct (HDEAD HL) as (Hov & E1 & E2' & Hb).
      split; [apply (GKc _ _ Hov); intros j Hj; cbn in Hj; apply IMGR; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia|].
      split; [exact E1|]. split; [exact E2'|]. intros Hc. destruct (Hb Hc) as [Hb1 Hb2].
      assert (N1 : gOUT <> key_addr kn) by (rewrite <- E1; intros E; exact (KNO (eq_sym E))).
      assert (N2 : gOUT <> G) by (rewrite <- E1; intros E; exact (GNO (eq_sym E))).
      assert (N3 : gOUT <> re_hp (nth i es_c no_entry)) by (rewrite <- E1; intros E; exact (HPO (eq_sym E))).
      split; [exact (proj1 (BKA gOUT N1 N2 N3 gCAP Hb1))|].
      apply (bytes_in_block L A mem L3 A3 m' gOUT gCAP); [exact Hb2 | exact (BKA gOUT N1 N2 N3) | exact Hb1 | lia |].
      destruct HOUT0 as [(C0 & _)|(_ & _ & _ & _ & _ & HlO & Hlj)]; [lia|]. rewrite length_app. lia. }
    intros HL. destruct (HLIVE HL) as (H1 & H2 & H3 & H4 & H5 & H6).
    assert (N1 : OUTc <> key_addr kn) by (intros E; exact (KNO (eq_sym E))).
    assert (N2 : OUTc <> G) by (intros E; exact (GNO (eq_sym E))).
    assert (N3 : OUTc <> re_hp (nth i es_c no_entry)) by (intros E; exact (HPO (eq_sym E))).
    split; [exact H1|]. split; [exact (proj1 (BKA OUTc N1 N2 N3 CAPc H2))|]. split; [exact H3|].
    split.
    { apply (bytes_in_block L A mem L3 A3 m' OUTc CAPc); [exact H4 | exact (BKA OUTc N1 N2 N3) | exact H2 | lia |].
      pose proof len_O. rewrite !length_app. lia. }
    split; [exact H5|].
    apply (GKc _ _ H6); intros j Hj; cbn in Hj; apply IMGR; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia.
Qed.

(* ----- end of gone_match sub-regions ----- *)

Lemma gone_match : forall i ks0 n H Ed c, (n < length H)%nat -> has_prefix gpre (nth n H []) = true ->
  AT_IN i ks0 n H Ed c -> SR segs c (AT_IN i ks0 n (swap_remove [] n H) (Ed ++ [nth n H []])).
Proof.
  intros i ks0 n H Ed c Hn Hp HA.
  eapply SR_bind; [exact (gm_E i ks0 n H Ed c Hn Hp HA)|]. intros c1 H1.
  eapply SR_bind; [exact (gm_GE i ks0 n H Ed c1 Hn Hp H1)|]. intros c2 H2.
  eapply SR_bind; [exact (gm_F i ks0 n H Ed c2 Hn H2)|]. intros c3 H3.
  exact (gm_FG i ks0 n H Ed c3 Hn Hp H3).
Qed.

(* ===== end of transition regions (gone_D and gone_fin regions below) ===== *)

Lemma gone_inner : forall i ks0 n H Ed c, (n < length H)%nat -> AT_IN i ks0 n H Ed c ->
  SR segs c (fun c' => exists n' H' Ed', AT_IN i ks0 n' H' Ed' c' /\ (length H' - n' < length H - n)%nat).
Proof.
  intros i ks0 n H Ed c Hn HA.
  destruct (has_prefix gpre (nth n H [])) eqn:Hp.
  - eapply SR_mono; [exact (gone_match i ks0 n H Ed c Hn Hp HA)|].
    intros c' H'. exists n, (swap_remove [] n H), (Ed ++ [nth n H []]). split; [exact H'|].
    rewrite (rig_len_swap [] n H Hn). lia.
  - eapply SR_mono; [exact (gone_skip i ks0 n H Ed c Hn Hp HA)|].
    intros c' H'. exists (S n), H, Ed. split; [exact H' | lia].
Qed.

(* ===== region gone_D ===== *)

Lemma gone_geia_end : forall f pre n (Ha : list (list Z * adrF)), (length Ha <= n)%nat -> geia_loop f pre n Ha = ([], Ha).
Proof. intros [|f] pre n Ha Hn; cbn [geia_loop]; [reflexivity|]. rewrite (proj2 (Nat.ltb_ge _ _) Hn). reflexivity. Qed.

Lemma gd_next : forall i ks0 n H Ed ka0 da0 Ha regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc,
  (i < length es)%nat -> (length H <= n)%nat ->
  GI i (inner_cur i ks0 n H Ed ka0 da0 Ha) (part_of i Ed)
    (gpos_k i da0 (gkept ks0 ka0) [] (skipn (length Ed) (gxks ks0 ka0))) (bound_in i Ed)
    regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc ->
  GI (S i) (pend_rel (S i)) [] (gpos_top (S i)) (gbound (S i)) regs L A mem md k qd es_c hs_c (kss ++ [ks0]) LB OUTc CAPc junkc.
Proof.
  intros i ks0 n H Ed ka0 da0 Ha regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc Hi Hn HG.
  unfold GI in HG. cbv zeta in HG.
  destruct HG as (G2 & G3 & G4 & G8 & G22 & CH & INIT & RES & BUD & POT & RA & GL & HNS & HGS & HGB & CCL & CBR & CDD
    & CEI & CERR & SRCH' & FR0 & FRB & FRS & HLE & HTAB & HEOK & HLH & HLK & HIL & HSRC & HDONE & HCUR & HPEND & HND
    & HSUR & HSV & HLB & HT & HDEAD & HLIVE).
  destruct (HCUR Hi) as (D0 & HK & _ & _ & HGEI & HHa & Hka & (Eda & HEda & HGA) & HL1 & HL2).
  rewrite (rig_gei_end _ gpre n H Hn) in HGEI. cbn [fst snd] in HGEI. rewrite app_nil_r in HGEI.
  assert (HnA : (length Ha <= n)%nat) by (rewrite <- HHa, length_map in Hn; exact Hn).
  rewrite (gone_geia_end _ gpre n Ha HnA) in HGA. cbn [fst snd] in HGA. rewrite app_nil_r in HGA.
  assert (NK : forall j, (j < i)%nat -> nth j (kss ++ [ks0]) [] = nth j kss []) by (intros j Hj; apply app_nth1; lia).
  assert (NI : nth i (kss ++ [ks0]) [] = ks0) by (rewrite app_nth2 by lia; rewrite HLK, Nat.sub_diag; reflexivity).
  unfold GI. cbv zeta.
  do 8 (split; [assumption|]).
  split.
  { destruct BUD as (oa & ssd & dsd & Lssd & Ldsd & EQ & OL & OD & DL).
    exists oa, (ssd ++ [gs_of i]),
      (dsd ++ [DA oa (da_buf da0) (da_hp da0) (gkept ks0 ka0) (da_pend da0) (da_ev da0) (da_erecs da0)]).
    split; [rewrite length_app, Lssd; cbn [length]; lia|].
    split; [rewrite length_app, Ldsd; cbn [length]; lia|].
    assert (XS : skipn (length Ed) (gxks ks0 ka0) = []).
    { unfold gxks. rewrite HGA. cbn [fst]. apply skipn_all2. rewrite length_map, <- HEda, length_map. lia. }
    split.
    { rewrite XS in EQ. unfold gpos_k in EQ. cbn [keys_end_run fold_right fst snd app nret map] in EQ.
      rewrite Z.add_0_r, !Nat.add_0_r in EQ.
      rewrite EQ. unfold gpos_top. rewrite <- !app_assoc. reflexivity. }
    split; [exact OL|]. split; [exact OD|].
    intros j Hj post. destruct (Nat.lt_ge_cases j i) as [Hj'|Hj'].
    - rewrite app_nth1 by lia. exact (DL j Hj' post).
    - assert (j = i) as -> by lia. rewrite app_nth2 by lia. rewrite Ldsd, Nat.sub_diag. cbn [nth].
      split.
      + unfold gkept. rewrite HGA. cbn [snd]. exact (HL1 post).
      + intros HE. exact (HL2 HE post). }
  do 19 (split; [assumption|]).
  split; [rewrite length_app; cbn [length]; lia|].
  split; [lia|].
  split; [assumption|].
  split.
  { intros j Hj. destruct (Nat.lt_ge_cases j i) as [Hj'|Hj'].
    - rewrite (NK j Hj'). exact (HDONE j Hj').
    - assert (j = i) as -> by lia. rewrite NI. split; [exact D0|]. rewrite HK, HGEI. reflexivity. }
  split; [intros Hs; apply HPEND; lia|].
  split; [intros j Hj; apply HPEND; lia|].
  do 3 (split; [assumption|]).
  split.
  { rewrite HLB, seq_S, map_app, concat_app. change (0 + i)%nat with i. cbn [map concat]. rewrite !app_nil_r.
    f_equal.
    - f_equal. apply map_ext_in. intros j Hj. apply in_seq in Hj. unfold seg_of. rewrite NK by lia. reflexivity.
    - unfold seg_of, part_of, gone_segment, lines_of. rewrite NI, HGEI. reflexivity. }
  split.
  { pose proof (gd_ed_len i _ _ ks0 Ed H D0 HGEI) as LE.
    assert (GS : gbound (S i) = gbound i + (pl_of i + 6001 + 6005 * (re_nheld (nth i es no_entry) + pl_of i)))
      by (unfold gbound; rewrite rig_fold_seq_S; reflexivity).
    rewrite GS. unfold bound_in in HT. lia. }
  split; assumption.
Qed.

Lemma gone_D : forall i ks0 n H Ed c, (length H <= n)%nat -> AT_IN i ks0 n H Ed c -> SR segs c (AT_TOP (S i)).
Proof.
  intros i ks0 n H Ed c Hn HA.
  destruct HA as (fx & regs & L & A & mem & md & k & qd & es_c & hs_c & kss & LB & OUTc & CAPc & junkc & jr & ka0 & da0 & Ha &
    -> & FRM & Hi & R18 & R19 & R23 & R24 & _ & _ & HG).
  replace (Nat.ltb n (length H)) with false by (symmetry; apply Nat.ltb_ge; exact Hn).
  pose proof (gd_next i ks0 n H Ed ka0 da0 Ha regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc Hi Hn HG) as HG2.
  clear HG.
  pose proof HG2 as (G2 & G3 & G4 & G8 & G22 & CH & _ & _ & _ & _ & RA & _ & HNS & _).
  pose proof CH as (M1 & _).
  destruct (mr_model Bm MR rig_laws L A mem md M1) as (Hh & Hl & _).
  assert (EP : (Z.of_nat i + 1 <? gN) = Nat.ltb (S i) (length es)).
  { unfold gN. destruct (Z.ltb_spec (Z.of_nat i + 1) (Z.of_nat (length es))) as [C1|C1];
      destruct (Nat.ltb_spec (S i) (length es)) as [C2|C2]; lia. }
  eapply (rig_run fx regs (Z_to_bv 64 0x13584) mem md); [exact RA | exact Hh | exact Hl | |].
  - unfold Regs6ss.mkR_of.
    assert (E22 : reg_get regs 22 = Z_to_bv 64 RIG_S6) by exact G22.
    assert (E23 : reg_get regs 23 = Z_to_bv 64 (Z.of_nat i)) by exact R23.
    rewrite E22, E23.
    rewrite SEGS in RA.
    apply (rig_segD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z.of_nat i) gN).
    + apply rw_cells_normalize; [exact RA | rewrite <- SEGS; exact HNS |].
      intros j Hj. cbn in Hj. apply rig_ro_glob. unfold RIG_NSRC. lia.
    + unfold gN. lia.
    + exact NLE.
  - intros s0 R' m' HQ REL ROS X.
    cbv beta in HQ. subst s0.
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *.
    pose proof RA as RAr. rewrite SEGS in RAr.
    pose proof (mem_rel_normalize rsegs mem RAr) as RN.
    pose proof (munch_rel rsegs [] mem _ m' _ RN REL ROS (munch_refl [] (normalize rsegs mem))) as MUr.
    pose proof (wmono_rel rsegs mem _ m' _ RN REL ROS (wmono_refl rsegs (normalize rsegs mem))) as WMr.
    pose proof (ro_agree_same rsegs mem m' RAr ROS) as RA'.
    rewrite <- SEGS in WMr, RA'.
    apply SR_ret.
    exists fx, R', L, A, m', md, k, qd, es_c, hs_c, (kss ++ [ks0]), LB, OUTc, CAPc, junkc.
    split; [rewrite EP, SEGS; reflexivity|].
    split; [exact FRM|].
    split.
    { intros _. repeat rewrite (getr_of_eqv _ _ _ X) by reflexivity. simp_regs.
      split; [exact R18|]. split; [exact R19|]. f_equal. lia. }
    apply (GI_stack _ _ _ _ _ regs R' L A mem m' md k qd es_c hs_c (kss ++ [ks0]) LB OUTc CAPc junkc [] HG2 MUr WMr RA').
    + intros x _ Ox. exfalso. apply Ox. exact I.
    + rewrite (getr_of_eqv _ _ _ X) by reflexivity. simp_regs. exact G2.
    + rewrite (getr_of_eqv _ _ _ X) by reflexivity. simp_regs. exact G3.
    + rewrite (getr_of_eqv _ _ _ X) by reflexivity. simp_regs. exact G4.
    + rewrite (getr_of_eqv _ _ _ X) by reflexivity. simp_regs. exact G8.
    + rewrite (getr_of_eqv _ _ _ X) by reflexivity. simp_regs. reflexivity.
Qed.

(* ===== region gone_fin ===== *)

Lemma gf_pick : forall L A m (l : list rentry), Forall (entry_okk L A m) l ->
  exists l', length l' = length l /\ Forall (entry_ok Bm L A m) l' /\
    map entry_bytes l' = map entry_bytes l /\ map entry_blocks l' = map entry_blocks l /\
    (forall j, (j < length l)%nat -> exists ks, map fst ks = map fst (re_keys (nth j l no_entry)) /\
       nth j l' no_entry = with_keys (nth j l no_entry) ks).
Proof.
  intros L A m l H. induction H as [|e l He _ IH].
  - exists []. split; [reflexivity|]. split; [constructor|]. split; [reflexivity|]. split; [reflexivity|].
    intros j Hj. cbn in Hj. lia.
  - destruct He as (ks & Eks & OK). destruct IH as (l' & EL & F & EB & EK & N).
    destruct (map_fst_keys (re_keys e) ks Eks) as (EA & _ & ELn & _ & _).
    exists (with_keys e ks :: l').
    split; [cbn [length]; rewrite EL; reflexivity|].
    split; [constructor; assumption|].
    split; [cbn [map]; rewrite EB, (entry_bytes_wk e ks ELn); reflexivity|].
    split; [cbn [map]; rewrite EK, (entry_blocks_wk e ks EA); reflexivity|].
    intros [|j] Hj; [exists ks; split; [exact Eks | reflexivity]|].
    cbn [nth length] in Hj |- *. apply N. lia.
Qed.

Lemma gf_links_wk : forall L A qs fa e ks, map fst ks = map fst (re_keys e) ->
  entry_links L A qs fa e -> entry_links L A qs fa (with_keys e ks).
Proof.
  intros L A qs fa e ks E (B1 & B2 & B3). unfold entry_links. cbn [with_keys re_cap re_buf re_hp re_kh re_keys].
  split; [exact B1|]. split; [exact B2|].
  revert B3. generalize (da_keys fa) as das. revert E. generalize (re_keys e) as ks0.
  induction ks as [|k ks IH]; intros [|k0 ks0] E das F; cbn [map] in E; try discriminate; [exact F|].
  injection E as E1 E2. inversion F as [|x y xs ys P F']; subst.
  constructor; [|exact (IH ks0 E2 ys F')].
  unfold key_addr, key_text in P |- *. rewrite E1. exact P.
Qed.

Lemma gone_fin : forall c, AT_TOP (length es) c -> SR segs c gone_Q.
Proof.
  intros c (fx & regs & L & A & mem & md & k & qd & es_c & hs_c & kss & LB & OUTc & CAPc & junkc & -> & FRM & _ & HG).
  rewrite Nat.ltb_irrefl.
  apply (gone_end gone_Q (length es) (pend_rel (length es)) [] (gpos_top (length es)) (gbound (length es))
    fx regs L A mem md k qd es_c hs_c kss LB OUTc CAPc junkc HG).
  intros regs' mem' CH' RP RA' GL' KB.
  destruct HG as (G2 & G3 & G4 & G8 & G22 & CH & INIT & RES & BUD & POT & RA & GL & HNS & HGS & HGB & CCL & CBR & CDD
    & CEI & CERR & SRCH' & FR0 & FRB & FRS & HLE & HTAB & HEOK & HLH & HLK & HIL & HSRC & HDONE & HCUR & HPEND & HND
    & HSUR & HSV & HLB & HT & HDEAD & HLIVE).
  pose proof gS_range as [[GSR1 GSR2] GSR3]. pose proof gS_low as GSL. pose proof alloc_ceiling_val as ACV.
  pose proof K_val as KV.
  pose proof CH as (M1 & _). pose proof CH' as (M1' & _).
  assert (KL : forall a, 0 <= a < gS - RELAY_INSTANCE_GONE_K -> ~ (G_LOCK + 4 <= a < G_LOCK + 8) -> kb2 mem mem' a)
    by (intros a Ha Hn; apply KB; [lia | lia | exact Hn]).
  assert (RWL : forall a cs, rw_cells segs mem a cs -> a + Z.of_nat (cells_size cs) <= gS - RELAY_INSTANCE_GONE_K ->
                  (a + Z.of_nat (cells_size cs) <= G_LOCK + 4 \/ G_LOCK + 8 <= a) -> rw_cells segs mem' a cs).
  { intros a cs H Hb Hd. apply (rw_kb2 mem); [exact H|]. intros j Hj. pose proof (rw_cells_bound _ _ _ _ H). apply KL; lia. }
  assert (GLOB : forall a cs, rw_cells segs mem a cs -> G_RELAY_LO <= a -> a + Z.of_nat (cells_size cs) <= G_S + SRC_SIZE * SOURCES_MAX ->
                   (a + Z.of_nat (cells_size cs) <= G_LOCK + 4 \/ G_LOCK + 8 <= a) -> rw_cells segs mem' a cs).
  { intros a cs H H1 H2 H3. apply RWL; [exact H | unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia | exact H3]. }
  assert (BK : forall q, bkept L A mem L A mem' q).
  { intros q kq Hin. split; [exact Hin|]. intros i Hi.
    pose proof Hin as Hin'. apply rig_blocks_in in Hin' as (p & Ep & Hp).
    pose proof (blk_low L A mem md q kq M1 Hin ltac:(lia)) as Hlo.
    destruct (rig_blk L A mem md q kq i M1 Hin Hi) as (_ & H4 & _).
    apply KL; [lia|]. intros X.
    apply (ax_blocks_img AX L A mem md p kq i M1 Hp Hi). rewrite Ep.
    exact (proj1 (IMGR (q + i) ltac:(unfold G_LOCK, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))). }
  assert (ELB : Z.of_nat (length (concat (map (fun i => gone_segment gpre (entry_lines (nth i es no_entry) (nth i hs no_hj))
                  (nth i kss [])) (seq 0 (length es))))) = Z.of_nat (length LB)).
  { rewrite <- (length_map bz LB). change (map bz LB) with (bzs LB). rewrite HLB, app_nil_r. reflexivity. }
  assert (HEOK' : Forall (entry_okk L A mem') es_c).
  { apply Forall_forall. intros e He. apply (entry_okk_kept L A mem L A mem' md e);
      [exact (proj1 (Forall_forall _ _) HEOK e He) | exact M1' | intros q _; apply BK]. }
  destruct (gf_pick L A mem' es_c HEOK') as (es' & EL' & FOK & EBY & EBL & NTH).
  assert (SRC' : forall j, (j < length es)%nat -> re_eof (nth j es no_entry) = 0 ->
                   src_at Bm L A mem' (gHA j) (nth j hs_c (fst (nth j hs no_hj)))).
  { intros j Hj He. apply (src_at_kept L A mem L A mem'); [exact (HSRC j Hj He) | | intros q _; apply BK].
    assert (Hjs : (snd (nth j hs no_hj) < 4)%nat).
    { pose proof (proj1 (Forall_forall _ _) GSO (nth j es no_entry, nth j hs no_hj)) as GO.
      assert (Hin : In (nth j es no_entry, nth j hs no_hj) (combine es hs)).
      { rewrite <- combine_nth by lia. apply nth_In. rewrite length_combine. lia. }
      destruct (GO Hin He) as (_ & Hl & _). exact Hl. }
    intros x Hx. apply KL; unfold gHA, G_S, SRC_SIZE, G_LOCK in *; lia. }
  destruct HTAB as (tl & Htl & Htr).
  destruct BUD as (oa & ssd & dsd & Lssd & Ldsd & EQ & OL & OD & DL). unfold gpos_top, gps in EQ.
  rewrite skipn_all2 in EQ by (rewrite length_combine; lia). cbn [gone_run fst snd] in EQ. rewrite !app_nil_r in EQ.
  pose proof (gone_shape glv gmx gpre gps gNO gCAP (fun _ => adr0) 0%nat adr0 gnm 0%nat (gnm gOUT)) as [SH1 SH2].
  change (gone_cap glv gmx gNO gCAP gpre es hs = snd (fst (fst grun))) in SH1.
  change (gone_states glv gmx gNO gCAP gpre es hs = gss) in SH2.
  unfold gone_Q.
  exists fx, L, A, regs', mem', md, OUTc, CAPc, junkc, LB, es', hs_c, kss, tl.
  cbv zeta. rewrite ELB.
  split; [reflexivity|]. split; [exact FRM|].
  split; [eapply chain_post; [exact CH' | exact RP]|].
  split; [exact INIT|].
  split.
  { destruct RES as (RL & _ & RO). exists qd.
    assert (GT : gtr = k) by (unfold gtr; rewrite EQ; reflexivity).
    assert (GO : gone_out glv gmx gNO gCAP gpre es hs gnm 0 (gnm gOUT) = oa)
      by (change (fst (snd grun) = oa); rewrite EQ; reflexivity).
    assert (GA : gone_adrs glv gmx gNO gCAP gpre es hs gnm 0 (gnm gOUT) = dsd)
      by (change (snd (snd grun) = dsd); rewrite EQ; reflexivity).
    rewrite GT, GO, GA. split; [exact RL|]. split; [exact RO|]. split.
    - intros HL. rewrite <- (app_nil_r qd). exact (OL HL []).
    - intros i Hi. destruct (DL i ltac:(lia) []) as [D1 D2]. rewrite app_nil_r in D1, D2.
      destruct (NTH i ltac:(lia)) as (ks & Eks & En). rewrite En.
      split; [exact (gf_links_wk L A qd _ _ ks Eks D1) | exact D2]. }
  split; [exact RA'|]. split; [exact GL'|].
  split; [apply GLOB; [exact HNS | unfold G_NSRC, G_RELAY_LO; lia | cbn; unfold G_NSRC, G_S, SRC_SIZE, SOURCES_MAX; lia
    | cbn; unfold G_NSRC, G_LOCK; lia]|].
  split; [apply GLOB; [exact HGS | unfold G_SRC, G_RELAY_LO; lia | cbn; unfold G_SRC, G_S, SRC_SIZE, SOURCES_MAX; lia
    | cbn; unfold G_SRC, G_LOCK; lia]|].
  split; [exact HGB|].
  split; [lia|].
  split.
  { unfold table_at. split; [rewrite EL'; exact Htl|]. rewrite EBY.
    apply (rw_in_block L A mem L A mem' G SRC_TABLE); [exact Htr | apply BK | exact HGB | lia | cbn; unfold SRC_TABLE, SRC_ENTRY; lia]. }
  split; [exact FOK|].
  split; [exact HLK|]. split; [lia|].
  split.
  { intros i Hi. rewrite SH2.
    destruct (HDONE i Hi) as (D0 & DK).
    unfold done0 in D0. cbv zeta in D0.
    destruct D0 as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
    unfold dsrel in D7. cbv zeta in D7. destruct D7 as (S1 & S2 & S3 & S4 & S5 & S6).
    destruct (NTH i ltac:(lia)) as (ks & Eks & En).
    destruct (map_fst_keys (re_keys (nth i es_c no_entry)) ks Eks) as (_ & _ & _ & _ & EX).
    rewrite En. cbn [with_keys re_fd re_eof re_skip re_U re_buf re_used re_cap re_keys].
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|].
    split; [rewrite EX; exact DK|].
    split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|].
    split; [|exact D6].
    intros He. split; [exact (SRC' i Hi He)|].
    destruct (D5 He) as (Y1 & Y2 & Y3 & Y4 & Y4a & Y4b & Y5 & Y6 & Y7 & Y8 & Y9 & Y9a & Y10 & Y11).
    destruct (S6 He) as [Z1 Z2].
    repeat split; assumption. }
  split; [rewrite HLB, app_nil_r; reflexivity|].
  split; [apply RWL; [exact CCL | cbn; unfold G_CLIENT; lia | cbn; unfold G_CLIENT, G_LOCK; lia]|].
  split; [apply GLOB; [exact CBR | unfold G_BROKEN, G_RELAY_LO; lia | cbn; unfold G_BROKEN, G_S, SRC_SIZE, SOURCES_MAX; lia
    | cbn; unfold G_BROKEN, G_LOCK; lia]|].
  split; [apply GLOB; [exact CDD | unfold G_DEAD, G_RELAY_LO; lia | cbn; unfold G_DEAD, G_S, SRC_SIZE, SOURCES_MAX; lia
    | cbn; unfold G_DEAD, G_LOCK; lia]|].
  split; [apply GLOB; [exact CEI | unfold G_EINTR, G_RELAY_LO; lia | cbn; unfold G_EINTR, G_S, SRC_SIZE, SOURCES_MAX; lia
    | cbn; unfold G_EINTR, G_LOCK; lia]|].
  split.
  { destruct CERR as [ev Hev]. exists ev. apply RWL; [exact Hev | |].
    - pose proof (in_img_low Bm SEGS (errno_addr Bm + 3) (IMGE (errno_addr Bm + 3) ltac:(lia))). cbn. lia.
    - right. unfold G_LOCK, G_LOCK_HI in *. lia. }
  split.
  { intros j Hj. apply GLOB; [exact (SRCH' j Hj) | unfold G_S, G_RELAY_LO, SRC_SIZE; lia
      | cbn; unfold G_S, SRC_SIZE, SOURCES_MAX; lia | right; unfold G_S, SRC_SIZE, G_LOCK; lia]. }
  split; [rewrite EBL; exact HND|].
  split; [exact HSUR|].
  split.
  { intros q m Hq0 Hm Nq Ne Nd.
    assert (HF : ~ Fcur (Z.of_nat (length LB)) q) by (intros [(_ & E)|[E|E]]; [exact (Nq E) | exact (Ne E) | exact (Nd E)]).
    destruct (HSV q m Hq0 Hm HF) as [X1 X2].
    split; [|split].
    - destruct (send_live cl br dd (Z.of_nat (length LB))) eqn:LV; [exact (X2 eq_refl)|].
      destruct (HDEAD eq_refl) as (_ & E1 & _). rewrite E1. exact Nq.
    - intros Y. apply X1. apply in_or_app. left. rewrite <- EBL. exact Y.
    - intros Y. apply X1. apply in_or_app. right. exact Y. }
  split.
  { intros q m Hq. destruct (POT q m Hq) as [X|[X|[X|X]]].
    - left. exact X.
    - right; left. rewrite EBL. exact X.
    - right; right; left. exact X.
    - right; right; right. exact X. }
  split.
  { intros HL. destruct (HDEAD HL) as (Hov & E1 & E2 & Hb).
    split; [apply GLOB; [exact Hov | unfold G_OUTV, G_RELAY_LO; lia | cbn; unfold G_OUTV, G_S, SRC_SIZE, SOURCES_MAX; lia
      | cbn; unfold G_OUTV, G_LOCK; lia]|].
    split; [exact E1|]. split; [exact E2|]. intros Hc. destruct (Hb Hc) as [Hb1 Hb2]. split; [exact Hb1|].
    apply (bytes_in_block L A mem L A mem' gOUT gCAP); [exact Hb2 | apply BK | exact Hb1 | lia |].
    destruct HOUT0 as [(C0 & _)|(_ & _ & _ & _ & _ & HlO & Hlj)]; [lia|]. rewrite length_app. lia. }
  intros HL. destruct (HLIVE HL) as (H1 & H2 & H3 & H4 & H5 & H6).
  split; [exact H1|]. split; [rewrite SH1, EQ; cbn [fst snd]; rewrite HL; reflexivity|].
  split; [exact H2|]. split; [exact H3|].
  split.
  { apply (bytes_in_block L A mem L A mem' OUTc CAPc); [exact H4 | apply BK | exact H2 | lia |].
    pose proof len_O. rewrite !length_app. lia. }
  split; [exact H5|].
  apply GLOB; [exact H6 | unfold G_OUTV, G_RELAY_LO; lia | cbn; unfold G_OUTV, G_S, SRC_SIZE, SOURCES_MAX; lia
    | cbn; unfold G_OUTV, G_LOCK; lia].
Qed.

(* ===== end of region gone_fin ===== *)

Lemma gone_loop : forall m i ks0 n H Ed c, (length H - n <= m)%nat -> AT_IN i ks0 n H Ed c -> SR segs c (AT_TOP (S i)).
Proof.
  induction m as [|m IH]; intros i ks0 n H Ed c Hm HA.
  - apply (gone_D i ks0 n H Ed c); [lia | exact HA].
  - destruct (Nat.lt_ge_cases n (length H)) as [Hn|Hn]; [|exact (gone_D i ks0 n H Ed c Hn HA)].
    eapply SR_bind; [exact (gone_inner i ks0 n H Ed c Hn HA)|].
    intros c' (n' & H' & Ed' & HA' & Hlt). apply (IH i ks0 n' H' Ed' c'); [lia | exact HA'].
Qed.

Lemma gone_outer : forall d i c, (length es - i <= d)%nat -> AT_TOP i c -> SR segs c gone_Q.
Proof.
  induction d as [|d IH]; intros i c Hd HA.
  - assert (Ei : i = length es).
    { destruct HA as (fx & regs & L & A & mem & md & k & qd & es_c & hs_c & kss & LB & OUTc & CAPc & junkc & _ & _ & _ & HG).
      destruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & _ & _ & _ & _ & _ & HIL & _). lia. }
    subst i. exact (gone_fin c HA).
  - destruct (Nat.lt_ge_cases i (length es)) as [Hi|Hi].
    + eapply SR_bind; [exact (gone_drain i c Hi HA)|]. intros c1 H1.
      eapply SR_bind; [exact (gone_C i c1 H1)|]. intros c2 (ks0 & H2).
      eapply SR_bind; [exact (gone_loop (length ks0) i ks0 0 ks0 [] c2 ltac:(lia) H2)|]. intros c3 H3.
      apply (IH (S i) c3); [lia | exact H3].
    + assert (Ei : i = length es).
      { destruct HA as (fx & regs & L & A & mem & md & k & qd & es_c & hs_c & kss & LB & OUTc & CAPc & junkc & _ & _ & _ & HG).
        destruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
          & _ & _ & _ & _ & _ & HIL & _). lia. }
      subst i. exact (gone_fin c HA).
Qed.

Lemma gone_main : SR segs (mkCfg (@YK11.mkst fx0 regs0 (Z_to_bv 64 RELAY_INSTANCE_GONE) mem0 (seg_rom segs)) md0) gone_Q.
Proof.
  eapply SR_bind; [exact gone_start|]. intros c HA. exact (gone_outer (length es) 0 c ltac:(lia) HA).
Qed.

End GONE.

End RIG.

Section MAIN.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTX : ctx_owned Bm API.
Hypothesis BSP : block_slack_present Bm API.
Hypothesis FREE_PC : ms_free Bm = RIG_FREE.
Hypothesis NODUP : forall L A mem md, aa_MR API L A mem md -> NoDup (map fst (blocks L A)).

Theorem relay_instance_gone_holds (RF : ResFormT) : pthread_mutex_lock_contract -> pthread_mutex_unlock_contract ->
  snprintf_contract -> strlen_contract -> strncmp_contract ->
  (forall fx' : YK11.FPState, free_contract_rt (fx := fx') Bm API RF) ->
  (forall fx' : YK11.FPState, @drain_contract fx' rc Bm API RF) ->
  (forall fx' : YK11.FPState, @gesture_end_contract fx' rc Bm API RF) ->
  relay_instance_gone_contract Bm API RF.
Proof.
  intros LOCK UNLOCK SNP SLEN SNCMP FREE DRAIN GEND.
  unfold relay_instance_gone_contract.
  intros L A regs mem md bnd es G tail hs fs os O junk cl br dd ei mx nout cap out.
  cbv zeta.
  intros SEGS [PRE TSZ] INIT0 TPE HERR RA0 FRM0 GOTG GRD IMGR IMGC IMGE IMG5 IDR GL0 NS0 GS0 NLE GB0 GF0 TAB0 EOK0 NDF LHS
    LFS LOS SRCH SRCD SRCR GSO ND0 Hcl Hbr Hdd Hei CCL0 CBR0 CDD0 CEI0 COUT0 CERR0 HOUT0 RES0 ROOM0.
  exact (gone_main Bm API AX CTX SEGS BSP LOCK UNLOCK SNP SLEN SNCMP RF FREE DRAIN GEND FREE_PC NODUP fx L A regs mem md
    bnd es G tail hs fs os O junk cl br dd ei mx nout cap out PRE TSZ INIT0 TPE HERR RA0 FRM0 GOTG GRD IMGR IMGC IMGE
    IMG5 IDR GL0 NS0 GS0 NLE GB0 GF0 TAB0 EOK0 NDF LHS LFS LOS SRCH SRCD SRCR GSO ND0 Hcl Hbr Hdd Hei CCL0 CBR0 CDD0 CEI0
    COUT0 CERR0 HOUT0 RES0 ROOM0).
Qed.

End MAIN.

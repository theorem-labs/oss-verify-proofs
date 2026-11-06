(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 618 of its 664 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass9G.v, with its module paths and module names changed; 466 of its 523 lines of code are new or changed and 607 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/HarnessGlue.v, with its module paths and module names changed; 293 of its 383 lines of code are new or changed and 433 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YO0u YO0x YI04 YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lf_ub_prid_lt : forall s p n, WF s -> In (p, n) (user_blocks s) -> (prid p < length (st_regions s))%nat.
Proof.
  intros s p n HW Hin.
  destruct (YO0x.user_blocks_frame s p n HW Hin) as (g & am & idx & fr & U & _ & _ & _ & _ & ->).
  unfold frame_ptr. rewrite YO0u.prid_padd, YO0u.prid_slot_start.
  exact (YO0u.used_group_prid_lt [] None U0 s g am HW U).
Qed.

Lemma lf_addr : forall A L L' p n, WF A -> layout_le A L L' -> In (p, n) (user_blocks A) ->
  ptr_addr L' p = ptr_addr L p.
Proof.
  intros A L L' p n HW (_ & _ & _ & G) Hp. pose proof (lf_ub_prid_lt A p n HW Hp) as Hr.
  destruct p as [r o]. unfold ptr_addr. cbn [loc_addr]. cbn [prid] in Hr. rewrite G by exact Hr. reflexivity.
Qed.

Lemma lf_layout_trans : forall A A1 L L1 L2, (length (st_regions A) <= length (st_regions A1))%nat ->
  layout_le A L L1 -> layout_le A1 L1 L2 -> layout_le A L L2.
Proof.
  intros A A1 L L1 L2 HL (C1 & S1 & R1 & G1) (C2 & S2 & R2 & G2).
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite G2 by lia. apply G1. exact Hr.
Qed.

Lemma lf_vm2 : forall h h' md, with_vmmaps h (with_vmmaps h' md) = with_vmmaps h md.
Proof. intros h h' md. destruct md. reflexivity. Qed.

Lemma lf_vm_id : forall md, with_vmmaps (m_vmmaps md) md = md.
Proof. intros [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma lf_outside_dec : forall W x, {outside W x} + {~ outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - right. intros [H _]. lia.
  - destruct (IH x) as [H|H]; [left; split; [lia | exact H] | right; intros [_ H']; exact (H H')].
  - destruct (IH x) as [H|H]; [left; split; [lia | exact H] | right; intros [_ H']; exact (H H')].
Qed.

Lemma lf_blocks_in : forall L A q k, In (q, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = q.
Proof.
  intros L A q k Hin. unfold blocks in Hin. apply in_map_iff in Hin. destruct Hin as ([p k0] & E & Hin).
  cbn [fst snd] in E. injection E as E1 E2. subst. exists p. split; [exact Hin | reflexivity].
Qed.

Lemma lf_blocks_of : forall L A p n, In (p, n) (user_blocks A) -> In (ptr_addr L p, n) (blocks L A).
Proof. intros L A p n Hin. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (p, n) Hin). Qed.

Section LF.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Let segs := ms_segs Bm.
Let MR := aa_MR API.
Hypothesis SEGS : ms_segs Bm = rsegs.
Hypothesis AX : AllocExtra Bm MR.
Hypothesis CTX : ctx_owned Bm API.

Definition errz (a : Z) : Prop := errno_addr Bm <= a < errno_addr Bm + 4.

Definition lmid (K sp : Z) (E F : Z -> Prop) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (forall p n, In (p, n) (user_blocks A) -> 0 < n -> ~ F (ptr_addr L p) -> In (p, n) (user_blocks A')) /\
  (forall p, In (p, 0) (user_blocks A) -> In (p, 0) (user_blocks A')) /\
  (forall a, in_img Bm a -> owned Bm L' A' a -> owned Bm L A a) /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, (YM05.alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) -> ~ owned Bm L A a -> ~ owned Bm L' A' a ->
     ~ (sp - K <= a < sp) -> ~ errz a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ~ F (ptr_addr L p) -> 0 <= i < n ->
     ~ E (ptr_addr L p + i) -> mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
  (forall a, (sp - K <= a < sp) \/ errz a -> writable_at segs mem' a).

Lemma lf_img_low : forall a, in_img Bm a -> 0 <= a < 2 ^ 21.
Proof. exact (in_img_low Bm SEGS). Qed.

Lemma lmid_trans : forall K sp E1 F1 E2 F2 L A mem md L1 A1 mem1 md1 L2 A2 mem2 md2,
  WF A ->
  lmid K sp E1 F1 L A mem md L1 A1 mem1 md1 ->
  lmid K sp E2 F2 L1 A1 mem1 md1 L2 A2 mem2 md2 ->
  lmid K sp (fun a => E1 a \/ E2 a) (fun q => F1 q \/ F2 q) L A mem md L2 A2 mem2 md2.
Proof.
  intros K sp E1 F1 E2 F2 L A mem md L1 A1 mem1 md1 L2 A2 mem2 md2 HW
    (M1 & W1 & B1 & LY1 & LN1 & SV1 & Z1 & OW1 & MD1 & FR1 & BK1 & SC1)
    (M2 & W2 & B2 & LY2 & LN2 & SV2 & Z2 & OW2 & MD2 & FR2 & BK2 & SC2).
  pose proof (aa_laws API) as LAWS. pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|].
  split; [exact (lf_layout_trans A A1 L L1 L2 LN1 LY1 LY2)|]. split; [lia|].
  split.
  { intros p n Hp Hn HF. cbv beta in HF.
    assert (H1 : In (p, n) (user_blocks A1)) by (apply SV1; [exact Hp | exact Hn | tauto]).
    apply SV2; [exact H1 | exact Hn |]. rewrite (lf_addr A L L1 p n HW LY1 Hp). tauto. }
  split; [intros p Hp; exact (Z2 p (Z1 p Hp))|].
  split; [intros a Ha Ho; exact (OW1 a Ha (OW2 a Ha Ho))|].
  split; [destruct MD1 as (v1 & ->); destruct MD2 as (v2 & ->); exists v2; apply lf_vm2|].
  split.
  { intros a Ha NO NO2 NS NE NE12.
    assert (NO1 : ~ owned Bm L1 A1 a).
    { intro X. destruct Ha as [Ha|Ha].
      - pose proof (owned_low Bm MR LAWS _ _ _ _ a M1 X). lia.
      - exact (NO (OW1 a Ha X)). }
    destruct (FR1 a Ha NO NO1 NS NE (fun X => NE12 (or_introl X))) as [Y1 Z1'].
    destruct (FR2 a Ha NO1 NO2 NS NE (fun X => NE12 (or_intror X))) as [Y2 Z2'].
    split; [congruence | tauto]. }
  split.
  { intros p n i Hp Hp2 HF Hi NE. cbv beta in HF, NE.
    assert (Hn : 0 < n) by lia.
    assert (H1 : In (p, n) (user_blocks A1)) by (apply SV1; [exact Hp | exact Hn | tauto]).
    pose proof (lf_addr A L L1 p n HW LY1 Hp) as EA.
    rewrite <- (BK1 p n i Hp H1 ltac:(tauto) Hi ltac:(tauto)).
    pose proof (BK2 p n i H1 Hp2 ltac:(rewrite EA; tauto) Hi ltac:(rewrite EA; tauto)) as X.
    rewrite EA in X. exact X. }
  exact SC2.
Qed.

Lemma lmid_A : forall K sp E L A mem md mem' W,
  MR L A mem md -> WF A -> bounded A ->
  YM05.alloc_ceiling <= sp - K -> sp <= 2 ^ 64 ->
  (forall a, (sp - K <= a < sp) \/ errz a -> writable_at segs mem a) ->
  munch W mem mem' -> wmono segs mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> (sp - K <= x < sp) \/ E x) ->
  (forall x, 0 <= x < YM05.alloc_ceiling -> owned Bm L A x -> outside W x) ->
  lmid K sp E (fun _ => False) L A mem md L A mem' md.
Proof.
  intros K sp E L A mem md mem' W HM HW HB HC HS HSW MU WM HE HO.
  pose proof (aa_laws API) as LAWS. pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  destruct (mr_model _ _ LAWS _ _ _ _ HM) as (Hh & Hl & Hmat).
  split.
  { apply (mr_frame _ _ LAWS L A mem mem' md md HM).
    - intros a Ho. destruct (owned_low Bm MR LAWS _ _ _ _ a HM Ho) as [Ha1 Ha2].
      apply (munch_mbyte segs W mem mem' a MU); [lia | apply HO; [lia | exact Ho]].
    - intros a Ho Hp. destruct (owned_low Bm MR LAWS _ _ _ _ a HM Ho) as [Ha1 Ha2].
      apply (munch_present W mem mem' a MU); [lia | apply HO; [lia | exact Ho] | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks _ _ LAWS L A mem md p n i HM Hin Hi) as (Hp & H4 & Hc & _).
      destruct (lf_outside_dec W (ptr_addr L p + i)) as [O|O].
      + exact (munch_present W mem mem' (ptr_addr L p + i) MU ltac:(lia) O Hp).
      + apply (present_of_writable_out Bm SEGS mem' (ptr_addr L p + i) ltac:(lia)).
        * exact (ax_blocks_img AX L A mem md p n i HM Hin Hi).
        * rewrite <- SEGS. unfold writable_at. apply WM. destruct Hp as [b Hb]. unfold wview. rewrite Hb. discriminate.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact HW|]. split; [exact HB|]. split; [apply layout_le_refl|]. split; [lia|].
  split; [intros p n Hp _ _; exact Hp|]. split; [intros p Hp; exact Hp|].
  split; [intros a _ Ho; exact Ho|].
  split; [exists (m_vmmaps md); symmetry; apply lf_vm_id|].
  split.
  { intros a Ha _ _ NS NZ NE.
    assert (R : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | pose proof (lf_img_low a Ha); lia]).
    destruct (lf_outside_dec W a) as [O|O].
    - split; [exact (munch_mbyte segs W mem mem' a MU R O) | exact (munch_writable segs W mem mem' a MU R O)].
    - destruct (HE a R O) as [X|X]; contradiction. }
  split.
  { intros p n i Hp _ _ Hi NE. destruct (mr_blocks _ _ LAWS L A mem md p n i HM Hp Hi) as (_ & H4 & Hc & _).
    destruct (lf_outside_dec W (ptr_addr L p + i)) as [O|O].
    - exact (munch_mbyte segs W mem mem' (ptr_addr L p + i) MU ltac:(lia) O).
    - destruct (HE (ptr_addr L p + i) ltac:(lia) O) as [X|X]; [lia | contradiction]. }
  intros a Ha. unfold writable_at. apply WM. exact (HSW a Ha).
Qed.

Lemma lmid_call : forall K sp K1 L A regs1 mem md E1 L' A' regs1' mem' md' (Fq : Z -> Prop),
  MR L A mem md ->
  call_post_k Bm MR K1 L A regs1 mem md E1 L' A' regs1' mem' md' ->
  (forall a, (YM05.alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) -> ~ E1 a) ->
  sp - K <= spZ regs1 - K1 -> spZ regs1 <= sp -> YM05.alloc_ceiling <= sp - K -> sp <= 2 ^ 64 ->
  (forall a, (sp - K <= a < sp) \/ errz a -> writable_at segs mem a) ->
  (forall p n, In (p, n) (user_blocks A) -> 0 < n -> ~ Fq (ptr_addr L p) -> In (p, n) (user_blocks A')) ->
  (forall p, In (p, 0) (user_blocks A) -> In (p, 0) (user_blocks A')) ->
  (length (st_regions A) <= length (st_regions A'))%nat ->
  lmid K sp (fun _ => False) Fq L A mem md L' A' mem' md'.
Proof.
  intros K sp K1 L A regs1 mem md E1 L' A' regs1' mem' md' Fq HM
    (M' & W' & B' & LY & PA & RP & MD & FR & BK & SC) HE1 H1 H2 H3 H4 HSW HSV HZ HLN.
  pose proof (aa_laws API) as LAWS. pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  split; [exact M'|]. split; [exact W'|]. split; [exact B'|]. split; [exact LY|]. split; [exact HLN|].
  split; [exact HSV|]. split; [exact HZ|].
  split.
  { intros a Hi [Ho|Ho]; [| right; exact Ho].
    exact (CTX L A mem md a HM (ax_img AX L' A' mem' md' a M' Hi Ho)). }
  split; [exact MD|].
  split.
  { intros a Ha NO NO' NS NZ _. apply FR; [exact Ha | exact NO | exact NO' | | exact (HE1 a Ha)].
    unfold scratch_k. intros [X|X]; [apply NS; lia | exact (NZ X)]. }
  split; [intros p n i Hp Hp' _ Hi _; exact (BK p n i Hp Hp' Hi)|].
  intros a Ha.
  assert (D : scratch_k Bm K1 regs1 a \/ ~ scratch_k Bm K1 regs1 a) by (unfold scratch_k; lia).
  destruct D as [D|D]; [exact (SC a D)|].
  destruct Ha as [Ha|Ha]; [|exfalso; apply D; right; exact Ha].
  assert (NO : ~ owned Bm L A a) by (intro X; pose proof (owned_low Bm MR LAWS _ _ _ _ a HM X); lia).
  assert (NO' : ~ owned Bm L' A' a) by (intro X; pose proof (owned_low Bm MR LAWS _ _ _ _ a M' X); lia).
  apply (proj2 (FR a ltac:(left; lia) NO NO' D (HE1 a ltac:(left; lia)))).
  apply HSW. left. exact Ha.
Qed.

Lemma rp_of_lmid : forall K E F L A regs mem md L' A' regs' mem' md',
  WF A -> lmid K (spZ regs) E F L A mem md L' A' mem' md' -> regs_preserved regs regs' ->
  relay_post Bm API K E F L A regs mem md L' A' regs' mem' md'.
Proof.
  intros K E F L A regs mem md L' A' regs' mem' md' HW
    (M' & W' & B' & LY & LN & SV & Z0 & OW & MD & FR & BK & SC) RP.
  split; [exact M'|]. split; [exact W'|]. split; [exact B'|]. split; [exact LY|]. split; [exact LN|].
  split; [intros p n Hp _ _; exact (lf_addr A L L' p n HW LY Hp)|].
  split; [exact SV|].
  split; [intros p Hp; split; [exact (Z0 p Hp) | exact (lf_addr A L L' p 0 HW LY Hp)]|].
  split; [exact OW|]. split; [exact RP|]. split; [exact MD|].
  split.
  { intros a Ha NO NO' NS NE. apply FR; [exact Ha | exact NO | exact NO' | | | exact NE];
      intro X; apply NS; unfold scratch_k; [left; exact X | right; exact X]. }
  split; [exact BK|].
  intros a Ha. apply SC. unfold scratch_k in Ha. exact Ha.
Qed.

Lemma rp_shrink : forall K E E' F L A regs mem md L' A' regs' mem' md',
  relay_post Bm API K E F L A regs mem md L' A' regs' mem' md' ->
  (forall a, E a -> E' a \/ (a < YM05.alloc_ceiling /\ ~ in_img Bm a /\
     forall p n, In (p, n) (user_blocks A) -> ~ F (ptr_addr L p) -> ~ (ptr_addr L p <= a < ptr_addr L p + n))) ->
  relay_post Bm API K E' F L A regs mem md L' A' regs' mem' md'.
Proof.
  intros K E E' F L A regs mem md L' A' regs' mem' md'
    (M' & W' & B' & LY & LN & PA & SV & Z0 & OW & RP & MD & FR & BK & SC) HS.
  split; [exact M'|]. split; [exact W'|]. split; [exact B'|]. split; [exact LY|]. split; [exact LN|].
  split; [exact PA|]. split; [exact SV|]. split; [exact Z0|]. split; [exact OW|]. split; [exact RP|].
  split; [exact MD|].
  split.
  { intros a Ha NO NO' NS NE'. apply FR; [exact Ha | exact NO | exact NO' | exact NS |].
    intro X. destruct (HS a X) as [Y | (Y1 & Y2 & _)]; [exact (NE' Y)|].
    destruct Ha as [Ha|Ha]; [lia | exact (Y2 Ha)]. }
  split.
  { intros p n i Hp Hp' HF Hi NE'. apply (BK p n i); [exact Hp | exact Hp' | exact HF | exact Hi |].
    intro X. destruct (HS _ X) as [Y | (_ & _ & Y)]; [exact (NE' Y)|]. exact (Y p n Hp HF ltac:(lia)). }
  exact SC.
Qed.

Lemma rp_F_weaken : forall K E F F' L A regs mem md L' A' regs' mem' md',
  relay_post Bm API K E F L A regs mem md L' A' regs' mem' md' -> (forall q, F q -> F' q) ->
  relay_post Bm API K E F' L A regs mem md L' A' regs' mem' md'.
Proof.
  intros K E F F' L A regs mem md L' A' regs' mem' md'
    (M' & W' & B' & LY & LN & PA & SV & Z0 & OW & RP & MD & FR & BK & SC) HF.
  split; [exact M'|]. split; [exact W'|]. split; [exact B'|]. split; [exact LY|]. split; [exact LN|].
  split; [intros p n Hp Hp' X; apply (PA p n Hp Hp'); intro Y; exact (X (HF _ Y))|].
  split; [intros p n Hp Hn X; apply (SV p n Hp Hn); intro Y; exact (X (HF _ Y))|].
  split; [exact Z0|]. split; [exact OW|]. split; [exact RP|]. split; [exact MD|]. split; [exact FR|].
  split; [intros p n i Hp Hp' X Hi NE; apply (BK p n i Hp Hp'); [intro Y; exact (X (HF _ Y)) | exact Hi | exact NE]|].
  exact SC.
Qed.

Lemma lmid_pre : forall K S E F L A regs mem md L1 A1 m1 md1 K1 f R1,
  call_pre_k Bm MR K L A regs mem md -> S = spZ regs ->
  lmid K S E F L A mem md L1 A1 m1 md1 -> st_init_done A1 = true ->
  spZ R1 = S - f -> spZ R1 mod 16 = 0 -> getr R1 4 = getr regs 4 -> YK0s.ret_ok (getr R1 1) ->
  0 <= f -> f + K1 <= K ->
  call_pre_k Bm MR K1 L1 A1 R1 m1 md1.
Proof.
  intros K S E F L A regs mem md L1 A1 m1 md1 K1 f R1 (HM & HW & HB & HRA & HAL & HC & H63 & HWS & HTP & HER & HAX) ->
    (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & SC1) HI Hsp Hal Htp Hra Hf HK.
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact Hra|]. split; [exact Hal|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; apply SC1; left; lia|].
  split; [exact (eq_trans Htp HTP)|].
  split; [intros a Ha; apply SC1; right; exact Ha|].
  intros X. rewrite HI in X. discriminate.
Qed.

Lemma rw_cp_block : forall K1 L A regs mem md E1 L' A' regs' mem' md' p k a cs,
  call_post_k Bm MR K1 L A regs mem md E1 L' A' regs' mem' md' ->
  In (p, k) (user_blocks A) -> In (p, k) (user_blocks A') ->
  ptr_addr L p <= a -> a + Z.of_nat (cells_size cs) <= ptr_addr L p + k ->
  rw_cells segs mem a cs -> rw_cells segs mem' a cs.
Proof.
  intros K1 L A regs mem md E1 L' A' regs' mem' md' p k a cs (M' & _ & _ & _ & PA & _ & _ & _ & BK & _)
    Hp Hp' H1 H2 RW.
  apply (rw_cells_transfer segs mem); [exact RW|]. intros i Hi.
  replace (a + i) with (ptr_addr L p + (a - ptr_addr L p + i)) by lia.
  split; [apply (BK p k); [exact Hp | exact Hp' | lia] |].
  intros _.
  destruct (mr_blocks _ _ (aa_laws API) L' A' mem' md' p k (a - ptr_addr L p + i) M' Hp' ltac:(lia)) as ((b & Hb) & _).
  rewrite (PA p k Hp Hp') in Hb.
  unfold writable_at, wview. rewrite Hb. discriminate.
Qed.

Lemma ba_cp_block : forall K1 L A regs mem md E1 L' A' regs' mem' md' p k a bs,
  call_post_k Bm MR K1 L A regs mem md E1 L' A' regs' mem' md' ->
  In (p, k) (user_blocks A) -> In (p, k) (user_blocks A') ->
  ptr_addr L p <= a -> a + Z.of_nat (length bs) <= ptr_addr L p + k ->
  bytes_at segs mem a bs -> bytes_at segs mem' a bs.
Proof.
  intros K1 L A regs mem md E1 L' A' regs' mem' md' p k a bs (_ & _ & _ & _ & _ & _ & _ & _ & BK & _)
    Hp Hp' H1 H2 BA.
  apply (bytes_at_transfer segs mem); [exact BA|]. intros i Hi.
  replace (a + i) with (ptr_addr L p + (a - ptr_addr L p + i)) by lia.
  apply (BK p k); [exact Hp | exact Hp' | lia].
Qed.

Lemma rw_cp_frame : forall K1 L A regs mem md E1 L' A' regs' mem' md' a cs,
  call_post_k Bm MR K1 L A regs mem md E1 L' A' regs' mem' md' ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
     (YM05.alloc_ceiling <= a + i < 2 ^ 64 \/ in_img Bm (a + i)) /\ ~ owned Bm L A (a + i) /\
     ~ owned Bm L' A' (a + i) /\ ~ scratch_k Bm K1 regs (a + i) /\ ~ E1 (a + i)) ->
  rw_cells segs mem a cs -> rw_cells segs mem' a cs.
Proof.
  intros K1 L A regs mem md E1 L' A' regs' mem' md' a cs (_ & _ & _ & _ & _ & _ & _ & FR & _ & _) H RW.
  apply (rw_cells_transfer segs mem); [exact RW|]. intros i Hi.
  destruct (H i Hi) as (H1 & H2 & H3 & H4 & H5). destruct (FR (a + i) H1 H2 H3 H4 H5) as [X Y].
  split; [exact X | apply Y].
Qed.

Lemma ba_cp_frame : forall K1 L A regs mem md E1 L' A' regs' mem' md' a bs,
  call_post_k Bm MR K1 L A regs mem md E1 L' A' regs' mem' md' ->
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     (YM05.alloc_ceiling <= a + i < 2 ^ 64 \/ in_img Bm (a + i)) /\ ~ owned Bm L A (a + i) /\
     ~ owned Bm L' A' (a + i) /\ ~ scratch_k Bm K1 regs (a + i) /\ ~ E1 (a + i)) ->
  bytes_at segs mem a bs -> bytes_at segs mem' a bs.
Proof.
  intros K1 L A regs mem md E1 L' A' regs' mem' md' a bs (_ & _ & _ & _ & _ & _ & _ & FR & _ & _) H BA.
  apply (bytes_at_transfer segs mem); [exact BA|]. intros i Hi.
  destruct (H i Hi) as (H1 & H2 & H3 & H4 & H5). exact (proj1 (FR (a + i) H1 H2 H3 H4 H5)).
Qed.

Lemma ba_ro : forall m m' a bs, ro_agree segs m -> ro_agree segs m' ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ro_addr segs (Z_to_bv 64 (a + i)) = true) ->
  bytes_at segs m a bs -> bytes_at segs m' a bs.
Proof.
  intros m m' a bs R R' H BA. apply (bytes_at_transfer segs m); [exact BA|]. intros i Hi.
  rewrite (mbyte_ro_agree _ _ _ R' (H i Hi)), (mbyte_ro_agree _ _ _ R (H i Hi)). reflexivity.
Qed.

Lemma lf_img_not_owned : forall L A mem md a, MR L A mem md -> img_plain Bm a -> ~ owned Bm L A a.
Proof.
  intros L A mem md a HM (Hi & Hs & Hc & He) [Ho|Ho];
    [exact (Hc (ax_img AX L A mem md a HM Hi Ho)) | exact (Hs Ho)].
Qed.

Lemma lf_block_present_rw : forall L A mem md q k a (n : nat), MR L A mem md -> In (q, k) (blocks L A) ->
  q <= a -> a + Z.of_nat n <= q + k -> exists junk, rw_cells segs mem a [CB n junk].
Proof.
  intros L A mem md q k a n HM Hin H1 H2.
  destruct (lf_blocks_in L A q k Hin) as (p & Hp & <-).
  pose proof (mr_blocks_range _ _ (aa_laws API) L A mem md p k HM Hp) as [R1 R2].
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  apply present_rw_cells; [lia | lia |]. intros i Hi.
  replace (a + i) with (ptr_addr L p + (a - ptr_addr L p + i)) by lia.
  exact (proj1 (mr_blocks _ _ (aa_laws API) L A mem md p k (a - ptr_addr L p + i) HM Hp ltac:(lia))).
Qed.

Lemma lift_run : forall regs pc mem md (W : list ivl) (Pm : (word -> option byte) -> Prop)
    (Rp : bvmap 5 word -> word -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  evt rsegs (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\ Rp R pc' /\
       munch W (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m' /\ Pm m')
     (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R R' pc' m1 m', Rp R pc' -> Regs6ss.xregs_eqv R R' -> munch W mem m1 -> wmono rsegs mem m1 ->
     ro_agree rsegs m1 -> mem_rel rsegs m1 m' -> Pm m' ->
     SR rsegs (mkCfg (YK11.mkst R' pc' m1 (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (YK11.mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md W Pm Rp P Hh Hl RO RUN K.
  eapply (evt_SR_canon rsegs); [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. apply (evt_normalize rsegs); [vm_compute; reflexivity | exact RO | exact RUN]. }
  intros ms1 (can1 & (s1 & Q1 & REL1 & ROS1) & EQ1).
  destruct Q1 as (R & pc' & m' & -> & HR & MU' & WM' & HP).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL1) as [CAN1 HR1].
  remember (ms_mem can1) as m1 eqn:Em1. subst can1. clear Em1.
  assert (RN0 : mem_rel rsegs mem (normalize rsegs mem)) by (apply mem_rel_normalize; exact RO).
  pose proof (munch_rel rsegs _ _ _ _ _ RN0 HR1 ROS1 MU') as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ RN0 HR1 ROS1 WM') as WM1.
  pose proof (ro_agree_same rsegs _ _ RO ROS1) as RO1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  exact (K R R1 pc' m1 m' HR X1 MU1 WM1 RO1 HR1 HP).
Qed.

Lemma pres_mkR : forall regs R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  Regs6ss.xregs_eqv (Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) R ->
  x2 = getr regs 2 -> x3 = getr regs 3 -> x4 = getr regs 4 -> x8 = getr regs 8 -> x9 = getr regs 9 ->
  x18 = getr regs 18 -> x19 = getr regs 19 -> x20 = getr regs 20 -> x21 = getr regs 21 -> x22 = getr regs 22 ->
  x23 = getr regs 23 -> x24 = getr regs 24 -> x25 = getr regs 25 -> x26 = getr regs 26 -> x27 = getr regs 27 ->
  regs_preserved regs R.
Proof.
  intros regs R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 X -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> r Hr.
  unfold callee_saved in Hr.
  assert (NZ : bv_eqb (Z_to_bv 5 r) 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia. }
  rewrite (getr_of_eqv _ _ _ X NZ).
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct C as [C|C]; [subst r; reflexivity|]). subst r. reflexivity.
Qed.

End LF.

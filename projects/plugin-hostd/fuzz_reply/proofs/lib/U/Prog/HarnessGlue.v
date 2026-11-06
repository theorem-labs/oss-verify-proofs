From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YO0u YO0x YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.

Lemma hg_ub_prid_lt : forall s p n, WF s -> In (p, n) (user_blocks s) -> (prid p < length (st_regions s))%nat.
Proof.
  intros s p n HW Hin.
  destruct (YO0x.user_blocks_frame s p n HW Hin) as (g & am & idx & fr & U & _ & _ & _ & _ & ->).
  unfold frame_ptr. rewrite YO0u.prid_padd, YO0u.prid_slot_start.
  exact (YO0u.used_group_prid_lt [] None U0 s g am HW U).
Qed.

Lemma hg_unsigned : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof. intros x Hx. apply unsigned_lit. exact Hx. Qed.

Section HG.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition sk (K sp a : Z) : Prop := (sp - K <= a < sp) \/ (errno_addr Bm <= a < errno_addr Bm + 4).

Definition rmid (K sp : Z) (E F : Z -> Prop)
    (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
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
     ~ owned Bm L A a -> ~ owned Bm L' A' a -> ~ sk K sp a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ~ F (ptr_addr L p) -> 0 <= i < n ->
     ~ E (ptr_addr L p + i) ->
     mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
  (forall a, sk K sp a -> writable_at segs mem' a).

Lemma rp_split : forall K E F L A regs mem md L' A' regs' mem' md',
  relay_post Bm API K E F L A regs mem md L' A' regs' mem' md' ->
  rmid K (spZ regs) E F L A mem md L' A' mem' md' /\ regs_preserved regs regs'.
Proof.
  intros K E F L A regs mem md L' A' regs' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14).
  split; [|exact H10].
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9
    (conj H11 (conj H12 (conj H13 H14)))))))))))).
Qed.

Lemma rp_join : forall K E F L A regs mem md L' A' regs' mem' md',
  rmid K (spZ regs) E F L A mem md L' A' mem' md' -> regs_preserved regs regs' ->
  relay_post Bm API K E F L A regs mem md L' A' regs' mem' md'.
Proof.
  intros K E F L A regs mem md L' A' regs' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H11 & H12 & H13 & H14) H10.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10
    (conj H11 (conj H12 (conj H13 H14))))))))))))).
Qed.

Lemma rmid_EF : forall K sp (E E' F F' : Z -> Prop) L A mem md L' A' mem' md',
  rmid K sp E F L A mem md L' A' mem' md' ->
  (forall a, E a -> E' a) -> (forall q, F q -> F' q) ->
  rmid K sp E' F' L A mem md L' A' mem' md'.
Proof.
  intros K sp E E' F F' L A mem md L' A' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H11 & H12 & H13 & H14) HE HF.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [intros p n Hp Hp' NF; exact (H6 p n Hp Hp' (fun X => NF (HF _ X)))|].
  split; [intros p n Hp Hn NF; exact (H7 p n Hp Hn (fun X => NF (HF _ X)))|].
  split; [exact H8|]. split; [exact H9|]. split; [exact H11|].
  split; [intros a Ha N1 N2 NS NE; exact (H12 a Ha N1 N2 NS (fun X => NE (HE _ X)))|].
  split; [intros p n i Hp Hp' NF Hi NE; exact (H13 p n i Hp Hp' (fun X => NF (HF _ X)) Hi (fun X => NE (HE _ X)))|].
  exact H14.
Qed.

Lemma rmid_seq : forall K sp E1 F1 E2 F2 L A mem md L1 A1 mem1 md1 L2 A2 mem2 md2,
  WF A ->
  rmid K sp E1 F1 L A mem md L1 A1 mem1 md1 ->
  rmid K sp E2 F2 L1 A1 mem1 md1 L2 A2 mem2 md2 ->
  rmid K sp (fun a => E1 a \/ E2 a) (fun q => F1 q \/ F2 q) L A mem md L2 A2 mem2 md2.
Proof.
  intros K sp E1 F1 E2 F2 L A mem md L1 A1 mem1 md1 L2 A2 mem2 md2 HW
    (M1 & W1 & B1 & LY1 & LN1 & PA1 & SV1 & Z01 & OW1 & MD1 & BY1 & BK1 & SC1)
    (M2 & W2 & B2 & LY2 & LN2 & PA2 & SV2 & Z02 & OW2 & MD2 & BY2 & BK2 & SC2).
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL. pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  assert (LYA : layout_le A L L2).
  { destruct LY1 as (C1 & S1 & R1 & G1), LY2 as (C2 & S2 & R2 & G2).
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros r Hr. rewrite G2 by lia. apply G1. exact Hr. }
  assert (SVA : forall p n, In (p, n) (user_blocks A) -> 0 < n -> ~ (F1 (ptr_addr L p) \/ F2 (ptr_addr L p)) ->
                In (p, n) (user_blocks A1)).
  { intros p n Hp Hn HF. apply SV1; [exact Hp | exact Hn | intro X; apply HF; left; exact X]. }
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|]. split; [exact LYA|]. split; [lia|].
  split.
  { intros p n Hp _ _. pose proof (hg_ub_prid_lt A p n HW Hp) as Hr. destruct LYA as (_ & _ & _ & G).
    destruct p as [r o]. unfold ptr_addr. cbn [loc_addr]. cbn [prid] in Hr. rewrite G by exact Hr. reflexivity. }
  split.
  { intros p n Hp Hn HF. pose proof (SVA p n Hp Hn HF) as H1.
    apply SV2; [exact H1 | exact Hn |].
    rewrite (PA1 p n Hp H1 (fun X => HF (or_introl X))). intro X; apply HF; right; exact X. }
  split.
  { intros p Hp. destruct (Z01 p Hp) as [H1 Q1]. destruct (Z02 p H1) as [H2 Q2]. split; [exact H2 | congruence]. }
  split.
  { intros a Ha Ho. apply OW1; [exact Ha|]. apply OW2; [exact Ha | exact Ho]. }
  split.
  { destruct MD1 as (v1 & ->). destruct MD2 as (v2 & ->). exists v2. apply YI04.with_vmmaps_twice. }
  split.
  { intros a Ha NO NO2 NS NE.
    assert (NO1 : ~ owned Bm L1 A1 a).
    { intro X. destruct Ha as [Ha|Ha].
      - pose proof (mr_owned_low _ _ LAWS _ _ _ _ a M1 X). lia.
      - exact (NO (OW1 a Ha X)). }
    destruct (BY1 a Ha NO NO1 NS (fun X => NE (or_introl X))) as [Y1 Z1].
    destruct (BY2 a Ha NO1 NO2 NS (fun X => NE (or_intror X))) as [Y2 Z2].
    split; [rewrite Y2, Y1; reflexivity | tauto]. }
  split.
  { intros p n i Hp Hp2 HF Hi NE.
    assert (Hn : 0 < n) by lia. pose proof (SVA p n Hp Hn HF) as Hp1.
    assert (NF1 : ~ F1 (ptr_addr L p)) by (intro X; apply HF; left; exact X).
    pose proof (PA1 p n Hp Hp1 NF1) as EA.
    pose proof (BK2 p n i Hp1 Hp2) as X2. rewrite EA in X2.
    rewrite (X2 (fun X => HF (or_intror X)) Hi (fun X => NE (or_intror X))).
    exact (BK1 p n i Hp Hp1 NF1 Hi (fun X => NE (or_introl X))). }
  exact SC2.
Qed.

Lemma rmid_widen : forall K1 sp1 K sp E F L A mem md L' A' mem' md',
  MR L A mem md ->
  sp - K <= sp1 - K1 -> sp1 <= sp -> alloc_ceiling <= sp - K -> sp <= 2 ^ 64 ->
  (forall a, sp - K <= a < sp -> writable_at segs mem a) ->
  (forall a, sp - K <= a < sp -> ~ E a) ->
  rmid K1 sp1 E F L A mem md L' A' mem' md' ->
  rmid K sp E F L A mem md L' A' mem' md'.
Proof.
  intros K1 sp1 K sp E F L A mem md L' A' mem' md' HM H1 H2 H3 H4 HWS HE
    (M1 & W1 & B1 & LY1 & LN1 & PA1 & SV1 & Z01 & OW1 & MD1 & BY1 & BK1 & SC1).
  pose proof (aa_laws API) as LAWS.
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact LY1|]. split; [exact LN1|].
  split; [exact PA1|]. split; [exact SV1|]. split; [exact Z01|]. split; [exact OW1|]. split; [exact MD1|].
  split.
  { intros a Ha NO NO' NS NE. apply BY1; [exact Ha | exact NO | exact NO' | | exact NE].
    unfold sk in *. intros [X|X]; apply NS; [left; lia | right; exact X]. }
  split; [exact BK1|].
  intros a Ha.
  assert (D : sk K1 sp1 a \/ ~ sk K1 sp1 a) by (unfold sk; lia).
  destruct D as [D|D]; [exact (SC1 a D)|].
  unfold sk in Ha. destruct Ha as [Ha|Ha]; [|exfalso; apply D; right; exact Ha].
  assert (NO : ~ owned Bm L A a) by (intro X; pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HM X); lia).
  assert (NO' : ~ owned Bm L' A' a) by (intro X; pose proof (mr_owned_low _ _ LAWS _ _ _ _ a M1 X); lia).
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL. pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  assert (Hr : alloc_ceiling <= a < 2 ^ 64) by lia.
  apply (proj2 (BY1 a (or_introl Hr) NO NO' D (HE a ltac:(lia)))). exact (HWS a ltac:(lia)).
Qed.

Lemma rmid_A : forall K sp E F L A mem md mem' W,
  MR L A mem md -> WF A -> bounded A ->
  (forall a, in_img Bm a -> 0 <= a < alloc_ceiling) ->
  alloc_ceiling <= sp - K ->
  (forall a, sk K sp a -> writable_at segs mem a) ->
  munch W mem mem' -> wmono segs mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> (sp - K <= x < sp) \/ E x) ->
  (forall a, owned Bm L A a -> outside W a) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> ~ outside W (ptr_addr L p + i) ->
     present mem' (ptr_addr L p + i)) ->
  rmid K sp E F L A mem md L A mem' md.
Proof.
  intros K sp E F L A mem md mem' W HM HWF HB HIMG HK HWS MU WM HWE HOW HBP.
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL. pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  destruct (mr_model _ _ LAWS _ _ _ _ HM) as (Hh & Hl & Hmat).
  assert (OD : forall x, outside W x \/ ~ outside W x).
  { clear. induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
    destruct (IH x) as [H|H]; [|right; tauto].
    destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi); [right; lia | left; split; [lia|exact H] ..]. }
  split.
  { apply (mr_frame _ _ LAWS L A mem mem' md md HM).
    - intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HM Ho).
      unfold mbyte. rewrite (MU (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit by lia. exact (HOW a Ho).
    - intros a Ho [b E1]. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HM Ho). exists b.
      rewrite (MU (Z_to_bv 64 a)); [exact E1|]. rewrite unsigned_lit by lia. exact (HOW a Ho).
    - intros p n i Hp Hi. destruct (mr_blocks _ _ LAWS _ _ _ _ p n i HM Hp Hi) as ([b E1] & R1 & R2 & _).
      destruct (OD (ptr_addr L p + i)) as [O|O]; [|exact (HBP p n i Hp Hi O)].
      exists b. rewrite (MU (Z_to_bv 64 (ptr_addr L p + i))); [exact E1|]. rewrite unsigned_lit by lia. exact O.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact HWF|]. split; [exact HB|]. split; [apply layout_le_refl|]. split; [lia|].
  split; [intros; reflexivity|].
  split; [intros p n Hp _ _; exact Hp|].
  split; [intros p Hp; split; [exact Hp | reflexivity]|].
  split; [intros a _ Ho; exact Ho|].
  split; [exists (m_vmmaps md); apply YI04.with_vmmaps_self|].
  split.
  { intros a Ha NO _ NS NE.
    assert (Ra : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | pose proof (HIMG a Ha); lia]).
    destruct (OD a) as [O|O].
    - unfold mbyte, writable_at, wview. rewrite (MU (Z_to_bv 64 a)); [tauto|]. rewrite unsigned_lit by lia. exact O.
    - exfalso. destruct (HWE a Ra O) as [X|X]; [apply NS; left; exact X | exact (NE X)]. }
  split.
  { intros p n i Hp _ _ Hi NE. destruct (mr_blocks _ _ LAWS _ _ _ _ p n i HM Hp Hi) as (_ & R1 & R2 & _).
    destruct (OD (ptr_addr L p + i)) as [O|O].
    - unfold mbyte. rewrite (MU (Z_to_bv 64 (ptr_addr L p + i))); [reflexivity|]. rewrite unsigned_lit by lia. exact O.
    - exfalso. destruct (HWE (ptr_addr L p + i) ltac:(lia) O) as [X|X]; [lia | exact (NE X)]. }
  intros a Ha. unfold writable_at. apply WM. exact (HWS a Ha).
Qed.

Lemma rmid_of_cpk : forall K E (F : Z -> Prop) L A regs mem md L' A' regs' mem' md',
  AllocExtra Bm MR -> ctx_owned Bm API -> MR L A mem md ->
  call_post_k Bm MR K L A regs mem md E L' A' regs' mem' md' ->
  (length (st_regions A) <= length (st_regions A'))%nat ->
  (forall p n, In (p, n) (user_blocks A) -> 0 < n -> ~ F (ptr_addr L p) -> In (p, n) (user_blocks A')) ->
  (forall p, In (p, 0) (user_blocks A) -> In (p, 0) (user_blocks A')) ->
  rmid K (spZ regs) E F L A mem md L' A' mem' md' /\ regs_preserved regs regs'.
Proof.
  intros K E F L A regs mem md L' A' regs' mem' md' AX CTX HM
    (M1 & W1 & B1 & LY1 & PA1 & RG1 & MD1 & BY1 & BK1 & SC1) LN SV Z0.
  split; [|exact RG1].
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact LY1|]. split; [exact LN|].
  split; [intros p n Hp Hp' _; exact (PA1 p n Hp Hp')|].
  split; [exact SV|].
  split; [intros p Hp; pose proof (Z0 p Hp) as Hp'; split; [exact Hp' | exact (PA1 p 0 Hp Hp')]|].
  split.
  { intros a Hi [Ho|Ho]; [|right; exact Ho].
    exact (CTX L A mem md a HM (ax_img AX L' A' mem' md' a M1 Hi Ho)). }
  split; [exact MD1|].
  split; [exact BY1|].
  split; [intros p n i Hp Hp' _ Hi _; exact (BK1 p n i Hp Hp' Hi)|].
  exact SC1.
Qed.

Lemma kseg : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  wx_apart rsegs = true -> ro_agree rsegs mem -> m_halted md = None -> m_vm_lazy md = [] ->
  evt rsegs Q (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall s0, Q s0 -> exists R pc' m0, s0 = MS R fp_regs pc' fp_csr None m0 (seg_rom rsegs)) ->
  (forall R pc' m0 regs1 m1, Q (MS R fp_regs pc' fp_csr None m0 (seg_rom rsegs)) ->
     (forall r, YK11.getr regs1 r = YK11.getr R r) -> mem_rel rsegs m1 m0 -> ro_same rsegs mem m1 ->
     SR rsegs (mkCfg (YK11.mkst regs1 pc' m1 (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (YK11.mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md Q P WX RO Hh Hl HE HS HK.
  eapply (evt_SR_canon rsegs (YK11.mkst regs pc mem (seg_rom rsegs)) _ md P); [ | exact Hh | exact Hl | ].
  { change (RegisterBridge.canonical_register_state (YK11.mkst regs pc mem (seg_rom rsegs)))
      with (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)).
    apply (evt_normalize rsegs); [exact WX | exact RO | exact HE]. }
  intros ms' (can & (s0 & HQ & REL & ROS) & EQV).
  destruct (HS s0 HQ) as (R & pc' & m0 & ->).
  destruct can as [r1 f1 p1 sv1 v1 c1 mm1 o1]. destruct ms' as [r f p sv v c mm o].
  destruct REL as (R1 & F1 & P1 & S1 & V1 & C1 & O1 & M1).
  destruct EQV as (X & F2 & P2 & S2 & V2 & C2 & M2 & O2).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in *.
  subst r1 f1 p1 sv1 v1 c1 o1. subst f p sv v c o mm1.
  apply (HK R pc' m0 r mm HQ); [| exact M1 | exact ROS].
  intros r0. unfold YK11.getr. destruct (bv_eqb r0 0) eqn:EZ; [reflexivity|].
  symmetry. apply X. exact EZ.
Qed.

Lemma kseg_raw : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  evt rsegs Q (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall s0, Q s0 -> exists R pc' m0, s0 = MS R fp_regs pc' fp_csr None m0 (seg_rom rsegs)) ->
  (forall R pc' m0 regs1, Q (MS R fp_regs pc' fp_csr None m0 (seg_rom rsegs)) ->
     (forall r, YK11.getr regs1 r = YK11.getr R r) ->
     SR rsegs (mkCfg (YK11.mkst regs1 pc' m0 (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (YK11.mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl HE HS HK.
  eapply (evt_SR_canon rsegs (YK11.mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & HQ & EQV).
  destruct (HS can HQ) as (R & pc' & m0 & ->).
  destruct ms' as [r f p sv v c mm o].
  destruct EQV as (X & F2 & P2 & S2 & V2 & C2 & M2 & O2).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in *.
  subst f p sv v c o mm.
  apply (HK R pc' m0 r HQ).
  intros r0. unfold YK11.getr. destruct (bv_eqb r0 0) eqn:EZ; [reflexivity|].
  symmetry. apply X. exact EZ.
Qed.

Lemma hg_img_not_owned : AllocExtra Bm MR -> forall L A mem md a, MR L A mem md -> img_plain Bm a -> ~ owned Bm L A a.
Proof.
  intros AX L A mem md a HM (Hi & Hs & Hc & He) [Ho|Ho];
    [exact (Hc (ax_img AX L A mem md a HM Hi Ho)) | exact (Hs Ho)].
Qed.

Lemma rmid_img : AllocExtra Bm MR -> forall K sp E F L A mem md L' A' mem' md' a,
  (forall x, in_img Bm x -> 0 <= x < alloc_ceiling) -> alloc_ceiling <= sp - K ->
  MR L A mem md -> rmid K sp E F L A mem md L' A' mem' md' -> img_plain Bm a -> ~ E a ->
  mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a).
Proof.
  intros AX K sp E F L A mem md L' A' mem' md' a HIMG HK HM R P NE.
  destruct R as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & BY & _).
  pose proof P as (Pi & _ & _ & Pe). pose proof (HIMG a Pi).
  apply BY; [right; exact Pi | exact (hg_img_not_owned AX L A mem md a HM P)
            | exact (hg_img_not_owned AX L' A' mem' md' a M1 P) | | exact NE].
  unfold sk. intros [X|X]; [lia | exact (Pe X)].
Qed.

Lemma rmid_rw_img : AllocExtra Bm MR -> forall K sp E F L A mem md L' A' mem' md' a cs,
  (forall x, in_img Bm x -> 0 <= x < alloc_ceiling) -> alloc_ceiling <= sp - K ->
  MR L A mem md -> rmid K sp E F L A mem md L' A' mem' md' ->
  rw_cells segs mem a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> img_plain Bm (a + i) /\ ~ E (a + i)) ->
  rw_cells segs mem' a cs.
Proof.
  intros AX K sp E F L A mem md L' A' mem' md' a cs HIMG HK HM R H D.
  apply (rw_cells_transfer segs mem); [exact H|]. intros i Hi. destruct (D i Hi) as [P NE].
  destruct (rmid_img AX K sp E F L A mem md L' A' mem' md' (a + i) HIMG HK HM R P NE) as [X Y].
  split; [exact X | apply Y].
Qed.

Lemma rmid_bytes_img : AllocExtra Bm MR -> forall K sp E F L A mem md L' A' mem' md' a bs,
  (forall x, in_img Bm x -> 0 <= x < alloc_ceiling) -> alloc_ceiling <= sp - K ->
  MR L A mem md -> rmid K sp E F L A mem md L' A' mem' md' ->
  bytes_at segs mem a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> img_plain Bm (a + i) /\ ~ E (a + i)) ->
  bytes_at segs mem' a bs.
Proof.
  intros AX K sp E F L A mem md L' A' mem' md' a bs HIMG HK HM R H D.
  apply (bytes_at_transfer segs mem); [exact H|]. intros i Hi. destruct (D i Hi) as [P NE].
  exact (proj1 (rmid_img AX K sp E F L A mem md L' A' mem' md' (a + i) HIMG HK HM R P NE)).
Qed.

Lemma rmid_hi : forall K sp E F L A mem md L' A' mem' md' a,
  alloc_ceiling <= sp -> errno_addr Bm + 4 <= sp ->
  MR L A mem md -> rmid K sp E F L A mem md L' A' mem' md' -> sp <= a < 2 ^ 64 -> ~ E a ->
  mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a).
Proof.
  intros K sp E F L A mem md L' A' mem' md' a H1 H2 HM R Ha NE.
  pose proof (aa_laws API) as LAWS.
  destruct R as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & BY & _).
  apply BY; [left; lia | | | | exact NE].
  - intro X. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HM X). lia.
  - intro X. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a M1 X). lia.
  - unfold sk. lia.
Qed.

Lemma rmid_rw_hi : forall K sp E F L A mem md L' A' mem' md' a cs,
  alloc_ceiling <= sp -> errno_addr Bm + 4 <= sp ->
  MR L A mem md -> rmid K sp E F L A mem md L' A' mem' md' ->
  rw_cells segs mem a cs -> sp <= a -> a + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ~ E (a + i)) ->
  rw_cells segs mem' a cs.
Proof.
  intros K sp E F L A mem md L' A' mem' md' a cs H1 H2 HM R H Ha Hb D.
  apply (rw_cells_transfer segs mem); [exact H|]. intros i Hi.
  destruct (rmid_hi K sp E F L A mem md L' A' mem' md' (a + i) H1 H2 HM R ltac:(lia) (D i Hi)) as [X Y].
  split; [exact X | apply Y].
Qed.

Lemma rmid_block : blocks_writable Bm API -> forall K sp E F L A mem md L' A' mem' md' q k i,
  rmid K sp E F L A mem md L' A' mem' md' -> In (q, k) (blocks L A) -> 0 < k -> ~ F q -> 0 <= i < k ->
  ~ E (q + i) ->
  In (q, k) (blocks L' A') /\ mbyte segs mem' (q + i) = mbyte segs mem (q + i) /\ writable_at segs mem' (q + i).
Proof.
  intros BW K sp E F L A mem md L' A' mem' md' q k i R Hin Hk NF Hi NE.
  destruct R as (M1 & _ & _ & _ & _ & PA & SV & _ & _ & _ & _ & BK & _).
  unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & EQ & Hp). cbn [fst snd] in EQ.
  injection EQ as <- <-.
  pose proof (SV p k' Hp Hk NF) as Hp'. pose proof (PA p k' Hp Hp' NF) as EA.
  assert (IB : In (ptr_addr L p, k') (blocks L' A')).
  { rewrite <- EA. unfold blocks. exact (in_map (fun b => (ptr_addr L' (fst b), snd b)) _ (p, k') Hp'). }
  split; [exact IB|]. split; [exact (BK p k' i Hp Hp' NF Hi NE)|].
  exact (BW L' A' mem' md' _ k' i M1 IB Hi).
Qed.

Lemma rmid_rw_block : blocks_writable Bm API -> forall K sp E F L A mem md L' A' mem' md' q k a cs,
  rmid K sp E F L A mem md L' A' mem' md' -> In (q, k) (blocks L A) -> 0 < k -> ~ F q ->
  rw_cells segs mem a cs -> q <= a -> a + Z.of_nat (cells_size cs) <= q + k ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ~ E (a + i)) ->
  rw_cells segs mem' a cs.
Proof.
  intros BW K sp E F L A mem md L' A' mem' md' q k a cs R Hin Hk NF H Ha Hb D.
  apply (rw_cells_transfer segs mem); [exact H|]. intros i Hi.
  replace (a + i) with (q + (a - q + i)) by lia.
  destruct (rmid_block BW K sp E F L A mem md L' A' mem' md' q k (a - q + i) R Hin Hk NF ltac:(lia)
              ltac:(replace (q + (a - q + i)) with (a + i) by lia; exact (D i Hi))) as (_ & X & Y).
  split; [exact X | intros _; exact Y].
Qed.

Lemma rmid_bytes_block : blocks_writable Bm API -> forall K sp E F L A mem md L' A' mem' md' q k a bs,
  rmid K sp E F L A mem md L' A' mem' md' -> In (q, k) (blocks L A) -> 0 < k -> ~ F q ->
  bytes_at segs mem a bs -> q <= a -> a + Z.of_nat (length bs) <= q + k ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ E (a + i)) ->
  bytes_at segs mem' a bs.
Proof.
  intros BW K sp E F L A mem md L' A' mem' md' q k a bs R Hin Hk NF H Ha Hb D.
  apply (bytes_at_transfer segs mem); [exact H|]. intros i Hi.
  replace (a + i) with (q + (a - q + i)) by lia.
  exact (proj1 (proj2 (rmid_block BW K sp E F L A mem md L' A' mem' md' q k (a - q + i) R Hin Hk NF ltac:(lia)
              ltac:(replace (q + (a - q + i)) with (a + i) by lia; exact (D i Hi))))).
Qed.

Lemma hg_img_low : ms_segs Bm = rsegs -> forall a, in_img Bm a -> 0 <= a < alloc_ceiling.
Proof.
  intros SEG a H. pose proof (in_img_low Bm SEG a H). pose proof (@YM05.alloc_ceiling_value rc). lia.
Qed.

Lemma rmid_norm : forall K sp E F L A mem md m0' m1 W,
  ms_segs Bm = rsegs -> ro_agree rsegs mem -> mem_rel rsegs m1 m0' -> ro_same rsegs mem m1 ->
  munch W (normalize rsegs mem) m0' -> wmono rsegs (normalize rsegs mem) m0' ->
  MR L A mem md -> WF A -> bounded A ->
  alloc_ceiling <= sp - K ->
  (forall a, sk K sp a -> writable_at segs mem a) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> (sp - K <= x < sp) \/ E x) ->
  (forall a, owned Bm L A a -> outside W a) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> ~ outside W (ptr_addr L p + i) ->
     present m1 (ptr_addr L p + i)) ->
  rmid K sp E F L A mem md L A m1 md /\ munch W mem m1 /\ wmono rsegs mem m1.
Proof.
  intros K sp E F L A mem md m0' m1 W SEG RO HR ROS MU WM HM HWF HB HK HWS HWE HOW HBP.
  pose proof (mem_rel_normalize rsegs mem RO) as HR0.
  pose proof (munch_rel rsegs W mem _ m1 m0' HR0 HR ROS MU) as MUr.
  pose proof (wmono_rel rsegs mem _ m1 m0' HR0 HR ROS WM) as WMr.
  split; [|split; [exact MUr | exact WMr]].
  apply (rmid_A K sp E F L A mem md m1 W HM HWF HB (hg_img_low SEG) HK HWS MUr); [| exact HWE | exact HOW | exact HBP].
  unfold segs. rewrite SEG. exact WMr.
Qed.

Lemma cpk_of_rmid : forall K sp E F L A mem md L' A' mem' md' regs' K',
  rmid K sp E F L A mem md L' A' mem' md' ->
  st_init_done A' = true ->
  YK0s.ret_ok (YK11.getr regs' 1) -> YK11.getr regs' 4 = Z_to_bv 64 (ms_tp Bm) ->
  spZ regs' mod 16 = 0 -> sp - K <= spZ regs' - K' -> spZ regs' <= sp -> 0 <= K' ->
  alloc_ceiling + K' <= spZ regs' -> spZ regs' < 2 ^ 63 ->
  call_pre_k Bm MR K' L' A' regs' mem' md'.
Proof.
  intros K sp E F L A mem md L' A' mem' md' regs' K'
    (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC) INI RA TP AL H1 H2 H3 H4 H5.
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact RA|]. split; [exact AL|].
  split; [exact H4|]. split; [exact H5|].
  split; [intros a Ha; apply SC; unfold sk; left; lia|].
  split; [exact TP|].
  split; [intros a Ha; apply SC; unfold sk; right; exact Ha|].
  intros X. rewrite INI in X. discriminate.
Qed.

End HG.

Lemma rw_cells_retype : forall segs m a cs cs', rw_cells segs m a cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells segs m a cs'.
Proof.
  intros segs m a cs cs' [[W B] Wr] W' E.
  assert (S : cells_size cs' = cells_size cs).
  { rewrite <- (cells_bytes_length cs' W'), <- (cells_bytes_length cs W), E. reflexivity. }
  split; [split; [exact W' | rewrite E; exact B]|]. rewrite S. exact Wr.
Qed.

Lemma hg_cut : forall segs m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[W B] (H0 & H1 & H)].
  apply cells_wf_app in W. destruct W as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in H1, H.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H. lia.
Qed.

Lemma hg_join : forall segs m A B cs1 cs2, rw_cells segs m A cs1 -> rw_cells segs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A B cs1 cs2 [[W1 B1] (H0 & H1 & H)] [[W2 B2] (G0 & G1 & G)] ->.
  split; split.
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - lia.
  - rewrite cells_size_app. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hlt|Hge]; [apply H; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G. lia.
Qed.

Lemma hg_not_out : forall W x, ~ outside W x -> exists lo hi, In (lo, hi) W /\ lo <= x < hi.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn [outside] in H; [exfalso; exact (H I)|].
  destruct (Z_le_gt_dec lo x) as [D1|D1]; destruct (Z_lt_ge_dec x hi) as [D2|D2].
  - exists lo, hi. split; [left; reflexivity | lia].
  - destruct (IH x) as (l0 & h0 & I1 & I2); [intro X; apply H; split; [lia | exact X]|].
    exists l0, h0. split; [right; exact I1 | exact I2].
  - destruct (IH x) as (l0 & h0 & I1 & I2); [intro X; apply H; split; [lia | exact X]|].
    exists l0, h0. split; [right; exact I1 | exact I2].
  - destruct (IH x) as (l0 & h0 & I1 & I2); [intro X; apply H; split; [lia | exact X]|].
    exists l0, h0. split; [right; exact I1 | exact I2].
Qed.

Lemma hg_out : forall W x, (forall lo hi, In (lo, hi) W -> x < lo \/ hi <= x) -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn [outside]; [exact I|].
  split; [destruct (H lo hi (or_introl eq_refl)); lia|]. apply IH. intros l0 h0 I1. exact (H l0 h0 (or_intror I1)).
Qed.

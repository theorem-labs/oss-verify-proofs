From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YI04 YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c RelayRep HarnessRep drain_b_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rk_vm_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma rk_vm_self : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma rk_ub_nonneg : forall s p n, WF s -> In (p, n) (user_blocks s) -> 0 <= n.
Proof.
  intros s p n HW Hin.
  destruct (YO10.in_user_blocks_inv s (p, n) Hin) as (g & am & i & fr & Hg & Hi & Hfr & _ & E).
  apply (YO10.used_metas_usedX s g am HW) in Hg.
  destruct (YO10.block_in_slot s g am i fr HW Hg Hi Hfr) as (_ & _ & H).
  injection E as _ ->. exact H.
Qed.

Lemma rk_blocks_in : forall L A a n, In (a, n) (blocks L A) <-> exists p, ptr_addr L p = a /\ In (p, n) (user_blocks A).
Proof.
  intros L A a n. unfold blocks. rewrite in_map_iff. split.
  - intros ([p k] & H & Hin). cbn in H. injection H as <- <-. exists p. auto.
  - intros (p & <- & Hin). exists (p, n). auto.
Qed.

Lemma rk_present_writable : forall segs m a, present m a -> writable_at segs m a.
Proof. intros segs m a [b E]. unfold writable_at, wview. rewrite E. discriminate. Qed.

Lemma rk_reg_eqv : forall M R (k : Z), Regs6ss.xregs_eqv M R -> 0 < k < 32 -> YK11.getr R (Z_to_bv 5 k) = reg_get M (Z_to_bv 5 k).
Proof.
  intros M R k X Hk. apply getr_of_eqv; [exact X|].
  unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia.
Qed.


Lemma rk_bytes_of_mbytes : forall segs m a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> exists b, mbyte segs m (a + i) = Some b) ->
  exists bs, length bs = n /\ bytes_at segs m a bs.
Proof.
  intros segs m a n. revert a. induction n as [|n IH]; intros a Ha Hn H.
  - exists []. split; [reflexivity|]. split; [exact Ha|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (H 0 ltac:(lia)) as [b Eb]. rewrite Z.add_0_r in Eb.
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Lb & Hb).
    { intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply H. lia. }
    exists (b :: bs). split; [cbn; lia|].
    change (b :: bs) with ([b] ++ bs). apply bytes_at_app. split.
    + split; [exact Ha|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i as [|i]; [|lia].
      cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Eb.
    + cbn [length Z.of_nat]. exact Hb.
Qed.

Lemma rk_c4_of_bytes : forall segs m A b0 b1 b2 b3,
  bytes_at segs m A [b0; b1; b2; b3] -> wr_at segs m A 4 ->
  rw_cells segs m A [C4 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3]))].
Proof.
  intros segs m A b0 b1 b2 b3 HB HW.
  pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3]) as B1. pose proof (bytes_le_to_Z_nonneg [b0; b1; b2; b3]) as B0.
  cbn [length Z.of_nat] in B1.
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le4. rewrite unsigned_lit by lia.
    change 4%nat with (length [b0; b1; b2; b3]). rewrite StrFun.Z_to_le_bytes_to_Z. exact HB.
  - cbn [cells_size csize]. exact HW.
Qed.

Lemma rk_rsegs_wr_rd : forallb (fun s => implb (seg_writable s) (seg_readable s)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rk_writable_mbyte : forall m a, writable_at rsegs m a -> exists b, mbyte rsegs m a = Some b.
Proof.
  intros m a W. revert W. unfold writable_at, wview, mbyte.
  destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; exists b; reflexivity|].
  destruct (find_segment rsegs (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:Fs; [|intros W; exfalso; exact (W eq_refl)].
  destruct (seg_writable seg) eqn:Wr; [|intros W; exfalso; exact (W eq_refl)].
  assert (Rd : seg_readable seg = true).
  { pose proof (proj1 (forallb_forall _ rsegs) rk_rsegs_wr_rd seg (proj1 (find_segment_in _ _ _ _ Fs))) as H.
    cbv beta in H. rewrite Wr in H. exact H. }
  unfold YK11.seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite Fs. cbv beta iota. rewrite Rd.
  cbv beta iota zeta. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at (seg_bytes seg) _) as [b|]; [intros _; exists b; reflexivity|].
  intros W. exfalso. exact (W eq_refl).
Qed.

Lemma rk_err_cells : forall m A, 0 <= A -> A + 4 <= 2 ^ 64 ->
  (forall i, 0 <= i < 4 -> writable_at rsegs m (A + i)) -> exists v, rw_cells rsegs m A [C4 v].
Proof.
  intros m A H0 H1 W.
  destruct (rk_bytes_of_mbytes rsegs m A 4 H0 H1) as (bs & Lb & Hb).
  { intros i Hi. apply rk_writable_mbyte. apply W. cbn in Hi. lia. }
  destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 bs]]]]]; cbn in Lb; try discriminate.
  eexists. apply rk_c4_of_bytes; [exact Hb|].
  split; [exact H0|]. split; [exact H1|]. intros i Hi. exact (W i Hi).
Qed.

Lemma rk_mkR_of : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 R,
  Regs6ss.xregs_eqv (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31) R ->
  Regs6ss.mkR_of R = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31.
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 R H.
  unfold Regs6ss.mkR_of. rewrite <- !H by reflexivity. reflexivity.
Qed.


Section RK.
Context {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Local Notation segs := (ms_segs Bm).
Local Notation MR := (aa_MR API).
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTX : ctx_owned Bm API.
Hypothesis SEGS : ms_segs Bm = rsegs.
Hypothesis BSP : block_slack_present Bm API.

Lemma rk_laws : MR_laws Bm MR.
Proof using. exact (aa_laws API). Qed.

Lemma rk_owned_low : forall L A mem md a, MR L A mem md -> owned Bm L A a -> 0 <= a < alloc_ceiling.
Proof using. intros L A mem md a HM Ho. exact (mr_owned_low Bm MR rk_laws L A mem md a HM Ho). Qed.

Lemma rk_blk : forall L A mem md q k i, MR L A mem md -> In (q, k) (blocks L A) -> 0 <= i < k ->
  present mem (q + i) /\ 4096 <= q /\ q + k <= alloc_ceiling /\ ~ owned Bm L A (q + i).
Proof using.
  intros L A mem md q k i HM Hin Hi. apply rk_blocks_in in Hin as (p & <- & Hp).
  exact (mr_blocks Bm MR rk_laws L A mem md p k i HM Hp Hi).
Qed.

Lemma rk_scratch_dec : forall K regs a, scratch_k Bm K regs a \/ ~ scratch_k Bm K regs a.
Proof using. intros K regs a. unfold scratch_k. lia. Qed.

Lemma rk_blk_disj : forall L A mem md p n q k, MR L A mem md -> In (p, n) (blocks L A) -> In (q, k) (blocks L A) ->
  p <> q -> p + n <= q \/ q + k <= p.
Proof using. intros. eapply (blocks_disjoint Bm API); eassumption. Qed.

Lemma rk_plain_unowned : forall L A mem md a, MR L A mem md -> img_plain Bm a -> ~ owned Bm L A a.
Proof using AX.
  intros L A mem md a HM (Hi & Hs & Hc & He) [Ho|Ho].
  - exact (Hc (ax_img AX L A mem md a HM Hi Ho)).
  - exact (Hs Ho).
Qed.

Lemma rk_img_owned : forall L A mem md L' A' mem' md' a, MR L A mem md -> MR L' A' mem' md' -> in_img Bm a ->
  owned Bm L' A' a -> owned Bm L A a.
Proof using AX CTX.
  intros L A mem md L' A' mem' md' a HM HM' Hi [Ho|Ho].
  - apply (CTX L A mem md a HM). exact (ax_img AX L' A' mem' md' a HM' Hi Ho).
  - right. exact Ho.
Qed.

Definition rk_chain (K : Z) (E F : Z -> Prop)
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

Lemma rk_chain_post : forall K E F L A regs mem md L' A' regs' mem' md',
  rk_chain K E F L A regs mem md L' A' mem' md' -> regs_preserved regs regs' ->
  relay_post Bm API K E F L A regs mem md L' A' regs' mem' md'.
Proof using.
  intros K E F L A regs mem md L' A' regs' mem' md'
    (M & W & B & LE & RG & AD & SV & Z0 & IO & VM & FR & BY & SW) RP.
  repeat (split; [eassumption|]). exact SW.
Qed.

Lemma rk_chain_refl : forall K E F L A regs mem md, MR L A mem md -> WF A -> bounded A ->
  (forall a, scratch_k Bm K regs a -> writable_at segs mem a) ->
  rk_chain K E F L A regs mem md L A mem md.
Proof using.
  intros K E F L A regs mem md HM HW HB HS.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [lia|]. split; [intros; reflexivity|]. split; [intros; assumption|].
  split; [intros p H; split; [exact H | reflexivity]|]. split; [intros; assumption|].
  split; [exists (m_vmmaps md); apply rk_vm_self|]. split; [intros; split; [reflexivity | tauto]|].
  split; [intros; reflexivity|]. exact HS.
Qed.

Lemma rk_chain_mono : forall K E F E' F' L A regs mem md L' A' mem' md',
  rk_chain K E F L A regs mem md L' A' mem' md' -> (forall a, E a -> E' a) -> (forall q, F q -> F' q) ->
  rk_chain K E' F' L A regs mem md L' A' mem' md'.
Proof using.
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

Lemma rk_chain_in : forall K E F L A regs mem md L1 A1 m1 md1 p n,
  WF A -> rk_chain K E F L A regs mem md L1 A1 m1 md1 -> In (p, n) (user_blocks A) -> ~ F (ptr_addr L p) ->
  In (p, n) (user_blocks A1) /\ ptr_addr L1 p = ptr_addr L p.
Proof using.
  intros K E F L A regs mem md L1 A1 m1 md1 p n HW
    (M & W & B & LE & RG & AD & SV & Z0 & IO & VM & FR & BY & SW) H0 HF.
  pose proof (rk_ub_nonneg A p n HW H0) as Hn.
  destruct (Z.eq_dec n 0) as [->|Hn'].
  - exact (Z0 p H0).
  - assert (H1 : In (p, n) (user_blocks A1)) by (apply SV; [exact H0 | lia | exact HF]).
    split; [exact H1 | exact (AD p n H0 H1 HF)].
Qed.

Lemma rk_chain_callee : forall K E F L A regs mem md L1 A1 m1 md1 K' E' F' R1 L2 A2 R2 m2 md2,
  WF A ->
  rk_chain K E F L A regs mem md L1 A1 m1 md1 ->
  relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  (forall a, scratch_k Bm K' R1 a -> scratch_k Bm K regs a) ->
  (forall a, scratch_k Bm K regs a -> ~ scratch_k Bm K' R1 a -> alloc_ceiling <= a < 2 ^ 64) ->
  (forall a, E' a -> a < alloc_ceiling /\ (in_img Bm a -> E a)) ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> 0 < n -> ~ F (ptr_addr L p) ->
     ~ F' (ptr_addr L p) /\ (forall i, 0 <= i < n -> ~ E (ptr_addr L p + i) -> ~ E' (ptr_addr L p + i))) ->
  rk_chain K E F L A regs mem md L2 A2 m2 md2.
Proof using.
  intros K E F L A regs mem md L1 A1 m1 md1 K' E' F' R1 L2 A2 R2 m2 md2 HW CH RP SC SC2 EH FB.
  pose proof (fun p n => rk_chain_in K E F L A regs mem md L1 A1 m1 md1 p n HW CH) as IN1.
  destruct CH as (M1 & W1 & B1 & LE1 & RG1 & AD1 & SV1 & Z1 & IO1 & VM1 & FR1 & BY1 & SW1).
  destruct RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|].
  split.
  { destruct LE1 as (c1 & s1 & b1 & r1). destruct LE2 as (c2 & s2 & b2 & r2).
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros r Hr. rewrite r2 by lia. apply r1. exact Hr. }
  split; [lia|].
  split.
  { intros p n H0 H2 HF. destruct (IN1 p n H0 HF) as [H1 E1]. rewrite <- E1.
    pose proof (rk_ub_nonneg A p n HW H0) as Hn.
    destruct (Z.eq_dec n 0) as [->|Hn'].
    - exact (proj2 (Z2 p H1)).
    - apply (AD2 p n H1 H2). rewrite E1. exact (proj1 (FB p n H0 H1 ltac:(lia) HF)). }
  split.
  { intros p n H0 Hn HF. destruct (IN1 p n H0 HF) as [H1 E1].
    apply (SV2 p n H1 Hn). rewrite E1. exact (proj1 (FB p n H0 H1 Hn HF)). }
  split.
  { intros p H0. destruct (Z1 p H0) as [H1 E1]. destruct (Z2 p H1) as [H2 E2]. split; [exact H2 | congruence]. }
  split.
  { intros a Ha Ho. apply IO1; [exact Ha|]. apply IO2; assumption. }
  split.
  { destruct VM1 as [v1 ->]. destruct VM2 as [v2 ->]. exists v2. apply rk_vm_twice. }
  split.
  { intros a Ha NO0 NO2 NS NE.
    assert (NO1 : ~ owned Bm L1 A1 a).
    { intros Ho. destruct Ha as [Ha|Ha].
      - destruct (rk_owned_low L1 A1 m1 md1 a M1 Ho). lia.
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
  destruct (rk_scratch_dec K' R1 a) as [X|X].
  - exact (SW2 a X).
  - pose proof (SW1 a Ha) as W.
    pose proof (SC2 a Ha X) as Hr.
    assert (NO1 : ~ owned Bm L1 A1 a) by (intros Ho; destruct (rk_owned_low L1 A1 m1 md1 a M1 Ho); lia).
    assert (NO2 : ~ owned Bm L2 A2 a) by (intros Ho; destruct (rk_owned_low L2 A2 m2 md2 a M2 Ho); lia).
    assert (NE' : ~ E' a) by (intros Y; destruct (EH a Y); lia).
    exact (proj1 (proj2 (FR2 a (or_introl Hr) NO1 NO2 X NE')) W).
Qed.

Lemma rk_nodup_fst : forall {X Y} (l : list (X * Y)) p a b, List.NoDup (map fst l) -> In (p, a) l -> In (p, b) l -> a = b.
Proof using.
  intros X Y l. induction l as [|[x y] l IH]; intros p a b ND Ha Hb; [destruct Ha|].
  cbn in ND. apply List.NoDup_cons_iff in ND as [Hn ND'].
  destruct Ha as [Ea|Ha]; destruct Hb as [Eb|Hb].
  - congruence.
  - injection Ea as Ex _. subst x. exfalso. apply Hn. apply in_map_iff. exists (p, b). auto.
  - injection Eb as Ex _. subst x. exfalso. apply Hn. apply in_map_iff. exists (p, a). auto.
  - exact (IH p a b ND' Ha Hb).
Qed.

Lemma rk_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof using.
  induction W as [|p W IH]; intros x; [left; exact I|]. destruct p as [lo hi]. cbn [outside].
  destruct (IH x) as [H|H]; [destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|]|].
  - right. intros [X _]. lia.
  - left. split; [lia | exact H].
  - left. split; [lia | exact H].
  - right. intros [_ X]. exact (H X).
Qed.

Lemma rk_chain_free : forall K E F L A regs mem md L1 A1 m1 md1 R1 L2 A2 R2 m2 md2 p n,
  WF A -> rk_chain K E F L A regs mem md L1 A1 m1 md1 ->
  call_post Bm MR L1 A1 R1 m1 md1 (fun a => ptr_addr L1 p <= a < ptr_addr L1 p + n) L2 A2 R2 m2 md2 ->
  (forall q k, In (q, k) (user_blocks A1) -> q <> p -> In (q, k) (user_blocks A2)) ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  In (p, n) (user_blocks A1) -> 0 < n ->
  (forall a, scratch Bm R1 a -> scratch_k Bm K regs a) ->
  (forall a, scratch_k Bm K regs a -> ~ scratch Bm R1 a -> alloc_ceiling <= a < 2 ^ 64) ->
  (forall p0 n0, In (p0, n0) (user_blocks A) -> In (p0, n0) (user_blocks A1) -> 0 < n0 -> ~ F (ptr_addr L p0) -> p0 <> p) ->
  rk_chain K E F L A regs mem md L2 A2 m2 md2.
Proof using AX CTX.
  intros K E F L A regs mem md L1 A1 m1 md1 R1 L2 A2 R2 m2 md2 p n HW CH CP KEEP RGN HIN HN SC SC2 NP.
  pose proof (fun p0 n0 => rk_chain_in K E F L A regs mem md L1 A1 m1 md1 p0 n0 HW CH) as IN1.
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
    exact (NP p0 n0 H0 H1 Hn HF). }
  split.
  { intros p0 H0. destruct (Z1 p0 H0) as [H1 E1].
    assert (Hne : p0 <> p).
    { intros ->. pose proof (rk_nodup_fst _ p 0 n (YO10.user_block_ptrs_NoDup A1 W1) H1 HIN). lia. }
    pose proof (KEEP p0 0 H1 Hne) as H2. split; [exact H2|]. rewrite (AD2 p0 0 H1 H2). exact E1. }
  split.
  { intros a Ha Ho. apply IO1; [exact Ha|]. exact (rk_img_owned L1 A1 m1 md1 L2 A2 m2 md2 a M1 M2 Ha Ho). }
  split.
  { destruct VM1 as [v1 ->]. destruct VM2 as [v2 ->]. exists v2. apply rk_vm_twice. }
  split.
  { intros a Ha NO0 NO2 NS NE.
    assert (NO1 : ~ owned Bm L1 A1 a).
    { intros Ho. destruct Ha as [Ha|Ha].
      - destruct (rk_owned_low L1 A1 m1 md1 a M1 Ho). lia.
      - exact (NO0 (IO1 a Ha Ho)). }
    destruct (FR1 a Ha NO0 NO1 NS NE) as [E01 W01].
    assert (NS' : ~ scratch Bm R1 a) by (intros X; exact (NS (SC a X))).
    assert (NE' : ~ (ptr_addr L1 p <= a < ptr_addr L1 p + n)).
    { intros X. pose proof (mr_blocks Bm MR rk_laws L1 A1 m1 md1 p n (a - ptr_addr L1 p) M1 HIN ltac:(lia)) as (_ & _ & Hc & _).
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
  destruct (rk_scratch_dec ALLOC_STACK R1 a) as [X|X].
  - exact (SW2 a X).
  - pose proof (SW1 a Ha) as W.
    pose proof (SC2 a Ha X) as Hr.
    assert (NO1 : ~ owned Bm L1 A1 a) by (intros Ho; destruct (rk_owned_low L1 A1 m1 md1 a M1 Ho); lia).
    assert (NO2 : ~ owned Bm L2 A2 a) by (intros Ho; destruct (rk_owned_low L2 A2 m2 md2 a M2 Ho); lia).
    assert (NE' : ~ (ptr_addr L1 p <= a < ptr_addr L1 p + n)).
    { intros Y. pose proof (mr_blocks Bm MR rk_laws L1 A1 m1 md1 p n (a - ptr_addr L1 p) M1 HIN ltac:(lia)) as (_ & _ & Hc & _).
      lia. }
    exact (proj1 (proj2 (FR2 a (or_introl Hr) NO1 NO2 X NE')) W).
Qed.

Lemma rk_chain_munch : forall K E F L A regs mem md L1 A1 m1 md1 W m2,
  rk_chain K E F L A regs mem md L1 A1 m1 md1 -> munch W m1 m2 -> wmono segs m1 m2 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x ->
     (scratch_k Bm K regs x /\ alloc_ceiling <= x) \/
     (E x /\ (img_plain Bm x \/ exists q k, In (q, k) (blocks L1 A1) /\ q <= x < q + k))) ->
  rk_chain K E F L A regs mem md L1 A1 m2 md1.
Proof using AX SEGS.
  intros K E F L A regs mem md L1 A1 m1 md1 W m2 CH MU WM HW.
  destruct CH as (M1 & W1 & B1 & LE1 & RG1 & AD1 & SV1 & Z1 & IO1 & VM1 & FR1 & BY1 & SW1).
  destruct (mr_model Bm MR rk_laws L1 A1 m1 md1 M1) as (Hh & Hl & Hm).
  assert (OWN : forall a, owned Bm L1 A1 a -> outside W a).
  { intros a Ho. pose proof (rk_owned_low L1 A1 m1 md1 a M1 Ho) as Hr.
    destruct (rk_outside_dec W a) as [O|O]; [exact O|].
    exfalso. destruct (HW a ltac:(pose proof alloc_ceiling_lt; lia) O) as [[_ X]|[_ [X|(q & k & Hq & Hx)]]]; [lia| |].
    - exact (rk_plain_unowned L1 A1 m1 md1 a M1 X Ho).
    - pose proof (rk_blk L1 A1 m1 md1 q k (a - q) M1 Hq ltac:(lia)) as (_ & _ & _ & Hn).
      replace (q + (a - q)) with a in Hn by ring. exact (Hn Ho). }
  assert (M2 : MR L1 A1 m2 md1).
  { eapply (mr_frame Bm MR rk_laws L1 A1 m1 m2 md1 md1 M1).
    - intros a Ho. pose proof (rk_owned_low L1 A1 m1 md1 a M1 Ho).
      eapply munch_mbyte; [exact MU | pose proof alloc_ceiling_lt; lia | exact (OWN a Ho)].
    - intros a Ho Hp. pose proof (rk_owned_low L1 A1 m1 md1 a M1 Ho).
      eapply munch_present; [exact MU | pose proof alloc_ceiling_lt; lia | exact (OWN a Ho) | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks Bm MR rk_laws L1 A1 m1 md1 p n i M1 Hin Hi) as (Hp & H4 & Hc & _).
      pose proof alloc_ceiling_lt.
      apply (present_of_writable_out Bm SEGS m2 (ptr_addr L1 p + i) ltac:(lia)).
      + exact (ax_blocks_img AX L1 A1 m1 md1 p n i M1 Hin Hi).
      + rewrite <- SEGS. apply WM. exact (rk_present_writable segs m1 _ Hp).
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
    { destruct (rk_outside_dec W a) as [O|O]; [exact O|].
      exfalso. destruct (HW a AR O) as [[X _]|[X _]]; [exact (NS X) | exact (NE X)]. }
    destruct (FR1 a Ha NO0 NO1 NS NE) as [E01 W01].
    split; [rewrite (munch_mbyte segs W m1 m2 a MU AR O); exact E01|].
    rewrite W01. exact (munch_writable segs W m1 m2 a MU AR O). }
  split.
  { intros p n i H0 H1 HF Hi HE.
    destruct (mr_blocks Bm MR rk_laws L1 A1 m1 md1 p n i M1 H1 Hi) as (_ & H4 & Hc & _).
    pose proof alloc_ceiling_lt.
    rewrite (AD1 p n H0 H1 HF) in H4, Hc.
    assert (O : outside W (ptr_addr L p + i)).
    { destruct (rk_outside_dec W (ptr_addr L p + i)) as [O|O]; [exact O|].
      exfalso. destruct (HW (ptr_addr L p + i) ltac:(lia) O) as [[_ X]|[X _]]; [lia | exact (HE X)]. }
    rewrite (munch_mbyte segs W m1 m2 (ptr_addr L p + i) MU ltac:(lia) O). exact (BY1 p n i H0 H1 HF Hi HE). }
  intros a Ha. apply WM. exact (SW1 a Ha).
Qed.

Definition rk_kb2 (m m' : word -> option byte) (a : Z) : Prop :=
  mbyte segs m' a = mbyte segs m a /\ (writable_at segs m a -> writable_at segs m' a).

Definition rk_bkept (L : layout) (A : astate) (m : word -> option byte) (L' : layout) (A' : astate)
    (m' : word -> option byte) (q : Z) : Prop :=
  forall k, In (q, k) (blocks L A) -> In (q, k) (blocks L' A') /\ forall i, 0 <= i < k -> rk_kb2 m m' (q + i).

Lemma rk_rw_kb2 : forall m m' a cs, rw_cells segs m a cs -> (forall i, 0 <= i < Z.of_nat (cells_size cs) -> rk_kb2 m m' (a + i)) ->
  rw_cells segs m' a cs.
Proof using. intros m m' a cs H K. apply (rw_cells_transfer segs m); [exact H|]. exact K. Qed.

Lemma rk_bytes_kb2 : forall m m' a bs, bytes_at segs m a bs -> (forall i, 0 <= i < Z.of_nat (length bs) -> rk_kb2 m m' (a + i)) ->
  bytes_at segs m' a bs.
Proof using. intros m m' a bs H K. apply (bytes_at_transfer segs m); [exact H|]. intros i Hi. exact (proj1 (K i Hi)). Qed.

Lemma rk_rw_in_block : forall L A m L' A' m' q k a cs, rw_cells segs m a cs -> rk_bkept L A m L' A' m' q ->
  In (q, k) (blocks L A) -> q <= a -> a + Z.of_nat (cells_size cs) <= q + k -> rw_cells segs m' a cs.
Proof using.
  intros L A m L' A' m' q k a cs H BK Hin H1 H2. apply (rk_rw_kb2 m); [exact H|].
  intros i Hi. destruct (BK k Hin) as [_ X]. replace (a + i) with (q + (a + i - q)) by ring. apply X. lia.
Qed.

Lemma rk_bytes_in_block : forall L A m L' A' m' q k a bs, bytes_at segs m a bs -> rk_bkept L A m L' A' m' q ->
  In (q, k) (blocks L A) -> q <= a -> a + Z.of_nat (length bs) <= q + k -> bytes_at segs m' a bs.
Proof using.
  intros L A m L' A' m' q k a bs H BK Hin H1 H2. apply (rk_bytes_kb2 m); [exact H|].
  intros i Hi. destruct (BK k Hin) as [_ X]. replace (a + i) with (q + (a + i - q)) by ring. apply X. lia.
Qed.

Lemma rk_rp_bkept : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q,
  MR L1 A1 m1 md1 ->
  relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 -> ~ F' q ->
  (forall k i, In (q, k) (blocks L1 A1) -> 0 <= i < k -> ~ E' (q + i)) ->
  rk_bkept L1 A1 m1 L2 A2 m2 q.
Proof using.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q M1 RP HF HE k Hin.
  destruct RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  apply rk_blocks_in in Hin as (p & Ep & Hp).
  pose proof (rk_ub_nonneg A1 p k (mr_wf Bm MR rk_laws L1 A1 m1 md1 M1) Hp) as Hk.
  subst q.
  destruct (Z.eq_dec k 0) as [->|Hk'].
  - destruct (Z2 p Hp) as [H2 E2]. split; [apply rk_blocks_in; exists p; split; [exact E2 | exact H2]|].
    intros i Hi. lia.
  - assert (H2 : In (p, k) (user_blocks A2)) by (apply SV2; [exact Hp | lia | exact HF]).
    pose proof (AD2 p k Hp H2 HF) as E2.
    split; [apply rk_blocks_in; exists p; split; [exact E2 | exact H2]|].
    intros i Hi. split.
    + apply (BY2 p k i Hp H2 HF Hi). apply HE with k; [apply rk_blocks_in; exists p; auto | exact Hi].
    + intros _. rewrite <- E2. apply rk_present_writable.
      exact (proj1 (mr_blocks Bm MR rk_laws L2 A2 m2 md2 p k i M2 H2 Hi)).
Qed.

Lemma rk_rp_gkept : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 a,
  MR L1 A1 m1 md1 ->
  relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  (img_plain Bm a \/ alloc_ceiling <= a < 2 ^ 64) -> ~ E' a -> ~ scratch_k Bm K' R1 a ->
  rk_kb2 m1 m2 a.
Proof using AX.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 a M1 RP Ha NE NS.
  destruct RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  assert (NO1 : ~ owned Bm L1 A1 a).
  { destruct Ha as [Ha|Ha]; [exact (rk_plain_unowned L1 A1 m1 md1 a M1 Ha)|].
    intros Ho. destruct (rk_owned_low L1 A1 m1 md1 a M1 Ho). lia. }
  assert (NO2 : ~ owned Bm L2 A2 a).
  { destruct Ha as [Ha|Ha]; [exact (rk_plain_unowned L2 A2 m2 md2 a M2 Ha)|].
    intros Ho. destruct (rk_owned_low L2 A2 m2 md2 a M2 Ho). lia. }
  assert (Ha' : alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) by (destruct Ha as [Ha|Ha]; [right; exact (proj1 Ha) | left; exact Ha]).
  destruct (FR2 a Ha' NO1 NO2 NS NE) as [E W]. split; [exact E | tauto].
Qed.

Lemma rk_cp_bkept : forall L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p n q,
  MR L1 A1 m1 md1 ->
  call_post Bm MR L1 A1 R1 m1 md1 (fun a => ptr_addr L1 p <= a < ptr_addr L1 p + n) L2 A2 R2 m2 md2 ->
  (forall q k, In (q, k) (user_blocks A1) -> q <> p -> In (q, k) (user_blocks A2)) ->
  q <> ptr_addr L1 p ->
  rk_bkept L1 A1 m1 L2 A2 m2 q.
Proof using.
  intros L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p n q M1 CP KEEP Hq k Hin.
  destruct CP as (M2 & W2 & B2 & LE2 & AD2 & RPr & VM2 & FR2 & BY2 & SW2).
  apply rk_blocks_in in Hin as (p0 & Ep & Hp). subst q.
  assert (Hne : p0 <> p) by (intros ->; exact (Hq eq_refl)).
  pose proof (KEEP p0 k Hp Hne) as H2. pose proof (AD2 p0 k Hp H2) as E2.
  split; [apply rk_blocks_in; exists p0; split; [exact E2 | exact H2]|].
  intros i Hi. split; [exact (BY2 p0 k i Hp H2 Hi)|].
  intros _. rewrite <- E2. apply rk_present_writable.
  exact (proj1 (mr_blocks Bm MR rk_laws L2 A2 m2 md2 p0 k i M2 H2 Hi)).
Qed.

Lemma rk_cp_gkept : forall L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p n a,
  MR L1 A1 m1 md1 -> In (p, n) (user_blocks A1) ->
  call_post Bm MR L1 A1 R1 m1 md1 (fun a => ptr_addr L1 p <= a < ptr_addr L1 p + n) L2 A2 R2 m2 md2 ->
  (img_plain Bm a \/ alloc_ceiling <= a < 2 ^ 64) -> ~ scratch Bm R1 a ->
  rk_kb2 m1 m2 a.
Proof using AX.
  intros L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p n a M1 HIN CP Ha NS.
  destruct CP as (M2 & W2 & B2 & LE2 & AD2 & RPr & VM2 & FR2 & BY2 & SW2).
  assert (NO1 : ~ owned Bm L1 A1 a).
  { destruct Ha as [Ha|Ha]; [exact (rk_plain_unowned L1 A1 m1 md1 a M1 Ha)|].
    intros Ho. destruct (rk_owned_low L1 A1 m1 md1 a M1 Ho). lia. }
  assert (NO2 : ~ owned Bm L2 A2 a).
  { destruct Ha as [Ha|Ha]; [exact (rk_plain_unowned L2 A2 m2 md2 a M2 Ha)|].
    intros Ho. destruct (rk_owned_low L2 A2 m2 md2 a M2 Ho). lia. }
  assert (NE : ~ (ptr_addr L1 p <= a < ptr_addr L1 p + n)).
  { intros X. pose proof (mr_blocks Bm MR rk_laws L1 A1 m1 md1 p n (a - ptr_addr L1 p) M1 HIN ltac:(lia)) as (_ & _ & Hc & _).
    destruct Ha as [Ha|Ha]; [|lia].
    apply (ax_blocks_img AX L1 A1 m1 md1 p n (a - ptr_addr L1 p) M1 HIN ltac:(lia)).
    replace (ptr_addr L1 p + (a - ptr_addr L1 p)) with a by ring. exact (proj1 Ha). }
  assert (Ha' : alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) by (destruct Ha as [Ha|Ha]; [right; exact (proj1 Ha) | left; exact Ha]).
  destruct (FR2 a Ha' NO1 NO2 NS NE) as [E W]. split; [exact E | tauto].
Qed.

Lemma rk_mu_kb2 : forall W m1 m2 a, munch W m1 m2 -> wmono segs m1 m2 -> 0 <= a < 2 ^ 64 -> outside W a -> rk_kb2 m1 m2 a.
Proof using.
  intros W m1 m2 a MU WM Ha O. split; [exact (munch_mbyte segs W m1 m2 a MU Ha O)|].
  intros X. apply WM. exact X.
Qed.

Lemma rk_mu_bkept : forall L A W m1 m2 md q, MR L A m1 md -> munch W m1 m2 -> wmono segs m1 m2 ->
  (forall k i, In (q, k) (blocks L A) -> 0 <= i < k -> outside W (q + i)) -> rk_bkept L A m1 L A m2 q.
Proof using.
  intros L A W m1 m2 md q M1 MU WM HO k Hin. split; [exact Hin|].
  intros i Hi. destruct (rk_blk L A m1 md q k i M1 Hin Hi) as (_ & H4 & Hc & _). pose proof alloc_ceiling_lt.
  apply (rk_mu_kb2 W); [exact MU | exact WM | lia | exact (HO k i Hin Hi)].
Qed.

Definition rk_with_keys (e : rentry) (ks : list (Z * list byte * list byte)) : rentry :=
  RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e) (re_hp e) (re_kh e) (re_pad2 e)
     ks (re_U e) (re_junk e).

Lemma rk_with_keys_self : forall e, rk_with_keys e (re_keys e) = e.
Proof using. intros []. reflexivity. Qed.

Lemma rk_map_fst_ext : forall {B} (g : Z * list byte -> B) (ks ks' : list (Z * list byte * list byte)),
  map fst ks' = map fst ks -> map (fun k => g (fst k)) ks' = map (fun k => g (fst k)) ks.
Proof using. intros B g ks ks' H. rewrite <- (map_map fst g ks'), <- (map_map fst g ks), H. reflexivity. Qed.

Lemma rk_map_fst_keys : forall (ks ks' : list (Z * list byte * list byte)), map fst ks' = map fst ks ->
  map key_addr ks' = map key_addr ks /\ map key_text ks' = map key_text ks /\ length ks' = length ks /\
  key_ptrs ks' = key_ptrs ks /\ keys_texts ks' = keys_texts ks.
Proof using.
  intros ks ks' H.
  assert (A1 : map key_addr ks' = map key_addr ks) by exact (rk_map_fst_ext fst ks ks' H).
  assert (A2 : map key_text ks' = map key_text ks) by exact (rk_map_fst_ext snd ks ks' H).
  assert (A3 : length ks' = length ks) by (rewrite <- (length_map fst ks'), <- (length_map fst ks), H; reflexivity).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split.
  - unfold key_ptrs. f_equal. exact (rk_map_fst_ext (fun x => le8 (Z_to_bv 64 (fst x))) ks ks' H).
  - unfold keys_texts. exact (rk_map_fst_ext (fun x => bzs (snd x)) ks ks' H).
Qed.

Lemma rk_map_fst_in : forall (ks ks' : list (Z * list byte * list byte)) k', map fst ks' = map fst ks -> In k' ks' ->
  exists k, In k ks /\ fst k = fst k'.
Proof using.
  intros ks ks' k' H Hin. assert (X : In (fst k') (map fst ks)) by (rewrite <- H; apply in_map; exact Hin).
  apply in_map_iff in X as (k & E & Hk). exists k. auto.
Qed.

Lemma rk_entry_bytes_wk : forall e ks, length ks = length (re_keys e) -> entry_bytes (rk_with_keys e ks) = entry_bytes e.
Proof using. intros e ks H. unfold entry_bytes, re_nheld. cbn [rk_with_keys re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_keys re_pad2]. rewrite H. reflexivity. Qed.

Lemma rk_entry_blocks_wk : forall e ks, map key_addr ks = map key_addr (re_keys e) -> entry_blocks (rk_with_keys e ks) = entry_blocks e.
Proof using. intros e ks H. unfold entry_blocks. cbn [rk_with_keys re_cap re_buf re_hp re_keys]. rewrite H. reflexivity. Qed.

Lemma rk_length_key_ptrs : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof using. induction ks as [|k ks IH]; [reflexivity|]. unfold key_ptrs in *. cbn [map concat length]. rewrite length_app, length_le8, IH. lia. Qed.

Definition rk_entry_okk (L : layout) (A : astate) (m : word -> option byte) (e : rentry) : Prop :=
  exists ks, map fst ks = map fst (re_keys e) /\ entry_ok Bm L A m (rk_with_keys e ks).

Lemma rk_entry_okk_of : forall L A m e, entry_ok Bm L A m e -> rk_entry_okk L A m e.
Proof using. intros L A m e H. exists (re_keys e). split; [reflexivity|]. rewrite rk_with_keys_self. exact H. Qed.

Lemma rk_slack_at : forall L A m md q n, MR L A m md -> In (q, n) (blocks L A) ->
  exists sl, bytes_at segs m (q + n) sl /\ Z.of_nat (length sl) = (- (q + n)) mod 8.
Proof using BSP.
  intros L A m md q n HM Hin.
  pose proof Hin as Hin'. apply rk_blocks_in in Hin' as (p & Ep & Hp).
  pose proof (rk_ub_nonneg A p n (mr_wf Bm MR rk_laws L A m md HM) Hp) as Hn.
  pose proof (mr_blocks_range Bm MR rk_laws L A m md p n HM Hp) as (H4 & Hc). rewrite Ep in H4, Hc.
  pose proof alloc_ceiling_lt as HL.
  pose proof (Z.mod_pos_bound (- (q + n)) 8 ltac:(lia)) as Hr.
  destruct (present_rw_cells segs m (q + n) (Z.to_nat ((- (q + n)) mod 8))) as [junk H]; [lia | rewrite Z2Nat.id by lia; lia | |].
  { intros i Hi. rewrite Z2Nat.id in Hi by lia. apply (BSP L A m md q n (q + n + i) HM Hin).
    Z.div_mod_to_equations. lia. }
  exists junk. destruct H as [[Hwf Hb] _]. cbn in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. split; [exact Hb|]. rewrite Hl. lia.
Qed.

Lemma rk_reslack : forall L A m md (ks : list (Z * list byte * list byte)), MR L A m md ->
  Forall (fun k => In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L A)) ks ->
  exists ks', map fst ks' = map fst ks /\
    Forall (fun k => bytes_at segs m (key_addr k + (Z.of_nat (length (key_text k)) + 1)) (key_slack k) /\
       (- (key_addr k + Z.of_nat (length (key_text k)) + 1)) mod 8 <= Z.of_nat (length (key_slack k))) ks'.
Proof using BSP.
  intros L A m md ks HM. induction ks as [|k ks IH]; intros HF.
  - exists []. split; [reflexivity | constructor].
  - pose proof (Forall_inv HF) as Hk. pose proof (Forall_inv_tail HF) as HF'.
    destruct (IH HF') as (ks' & E & F').
    destruct (rk_slack_at L A m md _ _ HM Hk) as (sl & Hb & Hl).
    exists ((fst k, sl) :: ks'). split; [cbn [map]; rewrite E; reflexivity|].
    constructor; [|exact F']. unfold key_addr, key_text, key_slack in *. cbn [fst snd]. split; [exact Hb|].
    rewrite Hl. replace (- (fst (fst k) + Z.of_nat (length (snd (fst k))) + 1))
      with (- (fst (fst k) + (Z.of_nat (length (snd (fst k))) + 1))) by ring. lia.
Qed.

Lemma rk_entry_okk_kept : forall L A m L' A' m' md' e,
  rk_entry_okk L A m e -> MR L' A' m' md' ->
  (forall q, In q (entry_blocks e) -> rk_bkept L A m L' A' m' q) ->
  rk_entry_okk L' A' m' e.
Proof using BSP.
  intros L A m L' A' m' md' e (ks & Eks & OK) M' BK.
  destruct (rk_map_fst_keys (re_keys e) ks Eks) as (EA & ET & EL & EP & EX).
  rewrite <- (rk_entry_blocks_wk e ks EA) in BK.
  unfold entry_ok in OK.
  destruct OK as (Heof & Hskip & Hp1 & Hp2 & Hfd & Hcap & HU & Hused & HUz & Hbuf & Hnh & Hhp & NDa & NDt & Hkeys).
  cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_junk re_hp re_kh re_keys rk_with_keys] in *.
  unfold re_nheld in Hnh, Hhp. cbn [re_keys rk_with_keys] in Hnh, Hhp.
  assert (KB : Forall (fun k => In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L' A')) ks).
  { apply Forall_forall. intros k Hk. pose proof (proj1 (Forall_forall _ _) Hkeys k Hk) as (H1 & _).
    refine (proj1 (BK (key_addr k) _ _ H1)).
    unfold entry_blocks. cbn [rk_with_keys re_cap re_buf re_hp re_keys].
    apply in_or_app; right; apply in_or_app; right; apply in_map; exact Hk. }
  destruct (rk_reslack L' A' m' md' ks M' KB) as (ks' & E' & F').
  destruct (rk_map_fst_keys ks ks' E') as (EA' & ET' & EL' & EP' & EX').
  exists ks'. split; [rewrite E'; exact Eks|].
  unfold entry_ok, re_nheld. cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_junk re_hp re_kh re_keys rk_with_keys].
  rewrite EL', EP', EA', ET'.
  do 9 (split; [assumption|]).
  split.
  { destruct Hbuf as [Hb|(H0 & Hin & Hf & Hj & Hrw)]; [left; exact Hb|right].
    assert (Hq : In (re_buf e) (entry_blocks (rk_with_keys e ks))).
    { unfold entry_blocks. cbn [rk_with_keys re_cap re_buf re_hp re_keys].
      destruct (re_cap e =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|]. left. reflexivity. }
    pose proof (BK _ Hq) as Hb. destruct (Hb _ Hin) as [Hin' _].
    split; [exact H0|]. split; [exact Hin'|]. split; [exact Hf|]. split; [exact Hj|].
    eapply rk_rw_in_block; [exact Hrw | exact Hb | exact Hin | lia | cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia]. }
  split; [exact Hnh|].
  split.
  { destruct Hhp as [Hh|(Hin & Hf & H8 & H8' & Hb0)]; [left; destruct Hh as [Hh0 Hh1]; split; [exact Hh0|]; subst ks; destruct ks'; [reflexivity | discriminate]|right].
    assert (Hq : In (re_hp e) (entry_blocks (rk_with_keys e ks))).
    { unfold entry_blocks. cbn [rk_with_keys re_cap re_buf re_hp re_keys].
      destruct Hf as (Hf0 & _). destruct (re_hp e =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|].
      apply in_or_app; right; left; reflexivity. }
    pose proof (BK _ Hq) as Hb. destruct (Hb _ Hin) as [Hin' _].
    split; [exact Hin'|]. split; [exact Hf|]. split; [exact H8|]. split; [exact H8'|].
    eapply rk_bytes_in_block; [exact Hb0 | exact Hb | exact Hin | lia | rewrite rk_length_key_ptrs; lia]. }
  split; [exact NDa|]. split; [exact NDt|].
  apply Forall_forall. intros k' Hk'.
  destruct (rk_map_fst_in ks ks' k' E' Hk') as (k & Hk & Ek).
  pose proof (proj1 (Forall_forall _ _) Hkeys k Hk) as (H1 & H2 & H3 & H4 & H5 & H6).
  pose proof (proj1 (Forall_forall _ _) F' k' Hk') as (S1 & S2).
  assert (EK1 : key_addr k' = key_addr k) by (unfold key_addr; rewrite Ek; reflexivity).
  assert (EK2 : key_text k' = key_text k) by (unfold key_text; rewrite Ek; reflexivity).
  rewrite EK1, EK2 in *.
  assert (Hq : In (key_addr k) (entry_blocks (rk_with_keys e ks))).
  { unfold entry_blocks. cbn [rk_with_keys re_cap re_buf re_hp re_keys].
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
      eapply rk_bytes_in_block; [exact H3 | exact Hb | exact H1 | lia | rewrite length_app; cbn [length]; lia].
    - rewrite length_app. cbn [length]. replace (key_addr k + Z.of_nat (length (key_text k) + 1))
        with (key_addr k + (Z.of_nat (length (key_text k)) + 1)) by lia. exact S1. }
  split; [exact H4|]. split; [exact H5|]. exact S2.
Qed.

Lemma rk_list_at_kept : forall L A m L' A' m' LA l b,
  list_at Bm L A m LA l b -> (forall i, 0 <= i < 16 -> rk_kb2 m m' (LA + i)) ->
  (forall q, In q (list_blocks l) -> rk_bkept L A m L' A' m' q) ->
  list_at Bm L' A' m' LA l b.
Proof using.
  intros L A m L' A' m' LA l b (Hc & Hn & Hv & ND1 & ND2 & Hr) KG BK.
  split; [apply (rk_rw_kb2 m); [exact Hc | intros i Hi; cbn in Hi; apply KG; lia]|].
  split; [exact Hn|].
  split.
  { destruct Hv as [Hv|(H0 & Hin & Hf & Hj & Hrw)]; [left; exact Hv|right].
    assert (Hq : In (hl_v l) (list_blocks l)).
    { unfold list_blocks. destruct (hl_cap l =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|]. left. reflexivity. }
    pose proof (BK _ Hq) as Hb. destruct (Hb _ Hin) as [Hin' _].
    split; [exact H0|]. split; [exact Hin'|]. split; [exact Hf|]. split; [exact Hj|].
    eapply rk_rw_in_block; [exact Hrw | exact Hb | exact Hin | lia | cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia]. }
  split; [exact ND1|]. split; [exact ND2|].
  apply Forall_forall. intros r Hr0. pose proof (proj1 (Forall_forall _ _) Hr r Hr0) as (H1 & H2 & H3 & H4 & H5).
  assert (Hq : In (fst r) (list_blocks l)) by (unfold list_blocks; apply in_or_app; right; apply in_map; exact Hr0).
  pose proof (BK _ Hq) as Hb. destruct (Hb _ H1) as [H1' _].
  split; [exact H1'|]. split; [exact H2|].
  split; [eapply rk_rw_in_block; [exact H3 | exact Hb | exact H1 | lia | cbn [cells_size csize]; lia]|].
  split; assumption.
Qed.

Lemma rk_src_at_kept : forall L A m L' A' m' HA h,
  src_at Bm L A m HA h -> (forall i, 0 <= i < 96 -> rk_kb2 m m' (HA + i)) ->
  (forall q, In q (hs_blocks h) -> rk_bkept L A m L' A' m' q) ->
  src_at Bm L' A' m' HA h.
Proof using.
  intros L A m L' A' m' HA h
    (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18) KG BK.
  assert (BKp : forall q, In q (list_blocks (hs_pending h)) -> rk_bkept L A m L' A' m' q)
    by (intros q Hq; apply BK; unfold hs_blocks; apply in_or_app; left; exact Hq).
  assert (BKe : forall q, In q (list_blocks (hs_expected h)) -> rk_bkept L A m L' A' m' q)
    by (intros q Hq; apply BK; unfold hs_blocks; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hq).
  assert (BKh : forall q, In q (list_blocks (hs_held h)) -> rk_bkept L A m L' A' m' q)
    by (intros q Hq; apply BK; unfold hs_blocks; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hq).
  assert (BKq : rk_bkept L A m L' A' m' (hs_partial h))
    by (apply BK; unfold hs_blocks; apply in_or_app; right; left; reflexivity).
  split; [apply (rk_rw_kb2 m); [exact S1 | intros i Hi; cbn in Hi; apply KG; lia]|].
  split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|].
  split; [apply (rk_list_at_kept L A m); [exact S6 | intros i Hi; replace (HA + 16 + i) with (HA + (16 + i)) by ring; apply KG; lia | exact BKp]|].
  split; [apply (rk_rw_kb2 m); [exact S7 | intros i Hi; cbn in Hi; replace (HA + 32 + i) with (HA + (32 + i)) by ring; apply KG; lia]|].
  split; [exact S8|]. split; [exact S9|]. split; [exact S10|].
  split; [exact (proj1 (BKq _ S11))|]. split; [exact S12|]. split; [exact S13|].
  split; [eapply rk_rw_in_block; [exact S14 | exact BKq | exact S11 | lia | cbn [cells_size csize]; lia]|].
  split; [exact S15|].
  split; [apply (rk_list_at_kept L A m); [exact S16 | intros i Hi; replace (HA + 64 + i) with (HA + (64 + i)) by ring; apply KG; lia | exact BKe]|].
  split; [apply (rk_list_at_kept L A m); [exact S17 | intros i Hi; replace (HA + 80 + i) with (HA + (80 + i)) by ring; apply KG; lia | exact BKh]|].
  exact S18.
Qed.

Lemma rk_run : forall (fxc : YK11.FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
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

Lemma rk_kb2_trans : forall m1 m2 m3 a, rk_kb2 m1 m2 a -> rk_kb2 m2 m3 a -> rk_kb2 m1 m3 a.
Proof using. intros m1 m2 m3 a [E1 W1] [E2 W2]. split; [congruence | tauto]. Qed.

Lemma rk_bkept_trans : forall L1 A1 m1 L2 A2 m2 L3 A3 m3 q,
  rk_bkept L1 A1 m1 L2 A2 m2 q -> rk_bkept L2 A2 m2 L3 A3 m3 q -> rk_bkept L1 A1 m1 L3 A3 m3 q.
Proof using.
  intros L1 A1 m1 L2 A2 m2 L3 A3 m3 q B1 B2 k Hin. destruct (B1 k Hin) as [H2 K1].
  destruct (B2 k H2) as [H3 K2]. split; [exact H3|]. intros i Hi. exact (rk_kb2_trans _ _ _ _ (K1 i Hi) (K2 i Hi)).
Qed.

Lemma rk_rp_kept : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k,
  MR L1 A1 m1 md1 ->
  relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 -> ~ F' q -> In (q, k) (blocks L1 A1) ->
  In (q, k) (blocks L2 A2) /\ (forall i, 0 <= i < k -> ~ E' (q + i) -> rk_kb2 m1 m2 (q + i)).
Proof using.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k M1 RP HF Hin.
  destruct RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  apply rk_blocks_in in Hin as (p & Ep & Hp).
  pose proof (rk_ub_nonneg A1 p k (mr_wf Bm MR rk_laws L1 A1 m1 md1 M1) Hp) as Hk.
  subst q.
  destruct (Z.eq_dec k 0) as [->|Hk'].
  - destruct (Z2 p Hp) as [H2 E2]. split; [apply rk_blocks_in; exists p; split; [exact E2 | exact H2]|].
    intros i Hi. lia.
  - assert (H2 : In (p, k) (user_blocks A2)) by (apply SV2; [exact Hp | lia | exact HF]).
    pose proof (AD2 p k Hp H2 HF) as E2.
    split; [apply rk_blocks_in; exists p; split; [exact E2 | exact H2]|].
    intros i Hi HE. split.
    + exact (BY2 p k i Hp H2 HF Hi HE).
    + intros _. rewrite <- E2. apply rk_present_writable.
      exact (proj1 (mr_blocks Bm MR rk_laws L2 A2 m2 md2 p k i M2 H2 Hi)).
Qed.

Lemma rk_run0 : forall (fxc : YK11.FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs Q (MS (Regs6ss.mkR_of regs) (@fp_regs fxc) pc (@fp_csr fxc) None mem (seg_rom rsegs)) ->
  (forall s0 R', Q s0 -> Regs6ss.xregs_eqv (ms_regs s0) R' ->
     SR segs (mkCfg {| ms_regs := R'; ms_fregs := ms_fregs s0; ms_pc_val := ms_pc_val s0;
                       ms_svc_pending := ms_svc_pending s0; ms_resv := ms_resv s0; ms_fcsr := ms_fcsr s0;
                       ms_mem := ms_mem s0; ms_rom := ms_rom s0 |} md) P) ->
  SR segs (mkCfg (@YK11.mkst fxc regs pc mem (seg_rom segs)) md) P.
Proof using SEGS.
  intros fxc regs pc mem md Q P Hh Hl HE K.
  apply (evt_SR_canon segs (@YK11.mkst fxc regs pc mem (seg_rom segs)) Q md P); [ | exact Hh | exact Hl | ].
  - rewrite SEGS. change (RegisterBridge.canonical_register_state (@YK11.mkst fxc regs pc mem (seg_rom rsegs)))
      with (MS (Regs6ss.mkR_of regs) (@fp_regs fxc) pc (@fp_csr fxc) None mem (seg_rom rsegs)).
    exact HE.
  - intros ms' (can & HQ & HEQ).
    destruct ms' as [r f pv sv rv c mm o], can as [cr cf cp csv crv cc cmm co].
    destruct HEQ as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
    subst.
    exact (K _ r HQ E1).
Qed.

End RK.

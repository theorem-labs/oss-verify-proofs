From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Exec MState PropExec.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0 AllocSlots AllocRoom.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c GrantSlotPlan SlotCompose UbsanHalts SlotImg.
Import ListNotations.
Local Open Scope Z_scope.

(* A Kind A phase run on the normalized memory, read back on the real memory. *)
Lemma phase_SR : forall (P Q : machine_state -> Prop) s md (R : config -> Prop),
  (forall s0, P s0 -> Exec.evt rsegs Q s0) ->
  norm_at P s -> MemNorm.ro_agree rsegs (ms_mem s) ->
  m_halted md = None -> m_vm_lazy md = [] ->
  (forall s', norm_at Q s' -> MemNorm.ro_same rsegs (ms_mem s) (ms_mem s') -> SR rsegs (mkCfg s' md) R) ->
  SR rsegs (mkCfg s md) R.
Proof.
  intros P Q s md R HE (s0 & HP & Hrel) HRO Hh Hl K.
  eapply evt_SR; [eapply MemNorm.evt_rel; [apply wx_apart_rsegs | exact Hrel | exact (HE s0 HP)] | exact Hh | exact Hl |].
  intros s' (s0' & HQ & Hrel' & Hsame). apply K; [exists s0'; split; assumption | exact Hsame].
Qed.

Lemma munch_point : forall W m m' a, Frame.munch W m m' -> 0 <= a < 2 ^ 64 -> Frame.outside W a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros W m m' a H Ha Ho. apply H. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Ho.
Qed.

Lemma point_mbyte : forall (m m' : word -> option byte) a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  YP09.mbyte rsegs m' a = YP09.mbyte rsegs m a /\
  (YP09.writable_at rsegs m a <-> YP09.writable_at rsegs m' a).
Proof.
  intros m m' a E. unfold YP09.mbyte, YP09.writable_at, wview. rewrite E. split; [reflexivity | tauto].
Qed.

Section Chain.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis HB : ms_segs B = rsegs.
Hypothesis FA : frame_allocator B API.
Hypothesis Herr : errno_addr B + 4 <= alloc_ceiling.

Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (p n : Z).

Definition S0 : Z := spZ regs0.

Definition outside_slot (a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\
  ((alloc_ceiling <= a /\ ~ lib_scratch B SLOT_STACK regs0 a) \/
   (in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
      ~ (errno_addr B <= a < errno_addr B + 4)) \/
   (exists q k, In (q, k) (user_blocks A0) /\ ptr_addr L0 q <= a < ptr_addr L0 q + k)).

Definition Rel0 (s : machine_state) (L : layout) (A : astate) (md : Model) : Prop :=
  (forall a, outside_slot a ->
     YP09.mbyte rsegs (ms_mem s) a = YP09.mbyte rsegs mem0 a /\
     (YP09.writable_at rsegs mem0 a <-> YP09.writable_at rsegs (ms_mem s) a)) /\
  (forall q k, In (q, k) (user_blocks A0) -> exists q', In (q', k) (user_blocks A) /\ ptr_addr L q' = ptr_addr L0 q) /\
  (forall a, S0 - SLOT_STACK <= a < S0 -> YP09.writable_at rsegs (ms_mem s) a) /\
  (exists vm, md = with_vmmaps vm md0).

(* A block the slot owns: a live user block of A, apart from the blocks the slot was given and from the image. *)
Definition own_ok (L : layout) (A : astate) (lo hi : Z) : Prop :=
  live_blk L A lo (hi - lo) /\
  (forall q k, In (q, k) (user_blocks A0) -> hi <= ptr_addr L0 q \/ ptr_addr L0 q + k <= lo) /\
  (forall a, lo <= a < hi -> ~ in_img B a).

Hypothesis HA0 : forall q k, In (q, k) (user_blocks A0) ->
  4096 <= ptr_addr L0 q /\ ptr_addr L0 q + k <= alloc_ceiling /\
  (forall i, 0 <= i < k -> ~ in_img B (ptr_addr L0 q + i)).

Lemma outside_of_forall : forall W a, (forall lo hi, In (lo, hi) W -> ~ (lo <= a < hi)) -> Frame.outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a H; cbn; [exact I|].
  split; [apply (H lo hi); left; reflexivity | apply IH; intros lo' hi' Hin; apply (H lo' hi'); right; exact Hin].
Qed.

Lemma img_low : forall a, in_img B a -> a < 0x51000.
Proof. intros a Ha. apply (proj1 (in_img_rsegs B a HB)) in Ha. lia. Qed.

Lemma rel0_phase : forall x W s s0 s0' s' L A md,
  Rel0 s L A md -> aa_MR API L A (ms_mem s) md ->
  MemNorm.ms_rel rsegs s s0 -> MemNorm.ms_rel rsegs s' s0' -> MemNorm.ro_same rsegs (ms_mem s) (ms_mem s') ->
  kept x W s0 s0' -> x_S x = S0 -> alloc_ceiling + SLOT_STACK <= S0 -> S0 <= 2 ^ 47 ->
  (forall lo hi, In (lo, hi) W -> own_ok L A lo hi) ->
  Rel0 s' L A md /\ aa_MR API L A (ms_mem s') md /\ Frame.wmono rsegs (ms_mem s) (ms_mem s').
Proof.
  intros x W s s0 s0' s' L A md (OUT & UB & SW & MD) MR Hr Hr' Hsame (MU & WM) HS HSc HS47 HW.
  destruct Hr as (_ & _ & _ & _ & _ & _ & _ & Hm). destruct Hr' as (_ & _ & _ & _ & _ & _ & _ & Hm').
  pose proof (MemNorm.munch_rel rsegs _ _ _ _ _ Hm Hm' Hsame MU) as MUr.
  pose proof (MemNorm.wmono_rel rsegs _ _ _ _ Hm Hm' Hsame WM) as WMr.
  pose proof (aa_laws API) as LAWS.
  destruct FA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AX & _).
  pose proof alloc_ceiling_value as (Hc1 & _).
  assert (OWNLOW : forall lo hi a, In (lo, hi) W -> lo <= a < hi -> 4096 <= a < alloc_ceiling /\ ~ in_img B a).
  { intros lo hi a Hin Ha. destruct (HW lo hi Hin) as ((q & Hq & Hpq) & _ & Himg).
    destruct (mr_blocks_range B _ LAWS L A (ms_mem s) md q (hi - lo) MR Hq) as (R1 & R2).
    split; [lia | exact (Himg a Ha)]. }
  assert (Hout : forall a, outside_slot a ->
      Frame.outside ((x_S x - LLVM_STACK, x_S x) :: W) a).
  { intros a (Ha & Hcase). cbn [Frame.outside]. split.
    - rewrite HS. unfold LLVM_STACK, LLVM_FRAME, YO0d.ALLOC_STACK. unfold S0 in *.
      destruct Hcase as [(Hc & Hns) | [(Hi & _) | (q & k & Hq & Hqa)]].
      + intros Hin. apply Hns. left. unfold SLOT_STACK. clear -Hin. lia.
      + apply img_low in Hi. unfold SLOT_STACK in *. clear -Hi Hc1 HSc. lia.
      + destruct (HA0 q k Hq) as (_ & H2 & _). unfold SLOT_STACK in *. clear -H2 Hqa HSc. lia.
    - apply outside_of_forall. intros lo hi Hin Hlo.
      destruct (OWNLOW lo hi a Hin Hlo) as (H1 & H2).
      destruct Hcase as [(Hc & _) | [(Hi & _) | (q & k & Hq & Hqa)]].
      + lia.
      + exact (H2 Hi).
      + destruct (HW lo hi Hin) as (_ & Hdis & _). destruct (Hdis q k Hq); lia. }
  split; [split; [| split; [exact UB | split; [| exact MD]]] |].
  - intros a Ho. destruct (OUT a Ho) as (E1 & E2).
    pose proof (point_mbyte (ms_mem s) (ms_mem s') a (munch_point _ _ _ a MUr (proj1 Ho) (Hout a Ho))) as (F1 & F2).
    rewrite F1, E1. split; [reflexivity | tauto].
  - intros a Ha. apply WMr. exact (SW a Ha).
  - split; [| exact WMr].
    destruct (mr_model B _ LAWS L A (ms_mem s) md MR) as (Hh & Hl & Hmat).
    assert (OWNOUT : forall a, owned B L A a -> Frame.outside ((x_S x - LLVM_STACK, x_S x) :: W) a).
    { intros a Ho. pose proof (mr_owned_low B _ LAWS L A (ms_mem s) md a MR Ho) as Hlow.
      cbn [Frame.outside]. split.
      - rewrite HS. unfold LLVM_STACK, LLVM_FRAME, YO0d.ALLOC_STACK, S0, SLOT_STACK in *. clear -Hlow HSc. lia.
      - apply outside_of_forall. intros lo hi Hin Hlo.
        destruct (HW lo hi Hin) as ((q & Hq & Hpq) & _ & _).
        destruct (mr_blocks B _ LAWS L A (ms_mem s) md q (hi - lo) (a - lo) MR Hq ltac:(lia)) as (_ & _ & _ & Hno).
        apply Hno. replace (ptr_addr L q + (a - lo)) with a by lia. exact Ho. }
    apply (mr_frame B _ LAWS L A (ms_mem s) (ms_mem s') md md MR).
    + intros a Ho. pose proof (mr_owned_low B _ LAWS L A (ms_mem s) md a MR Ho) as Hlow.
      rewrite HB. apply (point_mbyte (ms_mem s) (ms_mem s') a).
      apply (munch_point _ _ _ a MUr); [lia | exact (OWNOUT a Ho)].
    + intros a Ho (b0 & Hb0). pose proof (mr_owned_low B _ LAWS L A (ms_mem s) md a MR Ho) as Hlow.
      exists b0. rewrite (munch_point _ _ _ a MUr ltac:(lia) (OWNOUT a Ho)). exact Hb0.
    + intros q k i Hq Hi.
      destruct (mr_blocks B _ LAWS L A (ms_mem s) md q k i MR Hq Hi) as ((b0 & Hb0) & H4 & H5 & _).
      pose proof (ax_blocks_img AX L A (ms_mem s) md q k i MR Hq Hi) as Hni.
      pose proof (noimg_noseg B (ptr_addr L q + i) HB Hni) as Hns.
      assert (Hw : wview rsegs (ms_mem s) (Z_to_bv 64 (ptr_addr L q + i)) <> None)
        by (unfold wview; rewrite Hb0; discriminate).
      apply WMr in Hw. unfold wview in Hw.
      destruct (ms_mem s' (Z_to_bv 64 (ptr_addr L q + i))) as [b1|] eqn:E1; [exists b1; exact E1|].
      exfalso. apply Hw. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Z.mod_small by (pose proof alloc_ceiling_lt; lia). rewrite Hns. reflexivity.
    + reflexivity.
    + exact Hh.
    + exact Hl.
    + exact Hmat.
Qed.

(* The state of the slot between phases, on the real memory. *)
Definition St (x : slot_ctx) (s : machine_state) (L : layout) (A : astate) (md : Model) (b : sbound) : Prop :=
  MemNorm.ro_agree rsegs (ms_mem s) /\ ms_fregs s = fp_regs /\ ms_fcsr s = fp_csr /\
  alloc_state B API L A (ms_mem s) md b /\ errno_wr B (ms_mem s) /\ payload_blk B x L A /\ Rel0 s L A md.

Lemma st_phase : forall x W (P Q : machine_state -> Prop) s L A md b (R : config -> Prop),
  x_S x = S0 -> alloc_ceiling + SLOT_STACK <= S0 -> S0 <= 2 ^ 47 -> x_F x = fp_regs -> x_fc x = fp_csr ->
  St x s L A md b -> norm_at P s ->
  (forall s0, P s0 -> Exec.evt rsegs (fun s0' => kept x W s0 s0' /\ Q s0') s0) ->
  (forall s1, Q s1 -> ms_fregs s1 = x_F x /\ ms_fcsr s1 = x_fc x) ->
  (forall lo hi, In (lo, hi) W -> own_ok L A lo hi) ->
  (forall s', St x s' L A md b -> norm_at Q s' -> SR rsegs (mkCfg s' md) R) ->
  SR rsegs (mkCfg s md) R.
Proof.
  intros x W P Q s L A md b R HS HSc HS47 HF HFC (RO & Hfr & Hfc & AS & ER & PB & RL) (s0 & HP & Hrel) HE HQF HW K.
  pose proof (aa_laws API) as LAWS.
  destruct AS as (MR & WF & BD & INI & RES).
  destruct (mr_model B _ LAWS L A (ms_mem s) md MR) as (Hh & Hl & _).
  apply (phase_SR (fun s1 => P s1 /\ MemNorm.ms_rel rsegs s s1)
                  (fun s1' => exists s1, MemNorm.ms_rel rsegs s s1 /\ kept x W s1 s1' /\ Q s1') s md R).
  - intros s1 (HP1 & Hr1). eapply Exec.evt_mono; [exact (HE s1 HP1)|].
    intros s1' (Hk & HQ). exists s1. split; [exact Hr1 | split; assumption].
  - exists s0. split; [split; assumption | exact Hrel].
  - exact RO.
  - exact Hh.
  - exact Hl.
  - intros s' (s0' & (s1 & Hr1 & Hk & HQ) & Hr') Hsame.
    destruct (rel0_phase x W s s1 s0' s' L A md RL MR Hr1 Hr' Hsame Hk HS HSc HS47 HW) as (RL' & MR' & WM').
    apply K; [| exists s0'; split; assumption].
    split; [exact (MemNorm.ro_agree_same rsegs _ _ RO Hsame)|].
    destruct Hr' as (_ & Hf' & _ & _ & _ & Hc' & _ & _).
    destruct (HQF s0' HQ) as (Hq1 & Hq2).
    split; [rewrite Hf', Hq1; exact HF|].
    split; [rewrite Hc', Hq2; exact HFC|].
    split; [split; [exact MR' | split; [exact WF | split; [exact BD | split; [exact INI | exact RES]]]]|].
    split; [intros a Ha; pose proof (ER a Ha) as E1; unfold YP09.writable_at in *; rewrite HB in *;
            apply WM'; exact E1|].
    split; [exact PB | exact RL'].
Qed.

(* The SR posts of malloc_glue and free_glue (GrantSlotPlan.v), verbatim. *)
Definition mpost (x : slot_ctx) (Live : layout -> astate -> Prop) (nb : Z) (Post : Z -> machine_state -> Prop)
    (s : machine_state) (md : Model) (L : layout) (A : astate) (b : sbound) (c' : config) : Prop :=
  exists s' md' L' A' r,
    c' = mkCfg s' md' /\ glue_post B API x (Post r) Live s' md' L' A' (sb_malloc b nb) /\ live_blk L' A' r nb /\
    call_post_k B (aa_MR API) ALLOC_STACK L A (ms_regs s) (ms_mem s) md (fun _ => False) L' A' (ms_regs s')
      (ms_mem s') md' /\
    fresh_block B r nb /\ r mod 16 = 0 /\
    (exists b1 b2, blocks L' A' = b1 ++ (r, nb) :: b2 /\ blocks L A = b1 ++ b2) /\
    blocks_kept B L A (ms_mem s) (ms_mem s') (fun _ => False) /\ guard_kept B (ms_mem s) (ms_mem s') /\
    (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')).

Definition fpost (x : slot_ctx) (Live : layout -> astate -> Prop) (s0 nb : Z) (Post : machine_state -> Prop)
    (s : machine_state) (md : Model) (L : layout) (A : astate) (b : sbound) (q : sptr) (c' : config) : Prop :=
  exists s' md' L' A',
    c' = mkCfg s' md' /\ glue_post B API x Post Live s' md' L' A' (sb_free b nb) /\
    call_post B (aa_MR API) L A (ms_regs s) (ms_mem s) md (fun a => s0 <= a < s0 + nb) L' A' (ms_regs s')
      (ms_mem s') md' /\
    (exists b1 b2, blocks L A = b1 ++ (s0, nb) :: b2 /\ blocks L' A' = b1 ++ b2) /\
    blocks_kept B L A (ms_mem s) (ms_mem s') (fun a => a = s0) /\ guard_kept B (ms_mem s) (ms_mem s') /\
    (forall q' k, In (q', k) (user_blocks A) -> q' <> q -> In (q', k) (user_blocks A')).

(* (c1), (c2): the slot state through an allocator call. *)
Definition st_malloc_ok : Prop :=
  forall x Live nb Post s md L A b (owns : list (Z * Z)) c',
    x_S x = S0 -> spZ (ms_regs s) = S0 - LLVM_FRAME -> alloc_ceiling + SLOT_STACK <= S0 -> S0 <= 2 ^ 47 ->
    St x s L A md b -> (forall lo hi, In (lo, hi) owns -> own_ok L A lo hi) ->
    mpost x Live nb Post s md L A b c' ->
    exists s' md' L' A' r,
      c' = mkCfg s' md' /\ norm_at (Post r) s' /\ St x s' L' A' md' (sb_malloc b nb) /\ Live L' A' /\
      own_ok L' A' r (r + nb) /\ (forall lo hi, In (lo, hi) owns -> own_ok L' A' lo hi).

Definition st_free_ok : Prop :=
  forall x Live s0 nb Post s md L A b q (owns : list (Z * Z)) c',
    x_S x = S0 -> spZ (ms_regs s) = S0 - LLVM_FRAME -> alloc_ceiling + SLOT_STACK <= S0 -> S0 <= 2 ^ 47 ->
    St x s L A md b -> 0 < nb -> own_ok L A s0 (s0 + nb) -> In (q, nb) (user_blocks A) -> ptr_addr L q = s0 ->
    (forall lo hi, In (lo, hi) owns -> own_ok L A lo hi /\ hi - lo <> nb) ->
    fpost x Live s0 nb Post s md L A b q c' ->
    exists s' md' L' A',
      c' = mkCfg s' md' /\ norm_at Post s' /\ St x s' L' A' md' (sb_free b nb) /\ Live L' A' /\
      (forall lo hi, In (lo, hi) owns -> own_ok L' A' lo hi).

Definition row_off : Prop :=
  forall i, 0 <= i < 24 -> ~ static_owned B (CTRL_HEADAMP_ROW + i) /\
    ~ (ms_ctx B <= CTRL_HEADAMP_ROW + i < ms_ctx B + CTX_SIZE) /\
    ~ (errno_addr B <= CTRL_HEADAMP_ROW + i < errno_addr B + 4).

Lemma glue_pre_of : forall x Pre s md L A b,
  unit_binding B -> x_tp x = w64 (ms_tp B) -> row_off ->
  St x s L A md b -> norm_at Pre s -> glue_pre B API x Pre s md L A b.
Proof.
  intros x Pre s md L A b UB Htp RW (RO & Hf & Hc & AS & ER & PB & _) NP.
  unfold glue_pre. rewrite HB.
  exact (conj FA (conj UB (conj Htp (conj NP (conj RO (conj Hf (conj Hc (conj AS (conj ER (conj PB
         (conj Herr RW))))))))))).
Qed.

Lemma sp_of : forall x (P : machine_state -> Prop) s,
  (forall s0, P s0 -> rg s0 2 = w64 (SPL x)) -> 0 <= SPL x < 2 ^ 64 -> norm_at P s -> spZ (ms_regs s) = SPL x.
Proof.
  intros x P s HP Hr (s0 & H0 & (Hreg & _)). pose proof (HP s0 H0) as E.
  unfold spZ, rg, w64 in *. rewrite Hreg. change (YK11.getr (ms_regs s0) 2) with (PropExec.getr (ms_regs s0) (Z_to_bv 5 2)).
  rewrite E. apply MState.unsigned_lit. lia.
Qed.

Definition xent (pl : list byte) : slot_ctx :=
  mkctx S0 (PropExec.getr regs0 (Z_to_bv 5 1)) (PropExec.getr regs0 (Z_to_bv 5 3))
    (PropExec.getr regs0 (Z_to_bv 5 4)) (map (fun r => PropExec.getr regs0 (Z_to_bv 5 r)) SREGS) p pl
    fp_regs fp_csr.

Definition Ep (x : slot_ctx) (s0 : machine_state) : Prop :=
  ms_pc_val s0 = MState.ret_pc (x_ra x) /\ ms_fregs s0 = x_F x /\ ms_fcsr s0 = x_fc x /\ ms_resv s0 = None /\
  ms_svc_pending s0 = None /\ rg s0 1 = x_ra x /\ rg s0 2 = w64 (x_S x) /\ rg s0 3 = x_gp x /\
  rg s0 4 = x_tp x /\ sregs s0 = x_sv x /\ rg s0 10 = w64 0 /\ ms_rom s0 = seg_rom rsegs.

Lemma body_fr : forall x pc s, body x pc s -> ms_fregs s = x_F x /\ ms_fcsr s = x_fc x.
Proof. intros x pc s ((_ & HF & Hc & _) & _). split; assumption. Qed.

Lemma body_sp : forall x pc s, body x pc s -> rg s 2 = w64 (SPL x).
Proof. intros x pc s (_ & H & _). exact H. Qed.

Lemma own_live : forall L A lo nb, own_ok L A lo (lo + nb) -> exists q, In (q, nb) (user_blocks A) /\ ptr_addr L q = lo.
Proof. intros L A lo nb ((q & Hq & Hp) & _). replace (lo + nb - lo) with nb in Hq by lia. exists q. split; assumption. Qed.

Lemma own_live' : forall L A lo nb, own_ok L A lo (lo + nb) -> live_blk L A lo nb.
Proof. intros L A lo nb H. destruct (own_live L A lo nb H) as (q & Hq & Hp). exists q. split; assumption. Qed.

(* (d) the entry: the slot pre on the real memory gives the plan's At_entry on the normalized memory
   and the slot state St with the entry's own allocator state. *)
Definition entry_ok : Prop :=
  forall (ra empty : Z) (pl : list byte) (b : sbound),
    lib_pre_x B API SLOT_STACK empty L0 A0 regs0 mem0 md0 ra p n pl b ->
    G_img_c B frame_RELRO mem0 -> MemNorm.ro_agree (ms_segs B) mem0 -> empty = 0x30150 ->
    St (xent pl) (YK11.mkst regs0 (Z_to_bv 64 ENTRY) mem0 (seg_rom rsegs)) L0 A0 md0 b /\
    norm_at (At_entry (xent pl)) (YK11.mkst regs0 (Z_to_bv 64 ENTRY) mem0 (seg_rom rsegs)).

Ltac to_body H :=
  repeat match type of H with
  | body _ _ _ => fail 1
  | _ /\ _ => destruct H as [H _]
  | _ \/ _ => destruct H as [H|H]
  | _ => progress unfold At_ret0, At_mallocT, At_mallocT_ret, At_mallocSW1, At_mallocSW1_ret, At_freeSW1,
           At_raw, At_mallocSW2, At_mallocSW2_ret, At_freeSW2, At_freeSW2_ret, At_freeT, at_after_admit in H
  end.

Lemma kept_of_mem : forall x W s0 s0', ms_mem s0' = ms_mem s0 -> kept x W s0 s0'.
Proof. intros x W s0 s0' E. unfold kept. rewrite E. split; [apply Frame.munch_refl | apply Frame.wmono_refl]. Qed.

Lemma h_rows_rng : forall pl, 0 <= h_rows (header pl) < 256.
Proof.
  intros pl. unfold header.
  destruct (rd16 pl 0) as [u p1]. destruct (rd8 pl p1) as [i p2]. destruct (rd8 pl p2) as [r p3] eqn:E3.
  assert (V : 0 <= fst (rd8 pl p2) < 256).
  { unfold rd8. destruct (p2 <? length pl)%nat; cbn [fst]; [|lia].
    unfold pbz. pose proof (bv_unsigned_in_range _ (nth p2 pl (Z_to_bv 8 0))) as H.
    change (bv_modulus 8) with 256 in H. lia. }
  rewrite E3 in V. cbn in V |- *. lia.
Qed.

Lemma sw1_rng : forall x, 34 <= sw1_size x <= 8670.
Proof. intros x. unfold sw1_size, hd. pose proof (h_rows_rng (x_pl x)). lia. Qed.

Section Path.
Variables (pl : list byte) (b0 : sbound).
Hypotheses (HEAD : seg_head) (INIT : seg_init) (NSET : seg_nset) (STURN : seg_set_turn)
  (UENT : seg_unset_enter) (UTURN : seg_unset_turn) (ADMIT : seg_admit) (SWEEP : seg_sweep) (RAW : seg_raw)
  (RAWSW : seg_rawsweep) (SSETUP : seg_sched_setup) (SCHED : seg_sched_turn) (EPI : seg_epilogue).
Hypotheses (GMT : seg_mallocT B API) (GM1 : seg_mallocSW1 B API) (GM2 : seg_mallocSW2 B API)
  (GF1 : seg_freeSW1 B API) (GF2 : seg_freeSW2 B API) (GFT : seg_freeT B API).
Hypotheses (STM : st_malloc_ok) (STF : st_free_ok).
Hypotheses (UB : unit_binding B) (HTP : x_tp (xent pl) = w64 (ms_tp B)) (ROW : row_off).
Hypotheses (HSc : alloc_ceiling + SLOT_STACK <= S0) (HS47 : S0 <= 2 ^ 47).

Definition b1 : sbound := sb_malloc b0 460.
Definition res_end (b : sbound) : Prop := b = b0.

Hypothesis RB0 : sb_live b0 <= 64 /\ 0 <= sb_bytes b0 <= 2 ^ 28 /\ sb_cap b0 = CAPMAX.

Lemma RT : room_slots b0 460.
Proof. destruct RB0 as (H1 & H2 & H3). apply room_slots_small; unfold CAPMAX in *; lia. Qed.

Lemma R1 : room_slots b1 (sw1_size (xent pl)).
Proof.
  destruct RB0 as (H1 & H2 & H3). pose proof (sw1_rng (xent pl)).
  apply room_slots_small; unfold b1, sb_malloc; cbn [sb_live sb_bytes sb_cap]; unfold CAPMAX in *; lia.
Qed.

Lemma R2 : room_slots b1 4352.
Proof.
  destruct RB0 as (H1 & H2 & H3).
  apply room_slots_small; unfold b1, sb_malloc; cbn [sb_live sb_bytes sb_cap]; unfold CAPMAX in *; lia.
Qed.

Variable R : config -> Prop.
Hypothesis K : forall s L A md b, St (xent pl) s L A md b -> norm_at (Ep (xent pl)) s -> res_end b -> R (mkCfg s md).

Let x := xent pl.

Lemma HSx : x_S x = S0. Proof. reflexivity. Qed.
Lemma HST : alloc_ceiling + LLVM_STACK <= x_S x.
Proof. rewrite HSx. unfold LLVM_STACK, LLVM_FRAME, YO0d.ALLOC_STACK, SLOT_STACK in *. lia. Qed.
Lemma HSPL : 0 <= SPL x < 2 ^ 64.
Proof. unfold SPL, LLVM_FRAME. rewrite HSx. pose proof alloc_ceiling_value as (Hc & _). unfold SLOT_STACK in *. lia. Qed.

Lemma sp_body : forall pc (P : machine_state -> Prop) s, (forall s0, P s0 -> body x pc s0) -> norm_at P s ->
  spZ (ms_regs s) = S0 - LLVM_FRAME.
Proof.
  intros pc P s HP N. rewrite (sp_of x P s (fun s0 H => body_sp _ _ _ (HP s0 H)) HSPL N). unfold SPL. rewrite HSx. reflexivity.
Qed.

(* Epilogue: from At_ret0 to the return. *)
Lemma path_epi : forall s L A md b, res_end b -> St x s L A md b -> norm_at (At_ret0 x) s -> SR rsegs (mkCfg s md) R.
Proof.
  intros s L A md b Hb S1 N1.
  apply (st_phase x [] (At_ret0 x) (Ep x) s L A md b R HSx HSc HS47 eq_refl eq_refl S1 N1).
  - intros s0 H0. eapply Exec.evt_mono; [exact (EPI x s0 H0)|].
    intros s0' (Hm & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12). split.
    + apply kept_of_mem. exact Hm.
    + repeat split; assumption.
  - intros s1 (_ & HF & HC & _). split; assumption.
  - intros lo hi [].
  - intros s' S' N'. apply SR_ret. exact (K s' L A md b S' N' Hb).
Qed.

Ltac frq := let s1 := fresh "s1" in let Hq := fresh "Hq" in
  intros s1 Hq; to_body Hq; exact (body_fr _ _ _ Hq).
Ltac frq2 := let s1 := fresh "s1" in let Hq := fresh "Hq" in
  intros s1 [[_ Hq] | [_ Hq]]; to_body Hq; exact (body_fr _ _ _ Hq).

Ltac st_go W P Q := eapply (st_phase x W P Q); [exact HSx | exact HSc | exact HS47 | reflexivity | reflexivity | eassumption | eassumption | | | |].

Lemma path_freeT : forall s L A md b t, res_end (sb_free b 460) -> St x s L A md b -> own_ok L A t (t + 460) ->
  norm_at (At_freeT x t) s -> SR rsegs (mkCfg s md) R.
Proof.
  intros s L A md b t Hb S1 Ot N1.
  destruct (own_live L A t 460 Ot) as (q & Hq & Hp).
  apply (SR_bind rsegs _ (fpost x no_live t 460 (At_ret0 x) s md L A b q)).
  - pose proof (GFT x t HST s md L A b q (glue_pre_of x _ s md L A b UB HTP ROW S1 N1) I Hq Hp) as G.
    rewrite HB in G. exact G.
  - intros c' Hc.
    destruct (STF x no_live t 460 (At_ret0 x) s md L A b q [] c' HSx
                (sp_body _ (At_freeT x t) s (fun s0 H => proj1 H) N1) HSc HS47 S1 ltac:(lia) Ot Hq Hp
                (fun lo hi H => match H with end) Hc) as (s' & md' & L' & A' & -> & N' & S' & _ & _).
    exact (path_epi s' L' A' md' (sb_free b 460) Hb S' N').
Qed.

Lemma path_E5 : forall s L A md b t, res_end (sb_free b 460) -> St x s L A md b -> own_ok L A t (t + 460) ->
  norm_at (At_freeSW2_ret x t) s -> SR rsegs (mkCfg s md) R.
Proof.
  intros s L A md b t Hb S1 Ot N1.
  st_go [(t, t + 460)] (At_freeSW2_ret x t) (At_freeT x t).
  - intros s0 H0. exact (phase_E5 SSETUP SCHED x t s0 H0).
  - frq.
  - intros lo hi [E|[]]. inversion E; subst. exact Ot.
  - intros s' S' N'. exact (path_freeT s' L A md b t Hb S' Ot N').
Qed.

Lemma path_freeSW2 : forall s L A md b t sw, res_end (sb_free (sb_free b 4352) 460) -> St x s L A md b ->
  own_ok L A t (t + 460) -> own_ok L A sw (sw + 4352) -> norm_at (At_freeSW2 x t sw) s -> SR rsegs (mkCfg s md) R.
Proof.
  intros s L A md b t sw Hb S1 Ot Os N1.
  destruct (own_live L A sw 4352 Os) as (q & Hq & Hp).
  assert (OW : forall lo hi, In (lo, hi) [(t, t + 460)] -> own_ok L A lo hi /\ hi - lo <> 4352)
    by (intros lo hi [E|[]]; inversion E; subst; split; [exact Ot | lia]).
  apply (SR_bind rsegs _ (fpost x (fun L A => live_blk L A t 460) sw 4352 (At_freeSW2_ret x t) s md L A b q)).
  - pose proof (GF2 x t sw HST s md L A b q (glue_pre_of x _ s md L A b UB HTP ROW S1 N1) (own_live' L A t 460 Ot)
                  Hq Hp) as G.
    rewrite HB in G. exact G.
  - intros c' Hc.
    destruct (STF x (fun L A => live_blk L A t 460) sw 4352 (At_freeSW2_ret x t) s md L A b q [(t, t + 460)] c' HSx
                (sp_body _ (At_freeSW2 x t sw) s (fun s0 H => proj1 H) N1) HSc HS47 S1 ltac:(lia) Os Hq Hp
                OW Hc)
      as (s' & md' & L' & A' & -> & N' & S' & _ & Own').
    exact (path_E5 s' L' A' md' (sb_free b 4352) t Hb S' (Own' t (t + 460) (or_introl eq_refl)) N').
Qed.

Lemma path_SW2ret : forall s L A md b t sw, res_end (sb_free (sb_free b 4352) 460) -> St x s L A md b ->
  own_ok L A t (t + 460) -> own_ok L A sw (sw + 4352) -> norm_at (At_mallocSW2_ret x t sw) s ->
  SR rsegs (mkCfg s md) R.
Proof.
  intros s L A md b t sw Hb S1 Ot Os N1.
  st_go [(sw, sw + 4352)] (At_mallocSW2_ret x t sw) (At_freeSW2 x t sw).
  - intros s0 H0. exact (RAWSW x t sw s0 H0).
  - frq.
  - intros lo hi [E|[]]. inversion E; subst. exact Os.
  - intros s' S' N'. exact (path_freeSW2 s' L A md b t sw Hb S' Ot Os N').
Qed.

Lemma path_mallocSW2 : forall s L A md t, St x s L A md b1 ->
  own_ok L A t (t + 460) -> norm_at (At_mallocSW2 x t) s -> SR rsegs (mkCfg s md) R.
Proof.
  intros s L A md t S1 Ot N1.
  assert (OW : forall lo hi, In (lo, hi) [(t, t + 460)] -> own_ok L A lo hi)
    by (intros lo hi [E|[]]; inversion E; subst; exact Ot).
  apply (SR_bind rsegs _ (mpost x (fun L A => live_blk L A t 460) 4352 (fun s => At_mallocSW2_ret x t s) s md L A b1)).
  - pose proof (GM2 x t HST s md L A b1 (glue_pre_of x _ s md L A b1 UB HTP ROW S1 N1) (own_live' L A t 460 Ot)
                  R2) as G.
    rewrite HB in G. exact G.
  - intros c' Hc.
    destruct (STM x (fun L A => live_blk L A t 460) 4352 (fun s => At_mallocSW2_ret x t s) s md L A b1
                [(t, t + 460)] c' HSx (sp_body _ (At_mallocSW2 x t) s (fun s0 H => proj1 H) N1) HSc HS47 S1
                OW Hc)
      as (s' & md' & L' & A' & sw & -> & N' & S' & _ & Osw & Own').
    apply (path_SW2ret s' L' A' md' (sb_malloc b1 4352) t sw); [| exact S' | exact (Own' t (t + 460) (or_introl eq_refl)) |
           exact Osw | exact N'].
    unfold res_end, b1. rewrite !sb_free_malloc. reflexivity.
Qed.

Lemma path_raw : forall s L A md t pc, St x s L A md b1 ->
  own_ok L A t (t + 460) -> norm_at (At_raw x t pc) s -> SR rsegs (mkCfg s md) R.
Proof.
  intros s L A md t pc S1 Ot N1.
  st_go (@nil (Z * Z)) (At_raw x t pc) (At_mallocSW2 x t).
  - intros s0 H0. exact (RAW x t pc s0 H0).
  - frq.
  - intros lo hi [].
  - intros s' S' N'. exact (path_mallocSW2 s' L A md t S' Ot N').
Qed.

Lemma sw1_ne : 460 <> sw1_size x.
Proof. unfold sw1_size. pose proof (Z.le_max_r (h_rows (hd x)) 1). lia. Qed.

Lemma path_freeSW1 : forall s L A md t sw, St x s L A md (sb_malloc b1 (sw1_size x)) ->
  own_ok L A t (t + 460) -> own_ok L A sw (sw + sw1_size x) -> norm_at (At_freeSW1 x t sw) s ->
  SR rsegs (mkCfg s md) R.
Proof.
  intros s L A md t sw S1 Ot Os N1.
  destruct (own_live L A sw (sw1_size x) Os) as (q & Hq & Hp).
  assert (Hpos : 0 < sw1_size x) by (unfold sw1_size; pose proof (Z.le_max_r (h_rows (hd x)) 1); lia).
  assert (OW : forall lo hi, In (lo, hi) [(t, t + 460)] -> own_ok L A lo hi /\ hi - lo <> sw1_size x)
    by (intros lo hi [E|[]]; inversion E; subst; split; [exact Ot | pose proof sw1_ne; lia]).
  apply (SR_bind rsegs _ (fpost x (fun L A => live_blk L A t 460) sw (sw1_size x) (At_raw x t PC_FREE_SW1_RET)
                           s md L A (sb_malloc b1 (sw1_size x)) q)).
  - pose proof (GF1 x t sw HST s md L A (sb_malloc b1 (sw1_size x)) q
                  (glue_pre_of x _ s md L A _ UB HTP ROW S1 N1) (own_live' L A t 460 Ot) Hq Hp) as G.
    rewrite HB in G. exact G.
  - intros c' Hc.
    destruct (STF x (fun L A => live_blk L A t 460) sw (sw1_size x) (At_raw x t PC_FREE_SW1_RET) s md L A
                (sb_malloc b1 (sw1_size x)) q [(t, t + 460)] c' HSx
                (sp_body _ (At_freeSW1 x t sw) s (fun s0 H => proj1 (proj1 H)) N1) HSc HS47 S1 Hpos Os Hq Hp
                OW Hc)
      as (s' & md' & L' & A' & -> & N' & S' & _ & Own').
    rewrite sb_free_malloc in S'.
    exact (path_raw s' L' A' md' t PC_FREE_SW1_RET S' (Own' t (t + 460) (or_introl eq_refl)) N').
Qed.

Lemma path_SW1ret : forall s L A md t sw, St x s L A md (sb_malloc b1 (sw1_size x)) ->
  own_ok L A t (t + 460) -> own_ok L A sw (sw + sw1_size x) -> norm_at (At_mallocSW1_ret x t sw) s ->
  SR rsegs (mkCfg s md) R.
Proof.
  intros s L A md t sw S1 Ot Os N1.
  st_go [(sw, sw + sw1_size x)] (At_mallocSW1_ret x t sw) (At_freeSW1 x t sw).
  - intros s0 H0. exact (SWEEP x t sw s0 H0).
  - frq.
  - intros lo hi [E|[]]. inversion E; subst. exact Os.
  - intros s' S' N'. exact (path_freeSW1 s' L A md t sw S' Ot Os N').
Qed.

Lemma path_mallocSW1 : forall s L A md t, St x s L A md b1 -> own_ok L A t (t + 460) ->
  norm_at (At_mallocSW1 x t) s -> SR rsegs (mkCfg s md) R.
Proof.
  intros s L A md t S1 Ot N1.
  assert (OW : forall lo hi, In (lo, hi) [(t, t + 460)] -> own_ok L A lo hi)
    by (intros lo hi [E|[]]; inversion E; subst; exact Ot).
  apply (SR_bind rsegs _ (mpost x (fun L A => live_blk L A t 460) (sw1_size x) (fun s => At_mallocSW1_ret x t s)
                           s md L A b1)).
  - pose proof (GM1 x t HST s md L A b1 (glue_pre_of x _ s md L A b1 UB HTP ROW S1 N1) (own_live' L A t 460 Ot)
                  R1) as G.
    rewrite HB in G. exact G.
  - intros c' Hc.
    destruct (STM x (fun L A => live_blk L A t 460) (sw1_size x) (fun s => At_mallocSW1_ret x t s) s md L A b1
                [(t, t + 460)] c' HSx (sp_body _ (At_mallocSW1 x t) s (fun s0 H => proj1 (proj1 H)) N1) HSc HS47
                S1 OW Hc)
      as (s' & md' & L' & A' & sw & -> & N' & S' & _ & Osw & Own').
    exact (path_SW1ret s' L' A' md' t sw S' (Own' t (t + 460) (or_introl eq_refl)) Osw N').
Qed.

Lemma path_E1 : forall s L A md t, St x s L A md b1 -> own_ok L A t (t + 460) ->
  norm_at (At_mallocT_ret x t) s -> SR rsegs (mkCfg s md) R.
Proof.
  intros s L A md t S1 Ot N1.
  st_go [(t, t + 460)] (At_mallocT_ret x t)
    (fun s0 => (ok (x_pl x) = true /\ At_mallocSW1 x t s0) \/ (ok (x_pl x) = false /\ At_raw x t PC_RAW_NOK s0)).
  - intros s0 H0. exact (phase_E1 INIT NSET STURN UENT UTURN ADMIT x t s0 H0).
  - frq2.
  - intros lo hi [E|[]]. inversion E; subst. exact Ot.
  - intros s' S' (s0' & [[_ H1] | [_ H1]] & Hr).
    + exact (path_mallocSW1 s' L A md t S' Ot (ex_intro _ s0' (conj H1 Hr))).
    + exact (path_raw s' L A md t PC_RAW_NOK S' Ot (ex_intro _ s0' (conj H1 Hr))).
Qed.

Lemma path_mallocT : forall s, St x s L0 A0 md0 b0 -> norm_at (At_mallocT x) s -> SR rsegs (mkCfg s md0) R.
Proof.
  intros s S1 N1.
  apply (SR_bind rsegs _ (mpost x no_live 460 (fun t => At_mallocT_ret x t) s md0 L0 A0 b0)).
  - pose proof (GMT x HST s md0 L0 A0 b0 (glue_pre_of x _ s md0 L0 A0 b0 UB HTP ROW S1 N1) I RT) as G.
    rewrite HB in G. exact G.
  - intros c' Hc.
    destruct (STM x no_live 460 (fun t => At_mallocT_ret x t) s md0 L0 A0 b0 [] c' HSx
                (sp_body _ (At_mallocT x) s (fun s0 H => proj1 H) N1) HSc HS47 S1
                (fun lo hi H => match H with end) Hc)
      as (s' & md' & L' & A' & t & -> & N' & S' & _ & Ot & _).
    exact (path_E1 s' L' A' md' t S' Ot N').
Qed.

Theorem path_all : forall se, St x se L0 A0 md0 b0 -> norm_at (At_entry x) se -> SR rsegs (mkCfg se md0) R.
Proof.
  intros se S1 N1.
  st_go (@nil (Z * Z)) (At_entry x)
    (fun s0 => (2 ^ 26 <= x_n x /\ At_ret0 x s0) \/ (x_n x < 2 ^ 26 /\ At_mallocT x s0)).
  - intros s0 H0. exact (HEAD x s0 H0).
  - frq2.
  - intros lo hi [].
  - intros s' S' (s0' & [[_ H1] | [_ H1]] & Hr).
    + exact (path_epi s' L0 A0 md0 b0 eq_refl S' (ex_intro _ s0' (conj H1 Hr))).
    + exact (path_mallocT s' S' (ex_intro _ s0' (conj H1 Hr))).
Qed.

End Path.

Lemma st_eta : forall s, ms_fregs s = fp_regs -> ms_fcsr s = fp_csr -> ms_svc_pending s = None -> ms_resv s = None ->
  s = YK11.mkst (ms_regs s) (ms_pc_val s) (ms_mem s) (ms_rom s).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Lemma ret_pc_any : forall ra, ra mod 2 = 0 -> MState.ret_pc (Z_to_bv 64 ra) = Z_to_bv 64 ra.
Proof.
  intros ra H. replace (Z_to_bv 64 ra) with (Z_to_bv 64 (ra mod 2 ^ 64)).
  - apply MState.ret_pc_even; [apply Z.mod_pos_bound; lia|].
    rewrite <- Znumtheory.Zmod_div_mod; [exact H | lia | lia | exists (2 ^ 63); reflexivity].
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    apply Z.mod_mod. lia.
Qed.

Lemma with_vmmaps_os : forall vm md, with_vmmaps vm md = os_upd vm (m_fds md) (m_fs md) (procst_statpins (m_proc md)) md.
Proof. intros vm [[] [] [] [] [] [] []]; reflexivity. Qed.

(* (e) the return: the slot state at the epilogue gives lib_post_g. *)
Definition img_free (a : Z) : Prop :=
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).

Lemma final_holds : forall ra empty pl b0 s L A md,
  lib_pre_x B API SLOT_STACK empty L0 A0 regs0 mem0 md0 ra p n pl b0 -> ra mod 2 = 0 ->
  (forall n' bb, @lib_delta LS n' bb = bb) ->
  (img_free (@sk_threaded SK) /\ (forall k, 0 <= k < 4 -> img_free (@sk_ofl_lock SK + k)) /\
   (forall k, 0 <= k < 8 -> img_free (@sk_ofl_head SH + k))) ->
  St (xent pl) s L A md b0 -> norm_at (Ep (xent pl)) s ->
  mkCfg s md = mkCfg (YK11.mkst (ms_regs s) (Z_to_bv 64 ra) (ms_mem s) (seg_rom (ms_segs B))) md /\
  lib_post_g B API [] SLOT_STACK L0 A0 regs0 mem0 md0 p n b0 (LL 0 (m_fs md0) []) L A (ms_regs s) (ms_mem s) md.
Proof.
  intros ra empty pl b0 s L A md PRE Hra LD (SKt & SKl & SKh) (RO & Hf & Hc & AS & ER & PB & RL) (s0 & HE & Hrel).
  destruct PRE as ((MR0 & WF0 & BD0 & INI0 & Hra1 & Hsp16 & HSc0 & HS63 & HWin & Htp0 & Herrw & Hp0 & Hn0 & Hpn & ROD) &
                   Hlen & Hblk & Hres & Hroom & Hsink & Hfd & Hfs & HS47).
  destruct AS as (MR & WF & BD & INI & RESs).
  destruct RL as (OUT & UB & SW & (vm & Hmd)).
  destruct Hrel as (Hregs & Hfr & Hpc & Hsvc & Hrv & Hfc & Hrom & Hmrel).
  destruct HE as (Epc & EF & EC & Erv & Esvc & E1 & E2 & E3 & E4 & Esv & E10 & Erom).
  assert (IMG : forall a, img_free a -> outside_slot a).
  { intros a (H1 & H2 & H3 & H4). pose proof (img_low a H1) as Hl.
    apply (proj1 (in_img_rsegs B a HB)) in H1 as H1'. split; [lia|]. right. left.
    split; [exact H1|]. split; [exact H2|]. split; assumption. }
  assert (OUTm : forall a, outside_slot a -> YP09.mbyte (ms_segs B) (ms_mem s) a = YP09.mbyte (ms_segs B) mem0 a).
  { intros a Ha. rewrite HB. exact (proj1 (OUT a Ha)). }
  split.
  - f_equal. rewrite (st_eta s Hf Hc ltac:(rewrite Hsvc; exact Esvc) ltac:(rewrite Hrv; exact Erv)) at 1.
    f_equal.
    + rewrite Hpc, Epc. cbn [x_ra xent]. change (PropExec.getr regs0 (Z_to_bv 5 1)) with (YK11.getr regs0 1).
      rewrite Hra1. apply ret_pc_any. exact Hra.
    + rewrite Hrom, Erom, HB. reflexivity.
  - unfold lib_post_g.
    repeat match goal with |- _ /\ _ => split end.
    + exact MR.
    + exact WF.
    + exact BD.
    + exact INI.
    + rewrite Hregs. exact E10.
    + intros r Hr. rewrite Hregs.
      unfold sregs, SREGS, xent in Esv. cbn [map x_sv] in Esv.
      injection Esv as Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
      destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
      * transitivity (Z_to_bv 64 S0); [exact E2|]. unfold S0, spZ. apply Z_to_bv_bv_unsigned.
      * exact E3.
      * exact E4.
      * exact Q8.
      * exact Q9.
      * assert (r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
          as Hr' by lia.
        destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; assumption.
    + exists vm, (m_fds md0), (procst_statpins (m_proc md0)). split; [rewrite Hmd; apply with_vmmaps_os | reflexivity].
    + exact UB.
    + intros a Ha Hns. rewrite HB. apply OUT. pose proof alloc_ceiling_value as (Hcv & _).
      split; [clear -Ha Hcv; lia|]. left. split; [clear -Ha; lia | exact Hns].
    + intros a Hi Hst Hctx Herr' _. rewrite HB. apply OUT. apply IMG. split; [exact Hi|]. split; [exact Hst|].
      split; assumption.
    + intros a (lo & len & Hin & _). destruct Hin.
    + intros q k i Hq _ Hi. rewrite HB. destruct (HA0 q k Hq) as (H1 & H2 & _).
      pose proof alloc_ceiling_lt as Hcl. apply OUT. split; [clear -H1 H2 Hi Hcl; lia|]. right. right. exists q, k.
      split; [exact Hq | clear -Hi; lia].
    + intros a [Ha | Ha].
      * rewrite HB. apply SW. unfold S0. exact Ha.
      * exact (ER a Ha).
    + reflexivity.
    + reflexivity.
    + exact Hfs.
    + destruct Hsink as ((T1 & T2) & W1 & F1). split; [split|]; [| | split].
      * intros k Hk. rewrite <- (T1 k Hk). apply OUTm, IMG. assert (k = 0%nat) by (clear -Hk; lia). subst k.
        replace (sk_threaded + Z.of_nat 0) with sk_threaded by lia. exact SKt.
      * intros k Hk. rewrite <- (T2 k Hk). apply OUTm, IMG. apply SKl. clear -Hk; lia.
      * intros k Hk. rewrite <- (W1 k Hk). apply OUTm, IMG. apply SKh. clear -Hk; lia.
      * rewrite Hmd. exact F1.
    + rewrite HB. exact RO.
    + rewrite LD. exact RESs.
    + intros i Hi. destruct Hpn as [(Hn' & _) | (Hn' & q & Hq & Hpq)]; [clear -Hn' Hi; lia|].
      destruct (HA0 q n Hq) as (H1 & H2 & _). pose proof alloc_ceiling_lt as Hcl.
      apply OUTm. split; [clear -H1 H2 Hi Hcl Hpq; lia|]. right. right. exists q, n.
      split; [exact Hq | clear -Hi Hpq; lia].
Qed.

End Chain.

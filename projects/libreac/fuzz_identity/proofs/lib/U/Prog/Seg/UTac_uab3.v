From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Definition TB_TOP : Z := 0x100000.

Lemma tb_find_segment_in : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s segs IH]; intros a n seg E; cbn in E; [discriminate|].
  match type of E with context [if ?c then _ else _] => destruct c eqn:C end.
  - injection E as <-. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
    split; [left; reflexivity | lia].
  - destruct (IH a n seg E) as (H1 & H2 & H3). split; [right; exact H1 | lia].
Qed.

Lemma tb_rsegs_ok : forallb (fun s => let r := segment_reservation s in
    (bv_unsigned (fst r) <=? Z.of_N (seg_base s)) &&
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst r) + bv_unsigned (snd r)) &&
    (bv_unsigned (fst r) + bv_unsigned (snd r) <=? TB_TOP)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tb_rsegs_nonnil : rsegs <> [].
Proof. intros H. vm_compute in H. discriminate H. Qed.

Lemma tb_rsegs_seg : forall seg, In seg rsegs ->
  bv_unsigned (fst (segment_reservation seg)) <= Z.of_N (seg_base seg) /\
  Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=
    bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)) /\
  bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)) <= TB_TOP.
Proof.
  intros seg Hin. pose proof (proj1 (forallb_forall _ _) tb_rsegs_ok seg Hin) as H. cbv beta zeta in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma tb_find_top : forall a n seg, find_segment rsegs a n = Some seg -> a + n <= TB_TOP.
Proof.
  intros a n seg E. destruct (tb_find_segment_in rsegs a n seg E) as (Hin & H1 & H2).
  destruct (tb_rsegs_seg seg Hin) as (R1 & R2 & R3). lia.
Qed.

Lemma tb_in_img_top : forall B a, ms_segs B = rsegs -> in_img B a -> 0 <= a < TB_TOP.
Proof.
  intros B a HS [_ (s & Hin & Hr)]. rewrite HS in Hin. unfold segments_reserved in Hin.
  apply in_map_iff in Hin as (seg & <- & Hseg).
  destruct (tb_rsegs_seg seg Hseg) as (R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ (fst (segment_reservation seg))) as R. lia.
Qed.

Lemma tb_find_none : forall a, TB_TOP <= a -> find_segment rsegs a 1 = None.
Proof.
  intros a Ha. destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  pose proof (tb_find_top a 1 seg E). unfold TB_TOP in *. lia.
Qed.

Lemma tb_wview_hi : forall m a, TB_TOP <= a < 2 ^ 64 -> wview rsegs m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m a Ha. unfold wview. destruct (m (Z_to_bv 64 a)) as [b|]; [reflexivity|].
  rewrite (MState.unsigned_lit a ltac:(unfold TB_TOP in Ha; lia)).
  rewrite (tb_find_none a ltac:(lia)). reflexivity.
Qed.

Lemma tb_ro_hi : forall a, TB_TOP <= a < 2 ^ 64 -> Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. unfold Mem.ro_addr. rewrite (MState.unsigned_lit a ltac:(unfold TB_TOP in Ha; lia)).
  rewrite (tb_find_none a ltac:(lia)). reflexivity.
Qed.

Lemma tb_stk : forall m lo hi, TB_TOP <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [unfold TB_TOP in Hlo; lia|]. split; [lia|]. intros a Ha.
  pose proof (H a Ha) as W. unfold writable_at in W. rewrite (tb_wview_hi m a ltac:(lia)) in W.
  unfold Mem.wa. split.
  - rewrite (tb_wview_hi m a ltac:(lia)). exact W.
  - unfold Mem.mrd. destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Lemma tb_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tb_out : forall W x lo hi, (forall y, ~ outside W y -> lo <= y < hi) -> x < lo \/ hi <= x -> outside W x.
Proof.
  intros W x lo hi H Hx. destruct (kb_outside_dec W x) as [O|N]; [exact O|].
  specialize (H x N). lia.
Qed.

Lemma tb_bytes_keep : forall W m m' a bs, bytes_at rsegs m a bs -> munch W m m' ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> outside W (a + i)) -> bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs (Ha & Hl & H) Hm Ho. split; [lia|]. split; [lia|].
  intros i Hi. specialize (H i Hi). unfold mrd in *. rewrite Hm; [exact H|].
  rewrite wa_unsigned by lia. apply Ho. lia.
Qed.

Lemma tb_munch_at : forall W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof. intros W m m' a H Ha O. apply H. rewrite (MState.unsigned_lit a Ha). exact O. Qed.

Lemma tb_mm_refl : forall l n, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros l H; [reflexivity|].
  destruct l as [|b l]; cbn in *; [lia|]. rewrite Z.eqb_refl. apply IH. lia.
Qed.

Lemma tb_mm_eq : forall l r n, firstn n l = firstn n r -> (n <= length l)%nat -> (n <= length r)%nat ->
  memcmp_model l r n = Some 0.
Proof.
  intros l r n. revert l r. induction n as [|n IH]; intros l r E Hl Hr; [reflexivity|].
  destruct l as [|a l]; destruct r as [|b r]; cbn in *; try lia.
  injection E as -> E. rewrite Z.eqb_refl. apply IH; [exact E | lia | lia].
Qed.

Lemma tb_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Lemma tb_ltu_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Lemma tb_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. lia. Qed.

Lemma tb_firstn1 : forall (l : list byte) k, (k < length l)%nat -> firstn 1 (skipn k l) = [nthb l k].
Proof.
  intros l. induction l as [|x l IH]; intros [|k] Hk; cbn in *; try lia; [reflexivity|].
  apply IH. lia.
Qed.

Lemma tb_rd1 : forall m a bs k, bytes_at rsegs m a bs -> 0 <= k -> (Z.to_nat k < length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nthb bs (Z.to_nat k)].
Proof.
  intros m a bs k H Hk Hl. rewrite (bytes_at_read rsegs m a bs k 1 H Hk) by lia.
  rewrite tb_firstn1 by lia. reflexivity.
Qed.

Lemma tb_rd8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H. pose proof (bytes_at_read rsegs m a (le8 v) 0 8 H ltac:(lia)) as R.
  rewrite Z.add_0_r in R. change (Z.to_nat 0) with 0%nat in R. rewrite skipn_O in R.
  rewrite R by (rewrite length_le8; lia). all: try reflexivity.
  all: f_equal; apply firstn_all2; rewrite length_le8; lia.
Qed.

Lemma tb_addr_range : forall inp i, 0 <= rec_addr inp i < 65536.
Proof.
  intros inp i. unfold rec_addr, pick, rec_raw, h_raw, h_lo, h_hi.
  pose proof (inb_range inp (rec_c inp i)). pose proof (inb_range inp (rec_c inp i + 1)).
  unfold ADDR_FIRMWARE, ADDR_REAC_VERSION, ADDR_MODEL_NAME.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Lemma tb_ing0_ver : forall idb p, fst (ING idb ADDR_REAC_VERSION p) = 0 -> (length p < 8)%nat.
Proof.
  intros idb p H. rewrite ING_ver_dispatch in H. unfold ing_version in H.
  destruct (Nat.leb_spec REAC_VER_LEN (length p)) as [E|E]; [discriminate H | unfold REAC_VER_LEN in E; lia].
Qed.

Lemma tb_rec_hw_r0 : forall inp i, rec_r inp i = 0 -> rec_hw inp (S i) = rec_hw inp i.
Proof.
  intros inp i Hr. cbn [rec_hw]. pose proof (rec_pl_length inp i) as Hl. pose proof (rec_k_range inp i) as Hk.
  destruct (Z.eqb_spec (rec_addr inp i) ADDR_REAC_VERSION) as [Ea|Ea]; cbn [andb]; [|reflexivity].
  unfold rec_r in Hr. rewrite Ea in Hr. pose proof (tb_ing0_ver _ _ Hr) as Hs.
  destruct (Z.leb_spec 8 (rec_k inp i)); [lia | reflexivity].
Qed.

Ltac tb_psplit := repeat match goal with |- bytes_at _ _ _ _ => fail 1 | |- _ /\ _ => split end.

Ltac tb_out_side :=
  intros; unfold spk, fsp, SLOT_FRAME in *; rewrite ?length_le8, ?length_le4, ?length_app in *;
  cbn [outside length] in *; repeat split; try exact I; lia.

Ltac tb_keep MU :=
  match goal with |- bytes_at rsegs ?m' ?a ?bs =>
    match goal with H : bytes_at rsegs ?m a bs |- _ =>
      apply (tb_bytes_keep _ m m' a bs H MU); tb_out_side end end.

Ltac tb_regs HRL :=
  repeat (let h := fresh "R" in apply Forall_cons_iff in HRL; destruct HRL as [h HRL]; cbn [fst snd] in h).

Section T.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma tb_segs : ms_segs B = rsegs.
Proof. exact (proj1 FF). Qed.

Lemma tb_relro_img : forall a, in_globals frame_RELRO a -> in_img B a.
Proof.
  intros a H. destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & HR & _). exact (proj1 (HR a H)).
Qed.

Lemma tb_sink_addrs : @sk_ofl_head SH = 0x50b70 /\ @sk_ofl_lock SK = 0x50b68 /\ @sk_threaded SK = 0x50740 + 1.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _).
  auto.
Qed.

Lemma tb_alloc : frame_allocator B (APIf rc).
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact (H rc fx).
Qed.

Lemma tb_FR_kA : forall g km hb L A regs mem md regs' mem' W,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  getr regs' 2 = Z_to_bv 64 (fsp g) -> getr regs' 3 = getr (g_regs g) 3 -> getr regs' 4 = getr (g_regs g) 4 ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall x, ~ outside W x -> g_S g - SLOT_K <= x < g_S g - 104) ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' W HF HP E2 E3 E4 MU WM RO HW.
  pose proof tb_segs as SEGS.
  destruct HF as (HGV & _ & _ & _ & Hsv & _ & _ & Hrelro & HM & HWF & Hbd & Hid & Hmd & Hhigh & Himg & Hblk &
    Herr & Hsink & Hres & Hstw).
  pose proof HGV as (Hn & _ & _ & HS16 & HSc & HS47 & _ & _ & _).
  pose proof alloc_ceiling_value as Hac.
  unfold SLOT_K, SLOT_STACK in *.
  assert (OUT : forall x, x < g_S g - 65536 -> outside W x).
  { intros x Hx. apply (tb_out W x (g_S g - 65536) (g_S g - 104) HW). lia. }
  assert (OUTH : forall x, g_S g - 104 <= x -> outside W x).
  { intros x Hx. apply (tb_out W x (g_S g - 65536) (g_S g - 104) HW). lia. }
  assert (EQ : forall x, 0 <= x < 2 ^ 64 -> outside W x ->
     mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\
     (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)).
  { intros x Hx O. pose proof (tb_munch_at W mem mem' x MU Hx O) as E.
    unfold mbyte, writable_at, wview. rewrite E. tauto. }
  assert (WM' : forall x, writable_at (ms_segs B) mem x -> writable_at (ms_segs B) mem' x).
  { intros x Hw. unfold writable_at in *. rewrite SEGS in *. apply WM. exact Hw. }
  assert (LOW : forall x, 0 <= x < alloc_ceiling -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x).
  { intros x Hx. apply EQ; [lia|]. apply OUT. lia. }
  assert (Hstw' : forall a, g_S g - 65536 <= a < g_S g -> writable_at (ms_segs B) mem' a).
  { intros a Ha. apply WM'. apply Hstw. lia. }
  unfold FR; cbv zeta; unfold SLOT_K, SLOT_STACK.
  split; [exact HGV|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
  split.
  { apply (tb_bytes_keep W mem mem' _ _ Hsv MU). intros i Hi. apply OUTH. lia. }
  split.
  { unfold SLOT_K, SLOT_STACK. apply tb_stk; [unfold TB_TOP; lia | lia |]. intros a Ha. rewrite <- SEGS.
    apply Hstw'. lia. }
  split.
  { unfold MI. rewrite SEGS. exact RO. }
  split.
  { unfold relro, G_img_c in *. intros a Ha. pose proof (tb_in_img_top B a SEGS (tb_relro_img a Ha)) as Ht.
    unfold TB_TOP in Ht. rewrite (LOW a ltac:(lia)). exact (Hrelro a Ha). }
  split.
  { apply (kb_MR_A B (APIf rc) L A mem mem' md W HM MU). intros x Hx _. apply OUT. lia. }
  split; [exact HWF|]. split; [exact Hbd|]. split; [exact Hid|]. split; [exact Hmd|].
  split.
  { intros a Ha Hns Hne. destruct (Hhigh a Ha Hns Hne) as [F1 F2].
    assert (O : outside W a).
    { apply (tb_out W a (g_S g - 65536) (g_S g - 104) HW). lia. }
    destruct (EQ a ltac:(lia) O) as [E1 E1w]. split; [rewrite E1; exact F1 | rewrite F2; exact E1w]. }
  split.
  { intros a H1 H2 H3 H4. destruct (Himg a H1 H2 H3 H4) as [F1 F2].
    pose proof (tb_in_img_top B a SEGS H1) as Ht. unfold TB_TOP in Ht.
    destruct (EQ a ltac:(lia) (OUT a ltac:(lia))) as [E1 E1w].
    split; [rewrite E1; exact F1 | rewrite F2; exact E1w]. }
  split.
  { intros a k i Hin Hi.
    assert (Hin' : In (a, k) (blocks L A)).
    { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin. }
    assert (HO : forall x, 0 <= x < alloc_ceiling -> (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
       outside W x) by (intros x Hx _; apply OUT; lia).
    rewrite (kb_blocks_munch B (APIf rc) L A mem mem' md W HM MU HO a k i Hin' Hi).
    exact (Hblk a k i Hin Hi). }
  split; [intros a Ha; apply WM'; exact (Herr a Ha)|].
  split.
  { destruct tb_sink_addrs as (S1 & S2 & S3).
    destruct Hsink as ((T1 & T2) & T3 & T4). split; [split|split; [|exact T4]].
    - intros k Hk. rewrite LOW by (rewrite S3; lia). exact (T1 k Hk).
    - intros k Hk. rewrite LOW by (rewrite S2; lia). exact (T2 k Hk).
    - intros k Hk. rewrite LOW by (rewrite S1; lia). exact (T3 k Hk). }
  split; [exact Hres|].
  exact Hstw'.
Qed.

Definition XQ (g : ghost) (mem : word -> option byte) (pcX : Z) (W : list (Z * Z)) (RL : list (reg * word))
    (BL : list (Z * list byte)) (ms : machine_state) : Prop :=
  exists R m0', ms = MState.MS R fp_regs (Z_to_bv 64 pcX) fp_csr None m0' (seg_rom rsegs) /\
    getr R 2 = Z_to_bv 64 (fsp g) /\ getr R 3 = getr (g_regs g) 3 /\ getr R 4 = getr (g_regs g) 4 /\
    Forall (fun p : reg * word => getr R (fst p) = snd p) RL /\
    munch W (normalize rsegs mem) m0' /\ wmono rsegs (normalize rsegs mem) m0' /\
    Forall (fun p : Z * list byte => bytes_at rsegs m0' (fst p) (snd p)) BL.

Lemma tb_seg : forall g pcE pcX km hb (PE PX : bvmap 5 word -> (word -> option byte) -> Prop) c,
  CUTST B APIf ra empty g pcE km hb PE c ->
  (forall L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
     Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> PE regs mem ->
     exists W RL BL,
       (forall x, ~ outside W x -> g_S g - SLOT_K <= x < g_S g - 104) /\
       Exec.evt rsegs (XQ g mem pcX W RL BL)
         (MState.MS (rmk regs) fp_regs (Z_to_bv 64 pcE) fp_csr None (normalize rsegs mem) (seg_rom rsegs)) /\
       (forall regs' mem', Forall (fun p : reg * word => getr regs' (fst p) = snd p) RL -> munch W mem mem' ->
          Forall (fun p : Z * list byte => bytes_at rsegs mem' (fst p) (snd p)) BL -> PX regs' mem')) ->
  (forall c', CUTST B APIf ra empty g pcX km hb PX c' -> Rz (ms_segs B) c' (Post B APIf ra g)) ->
  Rz (ms_segs B) c (Post B APIf ra g).
Proof.
  intros g pcE pcX km hb PE PX c HC HK HX.
  destruct HC as (L & A & regs & mem & md & -> & HF & HP & HPE).
  destruct (HK L A regs mem md HF HP HPE) as (W & RL & BL & HW & HE & HG).
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  destruct (kb_md B (APIf rc) L A mem md HM) as [Hh Hl].
  pose proof tb_segs as SEGS.
  assert (HRO : ro_agree rsegs mem) by (unfold MI in HMI; rewrite SEGS in HMI; exact HMI).
  apply (kb_run_rz B regs (Z_to_bv 64 pcE) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 pcX /\ getr R 2 = Z_to_bv 64 (fsp g) /\
       getr R 3 = getr (g_regs g) 3 /\ getr R 4 = getr (g_regs g) 4 /\
       Forall (fun p : reg * word => getr R (fst p) = snd p) RL /\ munch W mem mem' /\ wmono rsegs mem mem' /\
       ro_agree rsegs mem' /\ Forall (fun p : Z * list byte => bytes_at rsegs mem' (fst p) (snd p)) BL) _ Hh Hl).
  - rewrite SEGS. eapply Exec.evt_mono; [exact (evt_normalize rsegs _ _ _ _ _ _ mem _ tb_wx HRO HE)|].
    intros s (s0 & (R & m0' & -> & E2 & E3 & E4 & HRL & MU & WM & HBL) & Hrel & Hsame).
    destruct s as [sr sf sp ss sv sc sm so].
    destruct Hrel as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *. subst.
    exists R, (Z_to_bv 64 pcX), sm. split; [reflexivity|].
    pose proof (mem_rel_normalize rsegs mem HRO) as HR0.
    split; [reflexivity|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact HRL|].
    split; [exact (munch_rel rsegs W mem (normalize rsegs mem) sm m0' HR0 Q8 Hsame MU)|].
    split; [exact (wmono_rel rsegs mem (normalize rsegs mem) sm m0' HR0 Q8 Hsame WM)|].
    split; [exact (ro_agree_same rsegs mem sm HRO Hsame)|].
    eapply Forall_impl; [|exact HBL]. intros [a bs] Hb. exact (proj2 (bytes_at_rel rsegs sm m0' a bs Q8) Hb).
  - intros R pc' mem' regs' (-> & E2 & E3 & E4 & HRL & MU & WM & RO' & HBL) HG'.
    apply HX. exists L, A, regs', mem', md. split; [reflexivity|].
    split.
    { apply (tb_FR_kA g km hb L A regs mem md regs' mem' W HF HP); try assumption; rewrite HG'; assumption. }
    split; [exact HP|].
    apply HG; [| exact MU | exact HBL].
    eapply Forall_impl; [|exact HRL]. intros [r v] Hr. cbn in *. rewrite HG'. exact Hr.
Qed.

Lemma tb_norm_frame : forall g km hb L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  ro_agree rsegs mem /\ mem_inv rsegs (normalize rsegs mem) /\
  wr_at rsegs (normalize rsegs mem) (g_S g - SLOT_K) SLOT_K /\
  stk rsegs (normalize rsegs mem) (g_S g - SLOT_K) (g_S g).
Proof.
  intros g km hb L A regs mem md HF. pose proof tb_segs as SEGS.
  destruct HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstw).
  pose proof HGV as (_ & _ & _ & _ & HSc & HS47 & _ & _ & _).
  pose proof alloc_ceiling_value as Hac. unfold SLOT_K, SLOT_STACK in *.
  assert (HRO : ro_agree rsegs mem) by (unfold MI in HMI; rewrite SEGS in HMI; exact HMI).
  assert (WR : wr_at rsegs (normalize rsegs mem) (g_S g - 65536) 65536).
  { apply (wr_at_norm rsegs mem (normalize rsegs mem) _ _ (mem_rel_normalize rsegs mem HRO)).
    - split; [lia|]. split; [lia|]. intros i Hi. pose proof (Hstw (g_S g - 65536 + i) ltac:(lia)) as H.
      unfold writable_at in H. rewrite SEGS in H. exact H.
    - intros i Hi. unfold Mem.wa. apply tb_ro_hi. unfold TB_TOP. lia. }
  split; [exact HRO|]. split; [apply mem_inv_normalize|]. split; [exact WR|].
  apply tb_stk; [unfold TB_TOP; lia | lia |]. intros a Ha. destruct WR as (_ & _ & H).
  pose proof (H (a - (g_S g - 65536)) ltac:(lia)) as H1. unfold writable_at.
  replace (g_S g - 65536 + (a - (g_S g - 65536))) with a in H1 by lia. exact H1.
Qed.

End T.

Lemma n_bytes_at_skipn : forall m a bs k a', bytes_at rsegs m a bs -> (k <= length bs)%nat ->
  a' = a + Z.of_nat k -> bytes_at rsegs m a' (skipn k bs).
Proof.
  intros m a bs k a' H Hk ->. rewrite <- (firstn_skipn k bs) in H.
  apply bytes_at_app in H as [_ H]. rewrite length_firstn in H.
  replace (Nat.min k (length bs)) with k in H by lia. exact H.
Qed.

Lemma n_fz_len : forall l, (RcIdentModel.first_zero l <= length l)%nat.
Proof.
  induction l as [|b l IH]; cbn [RcIdentModel.first_zero length]; [lia|].
  destruct (RcIdentModel.bz b =? 0); lia.
Qed.

Lemma n_fz_prefix : forall l r,
  RcIdentModel.first_zero (firstn (RcIdentModel.first_zero l) l ++ RcIdentModel.zb 0 :: r) =
  RcIdentModel.first_zero l.
Proof.
  induction l as [|b l IH]; intros r; [reflexivity|].
  cbn [RcIdentModel.first_zero].
  destruct (RcIdentModel.bz b =? 0) eqn:E; [reflexivity|].
  cbn [firstn app RcIdentModel.first_zero]. rewrite E. cbv iota. f_equal. apply IH.
Qed.

Lemma n_name_len_fz : forall p, RcIdentModel.name_len p =
  RcIdentModel.first_zero (firstn (Nat.min (length p - 1) (RcIdentModel.NAME_CAP - 1)) (skipn 1 p)).
Proof.
  intro p. unfold RcIdentModel.name_len. cbv zeta.
  pose proof (n_fz_len (firstn (Nat.min (length p - 1) (RcIdentModel.NAME_CAP - 1)) (skipn 1 p))) as H.
  rewrite length_firstn in H. lia.
Qed.

Lemma n_name_fz : forall p r,
  RcIdentModel.first_zero (firstn (RcIdentModel.name_len p) (skipn 1 p) ++ RcIdentModel.zb 0 :: r) =
  RcIdentModel.name_len p.
Proof.
  intros p r.
  replace (firstn (RcIdentModel.name_len p) (skipn 1 p)) with
    (firstn (RcIdentModel.name_len p) (firstn (Nat.min (length p - 1) (RcIdentModel.NAME_CAP - 1)) (skipn 1 p))).
  2: { rewrite firstn_firstn. f_equal. unfold RcIdentModel.name_len. cbv zeta. lia. }
  rewrite n_name_len_fz. apply n_fz_prefix.
Qed.

Lemma n_get_upd : forall (l bs : list byte) off m, (off + length bs <= length l)%nat -> (length bs <= m)%nat ->
  exists r, RcIdentModel.get (RcIdentModel.upd l off bs) off m = bs ++ r.
Proof.
  intros l bs off m H1 H2. unfold RcIdentModel.get, RcIdentModel.upd.
  rewrite skipn_app, length_firstn.
  assert (E : skipn off (firstn off l) = []) by (apply skipn_all2; rewrite length_firstn; lia).
  rewrite E. replace (off - Nat.min off (length l))%nat with 0%nat by lia.
  replace (skipn 0 (bs ++ skipn (off + length bs) l)) with (bs ++ skipn (off + length bs) l) by reflexivity.
  cbn [List.app]. exists (firstn (m - length bs) (skipn (off + length bs) l)).
  rewrite firstn_app. f_equal. apply firstn_all2. lia.
Qed.

Lemma n_nma : forall inp i, rec_r inp i = 1 -> rec_addr inp i = RcIdentModel.ADDR_MODEL_NAME ->
  RcIdentModel.has_model_name (rec_id inp (S i)) = 1 /\
  wn (rec_id inp (S i)) = Z.of_nat (RcIdentModel.name_len (rec_pl inp i)) /\
  (1 <= RcIdentModel.name_len (rec_pl inp i))%nat /\
  (RcIdentModel.name_len (rec_pl inp i) + 1 <= length (rec_pl inp i))%nat /\
  firstn (RcIdentModel.name_len (rec_pl inp i)) (skipn 3 (rec_id inp (S i))) =
    firstn (RcIdentModel.name_len (rec_pl inp i)) (skipn 1 (rec_pl inp i)).
Proof.
  intros inp i Hr Ha. unfold rec_r in Hr. cbn [rec_id]. rewrite Ha in *.
  pose proof (rec_id_length inp i) as Lid. revert Hr Lid.
  generalize (rec_id inp i) (rec_pl inp i). intros idb p Hr Lid.
  pose proof (name_len_le p) as [Wa Wb].
  change (RcIdentModel.ING idb RcIdentModel.ADDR_MODEL_NAME p) with (RcIdentModel.ing_name idb p) in *.
  unfold RcIdentModel.ing_name in *. cbv zeta in *. revert Hr.
  destruct ((2 <=? length p)%nat && (1 <=? RcIdentModel.name_len p)%nat) eqn:C; cbn [fst snd]; intros Hr;
    [|discriminate Hr].
  apply andb_true_iff in C as [C1 C2]. apply Nat.leb_le in C1. apply Nat.leb_le in C2.
  set (w := RcIdentModel.name_len p) in *.
  set (X := firstn w (skipn 1 p) ++ [RcIdentModel.zb 0]).
  assert (LA : length (firstn w (skipn 1 p)) = w) by (rewrite length_firstn, length_skipn; lia).
  assert (LX : length X = S w) by (unfold X; rewrite length_app, LA; cbn [length]; lia).
  unfold RcIdentModel.OFF_NAME, RcIdentModel.OFF_HAS_NAME, RcIdentModel.ID_SIZE in *.
  assert (LU : length (RcIdentModel.upd idb 3 X) = 38%nat) by (rewrite RcIdentModel.upd_length; lia).
  destruct (n_get_upd idb X 3 17) as [r Er]; [lia|lia|].
  split.
  { unfold RcIdentModel.has_model_name, RcIdentModel.nthb, RcIdentModel.OFF_HAS_NAME.
    rewrite nth_upd_in by (rewrite ?LU; cbn [length]; lia). reflexivity. }
  split.
  { unfold wn. f_equal. unfold RcIdentModel.model_name, RcIdentModel.OFF_NAME, RcIdentModel.NAME_CAP.
    rewrite get_upd_after by (rewrite ?LU; lia). rewrite Er. unfold X. rewrite <- app_assoc. cbn [app].
    apply n_name_fz. }
  split; [exact C2|]. split; [lia|].
  transitivity (firstn w (RcIdentModel.get (RcIdentModel.upd (RcIdentModel.upd idb 3 X) 20 [RcIdentModel.zb 1]) 3 17)).
  { unfold RcIdentModel.get. rewrite firstn_firstn. f_equal. lia. }
  rewrite get_upd_after by (rewrite ?LU; lia). rewrite Er. unfold X. rewrite <- app_assoc.
  rewrite firstn_app, LA, Nat.sub_diag, firstn_O, app_nil_r.
  apply firstn_all2. rewrite LA. lia.
Qed.

Lemma v1_bz_zb : forall x, RcIdentModel.bz (RcIdentModel.zb x) = x mod 256.
Proof. intros x. unfold RcIdentModel.bz, RcIdentModel.zb. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma v1_le16 : forall v, 0 <= v < 65536 ->
  RcIdentModel.bz (nth 0 (RcIdentModel.le16 v) (RcIdentModel.zb 0)) +
  256 * RcIdentModel.bz (nth 1 (RcIdentModel.le16 v) (RcIdentModel.zb 0)) = v.
Proof. intros v Hv. unfold RcIdentModel.le16. cbn [nth]. rewrite !v1_bz_zb. Z.div_mod_to_equations. lia. Qed.

Definition v1_U (l r A M C : list byte) : list byte :=
  RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd l 28 r) 22 A) 24 M)
    26 C) 36 [RcIdentModel.zb 1].

Lemma v1_nth_ver : forall (l r A M C : list byte) j,
  length l = 38%nat -> length r = 8%nat -> length A = 2%nat -> length M = 2%nat -> length C = 2%nat -> (j < 2)%nat ->
  RcIdentModel.nthb (v1_U l r A M C) (22 + j) = nth j A (RcIdentModel.zb 0) /\
  RcIdentModel.nthb (v1_U l r A M C) (24 + j) = nth j M (RcIdentModel.zb 0) /\
  RcIdentModel.nthb (v1_U l r A M C) (26 + j) = nth j C (RcIdentModel.zb 0).
Proof.
  intros l r A M C j Hl Hr HA HM HC Hj. unfold v1_U, RcIdentModel.nthb.
  assert (L1 : length (RcIdentModel.upd l 28 r) = 38%nat) by (rewrite RcIdentModel.upd_length; lia).
  assert (L2 : length (RcIdentModel.upd (RcIdentModel.upd l 28 r) 22 A) = 38%nat)
    by (rewrite RcIdentModel.upd_length; lia).
  assert (L3 : length (RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd l 28 r) 22 A) 24 M) = 38%nat)
    by (rewrite RcIdentModel.upd_length; lia).
  assert (L4 : length (RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd l 28 r) 22 A) 24 M)
    26 C) = 38%nat) by (rewrite RcIdentModel.upd_length; lia).
  split; [|split].
  - rewrite nth_upd_before by lia. rewrite nth_upd_before by lia. rewrite nth_upd_before by lia.
    rewrite nth_upd_in by lia. f_equal. lia.
  - rewrite nth_upd_before by lia. rewrite nth_upd_before by lia. rewrite nth_upd_in by lia. f_equal. lia.
  - rewrite nth_upd_before by lia. rewrite nth_upd_in by lia. f_equal. lia.
Qed.

Lemma v1_vb : forall inp i, rec_r inp i = 1 -> rec_addr inp i = RcIdentModel.ADDR_REAC_VERSION ->
  (8 <= length (rec_pl inp i))%nat /\
  RcIdentModel.has_reac_version (rec_id inp (S i)) = 1 /\
  RcIdentModel.raw (rec_id inp (S i)) = firstn 8 (rec_pl inp i) /\
  RcIdentModel.major (rec_id inp (S i)) =
    RcIdentModel.be16 (RcIdentModel.nthb (rec_pl inp i) 2) (RcIdentModel.nthb (rec_pl inp i) 3) /\
  RcIdentModel.minor (rec_id inp (S i)) =
    RcIdentModel.be16 (RcIdentModel.nthb (rec_pl inp i) 4) (RcIdentModel.nthb (rec_pl inp i) 5) /\
  RcIdentModel.patch (rec_id inp (S i)) =
    RcIdentModel.be16 (RcIdentModel.nthb (rec_pl inp i) 6) (RcIdentModel.nthb (rec_pl inp i) 7).
Proof.
  intros inp i Hr Ha. unfold rec_r in Hr. cbn [rec_id]. rewrite Ha in *.
  pose proof (rec_id_length inp i) as Hl.
  destruct (Nat.lt_ge_cases (length (rec_pl inp i)) 8) as [Hs|Hs].
  { rewrite (ING_ver_short _ _ Hs) in Hr. cbn [fst] in Hr. discriminate. }
  destruct (ING_ver_long _ _ Hl Hs) as (H1 & H2 & _).
  split; [exact Hs|]. split; [exact H1|]. split; [exact H2|].
  rewrite ING_ver_dispatch. unfold RcIdentModel.ing_version.
  destruct (Nat.leb_spec RcIdentModel.REAC_VER_LEN (length (rec_pl inp i))) as [E|E];
    [|unfold RcIdentModel.REAC_VER_LEN in E; lia].
  cbn [snd]. unfold RcIdentModel.OFF_RAW, RcIdentModel.OFF_MAJOR, RcIdentModel.OFF_MINOR, RcIdentModel.OFF_PATCH,
    RcIdentModel.OFF_HAS_VER, RcIdentModel.REAC_VER_LEN.
  set (pv := rec_pl inp i) in *.
  assert (Hr8 : length (firstn 8 pv) = 8%nat) by (rewrite length_firstn; lia).
  destruct (v1_nth_ver (rec_id inp i) (firstn 8 pv)
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 2) (RcIdentModel.nthb pv 3)))
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 4) (RcIdentModel.nthb pv 5)))
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 6) (RcIdentModel.nthb pv 7))) 0
    Hl Hr8 eq_refl eq_refl eq_refl ltac:(lia)) as (A0 & M0 & C0).
  destruct (v1_nth_ver (rec_id inp i) (firstn 8 pv)
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 2) (RcIdentModel.nthb pv 3)))
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 4) (RcIdentModel.nthb pv 5)))
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 6) (RcIdentModel.nthb pv 7))) 1
    Hl Hr8 eq_refl eq_refl eq_refl ltac:(lia)) as (A1 & M1 & C1).
  unfold v1_U in A0, M0, C0, A1, M1, C1. cbn [Nat.add] in A0, M0, C0, A1, M1, C1.
  unfold RcIdentModel.major, RcIdentModel.minor, RcIdentModel.patch.
  rewrite A0, A1, M0, M1, C0, C1.
  pose proof (bz_range (RcIdentModel.nthb pv 2)). pose proof (bz_range (RcIdentModel.nthb pv 3)).
  pose proof (bz_range (RcIdentModel.nthb pv 4)). pose proof (bz_range (RcIdentModel.nthb pv 5)).
  pose proof (bz_range (RcIdentModel.nthb pv 6)). pose proof (bz_range (RcIdentModel.nthb pv 7)).
  unfold RcIdentModel.be16. split; [|split]; apply v1_le16; lia.
Qed.

Lemma v1_mmp : forall x, 0 <= RcIdentModel.major x < 65536 /\ 0 <= RcIdentModel.minor x < 65536 /\
  0 <= RcIdentModel.patch x < 65536.
Proof.
  intros x. unfold RcIdentModel.major, RcIdentModel.minor, RcIdentModel.patch.
  pose proof (bz_range (RcIdentModel.nthb x 22)). pose proof (bz_range (RcIdentModel.nthb x 23)).
  pose proof (bz_range (RcIdentModel.nthb x 24)). pose proof (bz_range (RcIdentModel.nthb x 25)).
  pose proof (bz_range (RcIdentModel.nthb x 26)). pose proof (bz_range (RcIdentModel.nthb x 27)).
  lia.
Qed.

Lemma v1_dd_len : forall f x, (length (dec_digits f x) <= f)%nat.
Proof.
  induction f as [|f IH]; intros x; cbn [dec_digits]; [cbn [length]; lia|].
  rewrite length_app. destruct (x <? 10); cbn [length]; [lia|]. specialize (IH (x / 10)). lia.
Qed.

Lemma v1_DEC_len : forall x m, 0 <= x < 65536 -> 0 <= m <= 16 -> (length (DEC x m) <= 16)%nat.
Proof.
  intros x m Hx Hm. unfold DEC. rewrite length_app, repeat_length.
  pose proof (v1_dd_len (S (Z.to_nat (Z.log2 x))) x) as H.
  assert (L : Z.log2 x < 16).
  { destruct (Z.eq_dec x 0) as [->|Hx0]; [cbn; lia|].
    apply Z.log2_lt_pow2; [lia|]. change (2 ^ 16) with 65536. lia. }
  pose proof (Z.log2_nonneg x). lia.
Qed.

Lemma v1_wr_sub : forall segs m a n a' n', wr_at segs m a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n ->
  wr_at segs m a' n'.
Proof.
  intros segs m a n a' n' (H1 & H2 & H) Ha Hn Hb. split; [lia|]. split; [lia|]. intros j Hj.
  replace (a' + j) with (a + (a' - a + j)) by lia. apply H. lia.
Qed.

Lemma v1_stk_sub : forall segs m lo hi lo' hi', stk segs m lo hi -> lo <= lo' -> hi' <= hi -> stk segs m lo' hi'.
Proof. intros segs m lo hi lo' hi' (H1 & H2 & H) Hl Hh. split; [lia|]. split; [lia|]. intros a Ha. apply H. lia. Qed.

Lemma v1_st_ok : forall segs m a n x (j : nat), wr_at segs m a n -> a <= x -> x + Z.of_nat j <= a + n ->
  store_ok segs m (wa x) j = true.
Proof.
  intros segs m a n x j H Hx Hj. replace x with (a + (x - a)) by lia.
  apply (wr_at_store_ok segs m a n); [exact H | lia | lia].
Qed.

Ltac v1_br b :=
  lazymatch goal with
  | |- Exec.evt _ _ (MState.MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry]
  end.

Ltac v1_keep MU :=
  match goal with |- bytes_at rsegs ?m' ?a ?bs =>
    match goal with H : bytes_at rsegs ?m a bs |- _ =>
      apply (tb_bytes_keep _ m m' a bs H MU); intros;
      unfold spk, fsp, SLOT_FRAME in *;
      rewrite ?length_le8, ?length_le4, ?rec_id_length, ?rec_pl_length in *; unfold RcIdentModel.ID_SIZE in *;
      cbn [outside length] in *; repeat split; try exact I; lia end end.

Section Tac_v1.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma v1_pl_low : forall g km i pl L A regs mem md,
  FR B APIf ra empty g km (hb_pl g i pl) L A regs mem md ->
  Permutation (blocks L A) (hb_pl g i pl ++ blocks (g_L g) (g_A g)) ->
  0 <= pl /\ pl + Z.of_nat (length (rec_pl (g_in g) i)) <= alloc_ceiling.
Proof.
  intros g km i pl L A regs mem md HF HP.
  destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  assert (Hin : In (pl, rec_k (g_in g) i) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. left. reflexivity. }
  unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & Eq & Hq). cbn [fst snd] in Eq. injection Eq as Eq1 Eq2.
  destruct (mr_blocks_range _ _ (aa_laws (APIf rc)) _ _ _ _ q k' HM Hq) as [R1 R2].
  rewrite Eq1 in R1, R2. rewrite Eq2 in R2.
  rewrite rec_pl_length, Z2Nat.id by (apply rec_k_range). split; [lia | exact R2].
Qed.

End Tac_v1.

Lemma v2_lsd_len : forall k v, (length (lib.Prog.write_uint_c.write_uint_lsd k v) <= k)%nat.
Proof.
  induction k as [|k IH]; intros v; cbn [lib.Prog.write_uint_c.write_uint_lsd length]; [lia|].
  destruct (v <? 10); cbn [length]; [lia|]. specialize (IH (v / 10)). lia.
Qed.

Lemma v2_D_len : forall v, (length (lib.Prog.write_uint_c.write_uint_D v) <= 5)%nat.
Proof. intros v. unfold lib.Prog.write_uint_c.write_uint_D. rewrite length_rev. apply v2_lsd_len. Qed.

Lemma v2_LV : forall ma mi pa, 0 <= lib.Prog.reac_identity_reac_ver_str_c.reac_ver_str_LV ma mi pa <= 16.
Proof.
  intros ma mi pa. unfold lib.Prog.reac_identity_reac_ver_str_c.reac_ver_str_LV, lib.Prog.reac_identity_reac_ver_str_c.reac_ver_str_VER,
    lib.Prog.reac_identity_reac_ver_str_c.reac_ver_str_DEC2.
  pose proof (v2_D_len ma). pose proof (v2_D_len mi). pose proof (v2_D_len pa).
  rewrite !length_app. cbn [length]. destruct (pa <? 10); cbn [length]; lia.
Qed.

Lemma v2_dec_all : z_all (fun v => bytes_eqb (DEC v 1) (lib.Prog.write_uint_c.write_uint_D v) &&
    bytes_eqb (DEC v 2) (lib.Prog.reac_identity_reac_ver_str_c.reac_ver_str_DEC2 v)) (Z.to_nat 65536) 0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma v2_DEC : forall v, 0 <= v < 65536 ->
  DEC v 1 = lib.Prog.write_uint_c.write_uint_D v /\ DEC v 2 = lib.Prog.reac_identity_reac_ver_str_c.reac_ver_str_DEC2 v.
Proof.
  intros v Hv. pose proof (z_all_spec _ _ _ v2_dec_all v ltac:(rewrite Z2Nat.id by lia; lia)) as H.
  cbv beta in H. apply andb_true_iff in H as [H1 H2]. split; apply bytes_eqb_eq; assumption.
Qed.

Lemma v2_mmp : forall idb, 0 <= RcIdentModel.major idb < 65536 /\ 0 <= RcIdentModel.minor idb < 65536 /\
  0 <= RcIdentModel.patch idb < 65536.
Proof.
  intros idb. unfold RcIdentModel.major, RcIdentModel.minor, RcIdentModel.patch.
  pose proof (bz_range (RcIdentModel.nthb idb 22)). pose proof (bz_range (RcIdentModel.nthb idb 23)).
  pose proof (bz_range (RcIdentModel.nthb idb 24)). pose proof (bz_range (RcIdentModel.nthb idb 25)).
  pose proof (bz_range (RcIdentModel.nthb idb 26)). pose proof (bz_range (RcIdentModel.nthb idb 27)). lia.
Qed.

Lemma v2_EV : forall idb, EV idb = id_VER idb.
Proof.
  intros idb. destruct (v2_mmp idb) as (H1 & H2 & H3).
  destruct (v2_DEC _ H1) as [A1 _]. destruct (v2_DEC _ H2) as [A2 _]. destruct (v2_DEC _ H3) as [_ A3].
  unfold EV, EV2, EV1, id_VER, lib.Prog.reac_identity_reac_ver_str_c.reac_ver_str_VER.
  rewrite A1, A2, A3. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma v2_EV_len : forall idb, zlen (EV idb) = lib.Prog.reac_identity_reac_ver_str_c.reac_ver_str_LV
  (RcIdentModel.major idb) (RcIdentModel.minor idb) (RcIdentModel.patch idb).
Proof. intros idb. rewrite v2_EV. reflexivity. Qed.

Lemma v2_sok : forall m lo n a (j : nat), wr_at rsegs m lo n -> lo <= a -> a + Z.of_nat j <= lo + n ->
  store_ok rsegs m (wa a) j = true.
Proof.
  intros m lo n a j H H1 H2. replace a with (lo + (a - lo)) by lia.
  apply (wr_at_store_ok rsegs m lo n (a - lo) j H); lia.
Qed.

Lemma v2_wr_sub : forall m lo n a k, wr_at rsegs m lo n -> lo <= a -> 0 <= k -> a + k <= lo + n -> wr_at rsegs m a k.
Proof.
  intros m lo n a k (H1 & H2 & H) Ha Hk Hb. split; [lia|]. split; [lia|]. intros j Hj.
  replace (a + j) with (lo + (a - lo + j)) by lia. apply H. lia.
Qed.

Ltac v2_after_st :=
  lazymatch goal with
  | |- context [write_to_mem ?m ?a ?bs] =>
    let A := addr_expr a in
    change (write_to_mem m a bs) with (write_to_mem m (wa A) bs);
    repeat match goal with
    | H : bytes_at rsegs m ?A2 ?bs2 |- _ =>
        apply (bytes_at_write_other rsegs m A bs A2 bs2) in H; [ | lia | simpl_sizes; lia | simpl_sizes; lia ]
    | H : wr_at rsegs m ?A2 ?n2 |- _ => apply (wr_at_write rsegs m A2 n2 (wa A) bs) in H
    | H : stk rsegs m ?lo ?hi |- _ => apply (stk_write rsegs m lo hi A bs) in H; [ | lia | simpl_sizes; lia ]
    | H : munch ?W ?m0 m |- _ =>
        apply (munch_write W m0 m A bs) in H; [ | lia | simpl_sizes; lia | cbn [Frame.inside]; simpl_sizes; lia ]
    | H : wmono rsegs ?m0 m |- _ => apply (wmono_write rsegs m0 m (wa A) bs) in H
    | H : ov_read_bytes rsegs m _ _ = _ |- _ => clear H
    | H : store_ok rsegs m _ _ = true |- _ => clear H
    | H : mem_inv rsegs m |- _ => clear H
    end;
    let H := fresh "NW" in
    pose proof (bytes_at_write_same rsegs m A bs ltac:(lia) ltac:(simpl_sizes; lia)) as H;
    let m' := fresh "m" in
    remember (write_to_mem m (wa A) bs) as m' eqn:Heqm; clear Heqm
  end.

Ltac v3_st HS :=
  lazymatch goal with
  | |- context [write_to_mem ?m ?a ?bs] =>
    let A := addr_expr a in
    change (write_to_mem m a bs) with (write_to_mem m (wa A) bs);
    try (lazymatch goal with H : mem_inv rsegs m |- _ =>
      apply (mem_inv_store rsegs m (wa A) bs) in H;
      [| simpl_sizes; first [exact HS | rewrite <- HS; f_equal; f_equal; lia]] end);
    v2_after_st
  end.

Lemma tb_hwb_len : forall inp i, length (rec_hwb inp i) = 8%nat.
Proof.
  intros inp i. unfold rec_hwb. induction i as [|i IH]; cbn [rec_hw]; [reflexivity|].
  destruct ((rec_addr inp i =? RcIdentModel.ADDR_REAC_VERSION) && (8 <=? rec_k inp i)) eqn:E; [|exact IH].
  apply andb_prop in E as [_ E]. apply Z.leb_le in E.
  rewrite length_firstn, rec_pl_length. lia.
Qed.

Lemma ua_first2 : forall (l : list byte) k, (k + 2 <= length l)%nat ->
  firstn 2 (skipn k l) = [nthb l k; nthb l (S k)].
Proof.
  intros l. unfold nthb. induction l as [|x l IH]; intros [|k] Hk; cbn [length] in Hk; try lia.
  - destruct l as [|y l]; cbn [length] in Hk; [lia|]. reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

Lemma ua_lhu : forall (l : list byte) k, (k + 2 <= length l)%nat ->
  zext 64 (bv_extract 0 16 (le_bytes_to_word (firstn 2 (skipn k l)))) =
  Z_to_bv 64 (RcIdentModel.bz (nthb l k) + 256 * RcIdentModel.bz (nthb l (S k))).
Proof.
  intros l k Hk. rewrite (ua_first2 l k Hk). rewrite zext_small. f_equal. rewrite extract_low_mod by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. cbn [bytes_le_to_Z].
  rewrite Z.shiftl_0_l, Z.lor_0_r. unfold RcIdentModel.bz.
  pose proof (tb_byte_range (nthb l k)) as R0. pose proof (tb_byte_range (nthb l (S k))) as R1.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite Z.lor_comm.
  rewrite (kb_lor_low (bv_unsigned (nthb l (S k)) * 256) (bv_unsigned (nthb l k)) 8);
    [| lia | lia | change (2 ^ 8) with 256; lia | change (2 ^ 8) with 256; apply Z_mod_mult].
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ Z.of_N 16) with 65536.
  rewrite Z.mod_small by lia. rewrite Z.mod_small by lia. ring.
Qed.

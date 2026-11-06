(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 1051 of its 1066 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v, with its module paths, module names and numbers changed; 647 of its 708 lines of code are new or changed and 1005 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/arg_i.v, with its module paths, module names, addresses and numbers changed; 696 of its 779 lines of code are new or changed and 625 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_c verbs_receive_since verbs_receive_pro verbs_receive_trim verbs_receive_tok.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem verbs_receive_disp verbs_receive_words.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strndup_c strdup_c strlen_c strtok_r_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma window_apart : forall (a lo hi w : Z), 0 < w <= hi - lo ->
  (forall i, 0 <= i < w -> ~ (lo <= a + i < hi)) -> a + w <= lo \/ hi <= a.
Proof.
  intros a lo hi w Hw H. destruct (Z_le_gt_dec (a + w) lo) as [E|E]; [left; exact E|].
  destruct (Z_le_gt_dec hi a) as [E'|E']; [right; exact E'|]. exfalso.
  apply (H (Z.max 0 (lo - a))); lia.
Qed.

Lemma strnlen_res_le : forall n buf, 0 <= n -> 0 <= strnlen_res n buf <= n.
Proof.
  intros n buf Hn. unfold strnlen_res. destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:F; [|lia].
  destruct (find_byte_Some _ _ _ F) as (Hl & _). rewrite length_firstn in Hl. lia.
Qed.

Lemma nth_Z_to_le_bytes : forall n k z, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros k z Hk; [lia|]. destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. lia.
Qed.

Lemma word_mem_le8 : forall segs m a v, word_mem segs m a v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  bytes_at segs m a (le8 (Z_to_bv 64 v)).
Proof.
  intros segs m a v H Hv Ha Ha8. apply bytes_at_of_mbyte; [exact Ha | rewrite length_le8; lia|].
  intros i Hi. rewrite length_le8 in Hi. rewrite (H i Hi).
  change (le8 (Z_to_bv 64 v)) with (Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 v))).
  rewrite unsigned_lit by lia. rewrite nth_Z_to_le_bytes by lia. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold le_byte. change (bv_wrap 8 ?x) with (x mod 2 ^ 8).
  replace (8 * Z.of_nat 8) with 64 by reflexivity. rewrite (Z.mod_small v (2 ^ 64)) by lia.
  change 256 with (2 ^ 8). rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma find_byte_upto0 : forall D, match find_byte 0 D with Some i => firstn i D | None => D end = upto0 D.
Proof.
  unfold upto0. induction D as [|x D IH]; [reflexivity|]. cbn [find_byte upto].
  destruct (bv_unsigned x =? 0); [reflexivity|].
  destruct (find_byte 0 D) as [i|]; cbn [firstn]; f_equal; exact IH.
Qed.

Lemma strnlen_upto : forall D, firstn (Z.to_nat (strnlen_res (Z.of_nat (length D)) D)) D = upto0 D /\
  strnlen_res (Z.of_nat (length D)) D = Z.of_nat (length (upto0 D)).
Proof.
  intros D. pose proof (find_byte_upto0 D) as E. unfold strnlen_res. rewrite Nat2Z.id, firstn_all.
  destruct (find_byte 0 D) as [i|] eqn:F.
  - destruct (find_byte_Some _ _ _ F) as (Hl & _). rewrite Nat2Z.id. split; [exact E|].
    rewrite <- E, length_firstn. lia.
  - rewrite Nat2Z.id, firstn_all. split; [exact E|]. rewrite <- E. reflexivity.
Qed.

Lemma rw_cells_app_l : forall segs m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[Hwf Hb] (Ha & Hn & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hn, Hw. rewrite (cells_bytes_length cs1 W1) in B2.
  split.
  - split; [split; [exact W1 | exact B1]|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [exact W2 | exact B2]|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

Lemma rw_cells_app_r : forall segs m A cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A cs1 cs2 [[W1 B1] (Ha & Hn & Hw1)] [[W2 B2] (Ha2 & Hn2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. rewrite (cells_bytes_length cs1 W1). split; assumption.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_ge_dec i (Z.of_nat (cells_size cs1))) as [H|H]; [apply Hw1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply Hw2. lia.
Qed.

Lemma slack_shift : forall y k s, 0 <= k -> (- (y + k)) mod 8 <= s -> (- y) mod 8 <= k + s.
Proof. intros y k s Hk H. Z.div_mod_to_equations. lia. Qed.

Lemma trim_s_len : forall U, (length (trim_s U) <= length U)%nat.
Proof.
  intros U. unfold trim_s. rewrite length_rev. pose proof (verbs_receive_route.dropw_len is_trail (rev U)) as H.
  rewrite length_rev in H. exact H.
Qed.

Lemma zeros_cons : forall k, repeat (Z_to_bv 8 0) k ++ [Z_to_bv 8 0] = Z_to_bv 8 0 :: tl (repeat (Z_to_bv 8 0) k ++ [Z_to_bv 8 0]).
Proof. intros [|k]; reflexivity. Qed.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GUARDA : ms_guard B = 0x54730.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GLOBS : forall a, in_globals FrameAPI.frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GLOBO : forall L A mem md a, MR L A mem md -> in_globals FrameAPI.frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B MR.
Hypothesis CTXO : ctx_owned B API.
Hypothesis BSLACK : block_slack_present B API.
Hypothesis BWR : blocks_writable B API.
Hypothesis SNDUP : strndup_contract B API.
Hypothesis SDUP : strdup_contract B API.
Hypothesis SLEN : strlen_contract.
Hypothesis STOK : strtok_r_contract.

Lemma le_at_bytes : forall mem a bs, le_at B mem a bs -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at rsegs mem a bs.
Proof.
  intros mem a bs H H0 H1. apply bytes_at_of_mbyte; [exact H0 | exact H1|]. intros i Hi.
  unfold le_at, blk_data in H. rewrite <- SEGS. rewrite (H (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
Qed.

Lemma post_keep : forall K L1 A1 R1 m1 md1 E L2 A2 R2 m2 md2 a,
  call_post_k B MR K L1 A1 R1 m1 md1 E L2 A2 R2 m2 md2 -> MR L1 A1 m1 md1 ->
  alloc_ceiling <= a < 2 ^ 64 -> ~ scratch_k B K R1 a -> ~ E a ->
  mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a).
Proof.
  intros K L1 A1 R1 m1 md1 E L2 A2 R2 m2 md2 a (HM2 & _ & _ & _ & _ & _ & _ & HF & _) HM1 Ha Hs He.
  pose proof (aa_laws API) as LAWS. rewrite <- SEGS.
  apply HF; [left; exact Ha | | | exact Hs | exact He].
  - intros O. pose proof (owned_low B _ LAWS _ _ _ _ a HM1 O). lia.
  - intros O. pose proof (owned_low B _ LAWS _ _ _ _ a HM2 O). lia.
Qed.

Lemma slack_len : forall x, 0 <= x -> 8 * ((x + 7) / 8) - x = (- x) mod 8.
Proof. intros x Hx. Z.div_mod_to_equations. lia. Qed.

Definition vr_mid (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (b : sbound)
    (msg : Z) (D : list byte) (c : config) : Prop :=
  exists (L5 : layout) (A5 : astate) (R5 : bvmap 5 word) (m5 : word -> option byte) (md5 : Model) (lb cb : Z)
         (ps : list word) (can5 : word) (jk : list byte) (b1 b2 c1 c2 : list (Z * Z)),
    c = mkCfg (mkst R5 (Z_to_bv 64 (match toks D with [] => VR_EMPTY | _ => verbs_receive_disp.DISPATCH end)) m5
                 (seg_rom rsegs)) md5 /\
    vr_since B API (fun _ => False) L A regs mem md L5 A5 m5 md5 /\
    (forall a, vr_writes a -> mbyte rsegs m5 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m5 a)) /\
    ro_agree rsegs m5 /\
    getr R5 2 = Z_to_bv 64 (spZ regs - 608) /\ getr R5 3 = getr regs 3 /\ getr R5 4 = getr regs 4 /\
    getr R5 8 = Z_to_bv 64 lb /\ getr R5 9 = Z_to_bv 64 cb /\ getr R5 18 = Z_to_bv 64 msg /\
    (toks D <> [] -> getr R5 19 = verbs_receive_disp.ntokw (toks D) /\ getr R5 21 = verbs_receive_disp.ntokw (toks D)) /\
    getr R5 25 = getr regs 25 /\ getr R5 26 = getr regs 26 /\ getr R5 27 = getr regs 27 /\
    rw_cells rsegs m5 (spZ regs - 608 + 520)
      [CB 8 jk; C8 (getr regs 24); C8 (getr regs 23); C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20);
       C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] /\
    (exists junk, rw_cells rsegs m5 (spZ regs - 608) [CB 520 junk]) /\
    bytes_at rsegs m5 (spZ regs - 608 + 8) (concat (map le8 ps)) /\
    Forall2 (fun p w => VerbsMem.cstr0_at m5 (bv_unsigned p) w /\ cb <= bv_unsigned p /\
                        bv_unsigned p + Z.of_nat (length w) + 1 <= cb + Z.of_nat (length (line D)) + 1) ps (toks D) /\
    blocks L A = b1 ++ b2 /\ c1 ++ c2 = b1 ++ (lb, Z.of_nat (length (upto0 D)) + 1) :: b2 /\
    blocks L5 A5 = c1 ++ (cb, Z.of_nat (length (line D)) + 1) :: c2 /\
    fresh_block B lb (Z.of_nat (length (upto0 D)) + 1) /\ fresh_block B cb (Z.of_nat (length (line D)) + 1) /\
    (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A5)) /\ st_init_done A5 = true /\
    res_ok_slots A5 (sb_malloc (sb_malloc b (Z.of_nat (length (upto0 D)) + 1)) (Z.of_nat (length (line D)) + 1)) /\
    bytes_at rsegs m5 lb (line D ++ repeat (Z_to_bv 8 0) (length (upto0 D) - length (line D)) ++ [Z_to_bv 8 0]) /\
    VerbsMem.ssp_at m5 can5.

Lemma glob_writes : forall a, vr_writes a -> in_globals FrameAPI.frame_G a.
Proof.
  intros a H. exists 0x33ff0, 1020. split; [left; reflexivity|].
  unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT in H. lia.
Qed.

Lemma glob_low : forall a, in_globals FrameAPI.frame_G a -> 0x33ff0 <= a < 0x33ff0 + 1020.
Proof. intros a [lo [len [Hin Hr]]]. destruct Hin as [E|[]]. injection E as <- <-. exact Hr. Qed.

Lemma post_keep_glob : forall K L1 A1 R1 m1 md1 E L2 A2 R2 m2 md2 a,
  call_post_k B MR K L1 A1 R1 m1 md1 E L2 A2 R2 m2 md2 -> MR L1 A1 m1 md1 ->
  alloc_ceiling <= spZ R1 - K -> (forall x, E x -> ~ in_img B x) -> in_globals FrameAPI.frame_G a ->
  mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a).
Proof.
  intros K L1 A1 R1 m1 md1 E L2 A2 R2 m2 md2 a POST HM1 HK HE HG.
  pose proof POST as (HM2 & _ & _ & _ & _ & _ & _ & HF & _).
  destruct (GLOBS a HG) as (Hi & _ & _ & Herr). pose proof (glob_low a HG) as HL.
  pose proof alloc_ceiling_val as ACV. rewrite <- SEGS.
  apply HF; [right; exact Hi | exact (GLOBO _ _ _ _ a HM1 HG) | exact (GLOBO _ _ _ _ a HM2 HG) | | ].
  - unfold scratch_k. intros [Hs|Hs]; [lia | exact (Herr Hs)].
  - intros Hs. exact (HE a Hs Hi).
Qed.

Lemma vr_prefix : forall L A regs mem md b (msg data n : Z) (D : list byte) (P : config -> Prop),
  call_pre_k B MR VR_K L A regs mem md ->
  ro_agree (ms_segs B) mem ->
  getr regs 10 = Z_to_bv 64 msg -> msg mod 8 = 0 -> 4096 <= msg -> msg + 24 <= 2 ^ 63 ->
  le_at B mem (msg + 8) (Mem.le8 (Z_to_bv 64 data)) ->
  le_at B mem (msg + 16) (Mem.le8 (Z_to_bv 64 n)) ->
  outside B L A VR_K regs msg 24 ->
  In (data, Z.max n 1) (blocks L A) ->
  le_at B mem data D -> Z.of_nat (length D) = n -> n <= 8192 ->
  res_ok_slots A b -> room_slots (SB (sb_live b + 32) (sb_bytes b + 262208) (sb_cap b)) VR_REQ ->
  (forall c', vr_mid L A regs mem md b msg D c' -> SR (ms_segs B) c' P) ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 VERBS_RECEIVE) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros L A regs mem md b msg data n D P PRE RO A0 MAL M4K M63 HDATA HN OUTM INB HD LD NB RES ROOM KONT.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof (since_init B API (fun a => False) L A regs mem md PRE) as SI0.
  pose proof PRE as PRE0.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold VR_K in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  rewrite SEGS in RO, HWS, HERR.
  assert (ST : stk rsegs mem (bv_unsigned sp - 14944) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  assert (MAP : msg + 24 <= bv_unsigned sp - 14944 \/ bv_unsigned sp <= msg).
  { apply window_apart; [lia|]. intros i Hi Hw. destruct (OUTM i Hi) as [_ Hs]. apply Hs. left. exact Hw. }
  assert (BD : bytes_at rsegs mem (msg + 8) (Mem.le8 (Z_to_bv 64 data)))
    by (apply le_at_bytes; [exact HDATA | lia | rewrite length_le8; lia]).
  assert (BN : bytes_at rsegs mem (msg + 16) (Mem.le8 (Z_to_bv 64 n)))
    by (apply le_at_bytes; [exact HN | lia | rewrite length_le8; lia]).
  assert (UM : bv_unsigned (Z_to_bv 64 msg) = msg) by (apply unsigned_lit; lia).
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 msg) by exact A0. rewrite R10.
    apply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO |].
    eapply (vr_pro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp - 14944)).
    - apply stk_normalize; [exact ST | lia].
    - unfold VR_FRAME. lia.
    - rewrite UM. apply bytes_at_normalize; [exact RO | exact BD].
    - rewrite UM. apply bytes_at_normalize; [exact RO | exact BN].
    - rewrite UM. unfold VR_FRAME. lia.
    - rewrite UM. lia.
    - rewrite UM. lia.
    - apply mem_inv_normalize. }
  intros ms1 (can1 & (s1 & Q1 & REL1 & ROS1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' & junk1
    & -> & FR1' & MU1' & WM1' & MI1' & ST1').
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL1) as [CAN1 HR1].
  remember (ms_mem can1) as m1 eqn:Em1. subst can1. clear Em1.
  assert (RN0 : mem_rel rsegs mem (normalize rsegs mem)) by (apply mem_rel_normalize; exact RO).
  pose proof (munch_rel rsegs _ _ _ _ _ RN0 HR1 ROS1 MU1') as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ RN0 HR1 ROS1 WM1') as WM1.
  pose proof (ro_agree_same rsegs _ _ RO ROS1) as RO1.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ HR1 FR1') as FR1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  unfold VR_FRAME in *.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x17448) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 608))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 data) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_11 : getr R1 11 = Z_to_bv 64 n) by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_18 : getr R1 18 = Z_to_bv 64 msg) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 608) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 608 <= a < bv_unsigned sp) ->
            Frame.outside [(bv_unsigned sp - 608, bv_unsigned sp)] a) by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
  assert (MR1 : aa_MR API L A m1 md).
  { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      rewrite SEGS. eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - intros p k i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p k i HMR Hin Hi) as (Hp & H4 & Hc & _).
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  assert (SI1 : vr_since B API (fun _ => False) L A regs mem md L A m1 md).
  { eapply (since_mem B API); [exact SI0 | exact MR1 | | | ].
    - intros a D0 N0 Ns Nw. rewrite SEGS.
      assert (Hw : ~ (bv_unsigned sp - 608 <= a < bv_unsigned sp)).
      { intros Hw. apply Ns. left. unfold VR_K. change (spZ regs) with (bv_unsigned sp). lia. }
      assert (Ra : 0 <= a < 2 ^ 64).
      { destruct D0 as [D0|D0]; [lia|]. pose proof (in_img_low B SEGS a D0). lia. }
      split; [eapply munch_mbyte; [exact MU1 | exact Ra | apply OUT1; [exact Ra | exact Hw]]|].
      eapply munch_writable; [exact MU1 | exact Ra | apply OUT1; [exact Ra | exact Hw]].
    - intros p k i Hp _ _ Hi. destruct (mr_blocks B _ LAWS L A mem md p k i HMR Hp Hi) as (_ & H4 & Hc & _).
      rewrite SEGS. eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia].
    - intros a _ W. rewrite SEGS in *. apply WM1. exact W. }
  destruct (block_facts B _ LAWS L A mem md data (Z.max n 1) 0 HMR INB ltac:(lia)) as (_ & D4K & DCEIL & _).
  assert (HD1 : forall i, (i < length D)%nat -> mbyte rsegs m1 (data + Z.of_nat i) = nth_error D i).
  { intros i Hi. rewrite (munch_mbyte rsegs _ _ _ (data + Z.of_nat i) MU1 ltac:(lia) ltac:(apply OUT1; lia)).
    rewrite <- SEGS. unfold le_at, blk_data in HD. rewrite (HD (Z.of_nat i) ltac:(lia)), Nat2Z.id. reflexivity. }
  assert (SLR : 0 <= strnlen_res n D <= n) by (apply strnlen_res_le; lia).
  pose proof SNDUP as SND. unfold strndup_contract in SND. rewrite SEGS in SND.
  eapply SR_bind.
  { eapply (SND L A R1 m1 md data n D b); [ | exact E1_10 | exact E1_11 | lia | exact HD1 | | lia | | | lia | exact RES | | exact RO1].
    - split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
      split; [rewrite E1_1; apply bv_eq; vm_compute; reflexivity|].
      split; [rewrite SP1; replace (bv_unsigned sp - 608) with (bv_unsigned sp + (-38) * 16) by ring;
              rewrite Z.mod_add by lia; exact HAL|].
      split; [rewrite SP1; unfold STRNDUP_STACK, ALLOC_STACK; lia|].
      split; [rewrite SP1; lia|].
      split; [intros a Ha; rewrite SP1 in Ha; unfold STRNDUP_STACK, ALLOC_STACK in Ha; rewrite SEGS; apply WM1;
              apply HWS; lia|].
      split; [rewrite E1_4; exact HTP|].
      split; [intros a Ha; rewrite SEGS; apply WM1; apply HERR; exact Ha|].
      intros HI. specialize (HAUX HI). rewrite SP1.
      destruct HAUX as (av & ar & W1 & W2 & W3 & W4 & B1 & B2 & B3 & B4 & L1 & L2).
      exists av, ar.
      split.
      { eapply word_mem_munch; [exact MU1 | | exact W1]. intros k Hk.
        assert (SO : owned B L A (ms_libc B + 8 + Z.of_nat k)) by (right; unfold static_owned; lia).
        destruct (owned_low B _ LAWS _ _ _ _ _ HMR SO). split; [lia | apply OUT1; lia]. }
      split.
      { intros k Hk. eapply word_mem_munch; [exact MU1 | | exact (W2 k Hk)]. intros k' Hk'.
        split; [lia | apply OUT1; lia]. }
      split.
      { eapply word_mem_munch; [exact MU1 | | exact W3]. intros k Hk. split; [lia | apply OUT1; lia]. }
      split.
      { eapply word_mem_munch; [exact MU1 | | exact W4]. intros k Hk. split; [lia | apply OUT1; lia]. }
      lia.
    - unfold memchr_ok. rewrite <- LD, Nat2Z.id, firstn_all.
      destruct (find_byte 0 D); [left|]; lia.
    - left. rewrite SP1. unfold STRNDUP_STACK, ALLOC_STACK. lia.
    - right. left. exists data, (Z.max n 1). split; [exact INB|]. lia.
    - refine (RecKindB.room_slots_mono _ _ _ VR_REQ _ _ ROOM); [unfold RecKindB.sb_le; cbn [sb_live sb_bytes sb_cap]; lia | unfold VR_REQ; lia]. }
  intros c2 RET.
  destruct RET as (L2 & A2 & R2 & m2 & md2 & lb & -> & POST2 & A0' & NZ2 & AL2 & FRESH2 & BLK2 & KEPT2 & HLB & RO2 & GK2
    & UBK2 & INIT2 & RLEN2 & RES2).
  pose proof (since_call B API AX CTXO (fun _ => False) L A regs mem md L A m1 md STRNDUP_STACK R1 _ L2 A2 R2 m2 md2 SI1
    POST2 RLEN2 (fun p k H _ => H)) as SI2.
  pose proof POST2 as (HMR2 & HWF2 & HBD2 & HLE2 & HSTAB2 & HPRES2 & HVM2 & HFRAME2 & HBLKS2 & HSCR2).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR2) as (Hh2 & Hl2 & Hmat2).
  pose proof FRESH2 as (FL_lo & FL_hi & FL_img).
  destruct (strnlen_upto D) as [SU1 SU2]. rewrite LD in SU1, SU2.
  set (U := upto0 D) in *.
  rewrite SU2 in *. rewrite Nat2Z.id in SU1, HLB. rewrite SU1 in HLB.
  assert (SCR1 : forall a, scratch_k B STRNDUP_STACK R1 a -> scratch_k B VR_K regs a).
  { intros a. unfold scratch_k. rewrite SP1. unfold STRNDUP_STACK, ALLOC_STACK, VR_K.
    change (spZ regs) with (bv_unsigned sp). intros [H|H]; [left|right]; lia. }
  assert (SD1 : forall a, scratch_k B VR_K regs a -> ~ scratch_k B STRNDUP_STACK R1 a ->
                 alloc_ceiling <= a < 2 ^ 64 /\ ~ vr_writes a).
  { intros a. unfold scratch_k. rewrite SP1. unfold STRNDUP_STACK, ALLOC_STACK, VR_K.
    change (spZ regs) with (bv_unsigned sp). intros Hs Hn.
    assert (Hw : bv_unsigned sp - 14944 <= a < bv_unsigned sp) by (destruct Hs as [Hs|Hs]; [lia | exfalso; apply Hn; right; exact Hs]).
    split; [lia|]. unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT. lia. }
  specialize (SI2 SCR1).
  assert (EX2 : forall a, lb <= a < lb + Z.of_nat (length U) + 1 -> ~ vr_dom B a \/ vr_writes a).
  { intros a Ha. left. intros [Hd|Hd]; [lia|]. apply (FL_img (a - lb) ltac:(lia)).
    replace (lb + (a - lb)) with a by ring. exact Hd. }
  specialize (SI2 EX2 SD1).
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 608))
    by exact (eq_trans (HPRES2 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_10 : reg_get R2 10 = Z_to_bv 64 lb) by exact A0'.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 608)
                  (vr_frame_cells (reg_get regs 1) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18)
                     (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
                     (reg_get regs 24) junk1)).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct (post_keep _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp - 608 + i) POST2 MR1 ltac:(lia)) as [E W].
    - unfold scratch_k. rewrite SP1. unfold STRNDUP_STACK, ALLOC_STACK. intros [H|H]; [lia|].
      pose proof ERRNO_LOW. lia.
    - lia.
    - split; [exact E | apply W]. }
  assert (INLB : In (lb, Z.of_nat (length U) + 1) (blocks L2 A2)).
  { destruct BLK2 as (b1 & b2 & E1 & _). rewrite E1. apply in_or_app. right. left. reflexivity. }
  set (x := lb + Z.of_nat (length U) + 1).
  pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as XM.
  destruct (present_rw_cells rsegs m2 x (Z.to_nat ((- x) mod 8))) as [slk HSLK]; [lia | lia | |].
  { intros i Hi. eapply BSLACK; [exact HMR2 | exact INLB |].
    replace (lb + (Z.of_nat (length U) + 1)) with x by (unfold x; ring). pose proof (slack_len x ltac:(lia)). lia. }
  destruct HSLK as [[HSW HSB] _]. cbn [cells_bytes cbytes] in HSB. rewrite app_nil_r in HSB.
  cbn [cells_wf cell_wf] in HSW. destruct HSW as [HSL _].
  assert (LBU : u8arr rsegs m2 lb (U ++ [Z_to_bv 8 0])).
  { split.
    - apply bytes_at_of_mbyte; [lia | rewrite length_app; cbn [length]; lia|].
      intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply HLB. lia.
    - split; [lia|]. split; [rewrite length_app; cbn [length]; lia|]. intros i Hi.
      rewrite length_app in Hi. cbn [length] in Hi.
      pose proof (BWR L2 A2 m2 md2 lb (Z.of_nat (length U) + 1) i HMR2 INLB ltac:(lia)) as W.
      rewrite SEGS in W. exact W. }
  assert (NZU : ~ In (Z_to_bv 8 0) U).
  { intros Hin. unfold U, upto0 in Hin. apply upto_in in Hin. destruct Hin as [_ Hb]. vm_compute in Hb. discriminate. }
  unfold vr_frame_cells in FR2.
  apply (rw_cells_split_CB rsegs _ _ [] 528%nat junk1 _ [8; 520]%nat) in FR2; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR2.
  destruct (rw_cells_app_l rsegs m2 _ [CB 8 (firstn 8 junk1)] _ FR2) as [SV2 FRR2].
  cbn [cells_size csize Nat.add] in FRR2.
  rewrite E1_1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E2_2, E2_10.
    apply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO2 |].
    assert (ULB : bv_unsigned (Z_to_bv 64 lb) = lb) by (apply unsigned_lit; lia).
    assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 608)) = bv_unsigned sp - 608) by (apply unsigned_lit; lia).
    eapply (vr_trim SLEN) with (U := U) (slack := slk) (junk := firstn 8 junk1).
    - rewrite ULB. split.
      + apply bytes_at_normalize; [exact RO2 | exact (proj1 LBU)].
      + eapply wr_at_norm; [apply mem_rel_normalize; exact RO2 | exact (proj2 LBU) |].
        intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply (ro_addr_out B SEGS); [lia|].
        replace (lb + i) with (lb + i) by reflexivity. apply FL_img. lia.
    - exact NZU.
    - rewrite ULB. apply bytes_at_normalize; [exact RO2 | exact HSB].
    - rewrite ULB. rewrite HSL. fold x. lia.
    - rewrite ULB. lia.
    - rewrite USP. apply rw_cells_normalize; [exact RO2 | exact SV2|]. intros i Hi. cbn in Hi.
      apply ro_addr_hi. lia.
    - rewrite ULB, USP, HSL. left. lia.
    - apply mem_inv_normalize. }
  intros ms3 (can3 & (s3 & Q3 & REL3 & ROS3) & EQ3).
  destruct Q3 as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3'
    & -> & LBU3' & HSB3' & SV3' & MU3' & WM3' & MI3').
  assert (ULB' : bv_unsigned (Z_to_bv 64 lb) = lb) by (apply unsigned_lit; lia).
  assert (USP' : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 608)) = bv_unsigned sp - 608) by (apply unsigned_lit; lia).
  rewrite ULB' in LBU3', HSB3', MU3'. rewrite USP' in SV3', MU3'.
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL3) as [CAN3 HR3].
  remember (ms_mem can3) as m3 eqn:Em3. subst can3. clear Em3.
  assert (RN2 : mem_rel rsegs m2 (normalize rsegs m2)) by (apply mem_rel_normalize; exact RO2).
  pose proof (munch_rel rsegs _ _ _ _ _ RN2 HR3 ROS3 MU3') as MU3.
  pose proof (wmono_rel rsegs _ _ _ _ RN2 HR3 ROS3 WM3') as WM3.
  pose proof (ro_agree_same rsegs _ _ RO2 ROS3) as RO3.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ HR3 SV3') as SV3.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ HR3) HSB3') as HSB3.
  assert (LBU3 : u8arr rsegs m3 lb (trim_s U ++ repeat (Z_to_bv 8 0) (length U - length (trim_s U)) ++ [Z_to_bv 8 0])).
  { destruct LBU3' as [LB1 LB2]. split; [exact (proj2 (bytes_at_rel rsegs _ _ _ _ HR3) LB1)|].
    eapply wr_at_rel; [exact HR3 | exact LB2]. }
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x174b0) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 608))
    by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_4 : getr R3 4 = reg_get R2 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_8 : getr R3 8 = Z_to_bv 64 lb) by (rewrite (getr_of_eqv _ _ 8 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 lb) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity).
  assert (SP3 : spZ R3 = bv_unsigned sp - 608) by (unfold spZ; rewrite E3_2; exact USP').
  set (W3 := [(bv_unsigned sp - 608, bv_unsigned sp - 608 + 8); (lb, lb + Z.of_nat (length U) + 1)]) in *.
  assert (OUT3 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 608 <= a < bv_unsigned sp - 600) ->
                 ~ (lb <= a < lb + Z.of_nat (length U) + 1) -> Frame.outside W3 a).
  { intros a _ H1 H2. unfold W3. cbn. split; [lia|]. split; [exact H2 | exact I]. }
  assert (LBW : forall a, lb <= a < lb + Z.of_nat (length U) + 1 -> present m3 a).
  { intros a Ha. apply (present_of_writable_out B SEGS); [lia | |].
    - replace a with (lb + (a - lb)) by ring. apply FL_img. lia.
    - destruct LBU3 as [_ (_ & _ & Hw)].
      rewrite length_app, length_app, repeat_length in Hw. cbn [length] in Hw.
      pose proof (trim_s_len U).
      replace a with (lb + (a - lb)) by ring. apply Hw. lia. }
  assert (MR3 : aa_MR API L2 A2 m3 md2).
  { eapply (mr_frame B _ LAWS L2 A2 m2 m3 md2 md2 HMR2).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR2 Ho) as [Ha1 Ha2].
      assert (NL : ~ (lb <= a < lb + Z.of_nat (length U) + 1)).
      { intros Hin. destruct (block_facts B _ LAWS _ _ _ _ _ _ (a - lb) HMR2 INLB ltac:(lia)) as (_ & _ & _ & No).
        apply No. replace (lb + (a - lb)) with a by ring. exact Ho. }
      rewrite SEGS. eapply munch_mbyte; [exact MU3 | lia | apply OUT3; lia].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR2 Ho) as [Ha1 Ha2].
      assert (NL : ~ (lb <= a < lb + Z.of_nat (length U) + 1)).
      { intros Hin. destruct (block_facts B _ LAWS _ _ _ _ _ _ (a - lb) HMR2 INLB ltac:(lia)) as (_ & _ & _ & No).
        apply No. replace (lb + (a - lb)) with a by ring. exact Ho. }
      eapply munch_present; [exact MU3 | lia | apply OUT3; lia | exact Hp].
    - intros p k i Hin Hi. destruct (mr_blocks B _ LAWS L2 A2 m2 md2 p k i HMR2 Hin Hi) as (Hp & H4 & Hc & _).
      destruct (Z_le_gt_dec lb (ptr_addr L2 p + i)) as [Q1|Q1];
        [destruct (Z_lt_ge_dec (ptr_addr L2 p + i) (lb + Z.of_nat (length U) + 1)) as [Q2|Q2]|].
      + apply LBW. lia.
      + eapply munch_present; [exact MU3 | lia | apply OUT3; lia | exact Hp].
      + eapply munch_present; [exact MU3 | lia | apply OUT3; lia | exact Hp].
    - reflexivity.
    - exact Hh2.
    - exact Hl2.
    - exact Hmat2. }
  assert (SI3 : vr_since B API (fun _ => False) L A regs mem md L2 A2 m3 md2).
  { eapply (since_mem B API); [exact SI2 | exact MR3 | | | ].
    - intros a D0 N0 Ns Nw. rewrite SEGS.
      assert (Ra : 0 <= a < 2 ^ 64).
      { destruct D0 as [D0|D0]; [lia|]. pose proof (in_img_low B SEGS a D0). lia. }
      assert (Hw : ~ (bv_unsigned sp - 608 <= a < bv_unsigned sp - 600)).
      { intros Hw. apply Ns. left. unfold VR_K. change (spZ regs) with (bv_unsigned sp). lia. }
      assert (Hlb : ~ (lb <= a < lb + Z.of_nat (length U) + 1)).
      { intros Hlb. destruct D0 as [D0|D0]; [lia|]. apply (FL_img (a - lb) ltac:(lia)).
        replace (lb + (a - lb)) with a by ring. exact D0. }
      split; [eapply munch_mbyte; [exact MU3 | exact Ra | apply OUT3; assumption]|].
      eapply munch_writable; [exact MU3 | exact Ra | apply OUT3; assumption].
    - intros p k i Hp Hp2 _ Hi.
      assert (HB : In (ptr_addr L p, k) (blocks L A)) by (apply in_map_iff; exists (p, k); split; [reflexivity | exact Hp]).
      destruct BLK2 as (b1 & b2 & E1 & E2). rewrite E2 in HB.
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR2 E1 HB) as Dj.
      destruct (mr_blocks B _ LAWS L A mem md p k i HMR Hp Hi) as (_ & H4 & Hc & _).
      rewrite SEGS. eapply munch_mbyte; [exact MU3 | lia | apply OUT3; lia].
    - intros a _ W. rewrite SEGS in *. apply WM3. exact W. }
  assert (FRR3 : rw_cells rsegs m3 (bv_unsigned sp - 608 + 8)
                  [CB 520 (firstn 520 (skipn 8 junk1)); C8 (reg_get regs 24); C8 (reg_get regs 23); C8 (reg_get regs 22);
                   C8 (reg_get regs 21); C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18);
                   C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { eapply rw_cells_transport; [exact FRR2 | exact MU3 | exact WM3 |]. unfold W3. cbn. lia. }
  pose proof (rw_cells_app_r rsegs m3 _ [C8 (Z_to_bv 64 0)] _ SV3 FRR3) as FR3. cbn [app] in FR3.
  set (ln := trim_s U) in *.
  set (k0 := (length U - length ln)%nat) in *.
  set (slk2 := tl (repeat (Z_to_bv 8 0) k0 ++ [Z_to_bv 8 0]) ++ slk).
  assert (LNU : (length ln <= length U)%nat) by apply trim_s_len.
  assert (LSLK2 : length slk2 = (k0 + length slk)%nat).
  { unfold slk2. rewrite length_app. destruct k0 as [|k1]; cbn [repeat app tl length]; [lia|].
    rewrite length_app, repeat_length. cbn [length]. lia. }
  assert (BLN : bytes_at rsegs m3 lb (ln ++ Z_to_bv 8 0 :: slk2)).
  { replace (ln ++ Z_to_bv 8 0 :: slk2) with ((ln ++ repeat (Z_to_bv 8 0) k0 ++ [Z_to_bv 8 0]) ++ slk).
    - apply bytes_at_app. split; [exact (proj1 LBU3)|].
      rewrite length_app, length_app, repeat_length. cbn [length].
      replace (lb + Z.of_nat (length ln + (k0 + 1))) with (lb + Z.of_nat (length U) + 1) by (unfold k0; lia).
      exact HSB3.
    - unfold slk2. rewrite <- !app_assoc. f_equal. rewrite app_assoc. rewrite (zeros_cons k0) at 1. reflexivity. }
  assert (NZL : ~ In (Z_to_bv 8 0) ln).
  { intros Hin. apply NZU. unfold ln, trim_s in Hin. rewrite <- in_rev in Hin. apply dropw_in in Hin.
    rewrite <- in_rev in Hin. exact Hin. }
  pose proof SI3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SW3).
  pose proof SDUP as SDP. unfold strdup_contract in SDP. rewrite SEGS in SDP.
  eapply SR_bind.
  { eapply (SDP L2 A2 R3 m3 md2 lb ln slk2 (sb_malloc b (Z.of_nat (length U) + 1)));
      [ | exact E3_10 | | exact NZL | | lia | | | | exact RES2 | | exact RO3].
    - split; [exact MR3|]. split; [exact HWF2|]. split; [exact HBD2|].
      split; [rewrite E3_1; apply bv_eq; vm_compute; reflexivity|].
      split; [rewrite SP3; replace (bv_unsigned sp - 608) with (bv_unsigned sp + (-38) * 16) by ring;
              rewrite Z.mod_add by lia; exact HAL|].
      split; [rewrite SP3; unfold STRDUP_STACK, ALLOC_STACK; lia|].
      split; [rewrite SP3; lia|].
      split; [intros a Ha; rewrite SP3 in Ha; unfold STRDUP_STACK, ALLOC_STACK in Ha; apply SW3; left;
              unfold VR_K; change (spZ regs) with (bv_unsigned sp); lia|].
      split; [rewrite E3_4; exact (eq_trans (HPRES2 4 ltac:(unfold callee_saved; lia)) (eq_trans E1_4 HTP))|].
      split; [intros a Ha; apply SW3; right; exact Ha|].
      intros HI. rewrite INIT2 in HI. discriminate.
    - intros i Hi. apply (mbyte_of_bytes_at rsegs m3 lb _ i BLN Hi).
    - rewrite LSLK2, Nat2Z.inj_add, HSL. apply slack_shift; [lia|].
      replace (lb + Z.of_nat (length ln) + 1 + Z.of_nat k0) with x by (unfold x, k0; lia). lia.
    - left. rewrite SP3. rewrite length_app. cbn [length]. rewrite LSLK2. unfold STRDUP_STACK, ALLOC_STACK.
      rewrite HSL. unfold k0. lia.
    - right. left. exists lb, (Z.of_nat (length U) + 1). split; [exact INLB|]. lia.
    - lia.
    - refine (RecKindB.room_slots_mono _ _ _ VR_REQ _ _ ROOM); [unfold RecKindB.sb_le, sb_malloc; cbn [sb_live sb_bytes sb_cap]; lia | unfold VR_REQ; lia]. }
  intros c4 RET.
  destruct RET as (L4 & A4 & R4 & m4 & md4 & cb & -> & POST4 & A0'' & NZ4 & AL4 & FRESH4 & BLK4 & KEPT4 & HCB & RO4 & GK4
    & UBK4 & INIT4 & RLEN4 & RES4).
  assert (SCR3 : forall a, scratch_k B STRDUP_STACK R3 a -> scratch_k B VR_K regs a).
  { intros a. unfold scratch_k. rewrite SP3. unfold STRDUP_STACK, ALLOC_STACK, VR_K.
    change (spZ regs) with (bv_unsigned sp). intros [H|H]; [left|right]; lia. }
  assert (SD3 : forall a, scratch_k B VR_K regs a -> ~ scratch_k B STRDUP_STACK R3 a ->
                 alloc_ceiling <= a < 2 ^ 64 /\ ~ vr_writes a).
  { intros a. unfold scratch_k. rewrite SP3. unfold STRDUP_STACK, ALLOC_STACK, VR_K.
    change (spZ regs) with (bv_unsigned sp). intros Hs Hn.
    assert (Hw : bv_unsigned sp - 14944 <= a < bv_unsigned sp) by (destruct Hs as [Hs|Hs]; [lia | exfalso; apply Hn; right; exact Hs]).
    split; [lia|]. unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT. lia. }
  pose proof FRESH4 as (FC_lo & FC_hi & FC_img).
  assert (EX4 : forall a, cb <= a < cb + Z.of_nat (length ln) + 1 -> ~ vr_dom B a \/ vr_writes a).
  { intros a Ha. left. intros [Hd|Hd]; [lia|]. apply (FC_img (a - cb) ltac:(lia)).
    replace (cb + (a - cb)) with a by ring. exact Hd. }
  pose proof (since_call B API AX CTXO (fun _ => False) L A regs mem md L2 A2 m3 md2 STRDUP_STACK R3 _ L4 A4 R4 m4 md4 SI3
    POST4 RLEN4 (fun p k H H4 => UBK2 p k H) SCR3 EX4 SD3) as SI4.
  pose proof POST4 as (HMR4 & HWF4 & HBD4 & HLE4 & HSTAB4 & HPRES4 & HVM4 & HFRAME4 & HBLKS4 & HSCR4).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR4) as (Hh4 & Hl4 & Hmat4).
  assert (E4_2 : reg_get R4 2 = Z_to_bv 64 (bv_unsigned sp - 608))
    by exact (eq_trans (HPRES4 2 ltac:(unfold callee_saved; lia)) E3_2).
  assert (E4_10 : reg_get R4 10 = Z_to_bv 64 cb) by exact A0''.
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp - 608)
                  ([C8 (Z_to_bv 64 0); CB 520 (firstn 520 (skipn 8 junk1)); C8 (reg_get regs 24); C8 (reg_get regs 23);
                   C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20); C8 (reg_get regs 19);
                   C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)])).
  { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi.
    destruct (post_keep _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp - 608 + i) POST4 MR3 ltac:(lia)) as [E W].
    - unfold scratch_k. rewrite SP3. unfold STRDUP_STACK, ALLOC_STACK. intros [H|H]; [lia|].
      pose proof ERRNO_LOW. lia.
    - lia.
    - split; [exact E | apply W]. }
  assert (INCB : In (cb, Z.of_nat (length ln) + 1) (blocks L4 A4)).
  { destruct BLK4 as (c1 & c2 & E1 & _). rewrite E1. apply in_or_app. right. left. reflexivity. }
  assert (CBU : u8arr rsegs m4 cb (ln ++ [Z_to_bv 8 0])).
  { split.
    - apply bytes_at_of_mbyte; [lia | rewrite length_app; cbn [length]; lia|].
      intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply HCB. lia.
    - split; [lia|]. split; [rewrite length_app; cbn [length]; lia|]. intros i Hi.
      rewrite length_app in Hi. cbn [length] in Hi.
      pose proof (BWR L4 A4 m4 md4 cb (Z.of_nat (length ln) + 1) i HMR4 INCB ltac:(lia)) as W.
      rewrite SEGS in W. exact W. }
  destruct (ax_statics AX L4 A4 m4 md4 HMR4) as (GW4 & (g4 & Rg4 & GV4) & _).
  rewrite GOTG, GUARDA, SEGS in GW4. rewrite GUARDA, SEGS in GV4.
  assert (SSP4 : VerbsMem.ssp_at m4 (Z_to_bv 64 g4)).
  { unfold VerbsMem.ssp_at, VerbsMem.SSP_GOT, VerbsMem.SSP_GUARD.
    split; [apply word_mem_le8; [exact GW4 | lia | lia | lia] | apply word_mem_le8; [exact GV4 | lia | lia | lia]]. }
  pose proof SI4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SW4).
  assert (ST4 : stk rsegs m4 (bv_unsigned sp - 14944) (bv_unsigned sp - 608)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs m4 a) by (rewrite <- SEGS; apply SW4; left; unfold VR_K; change (spZ regs) with (bv_unsigned sp); lia).
    split; [exact W|].
    destruct (writable_hi_present m4 a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  unfold vr_frame_cells in *.
  apply (rw_cells_split_CB rsegs _ _ [C8 (Z_to_bv 64 0)] 520%nat _ _ [512; 8]%nat) in FR4; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR4.
  destruct (rw_cells_app_l rsegs m4 _ [C8 (Z_to_bv 64 0); CB 512 (firstn 512 (firstn 520 (skipn 8 junk1)))] _ FR4)
    as [TV4 FRR4].
  cbn [cells_size csize Nat.add] in FRR4.
  rewrite E3_1.
  eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E4_2, E4_10.
    apply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO4 |].
    assert (UCB : bv_unsigned (Z_to_bv 64 cb) = cb) by (apply unsigned_lit; lia).
    eapply (vr_tokenize STOK) with (T := ln) (lo := bv_unsigned sp - 14944) (can := Z_to_bv 64 g4).
    - rewrite UCB. split.
      + apply bytes_at_normalize; [exact RO4 | exact (proj1 CBU)].
      + eapply wr_at_norm; [apply mem_rel_normalize; exact RO4 | exact (proj2 CBU) |].
        intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply (ro_addr_out B SEGS); [lia|].
        apply FC_img. lia.
    - exact NZL.
    - rewrite UCB. lia.
    - rewrite UCB, USP'. left. lia.
    - rewrite USP'. apply rw_cells_normalize; [exact RO4 | exact TV4|]. intros i Hi. cbn in Hi.
      apply ro_addr_hi. lia.
    - split; apply bytes_at_normalize; [exact RO4 | exact (proj1 SSP4) | exact RO4 | exact (proj2 SSP4)].
    - rewrite USP'. apply stk_normalize; [exact ST4 | lia].
    - rewrite USP'. lia.
    - unfold verbs_receive_disp.IMG_TOP. lia.
    - apply mem_inv_normalize. }
  intros ms5 (can5 & (s5 & Q5 & REL5 & ROS5) & EQ5).
  destruct Q5 as (ra5 & t05 & t15 & t25 & a05 & a15 & a25 & a35 & a45 & a55 & a65 & a75 & s35 & s45 & s55 & s65 & s75
    & s85 & t35 & t45 & t55 & t65 & m5' & ps & -> & S35 & FW5' & (junk5 & TJ5') & TA5' & MU5' & WM5' & MI5' & ST5').
  assert (UCB : bv_unsigned (Z_to_bv 64 cb) = cb) by (apply unsigned_lit; lia).
  rewrite UCB in FW5', MU5'. rewrite USP' in TJ5', TA5', MU5'.
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL5) as [CAN5 HR5].
  remember (ms_mem can5) as m5 eqn:Em5. subst can5. clear Em5.
  assert (RN4 : mem_rel rsegs m4 (normalize rsegs m4)) by (apply mem_rel_normalize; exact RO4).
  pose proof (munch_rel rsegs _ _ _ _ _ RN4 HR5 ROS5 MU5') as MU5.
  pose proof (wmono_rel rsegs _ _ _ _ RN4 HR5 ROS5 WM5') as WM5.
  pose proof (ro_agree_same rsegs _ _ RO4 ROS5) as RO5.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ HR5 TJ5') as TJ5.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ HR5) TA5') as TA5.
  assert (FW5 : Forall2 (fun p w => VerbsMem.cstr0_at m5 (bv_unsigned p) w /\ cb <= bv_unsigned p /\
                   bv_unsigned p + Z.of_nat (length w) + 1 <= cb + Z.of_nat (length ln) + 1) ps (firstn 64 (Verbs.words ln))).
  { eapply Forall2_impl; [|exact FW5']. intros p w ((H1 & H2) & H3 & H4). split; [split|split]; try assumption.
    exact (proj2 (bytes_at_rel rsegs _ _ _ _ HR5) H1). }
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
  set (W5 := [(bv_unsigned sp - 608 - 128, bv_unsigned sp - 608); (bv_unsigned sp - 608, bv_unsigned sp - 608 + 520);
              (cb, cb + Z.of_nat (length ln) + 1)]) in *.
  assert (OUT5 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 736 <= a < bv_unsigned sp - 88) ->
                 ~ (cb <= a < cb + Z.of_nat (length ln) + 1) -> Frame.outside W5 a).
  { intros a _ H1 H2. unfold W5. cbn. split; [lia|]. split; [lia|]. split; [exact H2 | exact I]. }
  assert (CBW : forall a, cb <= a < cb + Z.of_nat (length ln) + 1 -> writable_at rsegs m5 a).
  { intros a Ha. apply WM5. destruct CBU as [_ (_ & _ & Hw)]. rewrite length_app in Hw. cbn [length] in Hw.
    replace a with (cb + (a - cb)) by ring. apply Hw. lia. }
  assert (MR5 : aa_MR API L4 A4 m5 md4).
  { eapply (mr_frame B _ LAWS L4 A4 m4 m5 md4 md4 HMR4).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR4 Ho) as [Ha1 Ha2].
      assert (NL : ~ (cb <= a < cb + Z.of_nat (length ln) + 1)).
      { intros Hin. destruct (block_facts B _ LAWS _ _ _ _ _ _ (a - cb) HMR4 INCB ltac:(lia)) as (_ & _ & _ & No).
        apply No. replace (cb + (a - cb)) with a by ring. exact Ho. }
      rewrite SEGS. eapply munch_mbyte; [exact MU5 | lia | apply OUT5; lia].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR4 Ho) as [Ha1 Ha2].
      assert (NL : ~ (cb <= a < cb + Z.of_nat (length ln) + 1)).
      { intros Hin. destruct (block_facts B _ LAWS _ _ _ _ _ _ (a - cb) HMR4 INCB ltac:(lia)) as (_ & _ & _ & No).
        apply No. replace (cb + (a - cb)) with a by ring. exact Ho. }
      eapply munch_present; [exact MU5 | lia | apply OUT5; lia | exact Hp].
    - intros p k i Hin Hi. destruct (mr_blocks B _ LAWS L4 A4 m4 md4 p k i HMR4 Hin Hi) as (Hp & H4 & Hc & _).
      destruct (Z_le_gt_dec cb (ptr_addr L4 p + i)) as [Q1|Q1];
        [destruct (Z_lt_ge_dec (ptr_addr L4 p + i) (cb + Z.of_nat (length ln) + 1)) as [Q2|Q2]|].
      + apply (present_of_writable_out B SEGS); [lia | | apply CBW; lia].
        replace (ptr_addr L4 p + i) with (cb + (ptr_addr L4 p + i - cb)) by ring. apply FC_img. lia.
      + eapply munch_present; [exact MU5 | lia | apply OUT5; lia | exact Hp].
      + eapply munch_present; [exact MU5 | lia | apply OUT5; lia | exact Hp].
    - reflexivity.
    - exact Hh4.
    - exact Hl4.
    - exact Hmat4. }
  destruct BLK2 as (b1 & b2 & BL2a & BL2b). destruct BLK4 as (c1 & c2 & BL4a & BL4b).
  assert (OLDB : forall p k, In (p, k) (user_blocks A) -> In (ptr_addr L p, k) (c1 ++ c2)).
  { intros p k Hp. rewrite <- BL4b, BL2a. assert (HB : In (ptr_addr L p, k) (blocks L A))
      by (apply in_map_iff; exists (p, k); split; [reflexivity | exact Hp]).
    rewrite BL2b in HB. apply in_app_or in HB. apply in_or_app. destruct HB as [HB|HB]; [left; exact HB|].
    right. right. exact HB. }
  assert (SI5 : vr_since B API (fun _ => False) L A regs mem md L4 A4 m5 md4).
  { eapply (since_mem B API); [exact SI4 | exact MR5 | | | ].
    - intros a D0 N0 Ns Nw. rewrite SEGS.
      assert (Ra : 0 <= a < 2 ^ 64).
      { destruct D0 as [D0|D0]; [lia|]. pose proof (in_img_low B SEGS a D0). lia. }
      assert (Hw : ~ (bv_unsigned sp - 736 <= a < bv_unsigned sp - 88)).
      { intros Hw. apply Ns. left. unfold VR_K. change (spZ regs) with (bv_unsigned sp). lia. }
      assert (Hcb : ~ (cb <= a < cb + Z.of_nat (length ln) + 1)).
      { intros Hcb. destruct D0 as [D0|D0]; [lia|]. apply (FC_img (a - cb) ltac:(lia)).
        replace (cb + (a - cb)) with a by ring. exact D0. }
      split; [eapply munch_mbyte; [exact MU5 | exact Ra | apply OUT5; assumption]|].
      eapply munch_writable; [exact MU5 | exact Ra | apply OUT5; assumption].
    - intros p k i Hp Hp4 _ Hi.
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR4 BL4a (OLDB p k Hp)) as Dj.
      destruct (mr_blocks B _ LAWS L A mem md p k i HMR Hp Hi) as (_ & H4 & Hc & _).
      rewrite SEGS. eapply munch_mbyte; [exact MU5 | lia | apply OUT5; lia].
    - intros a _ W. rewrite SEGS in *. apply WM5. exact W. }
  assert (WK : forall a, vr_writes a ->
            mbyte rsegs m5 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m5 a)).
  { intros a Hw. pose proof (glob_writes a Hw) as HG. pose proof (glob_low a HG) as HGL.
    destruct (GLOBS a HG) as (Hi & _ & _ & _).
    assert (NLB : ~ (lb <= a < lb + Z.of_nat (length U) + 1)).
    { intros H. apply (FL_img (a - lb) ltac:(lia)). replace (lb + (a - lb)) with a by ring. exact Hi. }
    assert (NCB : ~ (cb <= a < cb + Z.of_nat (length ln) + 1)).
    { intros H. apply (FC_img (a - cb) ltac:(lia)). replace (cb + (a - cb)) with a by ring. exact Hi. }
    assert (Ra : 0 <= a < 2 ^ 64) by lia.
    destruct (post_keep_glob _ _ _ _ _ _ _ _ _ _ _ _ a POST2 MR1 ltac:(rewrite SP1; unfold STRNDUP_STACK, ALLOC_STACK; lia)
      ltac:(intros y Hy; cbv beta in Hy; replace y with (lb + (y - lb)) by ring; apply FL_img; lia) HG) as [E2 K2].
    destruct (post_keep_glob _ _ _ _ _ _ _ _ _ _ _ _ a POST4 MR3 ltac:(rewrite SP3; unfold STRDUP_STACK, ALLOC_STACK; lia)
      ltac:(intros y Hy; cbv beta in Hy; replace y with (cb + (y - cb)) by ring; apply FC_img; lia) HG) as [E4 K4].
    pose proof (munch_mbyte rsegs _ _ _ a MU1 Ra (OUT1 a Ra ltac:(lia))) as E1.
    pose proof (munch_writable rsegs _ _ _ a MU1 Ra (OUT1 a Ra ltac:(lia))) as K1.
    pose proof (munch_mbyte rsegs _ _ _ a MU3 Ra (OUT3 a Ra ltac:(lia) NLB)) as E3.
    pose proof (munch_writable rsegs _ _ _ a MU3 Ra (OUT3 a Ra ltac:(lia) NLB)) as K3.
    pose proof (munch_mbyte rsegs _ _ _ a MU5 Ra (OUT5 a Ra ltac:(lia) NCB)) as E5.
    pose proof (munch_writable rsegs _ _ _ a MU5 Ra (OUT5 a Ra ltac:(lia) NCB)) as K5.
    split; [rewrite E5, E4, E3, E2, E1; reflexivity | tauto]. }
  assert (G5_2 : getr R5 2 = Z_to_bv 64 (bv_unsigned sp - 608))
    by (rewrite (getr_of_eqv _ _ 2 X5 eq_refl); simp_regs; reflexivity).
  assert (G5_9 : getr R5 9 = Z_to_bv 64 cb) by (rewrite (getr_of_eqv _ _ 9 X5 eq_refl); simp_regs; reflexivity).
  assert (G5_8 : getr R5 8 = Z_to_bv 64 lb).
  { rewrite (getr_of_eqv _ _ 8 X5 eq_refl). simp_regs. exact (eq_trans (HPRES4 8 ltac:(unfold callee_saved; lia)) E3_8). }
  assert (GC3 : getr R5 3 = getr regs 3).
  { rewrite (getr_of_eqv _ _ 3 X5 eq_refl). simp_regs.
    assert (A3 : getr R3 3 = reg_get R2 3) by (rewrite (getr_of_eqv _ _ 3 X3 eq_refl); simp_regs; reflexivity).
    assert (B1 : getr R1 3 = reg_get regs 3) by (rewrite (getr_of_eqv _ _ 3 X1 eq_refl); simp_regs; reflexivity).
    exact (eq_trans (HPRES4 3 ltac:(unfold callee_saved; lia))
             (eq_trans A3 (eq_trans (HPRES2 3 ltac:(unfold callee_saved; lia)) B1))). }
  assert (GC4 : getr R5 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X5 eq_refl). simp_regs.
    assert (A3 : getr R3 4 = reg_get R2 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs; reflexivity).
    assert (B1 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    exact (eq_trans (HPRES4 4 ltac:(unfold callee_saved; lia))
             (eq_trans A3 (eq_trans (HPRES2 4 ltac:(unfold callee_saved; lia)) B1))). }
  assert (GC25 : getr R5 25 = getr regs 25).
  { rewrite (getr_of_eqv _ _ 25 X5 eq_refl). simp_regs.
    assert (A3 : getr R3 25 = reg_get R2 25) by (rewrite (getr_of_eqv _ _ 25 X3 eq_refl); simp_regs; reflexivity).
    assert (B1 : getr R1 25 = reg_get regs 25) by (rewrite (getr_of_eqv _ _ 25 X1 eq_refl); simp_regs; reflexivity).
    exact (eq_trans (HPRES4 25 ltac:(unfold callee_saved; lia))
             (eq_trans A3 (eq_trans (HPRES2 25 ltac:(unfold callee_saved; lia)) B1))). }
  assert (GC26 : getr R5 26 = getr regs 26).
  { rewrite (getr_of_eqv _ _ 26 X5 eq_refl). simp_regs.
    assert (A3 : getr R3 26 = reg_get R2 26) by (rewrite (getr_of_eqv _ _ 26 X3 eq_refl); simp_regs; reflexivity).
    assert (B1 : getr R1 26 = reg_get regs 26) by (rewrite (getr_of_eqv _ _ 26 X1 eq_refl); simp_regs; reflexivity).
    exact (eq_trans (HPRES4 26 ltac:(unfold callee_saved; lia))
             (eq_trans A3 (eq_trans (HPRES2 26 ltac:(unfold callee_saved; lia)) B1))). }
  assert (GC27 : getr R5 27 = getr regs 27).
  { rewrite (getr_of_eqv _ _ 27 X5 eq_refl). simp_regs.
    assert (A3 : getr R3 27 = reg_get R2 27) by (rewrite (getr_of_eqv _ _ 27 X3 eq_refl); simp_regs; reflexivity).
    assert (B1 : getr R1 27 = reg_get regs 27) by (rewrite (getr_of_eqv _ _ 27 X1 eq_refl); simp_regs; reflexivity).
    exact (eq_trans (HPRES4 27 ltac:(unfold callee_saved; lia))
             (eq_trans A3 (eq_trans (HPRES2 27 ltac:(unfold callee_saved; lia)) B1))). }
  assert (G5_18 : getr R5 18 = Z_to_bv 64 msg).
  { rewrite (getr_of_eqv _ _ 18 X5 eq_refl). simp_regs.
    assert (A3 : getr R3 18 = reg_get R2 18) by (rewrite (getr_of_eqv _ _ 18 X3 eq_refl); simp_regs; reflexivity).
    exact (eq_trans (HPRES4 18 ltac:(unfold callee_saved; lia))
             (eq_trans A3 (eq_trans (HPRES2 18 ltac:(unfold callee_saved; lia)) E1_18))). }
  destruct (ax_statics AX L4 A4 m5 md4 MR5) as (GW5 & (g5 & Rg5 & GV5) & _).
  rewrite GOTG, GUARDA, SEGS in GW5. rewrite GUARDA, SEGS in GV5.
  assert (SSP5 : VerbsMem.ssp_at m5 (Z_to_bv 64 g5)).
  { unfold VerbsMem.ssp_at, VerbsMem.SSP_GOT, VerbsMem.SSP_GUARD.
    split; [apply word_mem_le8; [exact GW5 | lia | lia | lia] | apply word_mem_le8; [exact GV5 | lia | lia | lia]]. }
  assert (LB5 : bytes_at rsegs m5 lb (ln ++ repeat (Z_to_bv 8 0) k0 ++ [Z_to_bv 8 0])).
  { assert (LB4 : bytes_at rsegs m4 lb (ln ++ repeat (Z_to_bv 8 0) k0 ++ [Z_to_bv 8 0])).
    { apply (bytes_at_transfer rsegs m3); [exact (proj1 LBU3)|]. intros i Hi.
      rewrite !length_app, repeat_length in Hi. cbn [length] in Hi.
      pose proof (KEPT4 lb (Z.of_nat (length U) + 1) i INLB (fun F => F) ltac:(unfold k0 in Hi; lia)) as KE.
      rewrite SEGS in KE. exact KE. }
    apply (bytes_at_transfer rsegs m4); [exact LB4|]. intros i Hi.
    rewrite !length_app, repeat_length in Hi. cbn [length] in Hi.
    assert (HLin : In (lb, Z.of_nat (length U) + 1) (c1 ++ c2)) by (rewrite <- BL4b, BL2a; apply in_or_app; right; left; reflexivity).
    pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR4 BL4a HLin) as Dj.
    eapply munch_mbyte; [exact MU5 | lia | apply OUT5; unfold k0 in Hi; lia]. }
  assert (FRR5 : rw_cells rsegs m5 (bv_unsigned sp - 608 + 520)
                  [CB 8 (firstn 8 (skipn 512 (firstn 520 (skipn 8 junk1)))); C8 (reg_get regs 24); C8 (reg_get regs 23);
                   C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20); C8 (reg_get regs 19);
                   C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { replace (bv_unsigned sp - 608 + 520) with (bv_unsigned sp - 608 + Z.of_nat 520) by lia.
    eapply rw_cells_transport; [exact FRR4 | exact MU5 | exact WM5 |]. unfold W5. cbn. lia. }
  rewrite SEGS in KONT. apply KONT. unfold vr_mid.
  exists L4, A4, R5, m5, md4, lb, cb, ps, (Z_to_bv 64 g5), (firstn 8 (skipn 512 (firstn 520 (skipn 8 junk1)))), b1, b2, c1, c2.
  change (spZ regs) with (bv_unsigned sp).
  split; [reflexivity|]. split; [exact SI5|]. split; [exact WK|]. split; [exact RO5|].
  split; [exact G5_2|]. split; [exact GC3|]. split; [exact GC4|].
  split; [exact G5_8|]. split; [exact G5_9|]. split; [exact G5_18|].
  split.
  { intros HNE. destruct (S35 HNE) as [H3 H5].
    split; [rewrite (getr_of_eqv _ _ 19 X5 eq_refl); simp_regs; exact H3 | rewrite (getr_of_eqv _ _ 21 X5 eq_refl); simp_regs; exact H5]. }
  split; [exact GC25|]. split; [exact GC26|]. split; [exact GC27|].
  split; [exact FRR5|]. split; [exists junk5; exact TJ5|]. split; [exact TA5|]. split; [exact FW5|].
  split; [exact BL2b|]. split; [rewrite <- BL4b; exact BL2a|]. split; [exact BL4a|].
  split; [exact FRESH2|]. split; [exact FRESH4|].
  split; [intros q k H; apply UBK4, UBK2, H|]. split; [exact INIT4|]. split; [exact RES4|].
  split; [exact LB5 | exact SSP5].
Qed.

End P.

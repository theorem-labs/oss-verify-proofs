(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module paths, addresses and numbers changed; 779 of its 856 lines of code are new or changed and 471 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/rec_clear.v, with its module paths, addresses and numbers changed; 1564 of its 1647 lines of code are new or changed and 773 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/rec_calls_copy.v, with its module paths, module names, addresses and numbers changed; 1016 of its 1927 lines of code are new or changed and 736 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require rec_calls_free.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strlen_c memcpy_c rec_calls_copy_k rec_calls_copy_k2.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB RecChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecSeq RecStep RecGlue xmalloc_c rec_calls_copy_c.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Open Scope Z_scope.

Lemma rcc_b_app : forall b xs ys, rcc_b b (xs ++ ys) = rcc_b (rcc_b b xs) ys.
Proof. intros b xs ys. unfold rcc_b. apply fold_left_app. Qed.

Lemma rcc_b_snoc : forall b xs x, rcc_b b (xs ++ [x]) = sb_malloc (rcc_b b xs) (Z.of_nat (length x) + 1).
Proof. intros b xs x. rewrite rcc_b_app. reflexivity. Qed.

Lemma rcc_b_grow : forall ys b, sb_le b (rcc_b b ys).
Proof.
  induction ys as [|y ys IH]; intros b; unfold rcc_b in *; cbn [fold_left]; [apply sb_le_refl|].
  apply (sb_le_trans b (sb_malloc b (Z.of_nat (length y) + 1))); [apply sb_le_malloc; lia | apply IH].
Qed.

Lemma rcc_args_snoc : forall cs i c, nth_error cs i = Some c ->
  rcc_args (firstn (S i) cs) = rcc_args (firstn i cs) ++ snd c.
Proof.
  intros cs i c H. unfold rcc_args. rewrite (CF.rec_calls_free.firstn_snoc cs i c H), map_app, concat_app.
  cbn [map concat]. rewrite app_nil_r. reflexivity.
Qed.

Lemma rcc_args_split : forall cs i c, nth_error cs i = Some c ->
  rcc_args cs = rcc_args (firstn i cs) ++ snd c ++ rcc_args (skipn (S i) cs).
Proof.
  intros cs i c H. rewrite app_assoc, <- (rcc_args_snoc cs i c H). unfold rcc_args.
  rewrite <- concat_app, <- map_app, firstn_skipn. reflexivity.
Qed.

Lemma rcc_xs_snoc : forall (cs : list rcall) (i : nat) (c : rcall) (j : nat) (x : list byte), nth_error (snd c) j = Some x ->
  rcc_args (firstn i cs) ++ firstn (S j) (snd c) = (rcc_args (firstn i cs) ++ firstn j (snd c)) ++ [x].
Proof. intros cs i c j x H. rewrite (CF.rec_calls_free.firstn_snoc _ j x H), app_assoc. reflexivity. Qed.

Lemma rcc_room : forall b (cs : list rcall) (i : nat) (c : rcall) (j : nat) (x : list byte),
  nth_error cs i = Some c -> nth_error (snd c) j = Some x ->
  room_ag (rcc_b b (rcc_args cs)) (LMAX + 1) -> Z.of_nat (length x) <= LMAX ->
  room_ag (sb_malloc (rcc_b b (rcc_args (firstn i cs) ++ firstn j (snd c))) (Z.of_nat (length x) + 1))
    (Z.of_nat (length x) + 1).
Proof.
  intros b cs i c j x Hc Hx RM Hl.
  rewrite <- rcc_b_snoc, <- (rcc_xs_snoc cs i c j x Hx).
  apply (room_slots_mono _ (rcc_b b (rcc_args cs)) _ (LMAX + 1)); [| lia | exact RM].
  rewrite (rcc_args_split cs i c Hc). rewrite <- (firstn_skipn (S j) (snd c)) at 2.
  rewrite <- !app_assoc, app_assoc, (rcc_b_app b (rcc_args (firstn i cs) ++ firstn (S j) (snd c))).
  apply rcc_b_grow.
Qed.

Lemma not_out1 : forall lo hi a, ~ outside [(lo, hi)] a -> lo <= a < hi.
Proof.
  intros lo hi a H. destruct (Z_le_gt_dec lo a); destruct (Z_lt_ge_dec a hi);
    first [lia | exfalso; apply H; cbn; split; [lia | exact I]].
Qed.

Lemma mkR_getr : forall R : bvmap 5 word, Regs6ss.mkR_of R =
  mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9) (getr R 10)
      (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19)
      (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28)
      (getr R 29) (getr R 30) (getr R 31).
Proof. reflexivity. Qed.

Lemma rc_got_seg : forall i, 0 <= i < 8 -> find_segment rsegs (0x22d40 + i) 1 <> None.
Proof.
  intros i Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct C as [C | [C | [C | [C | [C | [C | [C | C]]]]]]]; subst i; intro F; vm_compute in F; discriminate F.
Qed.

Lemma k_zero_any : forall (sw dw ra0 gp tp s0_0 s1_0 s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0 : word)
    (F : bvmap 5 word) (fc : bv 32) (n : nat) (Q : machine_state -> Prop) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m
    junk,
  2 ^ 20 <= bv_unsigned sw - 128 -> n = 0%nat ->
  rw_cells rsegs m (bv_unsigned sw + -128) [CB 128 junk] ->
  rw_cells rsegs m 0x34030 [C4 (Z_to_bv 64 (Z.of_nat n))] ->
  (forall m', rw_cells rsegs m' (bv_unsigned sw + -104)
                (FRS ra0 s0_0 s1_0 s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0) ->
     munch [(bv_unsigned sw + -128, bv_unsigned sw)] m m' -> wmono rsegs m m' ->
     st_ret sw ra0 gp tp s0_0 s1_0 s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0 F fc n Q m') ->
  evt rsegs Q (entry_ms sw dw ra0 gp tp s0_0 s1_0 s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0 F fc
                 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m).
Proof.
  intros sw dw ra0 gp tp s0_0 s1_0 s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0 F fc n Q
    t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m junk HSW Hn FR NC HK.
  unfold entry_ms.
  pose proof (munch_refl [(bv_unsigned sw + -128, bv_unsigned sw)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  apply (rw_cells_split_CB rsegs _ _ [] 128%nat junk [] [24; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR;
    [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 17 step.
  rewrite rk_sx32 by lia.
  step.
  rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace (0 <? Z.of_nat n) with false by (rewrite Hn; reflexivity). cbn [andb negb].
  destruct (rk_app_split rsegs _ _ 24 [CB 24 (firstn 24 junk)]
              (FRS ra0 s0_0 s1_0 s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0) eq_refl FR) as [_ F2].
  replace (bv_unsigned sw + -128 + 24) with (bv_unsigned sw + -104) in F2 by lia.
  eapply (k_epi sw sw ra0 gp tp s0_0 s1_0 s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0 F fc n);
    [ | exact F2 | exact (HK _ F2 MU WM)].
  unfold KOK. rewrite Hn. cbn [Z.of_nat]. lia.
Qed.

Lemma rw_munch : forall W m m' a cs, rw_cells rsegs m a cs -> munch W m m' ->
  (forall t, 0 <= t < Z.of_nat (cells_size cs) -> 0 <= a + t < 2 ^ 64 /\ outside W (a + t)) ->
  rw_cells rsegs m' a cs.
Proof.
  intros W m m' a cs H MU D. apply (rw_cells_transfer rsegs m m' a cs H). intros t Ht.
  destruct (D t Ht) as [Ra Oa]. split; [exact (munch_mbyte rsegs W m m' _ MU Ra Oa)|].
  apply (munch_writable rsegs W m m' _ MU Ra Oa).
Qed.

Lemma by_munch : forall W m m' a bs, bytes_at rsegs m a bs -> munch W m m' ->
  (forall t, 0 <= t < Z.of_nat (length bs) -> 0 <= a + t < 2 ^ 64 /\ outside W (a + t)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs H MU D. apply (bytes_at_transfer rsegs m m' a bs H). intros t Ht.
  destruct (D t Ht) as [Ra Oa]. exact (munch_mbyte rsegs W m m' _ MU Ra Oa).
Qed.

Lemma wview_ext : forall m1 m2 x, m1 x = m2 x -> wview rsegs m1 x = wview rsegs m2 x.
Proof. intros m1 m2 x E. unfold wview. rewrite E. reflexivity. Qed.

Definition mmid (p n : Z) (m m' : word -> option byte) : word -> option byte :=
  fun x => if (p <=? bv_unsigned x) && (bv_unsigned x <? p + n) then m' x else m x.

Lemma munch2_mid : forall p n X m m', munch [(p, p + n); (X, X + 8)] m m' -> wmono rsegs m m' ->
  munch [(p, p + n)] m (mmid p n m m') /\ wmono rsegs m (mmid p n m m') /\
  munch [(X, X + 8)] (mmid p n m m') m' /\ wmono rsegs (mmid p n m m') m' /\
  (forall a, 0 <= a < 2 ^ 64 -> p <= a < p + n -> mbyte rsegs (mmid p n m m') a = mbyte rsegs m' a /\
     (writable_at rsegs m' a -> writable_at rsegs (mmid p n m m') a)).
Proof.
  intros p n X m m' MU WM.
  assert (IN : forall x, p <= bv_unsigned x < p + n -> mmid p n m m' x = m' x).
  { intros x Hx. unfold mmid. destruct (Z.leb_spec p (bv_unsigned x)); [|lia].
    destruct (Z.ltb_spec (bv_unsigned x) (p + n)); [reflexivity | lia]. }
  assert (OUT : forall x, ~ (p <= bv_unsigned x < p + n) -> mmid p n m m' x = m x).
  { intros x Hx. unfold mmid. destruct (Z.leb_spec p (bv_unsigned x)); [|reflexivity].
    destruct (Z.ltb_spec (bv_unsigned x) (p + n)); [lia | reflexivity]. }
  split; [|split; [|split; [|split]]].
  - intros x Hx. cbn [outside] in Hx. apply OUT. tauto.
  - intros x Hx. destruct (Z_le_gt_dec p (bv_unsigned x)); [destruct (Z_lt_ge_dec (bv_unsigned x) (p + n))|].
    + rewrite (wview_ext _ _ x (IN x ltac:(lia))). apply WM. exact Hx.
    + rewrite (wview_ext _ _ x (OUT x ltac:(lia))). exact Hx.
    + rewrite (wview_ext _ _ x (OUT x ltac:(lia))). exact Hx.
  - intros x Hx. cbn [outside] in Hx.
    destruct (Z_le_gt_dec p (bv_unsigned x)); [destruct (Z_lt_ge_dec (bv_unsigned x) (p + n))|].
    + rewrite (IN x ltac:(lia)). reflexivity.
    + rewrite (OUT x ltac:(lia)). apply MU. cbn [outside]. split; [lia|]. split; [tauto | exact I].
    + rewrite (OUT x ltac:(lia)). apply MU. cbn [outside]. split; [lia|]. split; [tauto | exact I].
  - intros x Hx. destruct (Z_le_gt_dec p (bv_unsigned x)); [destruct (Z_lt_ge_dec (bv_unsigned x) (p + n))|].
    + rewrite <- (wview_ext _ _ x (IN x ltac:(lia))). exact Hx.
    + rewrite (wview_ext _ _ x (OUT x ltac:(lia))) in Hx. apply WM. exact Hx.
    + rewrite (wview_ext _ _ x (OUT x ltac:(lia))) in Hx. apply WM. exact Hx.
  - intros a Ra Ha. assert (U : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
    split.
    + unfold mbyte. rewrite (IN (Z_to_bv 64 a) ltac:(lia)). reflexivity.
    + unfold writable_at. rewrite (wview_ext _ _ _ (IN (Z_to_bv 64 a) ltac:(lia))). tauto.
Qed.

Lemma minv_munch1 : forall lo hi m m', mem_inv rsegs m -> munch [(lo, hi)] m m' ->
  2 ^ 20 <= lo -> hi <= 2 ^ 64 -> mem_inv rsegs m'.
Proof.
  intros lo hi m m' MI MU H1 H2 a bb Ha. pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
  cbn in Ra.
  destruct (Z_le_gt_dec lo (bv_unsigned a)) as [L1|L1]; [destruct (Z_lt_ge_dec (bv_unsigned a) hi) as [L2|L2]|].
  - pose proof (hi_rw (bv_unsigned a) ltac:(lia)) as E. rewrite Z_to_bv_bv_unsigned in E. exact E.
  - rewrite (MU a ltac:(cbn [outside]; split; [lia | exact I])) in Ha. exact (MI a bb Ha).
  - rewrite (MU a ltac:(cbn [outside]; split; [lia | exact I])) in Ha. exact (MI a bb Ha).
Qed.

Section SR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis ERRNO : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis SLACK : block_slack_present B API.
Hypothesis XM : xmalloc_contract B API.
Hypothesis SLEN : strlen_contract.
Hypothesis MCPY : memcpy_contract.

Definition mchain (S K : Z) (E : Z -> Prop) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (b : sbound) (xs : list (list byte)) (N : list (Z * Z))
    (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model) : Prop :=
  aa_MR API Lc Ac memc mdc /\ WF Ac /\ bounded Ac /\
  layout_le A L Lc /\ (length (st_regions A) <= length (st_regions Ac))%nat /\
  (st_init_done A = true -> st_init_done Ac = true) /\
  (exists vm, mdc = with_vmmaps vm md) /\
  (forall y, In y (user_blocks A) -> In y (user_blocks Ac)) /\
  (forall p n, In (p, n) (user_blocks A) -> ptr_addr Lc p = ptr_addr L p) /\
  Permutation (blocks Lc Ac) (blocks L A ++ N) /\
  NoDup (map fst N) /\
  (forall pn q, In pn N -> In q (blocks L A) -> fst pn + snd pn <= fst q \/ fst q + snd q <= fst pn) /\
  (forall pn, In pn N -> 0 < snd pn) /\
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n ->
     mbyte (ms_segs B) memc (ptr_addr L p + i) = mbyte (ms_segs B) mem (ptr_addr L p + i)) /\
  (forall a, hi_img B a -> ~ owned B L A a -> ~ (S - K <= a < S) -> ~ errw B a -> ~ E a ->
     mbyte (ms_segs B) memc a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) memc a)) /\
  (forall a, S - K <= a < S \/ errw B a -> writable_at (ms_segs B) memc a) /\
  ro_agree (ms_segs B) memc /\ guard_kept B mem memc /\
  res_ok_slots Ac (rcc_b b xs).

Lemma mchain_init : forall S K E L A regs mem md b,
  call_pre_k B (aa_MR API) K L A regs mem md -> ro_agree (ms_segs B) mem -> res_ok_slots A b -> spZ regs = S ->
  mchain S K E L A mem md b [] [] L A mem md.
Proof.
  intros S K E L A regs mem md b (HM & HW & HB & _ & _ & _ & _ & HWS & _ & HERR & _) HRO HRES <-.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [lia|]. split; [tauto|]. split; [exists (m_vmmaps md); apply YI04.with_vmmaps_self|].
  split; [intros y Hy; exact Hy|]. split; [intros; reflexivity|].
  split; [rewrite app_nil_r; apply Permutation_refl|].
  split; [constructor|]. split; [intros pn q []|]. split; [intros pn []|].
  split; [intros; reflexivity|]. split; [intros; split; [reflexivity | tauto]|].
  split; [intros a [Ha|Ha]; [apply HWS; exact Ha | apply HERR; exact Ha]|].
  split; [exact HRO|]. split; [intros i _; reflexivity|]. exact HRES.
Qed.

Lemma mchain_own : forall S K E L A mem md b xs N Lc Ac memc mdc m' W,
  mchain S K E L A mem md b xs N Lc Ac memc mdc ->
  munch W memc m' -> wmono (ms_segs B) memc m' ->
  alloc_ceiling + K <= S -> S <= 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a ->
     (S - K <= a < S) \/ (E a /\ (alloc_ceiling <= a \/ in_globals frame_G a))) ->
  mchain S K E L A mem md b xs N Lc Ac m' mdc.
Proof using SEGS AX GOWN GFACT GOTG.
  intros S K E L A mem md b xs N Lc Ac memc mdc m' W
    (HMc & HWc & HBc & HLE & HRG & HINIT & HVM & HSUB & HPTR & HPERM & HND & HDJ & HPOS & HBYTES & HFRAME & HSCR
     & HRO & HGK & HRES) MU WM HK HS HW.
  pose proof alloc_ceiling_val as AC.
  assert (OUTL : forall a, 0 <= a < alloc_ceiling -> ~ in_globals frame_G a -> outside W a).
  { intros a Ha Hg. destruct (outside_dec W a) as [O|O]; [exact O|].
    destruct (HW a ltac:(lia) O) as [H|(_ & [H|H])]; [lia | lia | contradiction]. }
  assert (OUTB : forall q k i, In (q, k) (blocks Lc Ac) -> 0 <= i < k -> outside W (q + i)).
  { intros q k i Hin Hi. pose proof (block_facts B _ (aa_laws API) Lc Ac memc mdc q k i HMc Hin Hi) as (_ & H1 & H2 & _).
    apply OUTL; [lia|]. intros Hg. apply (block_not_img B API AX Lc Ac memc mdc q k i HMc Hin Hi).
    exact (proj1 (GFACT _ Hg)). }
  assert (OUTO : forall a, owned B Lc Ac a -> outside W a).
  { intros a Ho. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho). apply OUTL; [lia|].
    intros Hg. exact (GOWN _ _ _ _ a HMc Hg Ho). }
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HMc) as (Hh & Hl & Hmat).
  split.
  { eapply (mr_frame B _ (aa_laws API) Lc Ac memc m' mdc mdc HMc).
    - intros a Ho. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho).
      apply (munch_mbyte _ W memc m'); [exact MU | lia | exact (OUTO a Ho)].
    - intros a Ho Hp. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho).
      apply (munch_present W memc m'); [exact MU | lia | exact (OUTO a Ho) | exact Hp].
    - intros p n i Hin Hi.
      assert (Hb : In (ptr_addr Lc p, n) (blocks Lc Ac)) by (unfold blocks; apply in_map_iff; exists (p, n); auto).
      pose proof (block_facts B _ (aa_laws API) _ _ _ _ _ _ i HMc Hb Hi) as (Hp & H1 & H2 & _).
      apply (munch_present W memc m'); [exact MU | lia | exact (OUTB _ _ i Hb Hi) | exact Hp].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact HWc|]. split; [exact HBc|]. split; [exact HLE|]. split; [exact HRG|]. split; [exact HINIT|].
  split; [exact HVM|]. split; [exact HSUB|]. split; [exact HPTR|]. split; [exact HPERM|].
  split; [exact HND|]. split; [exact HDJ|]. split; [exact HPOS|].
  split.
  { intros p n i Hin Hi.
    assert (Hb : In (ptr_addr Lc p, n) (blocks Lc Ac))
      by (unfold blocks; apply in_map_iff; exists (p, n); split; [reflexivity | exact (HSUB _ Hin)]).
    pose proof (block_facts B _ (aa_laws API) _ _ _ _ _ _ i HMc Hb Hi) as (_ & H1 & H2 & _).
    rewrite <- (HPTR p n Hin).
    rewrite (munch_mbyte _ W memc m' (ptr_addr Lc p + i) MU ltac:(lia) (OUTB _ _ i Hb Hi)).
    rewrite (HPTR p n Hin). exact (HBYTES p n i Hin Hi). }
  split.
  { intros a Ha Hno Hs He HE. pose proof (hi_img_range B SEGS a Ha) as R.
    assert (O : outside W a).
    { destruct (outside_dec W a) as [O|O]; [exact O|]. exfalso.
      destruct (HW a R O) as [H|(H & _)]; [exact (Hs H) | exact (HE H)]. }
    destruct (HFRAME a Ha Hno Hs He HE) as [E1 E2].
    split; [rewrite (munch_mbyte _ W memc m' a MU R O); exact E1|].
    rewrite E2. exact (munch_writable _ W memc m' a MU R O). }
  split; [intros a Ha; apply WM; exact (HSCR a Ha)|].
  split.
  { intros y Hro. unfold mrd.
    destruct (outside_dec W (bv_unsigned y)) as [O|O].
    - rewrite (MU y O). exact (HRO y Hro).
    - exfalso. pose proof (bv_unsigned_in_range 64 y) as R. unfold bv_modulus in R.
      rewrite SEGS in Hro.
      destruct (HW (bv_unsigned y) ltac:(cbn in R; lia) O) as [H|(_ & [H|H])].
      + rewrite <- (Z_to_bv_bv_unsigned y) in Hro. rewrite (hi_rw (bv_unsigned y)) in Hro by lia. discriminate.
      + rewrite <- (Z_to_bv_bv_unsigned y) in Hro. rewrite (hi_rw (bv_unsigned y)) in Hro by (cbn in R; lia).
        discriminate.
      + rewrite <- (Z_to_bv_bv_unsigned y) in Hro. rewrite (fg_rw (bv_unsigned y) H) in Hro. discriminate. }
  split.
  { intros i Hi. rewrite <- (HGK i Hi). rewrite GOTG.
    apply (munch_mbyte _ W memc m'); [exact MU | lia|]. apply OUTL; [lia|]. rewrite fg_iff. lia. }
  exact HRES.
Qed.

Lemma mchain_x : forall S K E L A mem md b xs N Lc Ac memc mdc regs_c x p L2 A2 regs2 mem2 md2,
  aa_MR API L A mem md -> alloc_ceiling + K <= S -> S <= 2 ^ 64 ->
  mchain S K E L A mem md b xs N Lc Ac memc mdc ->
  S - K <= spZ regs_c - XMALLOC_K -> spZ regs_c <= S ->
  call_post_k B (aa_MR API) XMALLOC_K Lc Ac regs_c memc mdc (fun _ => False) L2 A2 regs2 mem2 md2 ->
  fresh_block B p (Z.of_nat (length x) + 1) ->
  (exists b1 b2, blocks L2 A2 = b1 ++ (p, Z.of_nat (length x) + 1) :: b2 /\ blocks Lc Ac = b1 ++ b2) ->
  (forall q k, In (q, k) (user_blocks Ac) -> In (q, k) (user_blocks A2)) ->
  ro_agree (ms_segs B) mem2 -> guard_kept B memc mem2 ->
  st_init_done A2 = true ->
  (length (st_regions Ac) <= length (st_regions A2))%nat ->
  res_ok_slots A2 (sb_malloc (rcc_b b xs) (Z.of_nat (length x) + 1)) ->
  mchain S K E L A mem md b (xs ++ [x]) (N ++ [(p, Z.of_nat (length x) + 1)]) L2 A2 mem2 md2.
Proof using CTX AX ERRNO.
  intros S K E L A mem md b xs N Lc Ac memc mdc regs_c x p L2 A2 regs2 mem2 md2 HM0 HK HS
    (HMc & HWc & HBc & HLE & HRG & HINIT & (vm & Hvm) & HSUB & HPTR & HPERM & HND & HDJ & HPOS & HBYTES & HFRAME
     & HSCR & HRO & HGK & HRES)
    Hlo Hhi (HM2 & HW2 & HB2 & HLE2 & HSTAB & _ & (vm2 & Hvm2) & HFR2 & HKB2 & HSCR2)
    (FP1 & FP2 & FP3) (b1 & b2 & EB2 & EB1) HUB HRO2 HGK2 HI2 HRG2 HRES2.
  pose proof alloc_ceiling_val as AC.
  assert (INC : forall q, In q (blocks Lc Ac) ->
            fst q + snd q <= p \/ p + (Z.of_nat (length x) + 1) <= fst q).
  { intros [q kq] Hq. rewrite EB1 in Hq.
    exact (blocks_mid_disjoint B _ (aa_laws API) L2 A2 mem2 md2 b1 b2 p _ q kq HM2 EB2 Hq). }
  split; [exact HM2|]. split; [exact HW2|]. split; [exact HB2|].
  split; [exact (layout_le_trans A Ac L Lc L2 HLE HLE2 HRG)|].
  split; [lia|]. split; [intros _; exact HI2|].
  split; [exists vm2; rewrite Hvm2, Hvm; apply YI04.with_vmmaps_twice|].
  split; [intros [q kq] Hy; apply HUB; apply HSUB; exact Hy|].
  split; [intros q kq Hq; rewrite (HSTAB q kq (HSUB _ Hq) (HUB q kq (HSUB _ Hq))); exact (HPTR q kq Hq)|].
  split.
  { rewrite EB2. apply (Permutation_trans (l' := (p, Z.of_nat (length x) + 1) :: b1 ++ b2));
      [apply Permutation_sym, Permutation_middle|].
    apply (Permutation_trans (l' := (b1 ++ b2) ++ [(p, Z.of_nat (length x) + 1)])); [apply Permutation_cons_append|].
    rewrite <- EB1, app_assoc. apply Permutation_app_tail. exact HPERM. }
  split.
  { apply nodup_fst_snoc; [exact HND|]. intros Hin. apply in_map_iff in Hin as ([q kq] & Eq & Hq). cbn in Eq. subst q.
    assert (Hc : In (p, kq) (blocks Lc Ac))
      by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; exact Hq).
    pose proof (HPOS _ Hq) as Hp. cbn in Hp. destruct (INC _ Hc) as [D|D]; cbn in D; lia. }
  split.
  { intros pn q Hpn Hq. apply in_app_or in Hpn as [Hpn|Hpn]; [exact (HDJ pn q Hpn Hq)|].
    destruct Hpn as [<-|[]]. cbn [fst snd].
    assert (Hc : In q (blocks Lc Ac))
      by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hq).
    destruct (INC q Hc) as [D|D]; [right; exact D | left; exact D]. }
  split; [intros pn Hpn; apply in_app_or in Hpn as [Hpn|[<-|[]]]; [exact (HPOS _ Hpn) | cbn; lia]|].
  split.
  { intros q kq i Hq Hi. pose proof (HSUB _ Hq) as Hc.
    pose proof (HKB2 q kq i Hc (HUB q kq Hc) Hi) as Eb. rewrite (HPTR q kq Hq) in Eb. rewrite Eb.
    exact (HBYTES q kq i Hq Hi). }
  split.
  { intros a Ha Hno Hs He HE. destruct (HFRAME a Ha Hno Hs He HE) as [E1 E2].
    assert (Hnc : ~ owned B Lc Ac a) by exact (own_any B API AX CTX L A mem md Lc Ac memc mdc a HM0 HMc Ha Hno).
    assert (Hn2 : ~ owned B L2 A2 a) by exact (own_any B API AX CTX L A mem md L2 A2 mem2 md2 a HM0 HM2 Ha Hno).
    assert (Hns : ~ scratch_k B XMALLOC_K regs_c a)
      by (unfold scratch_k; intros [H|H]; [apply Hs; lia | exact (He H)]).
    destruct (HFR2 a Ha Hnc Hn2 Hns (fun F => F)) as [F1 F2]. split; [congruence | tauto]. }
  split.
  { intros a Ha.
    destruct (Z_le_gt_dec (spZ regs_c - XMALLOC_K) a) as [D1|D1];
      [destruct (Z_lt_ge_dec a (spZ regs_c)) as [D2|D2]|].
    - apply HSCR2. left. lia.
    - destruct Ha as [Ha|Ha]; [|apply HSCR2; right; exact Ha].
      assert (Hh : alloc_ceiling <= a < 2 ^ 64) by lia.
      assert (Hn1 : ~ owned B Lc Ac a) by (intros Ho; pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho); lia).
      assert (Hn2 : ~ owned B L2 A2 a) by (intros Ho; pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho); lia).
      assert (Hns : ~ scratch_k B XMALLOC_K regs_c a) by (unfold scratch_k; intros [H|H]; lia).
      apply (proj2 (HFR2 a (or_introl Hh) Hn1 Hn2 Hns (fun F => F))). apply HSCR. left. exact Ha.
    - destruct Ha as [Ha|Ha]; [|apply HSCR2; right; exact Ha].
      assert (Hh : alloc_ceiling <= a < 2 ^ 64) by (unfold XMALLOC_K, ALLOC_STACK in *; lia).
      assert (Hn1 : ~ owned B Lc Ac a) by (intros Ho; pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho); lia).
      assert (Hn2 : ~ owned B L2 A2 a) by (intros Ho; pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho); lia).
      assert (Hns : ~ scratch_k B XMALLOC_K regs_c a) by (unfold scratch_k; intros [H|H]; lia).
      apply (proj2 (HFR2 a (or_introl Hh) Hn1 Hn2 Hns (fun F => F))). apply HSCR. left. exact Ha. }
  split; [exact HRO2|]. split; [intros i Hi; rewrite (HGK2 i Hi); exact (HGK i Hi)|].
  rewrite rcc_b_snoc. exact HRES2.
Qed.

Lemma mchain_blk : forall S K E L A mem md b xs N Lc Ac memc mdc m' p n,
  mchain S K E L A mem md b xs N Lc Ac memc mdc -> In (p, n) N ->
  munch [(p, p + n)] memc m' -> wmono (ms_segs B) memc m' ->
  (forall t, 0 <= t < n -> writable_at rsegs m' (p + t)) ->
  mchain S K E L A mem md b xs N Lc Ac m' mdc.
Proof using SEGS AX GOTG.
  intros S K E L A mem md b xs N Lc Ac memc mdc m' p n
    (HMc & HWc & HBc & HLE & HRG & HINIT & HVM & HSUB & HPTR & HPERM & HND & HDJ & HPOS & HBYTES & HFRAME & HSCR
     & HRO & HGK & HRES) HIN MU WM HWR.
  pose proof alloc_ceiling_val as AC.
  assert (PB : In (p, n) (blocks Lc Ac))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; exact HIN).
  pose proof (HPOS _ HIN) as Hn. cbn in Hn.
  pose proof (block_facts B _ (aa_laws API) Lc Ac memc mdc p n 0 HMc PB ltac:(lia)) as (_ & P1 & P2 & _).
  assert (OUTI : forall a, 0 <= a < 2 ^ 64 -> ~ (p <= a < p + n) -> outside [(p, p + n)] a)
    by (intros a R H; apply outside_one; [exact R | exact H]).
  assert (OUTO : forall a, owned B Lc Ac a -> outside [(p, p + n)] a).
  { intros a Ho. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho). apply OUTI; [lia|]. intros Hr.
    apply (proj2 (proj2 (proj2 (block_facts B _ (aa_laws API) _ _ _ _ _ _ (a - p) HMc PB ltac:(lia))))).
    replace (p + (a - p)) with a by ring. exact Ho. }
  assert (OUTH : forall a, hi_img B a -> outside [(p, p + n)] a).
  { intros a Ha. pose proof (hi_img_range B SEGS a Ha) as R. apply OUTI; [exact R|]. intros Hr.
    destruct Ha as [Ha|Ha]; [lia|].
    apply (block_not_img B API AX Lc Ac memc mdc p n (a - p) HMc PB ltac:(lia)).
    replace (p + (a - p)) with a by ring. exact Ha. }
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HMc) as (Hh & Hl & Hmat).
  split.
  { eapply (mr_frame B _ (aa_laws API) Lc Ac memc m' mdc mdc HMc).
    - intros a Ho. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho).
      apply (munch_mbyte _ [(p, p + n)] memc m'); [exact MU | lia | exact (OUTO a Ho)].
    - intros a Ho Hp. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho).
      apply (munch_present [(p, p + n)] memc m'); [exact MU | lia | exact (OUTO a Ho) | exact Hp].
    - intros q k i Hin Hi.
      assert (Hb : In (ptr_addr Lc q, k) (blocks Lc Ac)) by (unfold blocks; apply in_map_iff; exists (q, k); auto).
      pose proof (block_facts B _ (aa_laws API) _ _ _ _ _ _ i HMc Hb Hi) as (Hp & H1 & H2 & _).
      destruct (Z_le_gt_dec p (ptr_addr Lc q + i)) as [D1|D1];
        [destruct (Z_lt_ge_dec (ptr_addr Lc q + i) (p + n)) as [D2|D2]|].
      + apply (present_of_writable_out B SEGS m' (ptr_addr Lc q + i) ltac:(lia)).
        * exact (block_not_img B API AX Lc Ac memc mdc _ _ i HMc Hb Hi).
        * replace (ptr_addr Lc q + i) with (p + (ptr_addr Lc q + i - p)) by ring. apply HWR. lia.
      + apply (munch_present [(p, p + n)] memc m'); [exact MU | lia | apply OUTI; lia | exact Hp].
      + apply (munch_present [(p, p + n)] memc m'); [exact MU | lia | apply OUTI; lia | exact Hp].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact HWc|]. split; [exact HBc|]. split; [exact HLE|]. split; [exact HRG|]. split; [exact HINIT|].
  split; [exact HVM|]. split; [exact HSUB|]. split; [exact HPTR|]. split; [exact HPERM|].
  split; [exact HND|]. split; [exact HDJ|]. split; [exact HPOS|].
  split.
  { intros q k i Hin Hi.
    assert (Hb : In (ptr_addr L q, k) (blocks L A)) by (unfold blocks; apply in_map_iff; exists (q, k); auto).
    assert (Hb' : In (ptr_addr Lc q, k) (blocks Lc Ac))
      by (unfold blocks; apply in_map_iff; exists (q, k); split; [reflexivity | exact (HSUB _ Hin)]).
    pose proof (block_facts B _ (aa_laws API) _ _ _ _ _ _ i HMc Hb' Hi) as (_ & H1 & H2 & _).
    rewrite (HPTR q k Hin) in H1, H2.
    destruct (HDJ _ _ HIN Hb) as [D|D]; cbn [fst snd] in D;
      (rewrite (munch_mbyte _ _ memc m' (ptr_addr L q + i) MU ltac:(lia));
       [exact (HBYTES q k i Hin Hi) | apply OUTI; lia]). }
  split.
  { intros a Ha Hno Hs He HE. pose proof (hi_img_range B SEGS a Ha) as R.
    destruct (HFRAME a Ha Hno Hs He HE) as [E1 E2].
    split; [rewrite (munch_mbyte _ _ memc m' a MU R (OUTH a Ha)); exact E1|].
    rewrite E2. exact (munch_writable _ _ memc m' a MU R (OUTH a Ha)). }
  split; [intros a Ha; apply WM; exact (HSCR a Ha)|].
  split.
  { intros y Hro. unfold mrd. pose proof (bv_unsigned_in_range 64 y) as R. unfold bv_modulus in R.
    assert (O : outside [(p, p + n)] (bv_unsigned y)).
    { apply OUTH. right. apply (ro_in_img B SEGS); [cbn in R; lia|]. rewrite Z_to_bv_bv_unsigned.
      rewrite <- SEGS. exact Hro. }
    rewrite (MU y O). exact (HRO y Hro). }
  split.
  { intros i Hi. rewrite <- (HGK i Hi). rewrite GOTG.
    apply (munch_mbyte _ [(p, p + n)] memc m'); [exact MU | lia|]. apply OUTH. right.
    apply (in_img_found B SEGS); [lia | apply rc_got_seg; lia]. }
  exact HRES.
Qed.

Lemma mchain_post : forall S K E L A regs mem md b xs N L' A' regs' mem' md',
  spZ regs = S -> mchain S K E L A mem md b xs N L' A' mem' md' -> regs_preserved regs regs' ->
  call_post_k B (aa_MR API) K L A regs mem md E L' A' regs' mem' md'.
Proof.
  intros S K E L A regs mem md b xs N L' A' regs' mem' md' HS
    (HMc & HWc & HBc & HLE & HRG & HINIT & HVM & HSUB & HPTR & HPERM & HND & HDJ & HPOS & HBYTES & HFRAME & HSCR
     & HRO & HGK & HRES) HREGS.
  split; [exact HMc|]. split; [exact HWc|]. split; [exact HBc|]. split; [exact HLE|].
  split; [intros p n H1 _; exact (HPTR p n H1)|]. split; [exact HREGS|]. split; [exact HVM|].
  split.
  { intros a Ha Hno _ Hs HE. apply HFRAME; [exact Ha | exact Hno | | | exact HE].
    - intros H. apply Hs. unfold scratch_k. left. rewrite HS. exact H.
    - intros H. apply Hs. unfold scratch_k. right. exact H. }
  split; [intros p n i H1 _ Hi; exact (HBYTES p n i H1 Hi)|].
  intros a [Ha|Ha]; apply HSCR; [left; rewrite <- HS; exact Ha | right; exact Ha].
Qed.

Lemma rw2_bytes : forall segs m X u v, rw_cells segs m X [C4 u; C4 v] ->
  bytes_at segs m X (le4 u) /\ bytes_at segs m (X + 4) (le4 v) /\
  (forall t, 0 <= t < 8 -> writable_at segs m (X + t)).
Proof.
  intros segs m X u v [[_ HB] (_ & _ & HW)]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  apply bytes_at_app in HB as [H1 H2]. rewrite length_le4 in H2. change (Z.of_nat 4) with 4 in H2.
  split; [exact H1|]. split; [exact H2|]. intros t Ht. exact (HW t ltac:(cbn; lia)).
Qed.

Lemma rw2_intro : forall segs m X u v, bytes_at segs m X (le4 u) -> bytes_at segs m (X + 4) (le4 v) ->
  (forall t, 0 <= t < 8 -> writable_at segs m (X + t)) -> rw_cells segs m X [C4 u; C4 v].
Proof.
  intros segs m X u v H1 H2 HW. pose proof (bytes_at_bound _ _ _ _ H1) as B1.
  pose proof (bytes_at_bound _ _ _ _ H2) as B2. rewrite length_le4 in B1, B2.
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact H1|]. rewrite length_le4. exact H2.
  - split; [lia|]. split; [cbn; lia|]. intros t Ht. exact (HW t ltac:(cbn in Ht; lia)).
Qed.

Lemma rw8_bytes : forall segs m X w, rw_cells segs m X [C8 w] -> bytes_at segs m X (le8 w).
Proof. intros segs m X w [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

Lemma rw8_wr : forall segs m X w t, rw_cells segs m X [C8 w] -> 0 <= t < 8 -> writable_at segs m (X + t).
Proof. intros segs m X w t [_ (_ & _ & HW)] Ht. exact (HW t ltac:(cbn; lia)). Qed.

Lemma slack_rebuild' : forall m s x, bytes_at rsegs m s (x ++ [Z_to_bv 8 0]) -> 0 <= s ->
  s + Z.of_nat (length x) + 1 + 8 <= 2 ^ 64 ->
  (forall a, s + (Z.of_nat (length x) + 1) <= a < 8 * ((s + (Z.of_nat (length x) + 1) + 7) / 8) -> present m a) ->
  exists slack, bytes_at rsegs m s (x ++ Z_to_bv 8 0 :: slack) /\
    (- (s + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) /\
    s + Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) = 8 * ((s + (Z.of_nat (length x) + 1) + 7) / 8).
Proof.
  intros m s x H H0 H1 HP.
  destruct (slack_bytes rsegs m s (Z.of_nat (length x) + 1) (x ++ [Z_to_bv 8 0]) H
              ltac:(rewrite length_app; cbn [length]; lia) H0 ltac:(lia) HP) as (sl & HB & HL).
  exists sl. rewrite <- app_assoc in HB. cbn [app] in HB. split; [exact HB|].
  rewrite length_app. cbn [length]. split; Z.div_mod_to_equations; lia.
Qed.

Lemma ceil8_le : forall a b, a <= b -> b mod 8 = 0 -> 8 * ((a + 7) / 8) <= b.
Proof. intros a b H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma ceil8_mono : forall a b, a <= b -> 8 * ((a + 7) / 8) <= 8 * ((b + 7) / 8).
Proof. intros a b H. apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.div_le_mono; lia. Qed.

Section Run.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (R : rstate)
  (O : list (Z * Z)) (dst : Z) (b : sbound).
Hypothesis PRE : call_pre_k B (aa_MR API) RCC_K L A regs mem md.
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis A0 : getr regs 10 = Z_to_bv 64 dst.
Hypothesis GR : g_rec_rep (ms_segs B) L A mem R O.
Hypothesis ARR : forall j, 0 <= j < 56 * Z.of_nat (length (r_calls R)) ->
  spZ regs <= dst + j < 2 ^ 64 /\ writable_at (ms_segs B) mem (dst + j).
Hypothesis RES : res_ok_slots A b.
Hypothesis ROOM : room_ag (rcc_b b (rcc_args (r_calls R))) (LMAX + 1).

Definition POST : config -> Prop := fun c' => exists L' A' regs' mem' md' (qs : list (list (Z * Z))),
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
  call_post_k B (aa_MR API) RCC_K L A regs mem md (rcc_writes dst (r_calls R)) L' A' regs' mem' md' /\
  getr regs' 10 = Z_to_bv 64 (Z.of_nat (length (r_calls R))) /\
  length qs = length (r_calls R) /\
  (forall i c P, nth_error (r_calls R) i = Some c -> nth_error qs i = Some P ->
     call_at (ms_segs B) (blocks L' A') mem' (dst + 56 * Z.of_nat i) c P /\
     forall a s pn, nth_error (snd c) a = Some s -> nth_error P a = Some pn ->
       snd pn = Z.of_nat (length s) + 1 /\ fresh_block B (fst pn) (snd pn)) /\
  Permutation (blocks L' A') (blocks L A ++ concat qs) /\
  NoDup (map fst (concat qs)) /\
  (forall pn q, In pn (concat qs) -> In q (blocks L A) -> fst pn + snd pn <= fst q \/ fst q + snd q <= fst pn) /\
  blocks_kept B L A mem mem' (fun _ => False) /\
  (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
  g_rec_rep (ms_segs B) L' A' mem' R O /\
  (forall a, in_globals frame_G a ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) /\
  (forall j, 0 <= j < 56 * Z.of_nat (length (r_calls R)) -> writable_at (ms_segs B) mem' (dst + j)) /\
  ro_agree (ms_segs B) mem' /\ guard_kept B mem mem' /\
  (st_init_done A = true -> st_init_done A' = true) /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  res_ok_slots A' (rcc_b b (rcc_args (r_calls R))).

Definition CHS (xs : list (list byte)) (N : list (Z * Z)) (Lc : layout) (Ac : astate) (mc : word -> option byte)
    (mdc : Model) : Prop :=
  mchain (spZ regs) RCC_K (rcc_writes dst (r_calls R)) L A mem md b xs N Lc Ac mc mdc.

Lemma pre_facts : aa_MR API L A mem md /\ alloc_ceiling + RCC_K <= spZ regs /\ spZ regs < 2 ^ 63 /\
  spZ regs mod 16 = 0 /\ YK0s.ret_ok (getr regs 1) /\ WF A /\ getr regs 4 = Z_to_bv 64 (ms_tp B).
Proof using PRE.
  destruct PRE as (HM & HW & _ & HRA & HAL & HCE & H63 & _ & HTP & _). auto 7.
Qed.

Lemma rep_facts : (length (r_calls R) <= 16)%nat /\
  bytes_at (ms_segs B) mem 0x34030 (le4 (Z_to_bv 64 (Z.of_nat (length (r_calls R))))) /\
  (forall i c, nth_error (r_calls R) i = Some c -> exists P,
     call_at (ms_segs B) (blocks L A) mem (0x34038 + 56 * Z.of_nat i) c P /\
     Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)).
Proof using GR.
  destruct GR as (Q & (HS & (C1 & C2 & C3 & C4 & C5 & C6) & _) & _).
  split; [exact C1|]. split; [exact C3|].
  intros i c Hc. assert (Hi : (i < length (l_calls Q))%nat) by (rewrite C2; apply nth_error_Some; rewrite Hc; discriminate).
  destruct (nth_error (l_calls Q) i) as [P|] eqn:EP; [|apply nth_error_None in EP; lia].
  exists P. destruct (C4 i c P Hc EP) as [H1 H2]. split; [|exact H2].
  replace (0x34038 + 56 * Z.of_nat i) with (G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i)
    by (unfold G_REC, OFF_CALLS, CALL_SIZE; lia).
  exact H1.
Qed.

Lemma call_len : forall i c, nth_error (r_calls R) i = Some c -> (length (snd c) <= 6)%nat.
Proof using GR.
  intros i c Hc. destruct rep_facts as (_ & _ & H). destruct (H i c Hc) as (P & (_ & Hl & _) & _). exact Hl.
Qed.

Lemma dst_facts : (0 < length (r_calls R))%nat ->
  bv_unsigned (getr regs 10) = dst /\ spZ regs <= dst /\ dst + 56 * Z.of_nat (length (r_calls R)) <= 2 ^ 64.
Proof using A0 ARR.
  intros Hn. pose proof (bv_unsigned_in_range 64 (getr regs 2)) as RS. unfold bv_modulus in RS. cbn in RS.
  destruct (ARR 0 ltac:(lia)) as [H1 _].
  destruct (ARR (56 * Z.of_nat (length (r_calls R)) - 1) ltac:(lia)) as [H2 _].
  unfold spZ in *. split; [rewrite A0; apply unsigned_lit; lia|]. lia.
Qed.

Lemma ka_hyps : (0 < length (r_calls R))%nat ->
  KOK (getr regs 2) (getr regs 10) (length (r_calls R)) /\ bv_unsigned (getr regs 10) = dst.
Proof using PRE GR A0 ARR.
  intros Hn. destruct pre_facts as (_ & HCE & _). destruct rep_facts as (H16 & _).
  destruct (dst_facts Hn) as (UC & D1 & D2). pose proof alloc_ceiling_val as AC.
  unfold KOK, spZ, RCC_K, XMALLOC_K, ALLOC_STACK in *. rewrite UC. split; [|reflexivity].
  split; [exact H16|]. split; [lia|]. split; lia.
Qed.

Lemma rw_hi : forall a, rcc_writes dst (r_calls R) a ->
  spZ regs <= a < 2 ^ 64 /\ dst <= a < dst + 56 * Z.of_nat (length (r_calls R)).
Proof using GR A0 ARR.
  intros a (i & c & Hc & Ha). pose proof (call_len i c Hc) as Hl.
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  destruct (ARR (a - dst) ltac:(lia)) as [H _]. lia.
Qed.

Lemma mc_frame : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc ->
  forall a, hi_img B a -> ~ owned B L A a -> ~ (spZ regs - RCC_K <= a < spZ regs) -> ~ errw B a ->
    ~ rcc_writes dst (r_calls R) a ->
    mbyte (ms_segs B) mc a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mc a).
Proof. intros xs N Lc Ac mc mdc (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma mc_MR : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc -> aa_MR API Lc Ac mc mdc /\ WF Ac.
Proof. intros xs N Lc Ac mc mdc (H1 & H2 & _). auto. Qed.

Lemma mc_perm : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc -> Permutation (blocks Lc Ac) (blocks L A ++ N).
Proof. intros xs N Lc Ac mc mdc (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma mc_scr : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc ->
  forall a, spZ regs - RCC_K <= a < spZ regs \/ errw B a -> writable_at (ms_segs B) mc a.
Proof.
  intros xs N Lc Ac mc mdc (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma mc_misc : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc ->
  ro_agree (ms_segs B) mc /\ res_ok_slots Ac (rcc_b b xs) /\ bounded Ac /\
  (st_init_done A = true -> st_init_done Ac = true).
Proof.
  intros xs N Lc Ac mc mdc (_ & _ & HB & _ & _ & HI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _ & HRES).
  auto.
Qed.

Lemma old_kept : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc ->
  forall q k j, In (q, k) (blocks L A) -> 0 <= j < k ->
    mbyte (ms_segs B) mc (q + j) = mbyte (ms_segs B) mem (q + j).
Proof.
  intros xs N Lc Ac mc mdc (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HB & _) q k j Hq Hj.
  destruct (proj1 (YI04.blocks_In L A q k) Hq) as (p & Ep & Hp). subst q. exact (HB p k j Hp Hj).
Qed.

Lemma old_in : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc ->
  forall q, In q (blocks L A) -> In q (blocks Lc Ac).
Proof.
  intros xs N Lc Ac mc mdc CH q Hq. apply (Permutation_in _ (Permutation_sym (mc_perm _ _ _ _ _ _ CH))).
  apply in_or_app. left. exact Hq.
Qed.

Lemma glob_kept : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc ->
  forall a, in_globals frame_G a -> mbyte (ms_segs B) mc a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mc a).
Proof using PRE GR A0 ARR GFACT GOWN.
  intros xs N Lc Ac mc mdc CH a Ha. destruct pre_facts as (HM & HCE & _).
  destruct (GFACT a Ha) as (Hi & _ & _ & He). pose proof alloc_ceiling_val as AC.
  pose proof Ha as Ha'. apply fg_iff in Ha'.
  apply (mc_frame _ _ _ _ _ _ CH); [right; exact Hi | exact (GOWN _ _ _ _ a HM Ha) | | exact He |].
  - unfold RCC_K, XMALLOC_K, ALLOC_STACK in *. lia.
  - intros HW. destruct (rw_hi a HW). unfold RCC_K, XMALLOC_K, ALLOC_STACK in *. lia.
Qed.

Definition ARG (Lc : layout) (Ac : astate) (mc : word -> option byte) (i a : nat) (s : list byte) (pn : Z * Z)
    : Prop :=
  bytes_at (ms_segs B) mc (dst + 56 * Z.of_nat i + 8 + 8 * Z.of_nat a) (le8 (Z_to_bv 64 (fst pn))) /\
  fst pn <> 0 /\ In pn (blocks Lc Ac) /\ snd pn = Z.of_nat (length s) + 1 /\ fresh_block B (fst pn) (snd pn) /\
  bytes_at (ms_segs B) mc (fst pn) (s ++ [Z_to_bv 8 0]) /\ no0 s.

Definition ARGS (Lc : layout) (Ac : astate) (mc : word -> option byte) (i : nat) (c : rcall) (P : list (Z * Z))
    : Prop :=
  forall a s pn, nth_error (snd c) a = Some s -> nth_error P a = Some pn -> ARG Lc Ac mc i a s pn.

Definition HDR (mc : word -> option byte) (i : nat) (c : rcall) : Prop :=
  bytes_at (ms_segs B) mc (dst + 56 * Z.of_nat i) (le4 (Z_to_bv 64 (fst c))) /\
  bytes_at (ms_segs B) mc (dst + 56 * Z.of_nat i + 4) (le4 (Z_to_bv 64 (Z.of_nat (length (snd c))))).

Definition DONE (Lc : layout) (Ac : astate) (mc : word -> option byte) (i : nat) (qs : list (list (Z * Z)))
    : Prop :=
  length qs = i /\ forall i' c P, nth_error (r_calls R) i' = Some c -> nth_error qs i' = Some P ->
    length P = length (snd c) /\ HDR mc i' c /\ ARGS Lc Ac mc i' c P.

Definition DSTW (mc : word -> option byte) : Prop :=
  forall j, 0 <= j < 56 * Z.of_nat (length (r_calls R)) -> writable_at (ms_segs B) mc (dst + j).

Lemma args_transfer : forall Lc Ac mc Lc' Ac' mc' i c P,
  ARGS Lc Ac mc i c P ->
  (forall pn, In pn (blocks Lc Ac) -> In pn (blocks Lc' Ac')) ->
  (forall q k j, In (q, k) (blocks Lc Ac) -> 0 <= j < k ->
     mbyte (ms_segs B) mc' (q + j) = mbyte (ms_segs B) mc (q + j)) ->
  (forall j, 0 <= j < 8 + 8 * Z.of_nat (length (snd c)) ->
     mbyte (ms_segs B) mc' (dst + 56 * Z.of_nat i + j) = mbyte (ms_segs B) mc (dst + 56 * Z.of_nat i + j)) ->
  ARGS Lc' Ac' mc' i c P.
Proof.
  intros Lc Ac mc Lc' Ac' mc' i c P H HB HK HD a s pn Es Ep.
  destruct (H a s pn Es Ep) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  assert (Ha : (a < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  split.
  { apply (bytes_at_transfer _ mc); [exact P1|]. intros t Ht. rewrite length_le8 in Ht. change (Z.of_nat 8) with 8 in Ht.
    replace (dst + 56 * Z.of_nat i + 8 + 8 * Z.of_nat a + t) with (dst + 56 * Z.of_nat i + (8 + 8 * Z.of_nat a + t))
      by ring.
    apply HD. lia. }
  split; [exact P2|]. split; [exact (HB _ P3)|]. split; [exact P4|]. split; [exact P5|].
  split; [|exact P7].
  apply (bytes_at_transfer _ mc); [exact P6|]. intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
  destruct pn as [q k]. cbn [fst snd] in *. apply (HK q k t P3). lia.
Qed.

Lemma args_transfer_lt : forall Lc Ac mc Lc' Ac' mc' i c P,
  ARGS Lc Ac mc i c P ->
  (forall pn, In pn (blocks Lc Ac) -> In pn (blocks Lc' Ac')) ->
  (forall q k j, In (q, k) (blocks Lc Ac) -> 0 <= j < k ->
     mbyte (ms_segs B) mc' (q + j) = mbyte (ms_segs B) mc (q + j)) ->
  (forall a t, (a < length P)%nat -> 0 <= t < 8 ->
     mbyte (ms_segs B) mc' (dst + 56 * Z.of_nat i + 8 + 8 * Z.of_nat a + t) =
     mbyte (ms_segs B) mc (dst + 56 * Z.of_nat i + 8 + 8 * Z.of_nat a + t)) ->
  ARGS Lc' Ac' mc' i c P.
Proof.
  intros Lc Ac mc Lc' Ac' mc' i c P H HB HK HD a s pn Es Ep.
  destruct (H a s pn Es Ep) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  assert (Ha : (a < length P)%nat) by (apply nth_error_Some; rewrite Ep; discriminate).
  split.
  { apply (bytes_at_transfer _ mc); [exact P1|]. intros t Ht. rewrite length_le8 in Ht. change (Z.of_nat 8) with 8 in Ht.
    apply HD; [exact Ha | lia]. }
  split; [exact P2|]. split; [exact (HB _ P3)|]. split; [exact P4|]. split; [exact P5|].
  split; [|exact P7].
  apply (bytes_at_transfer _ mc); [exact P6|]. intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
  destruct pn as [q k]. cbn [fst snd] in *. apply (HK q k t P3). lia.
Qed.

Lemma args_transfer_P : forall Lc Ac mc mc' i c P,
  ARGS Lc Ac mc i c P ->
  (forall pn t, In pn P -> 0 <= t < snd pn ->
     mbyte (ms_segs B) mc' (fst pn + t) = mbyte (ms_segs B) mc (fst pn + t)) ->
  (forall j, 0 <= j < 8 + 8 * Z.of_nat (length (snd c)) ->
     mbyte (ms_segs B) mc' (dst + 56 * Z.of_nat i + j) = mbyte (ms_segs B) mc (dst + 56 * Z.of_nat i + j)) ->
  ARGS Lc Ac mc' i c P.
Proof.
  intros Lc Ac mc mc' i c P H HK HD a s pn Es Ep.
  destruct (H a s pn Es Ep) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  assert (Ha : (a < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  split.
  { apply (bytes_at_transfer _ mc); [exact P1|]. intros t Ht. rewrite length_le8 in Ht. change (Z.of_nat 8) with 8 in Ht.
    replace (dst + 56 * Z.of_nat i + 8 + 8 * Z.of_nat a + t) with (dst + 56 * Z.of_nat i + (8 + 8 * Z.of_nat a + t))
      by ring.
    apply HD. lia. }
  split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
  split; [|exact P7].
  apply (bytes_at_transfer _ mc); [exact P6|]. intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
  apply (HK pn t (nth_error_In _ _ Ep)). lia.
Qed.

Lemma hdr_transfer : forall mc mc' i c, HDR mc i c ->
  (forall j, 0 <= j < 8 ->
     mbyte (ms_segs B) mc' (dst + 56 * Z.of_nat i + j) = mbyte (ms_segs B) mc (dst + 56 * Z.of_nat i + j)) ->
  HDR mc' i c.
Proof.
  intros mc mc' i c (H1 & H2) HD. split.
  - apply (bytes_at_transfer _ mc); [exact H1|]. intros t Ht. rewrite length_le4 in Ht. change (Z.of_nat 4) with 4 in Ht.
    apply HD. lia.
  - apply (bytes_at_transfer _ mc); [exact H2|]. intros t Ht. rewrite length_le4 in Ht. change (Z.of_nat 4) with 4 in Ht.
    replace (dst + 56 * Z.of_nat i + 4 + t) with (dst + 56 * Z.of_nat i + (4 + t)) by ring. apply HD. lia.
Qed.

Lemma done_transfer : forall Lc Ac mc Lc' Ac' mc' i qs,
  DONE Lc Ac mc i qs ->
  (forall pn, In pn (blocks Lc Ac) -> In pn (blocks Lc' Ac')) ->
  (forall q k j, In (q, k) (blocks Lc Ac) -> 0 <= j < k ->
     mbyte (ms_segs B) mc' (q + j) = mbyte (ms_segs B) mc (q + j)) ->
  (forall j, 0 <= j < 56 * Z.of_nat i -> mbyte (ms_segs B) mc' (dst + j) = mbyte (ms_segs B) mc (dst + j)) ->
  DONE Lc' Ac' mc' i qs.
Proof using GR.
  intros Lc Ac mc Lc' Ac' mc' i qs (HL & HD) HB HK HM. split; [exact HL|].
  intros i' c P Hc HP. destruct (HD i' c P Hc HP) as (H1 & H2 & H3).
  assert (Hi : (i' < i)%nat) by (rewrite <- HL; apply nth_error_Some; rewrite HP; discriminate).
  pose proof (call_len i' c Hc) as Hl.
  assert (HM' : forall j, 0 <= j < 56 ->
            mbyte (ms_segs B) mc' (dst + 56 * Z.of_nat i' + j) = mbyte (ms_segs B) mc (dst + 56 * Z.of_nat i' + j)).
  { intros j Hj. replace (dst + 56 * Z.of_nat i' + j) with (dst + (56 * Z.of_nat i' + j)) by ring. apply HM. lia. }
  split; [exact H1|]. split.
  - apply (hdr_transfer mc); [exact H2|]. intros j Hj. apply HM'. lia.
  - apply (args_transfer Lc Ac mc); [exact H3 | exact HB | exact HK |]. intros j Hj. apply HM'. lia.
Qed.

Lemma done_transfer_P : forall Lc Ac mc mc' i qs,
  DONE Lc Ac mc i qs ->
  (forall pn t, In pn (concat qs) -> 0 <= t < snd pn ->
     mbyte (ms_segs B) mc' (fst pn + t) = mbyte (ms_segs B) mc (fst pn + t)) ->
  (forall j, 0 <= j < 56 * Z.of_nat i -> mbyte (ms_segs B) mc' (dst + j) = mbyte (ms_segs B) mc (dst + j)) ->
  DONE Lc Ac mc' i qs.
Proof using GR.
  intros Lc Ac mc mc' i qs (HL & HD) HK HM. split; [exact HL|].
  intros i' c P Hc HP. destruct (HD i' c P Hc HP) as (H1 & H2 & H3).
  assert (Hi : (i' < i)%nat) by (rewrite <- HL; apply nth_error_Some; rewrite HP; discriminate).
  pose proof (call_len i' c Hc) as Hl.
  assert (HM' : forall j, 0 <= j < 56 ->
            mbyte (ms_segs B) mc' (dst + 56 * Z.of_nat i' + j) = mbyte (ms_segs B) mc (dst + 56 * Z.of_nat i' + j)).
  { intros j Hj. replace (dst + 56 * Z.of_nat i' + j) with (dst + (56 * Z.of_nat i' + j)) by ring. apply HM. lia. }
  split; [exact H1|]. split.
  - apply (hdr_transfer mc); [exact H2|]. intros j Hj. apply HM'. lia.
  - apply (args_transfer_P Lc Ac mc); [exact H3 | | intros j Hj; apply HM'; lia].
    intros pn t Hpn Ht. apply HK; [|exact Ht]. apply in_concat. exists P.
    split; [exact (nth_error_In _ _ HP) | exact Hpn].
Qed.

Definition RGB (Rc : bvmap 5 word) : Prop :=
  getr Rc 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -128) /\ getr Rc 3 = getr regs 3 /\ getr Rc 4 = getr regs 4.

Definition RG (Rc : bvmap 5 word) (i : nat) : Prop :=
  RGB Rc /\ getr Rc 10 = getr regs 10 /\ getr Rc 11 = Z_to_bv 64 (Z.of_nat (length (r_calls R))) /\
  getr Rc 14 = Z_to_bv 64 0x33ff0 /\ getr Rc 21 = Z_to_bv 64 (Z.of_nat i) /\ getr Rc 23 = S7 i /\
  getr Rc 24 = S8 (getr regs 10) i.

Definition RGI (Rc : bvmap 5 word) (i j : nat) : Prop :=
  RGB Rc /\ getr Rc 8 = Z_to_bv 64 0x33ff0 /\ getr Rc 20 = N4 (getr regs 10) i /\
  getr Rc 21 = Z_to_bv 64 (Z.of_nat i) /\ getr Rc 22 = Z_to_bv 64 (Z.of_nat j) /\ getr Rc 23 = S7 i /\
  getr Rc 24 = S8 (getr regs 10) i /\ getr Rc 25 = N9 i /\ getr Rc 26 = Z_to_bv 64 (8 * Z.of_nat j) /\
  getr Rc 27 = Z_to_bv 64 (bv_unsigned (getr regs 10) + 56 * Z.of_nat i).

Definition RGX (Rc : bvmap 5 word) (i j : nat) (len : Z) (pw : word) : Prop :=
  RGI Rc i j /\ getr Rc 18 = pw /\ getr Rc 19 = Z_to_bv 64 (len + 1).

Lemma mkR_of_RG : forall Rc i, RG Rc i -> Regs6ss.mkR_of Rc =
  mkR (getr Rc 1) (Z_to_bv 64 (bv_unsigned (getr regs 2) + -128)) (getr regs 3) (getr regs 4) (getr Rc 5) (getr Rc 6)
      (getr Rc 7) (getr Rc 8) (getr Rc 9) (getr regs 10) (Z_to_bv 64 (Z.of_nat (length (r_calls R))))
      (getr Rc 12) (getr Rc 13) (Z_to_bv 64 0x33ff0) (getr Rc 15) (getr Rc 16) (getr Rc 17) (getr Rc 18)
      (getr Rc 19) (getr Rc 20) (Z_to_bv 64 (Z.of_nat i)) (getr Rc 22) (S7 i) (S8 (getr regs 10) i)
      (getr Rc 25) (getr Rc 26) (getr Rc 27) (getr Rc 28) (getr Rc 29) (getr Rc 30) (getr Rc 31).
Proof.
  intros Rc i ((G2 & G3 & G4) & G10 & G11 & G14 & G21 & G23 & G24).
  rewrite mkR_getr, G2, G3, G4, G10, G11, G14, G21, G23, G24. reflexivity.
Qed.

Lemma mkR_of_RGI : forall Rc i j, RGI Rc i j -> Regs6ss.mkR_of Rc =
  mkR (getr Rc 1) (Z_to_bv 64 (bv_unsigned (getr regs 2) + -128)) (getr regs 3) (getr regs 4) (getr Rc 5) (getr Rc 6)
      (getr Rc 7) (Z_to_bv 64 0x33ff0) (getr Rc 9) (getr Rc 10) (getr Rc 11) (getr Rc 12) (getr Rc 13) (getr Rc 14)
      (getr Rc 15) (getr Rc 16) (getr Rc 17) (getr Rc 18) (getr Rc 19) (N4 (getr regs 10) i)
      (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (Z.of_nat j)) (S7 i) (S8 (getr regs 10) i) (N9 i)
      (Z_to_bv 64 (8 * Z.of_nat j)) (Z_to_bv 64 (bv_unsigned (getr regs 10) + 56 * Z.of_nat i))
      (getr Rc 28) (getr Rc 29) (getr Rc 30) (getr Rc 31).
Proof.
  intros Rc i j ((G2 & G3 & G4) & G8 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  rewrite mkR_getr, G2, G3, G4, G8, G20, G21, G22, G23, G24, G25, G26, G27. reflexivity.
Qed.

Lemma mkR_of_RGX : forall Rc i j len pw, RGX Rc i j len pw -> Regs6ss.mkR_of Rc =
  mkR (getr Rc 1) (Z_to_bv 64 (bv_unsigned (getr regs 2) + -128)) (getr regs 3) (getr regs 4) (getr Rc 5) (getr Rc 6)
      (getr Rc 7) (Z_to_bv 64 0x33ff0) (getr Rc 9) (getr Rc 10) (getr Rc 11) (getr Rc 12) (getr Rc 13) (getr Rc 14)
      (getr Rc 15) (getr Rc 16) (getr Rc 17) pw (Z_to_bv 64 (len + 1)) (N4 (getr regs 10) i)
      (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (Z.of_nat j)) (S7 i) (S8 (getr regs 10) i) (N9 i)
      (Z_to_bv 64 (8 * Z.of_nat j)) (Z_to_bv 64 (bv_unsigned (getr regs 10) + 56 * Z.of_nat i))
      (getr Rc 28) (getr Rc 29) (getr Rc 30) (getr Rc 31).
Proof.
  intros Rc i j len pw (GI & G18 & G19). rewrite (mkR_of_RGI Rc i j GI), G18, G19. reflexivity.
Qed.

Lemma rg_mkR : forall i y1 y5 y6 y7 y8 y9 y12 y13 y15 y16 y17 y18 y19 y20 y22 y25 y26 y27 y28 y29 y30 y31 Rc,
  Rc = mkR y1 (Z_to_bv 64 (bv_unsigned (getr regs 2) + -128)) (getr regs 3) (getr regs 4) y5 y6 y7 y8 y9
         (getr regs 10) (Z_to_bv 64 (Z.of_nat (length (r_calls R)))) y12 y13 (Z_to_bv 64 0x33ff0) y15 y16 y17
         y18 y19 y20 (Z_to_bv 64 (Z.of_nat i)) y22 (S7 i) (S8 (getr regs 10) i) y25 y26 y27 y28 y29 y30 y31 ->
  RG Rc i.
Proof. intros. subst Rc. unfold RG, RGB. repeat split. Qed.

Lemma rgi_mkR : forall i j y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 Rc,
  Rc = mkR y1 (Z_to_bv 64 (bv_unsigned (getr regs 2) + -128)) (getr regs 3) (getr regs 4) y5 y6 y7
         (Z_to_bv 64 0x33ff0) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 (N4 (getr regs 10) i)
         (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (Z.of_nat j)) (S7 i) (S8 (getr regs 10) i) (N9 i)
         (Z_to_bv 64 (8 * Z.of_nat j)) (Z_to_bv 64 (bv_unsigned (getr regs 10) + 56 * Z.of_nat i)) y28 y29 y30 y31 ->
  RGI Rc i j.
Proof. intros. subst Rc. unfold RGI, RGB. repeat split. Qed.

Lemma rgx_mkR : forall i j len pw y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 Rc,
  Rc = mkR (Z_to_bv 64 0x15d20) (Z_to_bv 64 (bv_unsigned (getr regs 2) + -128)) (getr regs 3) (getr regs 4)
         y5 y6 y7 (Z_to_bv 64 0x33ff0) y9 (Z_to_bv 64 (len + 1)) y11 y12 y13 y14 y15 y16 y17 pw
         (Z_to_bv 64 (len + 1)) (N4 (getr regs 10) i) (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (Z.of_nat j)) (S7 i)
         (S8 (getr regs 10) i) (N9 i) (Z_to_bv 64 (8 * Z.of_nat j))
         (Z_to_bv 64 (bv_unsigned (getr regs 10) + 56 * Z.of_nat i)) y28 y29 y30 y31 ->
  getr Rc 1 = Z_to_bv 64 0x15d20 /\ getr Rc 10 = Z_to_bv 64 (len + 1) /\ RGX Rc i j len pw.
Proof. intros. subst Rc. unfold RGX, RGI, RGB. repeat split. Qed.

Lemma pres_mkR : forall y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 Rc,
  Rc = mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) y5 y6 y7 (getr regs 8) (getr regs 9)
         (Z_to_bv 64 (Z.of_nat (length (r_calls R)))) y11 y12 y13 y14 y15 y16 y17
         (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
         (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) y28 y29 y30 y31 ->
  regs_preserved regs Rc /\ getr Rc 10 = Z_to_bv 64 (Z.of_nat (length (r_calls R))).
Proof.
  intros. subst Rc. split; [|reflexivity]. intros r Hr. unfold callee_saved in Hr.
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct C as [C|C]; [subst r; reflexivity|]). subst r. reflexivity.
Qed.

Lemma rgx_pres : forall Rc Rc' i j len pw, regs_preserved Rc Rc' -> RGX Rc i j len pw -> RGX Rc' i j len pw.
Proof.
  intros Rc Rc' i j len pw HP (((G2 & G3 & G4) & G8 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27) & G18 & G19).
  assert (E : forall r, callee_saved r -> getr Rc' (Z_to_bv 5 r) = getr Rc (Z_to_bv 5 r)) by exact HP.
  assert (CS : forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ (18 <= r <= 27) -> callee_saved r)
    by (intros r Hr; exact Hr).
  unfold RGX, RGI, RGB. repeat split.
  - exact (eq_trans (E 2 (CS 2 ltac:(lia))) G2).
  - exact (eq_trans (E 3 (CS 3 ltac:(lia))) G3).
  - exact (eq_trans (E 4 (CS 4 ltac:(lia))) G4).
  - exact (eq_trans (E 8 (CS 8 ltac:(lia))) G8).
  - exact (eq_trans (E 20 (CS 20 ltac:(lia))) G20).
  - exact (eq_trans (E 21 (CS 21 ltac:(lia))) G21).
  - exact (eq_trans (E 22 (CS 22 ltac:(lia))) G22).
  - exact (eq_trans (E 23 (CS 23 ltac:(lia))) G23).
  - exact (eq_trans (E 24 (CS 24 ltac:(lia))) G24).
  - exact (eq_trans (E 25 (CS 25 ltac:(lia))) G25).
  - exact (eq_trans (E 26 (CS 26 ltac:(lia))) G26).
  - exact (eq_trans (E 27 (CS 27 ltac:(lia))) G27).
  - exact (eq_trans (E 18 (CS 18 ltac:(lia))) G18).
  - exact (eq_trans (E 19 (CS 19 ltac:(lia))) G19).
Qed.

Lemma rg_eqv : forall Rc Rc' i, RG Rc i -> Regs6ss.xregs_eqv Rc Rc' -> RG Rc' i.
Proof. intros Rc Rc' i G X. unfold RG, RGB in *. repeat rewrite (CF.rec_calls_free.getr_eqv Rc Rc' _ X). exact G. Qed.

Lemma rgi_eqv : forall Rc Rc' i j, RGI Rc i j -> Regs6ss.xregs_eqv Rc Rc' -> RGI Rc' i j.
Proof. intros Rc Rc' i j G X. unfold RGI, RGB in *. repeat rewrite (CF.rec_calls_free.getr_eqv Rc Rc' _ X). exact G. Qed.

Lemma rgx_eqv : forall Rc Rc' i j len pw, RGX Rc i j len pw -> Regs6ss.xregs_eqv Rc Rc' -> RGX Rc' i j len pw.
Proof.
  intros Rc Rc' i j len pw G X. unfold RGX, RGI, RGB in *. repeat rewrite (CF.rec_calls_free.getr_eqv Rc Rc' _ X).
  exact G.
Qed.

Lemma pres_eqv : forall Rc Rc', regs_preserved regs Rc -> Regs6ss.xregs_eqv Rc Rc' -> regs_preserved regs Rc'.
Proof. intros Rc Rc' P X r Hr. rewrite (CF.rec_calls_free.getr_eqv Rc Rc' _ X). exact (P r Hr). Qed.

Lemma run_ka : forall Rc pc mc mdc (Q : machine_state -> Prop),
  m_halted mdc = None -> m_vm_lazy mdc = [] -> ro_agree (ms_segs B) mc ->
  evt rsegs Q (MS (Regs6ss.mkR_of Rc) fp_regs pc fp_csr None (normalize rsegs mc) (seg_rom rsegs)) ->
  (forall ms', (exists can, (exists s0, Q s0 /\ ms_rel rsegs can s0 /\ ro_same rsegs mc (ms_mem can)) /\
                 Regs6ss.ms_eqv can ms') -> SR rsegs (mkCfg ms' mdc) POST) ->
  SR (ms_segs B) (mkCfg (mkst Rc pc mc (seg_rom (ms_segs B))) mdc) POST.
Proof using SEGS.
  intros Rc pc mc mdc Q Hh Hl HRO HE K. rewrite SEGS in HRO |- *.
  eapply evt_SR_canon; [rewrite canon_mkst; apply (evt_normalize rsegs); [exact wx_apart_rsegs | exact HRO | exact HE]
    | exact Hh | exact Hl | exact K].
Qed.

Lemma norm_back : forall mc mn m' W, ro_agree rsegs mc -> mem_rel rsegs m' mn -> ro_same rsegs mc m' ->
  munch W (normalize rsegs mc) mn -> wmono rsegs (normalize rsegs mc) mn ->
  munch W mc m' /\ wmono rsegs mc m' /\ ro_agree rsegs m'.
Proof.
  intros mc mn m' W RA MR RS MU WM.
  split; [exact (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mc RA) MR RS MU)|].
  split; [exact (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mc RA) MR RS WM)|].
  exact (ro_agree_same rsegs _ _ RA RS).
Qed.

Definition FRM (mc : word -> option byte) : Prop :=
  rw_cells rsegs mc (bv_unsigned (getr regs 2) + -128) (FRL (getr regs 10)) /\
  rw_cells rsegs mc (bv_unsigned (getr regs 2) + -104)
    (FRS (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
         (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).

Definition XS (i j : nat) (c : rcall) : list (list byte) := rcc_args (firstn i (r_calls R)) ++ firstn j (snd c).

Lemma frm_keep : forall mc m', FRM mc ->
  (forall a, spZ regs - 128 <= a < spZ regs ->
     mbyte (ms_segs B) m' a = mbyte (ms_segs B) mc a /\
     (writable_at (ms_segs B) mc a <-> writable_at (ms_segs B) m' a)) ->
  FRM m'.
Proof using SEGS.
  intros mc m' [F1 F2] KH. unfold FRM. rewrite <- SEGS in F1, F2 |- *. split.
  - apply (rw_cells_transfer _ mc); [exact F1|].
    intros t Ht. unfold FRL in Ht. cbn [cells_size csize Nat.add] in Ht.
    destruct (KH (bv_unsigned (getr regs 2) + -128 + t)) as [E1 E2]; [unfold spZ; lia|].
    split; [exact E1 | apply E2].
  - apply (rw_cells_transfer _ mc); [exact F2|].
    intros t Ht. unfold FRS in Ht. cbn [cells_size csize Nat.add] in Ht.
    destruct (KH (bv_unsigned (getr regs 2) + -104 + t)) as [E1 E2]; [unfold spZ; lia|].
    split; [exact E1 | apply E2].
Qed.

Lemma frm_norm : forall mc, FRM mc -> ro_agree (ms_segs B) mc -> FRM (normalize rsegs mc).
Proof using SEGS PRE.
  intros mc [F1 F2] HRO. destruct pre_facts as (_ & HCE & H63 & _). pose proof alloc_ceiling_val as AC.
  unfold RCC_K, XMALLOC_K, ALLOC_STACK, spZ in *. rewrite SEGS in HRO. split.
  - apply rw_cells_normalize; [exact HRO | exact F1 |]. intros t Ht. unfold FRL in Ht.
    cbn [cells_size csize Nat.add] in Ht. unfold wa. apply hi_rw. lia.
  - apply rw_cells_normalize; [exact HRO | exact F2 |]. intros t Ht. unfold FRS in Ht.
    cbn [cells_size csize Nat.add] in Ht. unfold wa. apply hi_rw. lia.
Qed.

Lemma frm_back : forall mn m', mem_rel rsegs m' mn -> FRM mn -> FRM m'.
Proof.
  intros mn m' MR [F1 F2]. split; [exact (rw_cells_rel rsegs _ _ _ _ MR F1) | exact (rw_cells_rel rsegs _ _ _ _ MR F2)].
Qed.

Lemma src_slack : forall xs N Lc Ac mc mdc i c Po j s opn,
  CHS xs N Lc Ac mc mdc ->
  call_at (ms_segs B) (blocks L A) mem (0x34038 + 56 * Z.of_nat i) c Po ->
  nth_error (snd c) j = Some s -> nth_error Po j = Some opn ->
  exists slack, bytes_at rsegs mc (fst opn) (s ++ Z_to_bv 8 0 :: slack) /\
    (- (fst opn + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) /\ no0 s /\
    fst opn + Z.of_nat (length (s ++ Z_to_bv 8 0 :: slack)) <= alloc_ceiling.
Proof using SEGS SLACK.
  intros xs N Lc Ac mc mdc i c Po j s opn CH CA Es Eo.
  destruct CA as (CF & CL & CP & CB1 & CB2 & CND & CK).
  destruct (CK j s opn Es Eo) as (OB & ONZ & OIN & OSZ & OBY & ON0).
  destruct (mc_MR _ _ _ _ _ _ CH) as (HMc & HWc).
  pose proof alloc_ceiling_val as AC.
  destruct opn as [q k]. cbn [fst snd] in *.
  assert (QIN : In (q, k) (blocks Lc Ac)) by exact (old_in _ _ _ _ _ _ CH _ OIN).
  pose proof (block_facts B _ (aa_laws API) Lc Ac mc mdc q k 0 HMc QIN ltac:(lia)) as (_ & Q1 & Q2 & _).
  assert (SBY : bytes_at (ms_segs B) mc q (s ++ [Z_to_bv 8 0])).
  { apply (bytes_at_transfer _ mem); [exact OBY|]. intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
    apply (old_kept _ _ _ _ _ _ CH q k t OIN). lia. }
  rewrite SEGS in SBY.
  destruct (slack_rebuild' mc q s SBY ltac:(lia) ltac:(lia)) as (slack & SBS & SAL & SEND).
  { intros a Ha. destruct (Z_lt_ge_dec a (q + k)) as [D|D].
    - replace a with (q + (a - q)) by ring.
      exact (proj1 (block_facts B _ (aa_laws API) Lc Ac mc mdc q k (a - q) HMc QIN ltac:(lia))).
    - apply (SLACK Lc Ac mc mdc q k a HMc QIN). split; [lia|].
      pose proof (ceil8_mono (q + (Z.of_nat (length s) + 1)) (q + k) ltac:(lia)). lia. }
  assert (AC8 : alloc_ceiling mod 8 = 0) by (Z.div_mod_to_equations; lia).
  exists slack. split; [exact SBS|]. split; [exact SAL|]. split; [exact ON0|].
  rewrite SEND. pose proof (ceil8_le (q + (Z.of_nat (length s) + 1)) alloc_ceiling ltac:(lia) AC8). lia.
Qed.

Lemma xm_step : forall i c Po j s opn pw Rc mc mdc Lc Ac qs Pn,
  nth_error (r_calls R) i = Some c ->
  call_at (ms_segs B) (blocks L A) mem (0x34038 + 56 * Z.of_nat i) c Po ->
  Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c) ->
  nth_error (snd c) j = Some s -> nth_error Po j = Some opn ->
  getr Rc 1 = Z_to_bv 64 0x15d20 -> getr Rc 10 = Z_to_bv 64 (Z.of_nat (length s) + 1) ->
  RGX Rc i j (Z.of_nat (length s)) pw -> FRM mc ->
  CHS (XS i j c) (concat qs ++ Pn) Lc Ac mc mdc -> DONE Lc Ac mc i qs -> HDR mc i c -> ARGS Lc Ac mc i c Pn ->
  DSTW mc ->
  (forall L2 A2 R2 m2 md2 p, RGX R2 i j (Z.of_nat (length s)) pw -> getr R2 10 = Z_to_bv 64 p -> FRM m2 ->
     CHS (XS i (S j) c) ((concat qs ++ Pn) ++ [(p, Z.of_nat (length s) + 1)]) L2 A2 m2 md2 ->
     DONE L2 A2 m2 i qs -> HDR m2 i c -> ARGS L2 A2 m2 i c Pn -> DSTW m2 ->
     p <> 0 -> p mod 16 = 0 -> In (p, Z.of_nat (length s) + 1) (blocks L2 A2) ->
     fresh_block B p (Z.of_nat (length s) + 1) ->
     bytes_at (ms_segs B) m2 (fst opn) (s ++ [Z_to_bv 8 0]) ->
     fst opn + (Z.of_nat (length s) + 1) <= p \/ p + (Z.of_nat (length s) + 1) <= fst opn ->
     SR (ms_segs B) (mkCfg (mkst R2 (Z_to_bv 64 0x15d20) m2 (seg_rom (ms_segs B))) md2) POST) ->
  SR (ms_segs B) (mkCfg (mkst Rc (Z_to_bv 64 XMALLOC) mc (seg_rom (ms_segs B))) mdc) POST.
Proof using PRE GR A0 ARR ROOM SEGS AX CTX GOWN GFACT ERRNO XM.
  intros i c Po j s opn pw Rc mc mdc Lc Ac qs Pn Hc CA FL Es Eo G1 G10 GX FR CH DN HD AG DW K.
  destruct pre_facts as (HM0 & HCE & H63 & HAL & HRA & HWA & HTP).
  pose proof alloc_ceiling_val as AC.
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  destruct (ka_hyps ltac:(lia)) as ((H16 & HSW & HDW & HDN) & UC).
  destruct (dst_facts ltac:(lia)) as (_ & D1 & D2).
  destruct CA as (CF & CL & CP & CB1 & CB2 & CND & CK).
  destruct (CK j s opn Es Eo) as (OB & ONZ & OIN & OSZ & OBY & ON0).
  assert (LX : Z.of_nat (length s) <= LMAX) by (rewrite Forall_forall in FL; apply FL; eapply nth_error_In; exact Es).
  destruct (mc_MR _ _ _ _ _ _ CH) as (HMc & HWc).
  destruct (mc_misc _ _ _ _ _ _ CH) as (HROc & HRESc & HBc & HINc).
  destruct opn as [q k]. cbn [fst snd] in *.
  assert (QIN : In (q, k) (blocks Lc Ac)) by exact (old_in _ _ _ _ _ _ CH _ OIN).
  assert (SBY : bytes_at (ms_segs B) mc q (s ++ [Z_to_bv 8 0])).
  { apply (bytes_at_transfer _ mem); [exact OBY|]. intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
    apply (old_kept _ _ _ _ _ _ CH q k t OIN). lia. }
  assert (SPC : spZ Rc = spZ regs - 128).
  { destruct GX as (((G2 & _) & _) & _). unfold spZ at 1. rewrite G2. change (bv_unsigned (getr regs 2)) with (spZ regs).
    unfold RCC_K, XMALLOC_K, ALLOC_STACK in *. rewrite unsigned_lit; lia. }
  assert (G4 : getr Rc 4 = getr regs 4) by (destruct GX as (((_ & _ & G4) & _) & _); exact G4).
  assert (INITA : st_init_done A = true).
  { destruct (proj1 (YI04.blocks_In L A q k) OIN) as (p0 & _ & Hp0). exact (YI04.init_done_of_block A (p0, k) HWA Hp0). }
  assert (PREc : call_pre_k B (aa_MR API) XMALLOC_K Lc Ac Rc mc mdc).
  { split; [exact HMc|]. split; [exact HWc|]. split; [exact HBc|].
    split; [rewrite G1; apply bv_eq; vm_compute; reflexivity|].
    unfold RCC_K, XMALLOC_K, ALLOC_STACK in *.
    split; [rewrite SPC; replace (spZ regs - 128) with (spZ regs + (-8) * 16) by ring; rewrite Z.mod_add by lia;
            exact HAL|].
    split; [rewrite SPC; lia|]. split; [rewrite SPC; lia|].
    split; [intros a Ha; rewrite SPC in Ha; apply (mc_scr _ _ _ _ _ _ CH); left; unfold RCC_K, XMALLOC_K, ALLOC_STACK;
            lia|].
    split; [rewrite G4; exact HTP|].
    split; [intros a Ha; apply (mc_scr _ _ _ _ _ _ CH); right; exact Ha|].
    intros Hni. rewrite (HINc INITA) in Hni. discriminate. }
  assert (XSZ : xmalloc_size (Z.of_nat (length s) + 1) = Z.of_nat (length s) + 1)
    by (unfold xmalloc_size; destruct (Z.eqb_spec (Z.of_nat (length s) + 1) 0); lia).
  pose proof XM as XMc. unfold xmalloc_contract in XMc.
  eapply SR_bind.
  { apply (XMc Lc Ac Rc mc mdc (Z.of_nat (length s) + 1) (rcc_b b (XS i j c)) PREc G10);
      [lia | exact HRESc | | exact HROc].
    rewrite XSZ. exact (rcc_room b (r_calls R) i c j s Hc Es ROOM LX). }
  intros c2 RET. rewrite XSZ in RET.
  destruct RET as (L2 & A2 & R2 & m2 & md2 & p & -> & POST2 & A0' & PNZ & PAL & FRESH & BL & BKP & RA2 & GK2 & UB
    & INIT2 & RGN2 & RES2).
  pose proof POST2 as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  destruct BL as (b1 & b2 & EB2 & EB1).
  assert (KH : forall a, spZ regs - 128 <= a < 2 ^ 64 ->
            mbyte (ms_segs B) m2 a = mbyte (ms_segs B) mc a /\
            (writable_at (ms_segs B) mc a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha. unfold RCC_K, XMALLOC_K, ALLOC_STACK in *. apply PF.
    - left. lia.
    - intros Ho. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho). lia.
    - intros Ho. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a PM Ho). lia.
    - unfold scratch_k. rewrite SPC. intros [H|H]; lia.
    - intros F; exact F. }
  assert (BINC : forall pn, In pn (blocks Lc Ac) -> In pn (blocks L2 A2)).
  { intros pn Hpn. rewrite EB1 in Hpn. rewrite EB2. apply in_app_or in Hpn as [H|H]; apply in_or_app; [left | right; right];
      exact H. }
  assert (BKEEP : forall q0 k0 t, In (q0, k0) (blocks Lc Ac) -> 0 <= t < k0 ->
            mbyte (ms_segs B) m2 (q0 + t) = mbyte (ms_segs B) mc (q0 + t)).
  { intros q0 k0 t Hq Ht. exact (BKP q0 k0 t Hq (fun F => F) Ht). }
  assert (DKEEP : forall t, 0 <= t < 56 * Z.of_nat (length (r_calls R)) ->
            mbyte (ms_segs B) m2 (dst + t) = mbyte (ms_segs B) mc (dst + t)).
  { intros t Ht. apply (KH (dst + t)). lia. }
  assert (QD : q + k <= p \/ p + (Z.of_nat (length s) + 1) <= q).
  { pose proof QIN as QIN'. rewrite EB1 in QIN'.
    exact (blocks_mid_disjoint B _ (aa_laws API) L2 A2 m2 md2 b1 b2 p _ q k PM EB2 QIN'). }
  rewrite G1. apply (K L2 A2 R2 m2 md2 p).
  - exact (rgx_pres Rc R2 i j _ pw PR GX).
  - exact A0'.
  - apply (frm_keep mc); [exact FR|]. intros a Ha. apply KH. lia.
  - unfold CHS, XS. rewrite (rcc_xs_snoc (r_calls R) i c j s Es).
    eapply (mchain_x _ _ _ L A mem md b _ _ Lc Ac mc mdc Rc s p L2 A2 R2 m2 md2 HM0); [ | | exact CH | | | exact POST2
      | exact FRESH | exists b1, b2; split; [exact EB2 | exact EB1] | exact UB | exact RA2 | exact GK2 | exact INIT2
      | exact RGN2 | exact RES2].
    + exact HCE.
    + lia.
    + rewrite SPC. unfold RCC_K, XMALLOC_K, ALLOC_STACK. lia.
    + rewrite SPC. lia.
  - apply (done_transfer Lc Ac mc); [exact DN | exact BINC | exact BKEEP |]. intros t Ht. apply DKEEP. lia.
  - apply (hdr_transfer mc); [exact HD|]. intros t Ht.
    replace (dst + 56 * Z.of_nat i + t) with (dst + (56 * Z.of_nat i + t)) by ring. apply DKEEP. lia.
  - pose proof (call_len i c Hc) as Hl6.
    apply (args_transfer Lc Ac mc); [exact AG | exact BINC | exact BKEEP |]. intros t Ht.
    replace (dst + 56 * Z.of_nat i + t) with (dst + (56 * Z.of_nat i + t)) by ring. apply DKEEP. lia.
  - intros t Ht. apply (proj1 (proj2 (KH (dst + t) ltac:(lia)))). exact (DW t Ht).
  - exact PNZ.
  - exact PAL.
  - rewrite EB2. apply in_or_app. right. left. reflexivity.
  - exact FRESH.
  - apply (bytes_at_transfer _ mc); [exact SBY|]. intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
    apply (BKEEP q k t QIN). lia.
  - lia.
Qed.

Lemma glob_cells : forall m a cs, cells_wf cs -> bytes_at rsegs m a (cells_bytes cs) ->
  GLOB_LO <= a -> a + Z.of_nat (cells_size cs) <= GLOB_LO + Z.of_nat GLOB_N -> rw_cells rsegs m a cs.
Proof.
  intros m a cs Hw Hb H1 H2. split; [split; assumption|].
  split; [unfold GLOB_LO in H1; lia|]. split; [unfold GLOB_LO in *; change (Z.of_nat GLOB_N) with 1020 in H2; lia|].
  intros t Ht. exact (glob_writable m (a + t) ltac:(lia)).
Qed.

Lemma rec_cells : forall xs N Lc Ac mc mdc a cs k, CHS xs N Lc Ac mc mdc -> cells_wf cs ->
  bytes_at (ms_segs B) mem a (cells_bytes cs) -> Z.of_nat (cells_size cs) = k ->
  GLOB_LO <= a -> a + k <= GLOB_LO + Z.of_nat GLOB_N -> rw_cells rsegs mc a cs.
Proof using PRE GR A0 ARR GFACT GOWN SEGS.
  intros xs N Lc Ac mc mdc a cs k CH Hw Hb Hk H1 H2. apply glob_cells; [exact Hw | | exact H1 | lia].
  rewrite <- SEGS. apply (bytes_at_transfer _ mem); [exact Hb|]. intros t Ht.
  rewrite (cells_bytes_length cs Hw) in Ht.
  apply (glob_kept _ _ _ _ _ _ CH). apply glob_in. lia.
Qed.

Lemma dst_cells : forall mc (o : Z) (k : nat), DSTW mc -> (0 < length (r_calls R))%nat -> 0 <= o ->
  o + Z.of_nat k <= 56 * Z.of_nat (length (r_calls R)) ->
  exists junk, rw_cells rsegs mc (dst + o) [CB k junk].
Proof using PRE GR A0 ARR SEGS.
  intros mc o k DW Hn H1 H2. destruct (ka_hyps Hn) as ((_ & HSW & HDW & _) & UC).
  destruct (dst_facts Hn) as (_ & D1 & D2). unfold spZ in *.
  apply present_rw_cells; [lia | lia |]. intros t Ht. apply writable_hi_present; [lia|].
  rewrite <- SEGS. replace (dst + o + t) with (dst + (o + t)) by ring. apply DW. lia.
Qed.

Definition XW (X : Z) (cs : list cell) (mc m' : word -> option byte) : Prop :=
  rw_cells rsegs m' X cs /\ munch [(X, X + 8)] mc m' /\ wmono rsegs mc m'.

Lemma slot_store_common : forall xs N Lc Ac mc mdc m' X cs i c o,
  nth_error (r_calls R) i = Some c -> CHS xs N Lc Ac mc mdc -> FRM mc -> DSTW mc -> XW X cs mc m' ->
  X = dst + 56 * Z.of_nat i + o -> 0 <= o -> o + 8 <= 8 + 8 * Z.of_nat (length (snd c)) ->
  CHS xs N Lc Ac m' mdc /\ FRM m' /\ DSTW m' /\
  (forall q k t, In (q, k) (blocks Lc Ac) -> 0 <= t < k ->
     mbyte (ms_segs B) m' (q + t) = mbyte (ms_segs B) mc (q + t)) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (X <= a < X + 8) -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) mc a).
Proof using PRE GR A0 ARR SEGS AX GOWN GFACT GOTG.
  intros xs N Lc Ac mc mdc m' X cs i c o Hc CH FR DW (CW & MU & WM) HX Ho1 Ho2.
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  pose proof (call_len i c Hc) as Hl6.
  destruct (ka_hyps ltac:(lia)) as ((_ & HSW & HDW & HDN) & UC).
  destruct (dst_facts ltac:(lia)) as (_ & D1 & D2).
  destruct pre_facts as (HM0 & HCE & H63 & _).
  unfold RCC_K, XMALLOC_K, ALLOC_STACK in HCE.
  pose proof alloc_ceiling_val as AC.
  destruct (mc_MR _ _ _ _ _ _ CH) as (HMc & _).
  assert (OUT : forall a, 0 <= a < 2 ^ 64 -> ~ (X <= a < X + 8) -> outside [(X, X + 8)] a)
    by (intros a Ra Ha; apply outside_one; [exact Ra | exact Ha]).
  split.
  { apply (mchain_own _ _ _ L A mem md b xs N Lc Ac mc mdc m' [(X, X + 8)] CH MU); [rewrite SEGS; exact WM | | lia |].
    - unfold RCC_K, XMALLOC_K, ALLOC_STACK. lia.
    - intros a Ra Hn. apply not_out1 in Hn. right. split.
      + exists i, c. split; [exact Hc | lia].
      + left. lia. }
  split.
  { apply (frm_keep mc); [exact FR|]. intros a Ha.
    assert (Ow : outside [(X, X + 8)] a) by (apply OUT; unfold spZ in *; lia).
    split; [exact (munch_mbyte _ _ _ _ a MU ltac:(unfold spZ in *; lia) Ow)
           | exact (munch_writable _ _ _ _ a MU ltac:(unfold spZ in *; lia) Ow)]. }
  split.
  { intros t Ht. rewrite <- SEGS in WM. apply WM. exact (DW t Ht). }
  split.
  { intros q k t Hq Ht. pose proof (block_facts B _ (aa_laws API) Lc Ac mc mdc q k t HMc Hq Ht) as (_ & B1 & B2 & _).
    apply (munch_mbyte _ _ _ _ _ MU); [lia|]. apply OUT; [lia|]. lia. }
  intros a Ra Ha. exact (munch_mbyte _ _ _ _ a MU Ra (OUT a Ra Ha)).
Qed.

Lemma ar_store : forall xs N Lc Ac mc mdc m' i c j s pn qs Pn,
  nth_error (r_calls R) i = Some c -> nth_error (snd c) j = Some s -> length Pn = j ->
  CHS xs N Lc Ac mc mdc -> FRM mc -> DSTW mc -> DONE Lc Ac mc i qs -> HDR mc i c -> ARGS Lc Ac mc i c Pn ->
  fst pn <> 0 -> In pn (blocks Lc Ac) -> snd pn = Z.of_nat (length s) + 1 -> fresh_block B (fst pn) (snd pn) ->
  bytes_at (ms_segs B) mc (fst pn) (s ++ [Z_to_bv 8 0]) -> no0 s ->
  XW (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) [C8 (Z_to_bv 64 (fst pn))] mc m' ->
  CHS xs N Lc Ac m' mdc /\ FRM m' /\ DSTW m' /\ DONE Lc Ac m' i qs /\ HDR m' i c /\ ARGS Lc Ac m' i c (Pn ++ [pn]).
Proof using PRE GR A0 ARR SEGS AX GOWN GFACT GOTG.
  intros xs N Lc Ac mc mdc m' i c j s pn qs Pn Hc Es HL CH FR DW DN HD AG PNZ PIN PSZ PFR PBY PN0 XWr.
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  assert (Hj : (j < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  pose proof (call_len i c Hc) as Hl6.
  destruct (ka_hyps ltac:(lia)) as ((_ & HSW & HDW & HDN) & UC).
  rewrite UC in XWr.
  destruct (slot_store_common xs N Lc Ac mc mdc m' _ _ i c (8 + 8 * Z.of_nat j) Hc CH FR DW XWr ltac:(lia)
              ltac:(lia) ltac:(lia)) as (CH' & FR' & DW' & BK & KO).
  destruct XWr as (CW & _ & _).
  destruct (dst_facts ltac:(lia)) as (_ & D1 & D2).
  split; [exact CH'|]. split; [exact FR'|]. split; [exact DW'|].
  split.
  { apply (done_transfer Lc Ac mc); [exact DN | intros pn' H; exact H | exact BK |]. intros t Ht. apply KO; lia. }
  split.
  { apply (hdr_transfer mc); [exact HD|]. intros t Ht. apply KO; lia. }
  intros a s' pn' Es' Ep'.
  destruct (Nat.lt_ge_cases a j) as [Ha|Ha].
  - rewrite nth_error_app1 in Ep' by lia.
    apply (args_transfer_lt Lc Ac mc Lc Ac m' i c Pn AG (fun pn0 H => H) BK); [| exact Es' | exact Ep'].
    intros a' t Ha' Ht. apply KO; lia.
  - rewrite nth_error_app2 in Ep' by lia.
    destruct (a - length Pn)%nat as [|a0] eqn:E0; [|destruct a0; cbn in Ep'; discriminate].
    cbn in Ep'. injection Ep' as <-. assert (Ea : a = j) by lia. subst a.
    rewrite Es in Es'. injection Es' as <-.
    split.
    { apply rw8_bytes in CW. rewrite SEGS.
      replace (dst + 56 * Z.of_nat i + 8 + 8 * Z.of_nat j) with (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) by lia.
      exact CW. }
    split; [exact PNZ|]. split; [exact PIN|]. split; [exact PSZ|]. split; [exact PFR|].
    split; [|exact PN0].
    apply (bytes_at_transfer _ mc); [exact PBY|]. intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
    destruct pn as [q k]. cbn [fst snd] in *. apply (BK q k t PIN). lia.
Qed.

Lemma cp_store : forall xs Lc Ac mc mdc m' i c qs Pn p n,
  nth_error (r_calls R) i = Some c ->
  CHS xs ((concat qs ++ Pn) ++ [(p, n)]) Lc Ac mc mdc -> FRM mc -> DSTW mc -> DONE Lc Ac mc i qs -> HDR mc i c ->
  ARGS Lc Ac mc i c Pn ->
  munch [(p, p + n)] mc m' -> wmono rsegs mc m' -> (forall t, 0 <= t < n -> writable_at rsegs m' (p + t)) ->
  CHS xs ((concat qs ++ Pn) ++ [(p, n)]) Lc Ac m' mdc /\ FRM m' /\ DSTW m' /\ DONE Lc Ac m' i qs /\ HDR m' i c /\
  ARGS Lc Ac m' i c Pn.
Proof using PRE GR A0 ARR SEGS AX GOTG.
  intros xs Lc Ac mc mdc m' i c qs Pn p n Hc CH FR DW DN HD AG MU WM HWR.
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  pose proof (call_len i c Hc) as Hl6.
  destruct (dst_facts ltac:(lia)) as (_ & D1 & D2).
  destruct pre_facts as (HM0 & HCE & H63 & _).
  unfold RCC_K, XMALLOC_K, ALLOC_STACK in HCE.
  pose proof alloc_ceiling_val as AC.
  destruct (mc_MR _ _ _ _ _ _ CH) as (HMc & _).
  pose proof CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPERM & HND & _ & HPOS & _).
  assert (HIN : In (p, n) ((concat qs ++ Pn) ++ [(p, n)])) by (apply in_or_app; right; left; reflexivity).
  assert (PB : In (p, n) (blocks Lc Ac))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; exact HIN).
  pose proof (HPOS _ HIN) as Hn. cbn in Hn.
  pose proof (block_facts B _ (aa_laws API) Lc Ac mc mdc p n 0 HMc PB ltac:(lia)) as (_ & P1 & P2 & _).
  assert (OUTI : forall a, 0 <= a < 2 ^ 64 -> ~ (p <= a < p + n) -> outside [(p, p + n)] a)
    by (intros a R0 H; apply outside_one; [exact R0 | exact H]).
  assert (KHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) mc a /\
            (writable_at (ms_segs B) mc a <-> writable_at (ms_segs B) m' a)).
  { intros a Ha. split.
    - apply (munch_mbyte _ _ mc m' a MU); [lia | apply OUTI; lia].
    - apply (munch_writable _ _ mc m' a MU); [lia | apply OUTI; lia]. }
  assert (NEQ : forall pn, In pn (concat qs ++ Pn) -> fst pn <> p).
  { intros pn Hpn E. apply NoDup_ListNoDup in HND. rewrite map_app in HND. cbn [map fst] in HND.
    apply NoDup_remove_2 in HND. apply HND.
    rewrite app_nil_r. apply in_map_iff. exists pn. split; [exact E | exact Hpn]. }
  assert (KB : forall pn t, In pn (concat qs ++ Pn) -> 0 <= t < snd pn ->
             mbyte (ms_segs B) m' (fst pn + t) = mbyte (ms_segs B) mc (fst pn + t)).
  { intros [q k] t Hq Ht. pose proof (NEQ _ Hq) as Hne. cbn [fst snd] in *.
    assert (Qb : In (q, k) (blocks Lc Ac))
      by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; apply in_or_app; left; exact Hq).
    pose proof (block_facts B _ (aa_laws API) Lc Ac mc mdc q k t HMc Qb Ht) as (_ & Q1 & Q2 & _).
    destruct (in_split _ _ PB) as (l1 & l2 & EL).
    assert (Q12 : In (q, k) (l1 ++ l2)).
    { rewrite EL in Qb. apply in_app_or in Qb as [H|[H|H]].
      - apply in_or_app. left. exact H.
      - exfalso. apply Hne. injection H as E1 E2. congruence.
      - apply in_or_app. right. exact H. }
    pose proof (blocks_mid_disjoint B _ (aa_laws API) Lc Ac mc mdc l1 l2 p n q k HMc EL Q12) as DJ.
    apply (munch_mbyte _ _ mc m' _ MU); [lia | apply OUTI; lia]. }
  split; [exact (mchain_blk _ _ _ L A mem md b xs _ Lc Ac mc mdc m' p n CH HIN MU ltac:(rewrite SEGS; exact WM) HWR)|].
  split.
  { apply (frm_keep mc); [exact FR|]. intros a Ha. apply KHI. unfold spZ in *. lia. }
  split.
  { intros t Ht. apply (proj1 (proj2 (KHI (dst + t) ltac:(lia)))). exact (DW t Ht). }
  split.
  { apply (done_transfer_P Lc Ac mc); [exact DN | |].
    - intros pn t Hpn Ht. apply KB; [apply in_or_app; left; exact Hpn | exact Ht].
    - intros t Ht. assert (Hq : (length qs = i)) by exact (proj1 DN). apply (proj1 (KHI (dst + t) ltac:(lia))). }
  split.
  { apply (hdr_transfer mc); [exact HD|]. intros t Ht.
    apply (proj1 (KHI (dst + 56 * Z.of_nat i + t) ltac:(lia))). }
  apply (args_transfer_P Lc Ac mc); [exact AG | |].
  - intros pn t Hpn Ht. apply KB; [apply in_or_app; right; exact Hpn | exact Ht].
  - intros t Ht. apply (proj1 (KHI (dst + 56 * Z.of_nat i + t) ltac:(lia))).
Qed.

Lemma done_snoc : forall Lc Ac mc i qs c P, DONE Lc Ac mc i qs -> nth_error (r_calls R) i = Some c ->
  HDR mc i c -> ARGS Lc Ac mc i c P -> length P = length (snd c) -> DONE Lc Ac mc (S i) (qs ++ [P]).
Proof.
  intros Lc Ac mc i qs c P (HL & HD) Hc H1 H2 H3. split; [rewrite length_app; cbn [length]; lia|].
  intros i' c' P' Hc' HP'. destruct (Nat.lt_ge_cases i' i) as [Hlt|Hge].
  - rewrite nth_error_app1 in HP' by lia. exact (HD i' c' P' Hc' HP').
  - rewrite nth_error_app2 in HP' by lia.
    destruct (i' - length qs)%nat as [|a0] eqn:E0; [|destruct a0; cbn in HP'; discriminate].
    cbn in HP'. injection HP' as <-. assert (E : i' = i) by lia. subst i'.
    rewrite Hc in Hc'. injection Hc' as <-. split; [exact H3|]. split; [exact H1 | exact H2].
Qed.

Lemma concat_split : forall (qs : list (list (Z * Z))) i P, nth_error qs i = Some P ->
  concat qs = concat (firstn i qs) ++ P ++ concat (skipn (S i) qs).
Proof.
  intros qs i P H. rewrite <- (firstn_skipn (S i) qs) at 1. rewrite (CF.rec_calls_free.firstn_snoc qs i P H).
  rewrite !concat_app. cbn [concat]. rewrite app_nil_r, app_assoc. reflexivity.
Qed.

Lemma nodup_mid : forall X P Y : list (Z * Z), NoDup (map fst (X ++ P ++ Y)) -> NoDup (map fst P).
Proof.
  intros X P Y H. rewrite !map_app in H. apply list_relations.list.NoDup_app in H as (_ & _ & H).
  apply list_relations.list.NoDup_app in H as (H & _ & _). exact H.
Qed.

Lemma O_old : forall pn, In pn O -> In pn (blocks L A).
Proof using GR.
  intros pn Hin. destruct GR as (Q & HR & HO).
  exact (rep_at_blocks (ms_segs B) _ _ _ _ _ _ pn HR (proj1 (HO pn) Hin)).
Qed.

Lemma ret_post : forall Rf mf mdf Lf Af qs, regs_preserved regs Rf ->
  getr Rf 10 = Z_to_bv 64 (Z.of_nat (length (r_calls R))) ->
  CHS (rcc_args (r_calls R)) (concat qs) Lf Af mf mdf -> DONE Lf Af mf (length (r_calls R)) qs -> DSTW mf ->
  SR (ms_segs B) (mkCfg (mkst Rf (ret_pc (getr regs 1)) mf (seg_rom (ms_segs B))) mdf) POST.
Proof using PRE GR A0 ARR GFACT GOWN.
  intros Rf mf mdf Lf Af qs HR H10 CH (DL & DD) DW.
  destruct pre_facts as (HM0 & HCE & H63 & HAL & HRA & HWA & HTP).
  rewrite (ret_pc_of_ok _ HRA). apply SR_ret.
  pose proof CH as (HMc & HWc & HBc & HLE & HRG & HINIT & HVM & HSUB & HPTR & HPERM & HND & HDJ & HPOS & HBYTES
    & HFRAME & HSCR & HRO & HGK & HRES).
  exists Lf, Af, Rf, mf, mdf, qs. split; [reflexivity|].
  split; [exact (mchain_post _ _ _ L A regs mem md b _ _ Lf Af Rf mf mdf eq_refl CH HR)|].
  split; [exact H10|]. split; [exact DL|].
  split.
  { intros i c P Hc HP. destruct (DD i c P Hc HP) as (PL & (H1 & H2) & AG).
    destruct rep_facts as (_ & _ & RF). destruct (RF i c Hc) as (Po & (CF & CL & CP & _ & _ & _ & _) & FL).
    split.
    - split; [exact CF|]. split; [exact CL|]. split; [exact PL|].
      split; [unfold CALL_OFF_FN; rewrite Z.add_0_r; exact H1|]. split; [exact H2|].
      split.
      { apply (nodup_mid (concat (firstn i qs)) P (concat (skipn (S i) qs))).
        rewrite <- (concat_split qs i P HP). exact HND. }
      intros a s pn Es Ep. destruct (AG a s pn Es Ep) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
      assert (LX : Z.of_nat (length s) <= LMAX)
        by (rewrite Forall_forall in FL; apply FL; eapply nth_error_In; exact Es).
      split; [unfold CALL_OFF_ARGS; exact P1|]. split; [exact P2|]. split; [exact P3|].
      split; [unfold LMAX in *; lia|]. split; [exact P6 | exact P7].
    - intros a s pn Es Ep. destruct (AG a s pn Es Ep) as (_ & _ & _ & P4 & P5 & _). split; [exact P4 | exact P5]. }
  split; [exact HPERM|]. split; [exact HND|]. split; [exact HDJ|].
  split; [intros a k t Hin _ Ht; exact (old_kept _ _ _ _ _ _ CH a k t Hin Ht)|].
  split; [intros q k Hq; exact (HSUB _ Hq)|].
  split.
  { unfold g_rec_rep in *. apply (rec_rep_frame (ms_segs B) G_REC REC_SC L A mem R O Lf Af mf GR).
    - intros a Ha.
      assert (Hg : in_globals frame_G a) by (apply fg_iff; unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia).
      destruct (glob_kept _ _ _ _ _ _ CH a Hg) as [E1 E2]. split; [exact E1 | apply E2].
    - intros p n t Hp Ht. exact (old_kept _ _ _ _ _ _ CH p n t (O_old _ Hp) Ht).
    - intros pn Hpn. exact (old_in _ _ _ _ _ _ CH pn (O_old _ Hpn)). }
  split; [intros a Ha; exact (glob_kept _ _ _ _ _ _ CH a Ha)|].
  split; [exact DW|]. split; [exact HRO|]. split; [exact HGK|]. split; [exact HINIT|]. split; [exact HRG|].
  exact HRES.
Qed.

Definition QH (i : nat) (X : (word -> option byte) -> Prop) (ms : machine_state) : Prop :=
  exists Rc m', ms = MS Rc fp_regs (Z_to_bv 64 0x15c94) fp_csr None m' (seg_rom rsegs) /\ RG Rc i /\ X m'.

Definition QRET (X : (word -> option byte) -> Prop) (ms : machine_state) : Prop :=
  exists Rc m', ms = MS Rc fp_regs (ret_pc (getr regs 1)) fp_csr None m' (seg_rom rsegs) /\
    (regs_preserved regs Rc /\ getr Rc 10 = Z_to_bv 64 (Z.of_nat (length (r_calls R)))) /\ X m'.

Definition QXM (i j : nat) (len : Z) (pw : word) (X : (word -> option byte) -> Prop) (ms : machine_state) : Prop :=
  exists Rc m', ms = MS Rc fp_regs (Z_to_bv 64 0x15a88) fp_csr None m' (seg_rom rsegs) /\
    (getr Rc 1 = Z_to_bv 64 0x15d20 /\ getr Rc 10 = Z_to_bv 64 (len + 1) /\ RGX Rc i j len pw) /\ X m'.

Definition QLP (i j : nat) (X : (word -> option byte) -> Prop) (ms : machine_state) : Prop :=
  exists Rc m', ms = MS Rc fp_regs (Z_to_bv 64 0x15d00) fp_csr None m' (seg_rom rsegs) /\ RGI Rc i j /\ X m'.

Definition INV (i : nat) (cfg : config) : Prop :=
  exists Rc mc mdc Lc Ac qs, cfg = mkCfg (mkst Rc (Z_to_bv 64 0x15c94) mc (seg_rom (ms_segs B))) mdc /\
    RG Rc i /\ FRM mc /\ CHS (rcc_args (firstn i (r_calls R))) (concat qs) Lc Ac mc mdc /\ DONE Lc Ac mc i qs /\
    DSTW mc.

Definition NEXT (i : nat) : Prop :=
  (S i < length (r_calls R))%nat -> forall cfg, INV (S i) cfg -> SR (ms_segs B) cfg POST.

Lemma chs_end : forall i c qs Pn Lc Ac mc mdc, nth_error (r_calls R) i = Some c -> length Pn = length (snd c) ->
  CHS (XS i (length (snd c)) c) (concat qs ++ Pn) Lc Ac mc mdc ->
  CHS (rcc_args (firstn (S i) (r_calls R))) (concat (qs ++ [Pn])) Lc Ac mc mdc.
Proof.
  intros i c qs Pn Lc Ac mc mdc Hc HL CH. unfold XS in CH. rewrite firstn_all in CH.
  rewrite (rcc_args_snoc _ i c Hc), concat_app. cbn [concat]. rewrite app_nil_r. exact CH.
Qed.

Lemma cells_norm : forall mc a cs, ro_agree rsegs mc -> rw_cells rsegs mc a cs ->
  (forall t, 0 <= t < Z.of_nat (cells_size cs) -> 2 ^ 20 <= a + t < 2 ^ 64 \/ in_globals frame_G (a + t)) ->
  rw_cells rsegs (normalize rsegs mc) a cs.
Proof.
  intros mc a cs RA H HA. apply rw_cells_normalize; [exact RA | exact H |]. intros t Ht. unfold wa.
  destruct (HA t Ht) as [Hh|Hg]; [apply hi_rw; exact Hh | apply fg_rw; exact Hg].
Qed.

Lemma blk_cells : forall xs N Lc Ac mc mdc p n, CHS xs N Lc Ac mc mdc -> In (p, n) (blocks Lc Ac) -> 0 < n ->
  exists junk, rw_cells rsegs (normalize rsegs mc) p [CB (Z.to_nat n) junk].
Proof using SEGS AX.
  intros xs N Lc Ac mc mdc p n CH Hin Hn. destruct (mc_MR _ _ _ _ _ _ CH) as (HMc & _).
  pose proof alloc_ceiling_val as AC.
  pose proof (block_facts B _ (aa_laws API) Lc Ac mc mdc p n 0 HMc Hin ltac:(lia)) as (_ & P1 & P2 & _).
  apply present_rw_cells; [lia | rewrite Z2Nat.id by lia; lia |].
  intros t Ht. rewrite Z2Nat.id in Ht by lia.
  destruct (proj1 (block_facts B _ (aa_laws API) _ _ _ _ _ _ t HMc Hin Ht)) as [bb E].
  exists bb. rewrite normalize_rw; [exact E|]. apply (ro_addr_out B SEGS); [lia|].
  exact (block_not_img B API AX Lc Ac mc mdc p n t HMc Hin Ht).
Qed.

Hypothesis AL8 : (0 < length (r_calls R))%nat -> dst mod 8 = 0.

Lemma src_slack8 : forall xs N Lc Ac mc mdc i c Po j s opn,
  CHS xs N Lc Ac mc mdc ->
  call_at (ms_segs B) (blocks L A) mem (0x34038 + 56 * Z.of_nat i) c Po ->
  nth_error (snd c) j = Some s -> nth_error Po j = Some opn ->
  exists slack, bytes_at rsegs mc (fst opn) (s ++ Z_to_bv 8 0 :: slack) /\
    (- (fst opn + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) /\ no0 s /\
    fst opn + Z.of_nat (length (s ++ Z_to_bv 8 0 :: slack)) <= alloc_ceiling /\
    fst opn + Z.of_nat (length (s ++ Z_to_bv 8 0 :: slack)) = 8 * ((fst opn + (Z.of_nat (length s) + 1) + 7) / 8) /\
    In opn (blocks L A) /\ Z.of_nat (length s) + 1 <= snd opn.
Proof using SEGS SLACK.
  clear AL8.
  intros xs N Lc Ac mc mdc i c Po j s opn CH CA Es Eo.
  destruct CA as (CF & CL & CP & CB1 & CB2 & CND & CK).
  destruct (CK j s opn Es Eo) as (OB & ONZ & OIN & OSZ & OBY & ON0).
  destruct (mc_MR _ _ _ _ _ _ CH) as (HMc & HWc).
  pose proof alloc_ceiling_val as AC.
  destruct opn as [q k]. cbn [fst snd] in *.
  assert (QIN : In (q, k) (blocks Lc Ac)) by exact (old_in _ _ _ _ _ _ CH _ OIN).
  pose proof (block_facts B _ (aa_laws API) Lc Ac mc mdc q k 0 HMc QIN ltac:(lia)) as (_ & Q1 & Q2 & _).
  assert (SBY : bytes_at (ms_segs B) mc q (s ++ [Z_to_bv 8 0])).
  { apply (bytes_at_transfer _ mem); [exact OBY|]. intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
    apply (old_kept _ _ _ _ _ _ CH q k t OIN). lia. }
  rewrite SEGS in SBY.
  destruct (slack_rebuild' mc q s SBY ltac:(lia) ltac:(lia)) as (slack & SBS & SAL & SEND).
  { intros a Ha. destruct (Z_lt_ge_dec a (q + k)) as [D|D].
    - replace a with (q + (a - q)) by ring.
      exact (proj1 (block_facts B _ (aa_laws API) Lc Ac mc mdc q k (a - q) HMc QIN ltac:(lia))).
    - apply (SLACK Lc Ac mc mdc q k a HMc QIN). split; [lia|].
      pose proof (ceil8_mono (q + (Z.of_nat (length s) + 1)) (q + k) ltac:(lia)). lia. }
  assert (AC8 : alloc_ceiling mod 8 = 0) by (Z.div_mod_to_equations; lia).
  exists slack. split; [exact SBS|]. split; [exact SAL|]. split; [exact ON0|].
  split; [rewrite SEND; pose proof (ceil8_le (q + (Z.of_nat (length s) + 1)) alloc_ceiling ltac:(lia) AC8); lia|].
  split; [exact SEND|]. split; [exact OIN | lia].
Qed.

Lemma arg_cell : forall xs N Lc Ac mc mdc i c Po j s opn, CHS xs N Lc Ac mc mdc ->
  nth_error (r_calls R) i = Some c -> call_at (ms_segs B) (blocks L A) mem (0x34038 + 56 * Z.of_nat i) c Po ->
  nth_error (snd c) j = Some s -> nth_error Po j = Some opn ->
  rw_cells rsegs (normalize rsegs mc) (0x34040 + 56 * Z.of_nat i + 8 * Z.of_nat j) [C8 (Z_to_bv 64 (fst opn))].
Proof using PRE GR A0 ARR GFACT GOWN SEGS.
  clear AL8.
  intros xs N Lc Ac mc mdc i c Po j s opn CH Hc CA Es Eo.
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  assert (Hj : (j < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  destruct rep_facts as (H16 & _). pose proof (call_len i c Hc) as Hl6.
  destruct CA as (_ & _ & _ & _ & _ & _ & CK). destruct (CK j s opn Es Eo) as (OB & _).
  destruct (mc_misc _ _ _ _ _ _ CH) as (HRO & _).
  apply cells_norm; [rewrite <- SEGS; exact HRO | |].
  - apply (rec_cells _ _ _ _ _ _ _ _ 8 CH); [cbn; tauto | | reflexivity | unfold GLOB_LO; lia
      | unfold GLOB_LO; change (Z.of_nat GLOB_N) with 1020; lia].
    cbn [cells_bytes cbytes]. rewrite app_nil_r.
    replace (0x34040 + 56 * Z.of_nat i + 8 * Z.of_nat j) with (0x34038 + 56 * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat j)
      by (unfold CALL_OFF_ARGS; lia).
    exact OB.
  - intros t Ht. cbn in Ht. right. apply fg_iff. lia.
Qed.

Definition AFX (i j : nat) (p : Z) (s : list byte) (m2 m' : word -> option byte) : Prop :=
  rw_cells rsegs m' p [CB (Z.to_nat (Z.of_nat (length s) + 1)) (s ++ [Z_to_bv 8 0])] /\
  rw_cells rsegs m' (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) [C8 (Z_to_bv 64 p)] /\
  munch [(p, p + (Z.of_nat (length s) + 1));
         (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j,
          bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j + 8)] (normalize rsegs m2) m' /\
  wmono rsegs (normalize rsegs m2) m'.

Lemma af_back : forall xs i c j s qs Pn Lc Ac m2 mdc mn mf p,
  nth_error (r_calls R) i = Some c -> nth_error (snd c) j = Some s -> length Pn = j ->
  CHS xs ((concat qs ++ Pn) ++ [(p, Z.of_nat (length s) + 1)]) Lc Ac m2 mdc -> FRM m2 -> DSTW m2 ->
  DONE Lc Ac m2 i qs -> HDR m2 i c -> ARGS Lc Ac m2 i c Pn ->
  p <> 0 -> In (p, Z.of_nat (length s) + 1) (blocks Lc Ac) -> fresh_block B p (Z.of_nat (length s) + 1) -> no0 s ->
  AFX i j p s m2 mn -> mem_rel rsegs mf mn -> ro_same rsegs m2 mf ->
  CHS xs ((concat qs ++ Pn) ++ [(p, Z.of_nat (length s) + 1)]) Lc Ac mf mdc /\ FRM mf /\ DSTW mf /\
  DONE Lc Ac mf i qs /\ HDR mf i c /\ ARGS Lc Ac mf i c (Pn ++ [(p, Z.of_nat (length s) + 1)]).
Proof using PRE GR A0 ARR SEGS AX GOWN GFACT GOTG.
  clear AL8.
  intros xs i c j s qs Pn Lc Ac m2 mdc mn mf p Hc Es HL CH FR DW DN HD AG PNZ PIN PFR PN0 (CBn & CSn & MUn & WMn) MR ROS.
  destruct (mc_misc _ _ _ _ _ _ CH) as (HRO & _).
  assert (RA : ro_agree rsegs m2) by (rewrite <- SEGS; exact HRO).
  destruct (norm_back m2 mn mf _ RA MR ROS MUn WMn) as (MU & WM & _).
  pose proof (rw_cells_rel rsegs _ _ _ _ MR CBn) as CBK.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR CSn) as CS.
  destruct (munch2_mid p (Z.of_nat (length s) + 1) _ m2 mf MU WM) as (MU1 & WM1 & MU2 & WM2 & EQ).
  destruct (mc_MR _ _ _ _ _ _ CH) as (HM2 & _).
  pose proof (block_facts B _ (aa_laws API) Lc Ac m2 mdc p _ 0 HM2 PIN ltac:(lia)) as (_ & P1 & P2 & _).
  pose proof alloc_ceiling_val as AC.
  assert (SZ : Z.of_nat (cells_size [CB (Z.to_nat (Z.of_nat (length s) + 1)) (s ++ [Z_to_bv 8 0])]) =
               Z.of_nat (length s) + 1) by (cbn [cells_size csize]; lia).
  destruct CBK as [[_ HB] (_ & _ & HW)]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  assert (HWR : forall t, 0 <= t < Z.of_nat (length s) + 1 -> writable_at rsegs (mmid p (Z.of_nat (length s) + 1) m2 mf) (p + t)).
  { intros t Ht. apply (proj2 (EQ (p + t) ltac:(lia) ltac:(lia))). apply HW. lia. }
  assert (PBY : bytes_at (ms_segs B) (mmid p (Z.of_nat (length s) + 1) m2 mf) p (s ++ [Z_to_bv 8 0])).
  { rewrite SEGS. apply (bytes_at_transfer rsegs mf); [exact HB|]. intros t Ht. rewrite length_app in Ht.
    cbn [length] in Ht. apply (proj1 (EQ (p + t) ltac:(lia) ltac:(lia))). }
  destruct (cp_store xs Lc Ac m2 mdc _ i c qs Pn p _ Hc CH FR DW DN HD AG MU1 WM1 HWR)
    as (CH' & FR' & DW' & DN' & HD' & AG').
  exact (ar_store xs _ Lc Ac _ mdc mf i c j s (p, Z.of_nat (length s) + 1) qs Pn Hc Es HL CH' FR' DW' DN' HD' AG'
           PNZ PIN eq_refl PFR PBY PN0 (conj CS (conj MU2 WM2))).
Qed.

Lemma af_run : forall i c Po j s opn L2 A2 R2 m2 md2 p qs Pn,
  nth_error (r_calls R) i = Some c -> call_at (ms_segs B) (blocks L A) mem (0x34038 + 56 * Z.of_nat i) c Po ->
  NEXT i -> nth_error (snd c) j = Some s -> nth_error Po j = Some opn -> length Pn = j ->
  RGX R2 i j (Z.of_nat (length s)) (Z_to_bv 64 (fst opn)) -> getr R2 10 = Z_to_bv 64 p -> FRM m2 ->
  CHS (XS i (S j) c) ((concat qs ++ Pn) ++ [(p, Z.of_nat (length s) + 1)]) L2 A2 m2 md2 ->
  DONE L2 A2 m2 i qs -> HDR m2 i c -> ARGS L2 A2 m2 i c Pn -> DSTW m2 ->
  p <> 0 -> p mod 16 = 0 -> In (p, Z.of_nat (length s) + 1) (blocks L2 A2) ->
  fresh_block B p (Z.of_nat (length s) + 1) ->
  bytes_at (ms_segs B) m2 (fst opn) (s ++ [Z_to_bv 8 0]) ->
  fst opn + (Z.of_nat (length s) + 1) <= p \/ p + (Z.of_nat (length s) + 1) <= fst opn ->
  (forall s' opn' Rc mc, nth_error (snd c) (S j) = Some s' -> nth_error Po (S j) = Some opn' ->
     getr Rc 1 = Z_to_bv 64 0x15d20 -> getr Rc 10 = Z_to_bv 64 (Z.of_nat (length s') + 1) ->
     RGX Rc i (S j) (Z.of_nat (length s')) (Z_to_bv 64 (fst opn')) -> FRM mc ->
     CHS (XS i (S j) c) (concat qs ++ Pn ++ [(p, Z.of_nat (length s) + 1)]) L2 A2 mc md2 ->
     DONE L2 A2 mc i qs -> HDR mc i c -> ARGS L2 A2 mc i c (Pn ++ [(p, Z.of_nat (length s) + 1)]) -> DSTW mc ->
     SR (ms_segs B) (mkCfg (mkst Rc (Z_to_bv 64 XMALLOC) mc (seg_rom (ms_segs B))) md2) POST) ->
  SR (ms_segs B) (mkCfg (mkst R2 (Z_to_bv 64 0x15d20) m2 (seg_rom (ms_segs B))) md2) POST.
Proof using PRE GR A0 ARR SEGS AX GOWN GFACT GOTG SLACK SLEN MCPY.
  clear AL8.
  intros i c Po j s opn L2 A2 R2 m2 md2 p qs Pn Hc CA NX Es Eo HL GX2 A10 FR2 CH2 DN2 HD2 AG2 DW2 PNZ PAL PIN PFR
    PBY SEP K.
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  assert (Hj : (j < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  pose proof (call_len i c Hc) as Hl6.
  destruct (ka_hyps ltac:(lia)) as (KO & UC). pose proof KO as (HN0 & HSW0 & HDW0 & HDN0).
  destruct (dst_facts ltac:(lia)) as (_ & D1 & D2).
  destruct rep_facts as (H16 & NCB & _).
  pose proof CA as (CF & CL & CP & CB1 & CB2 & CND & CK).
  destruct (CK j s opn Es Eo) as (_ & _ & _ & _ & _ & ON0).
  pose proof alloc_ceiling_val as AC.
  destruct pre_facts as (_ & HCE & H63 & _).
  unfold RCC_K, XMALLOC_K, ALLOC_STACK, spZ in HCE, H63. unfold spZ in D1.
  destruct (mc_MR _ _ _ _ _ _ CH2) as (HM2 & _).
  destruct (mc_misc _ _ _ _ _ _ CH2) as (HRO2 & _).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM2) as (Hh & Hl & _).
  pose proof CH2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDJ & _).
  pose proof (block_facts B _ (aa_laws API) L2 A2 m2 md2 p _ 0 HM2 PIN ltac:(lia)) as (_ & P1 & P2 & _).
  assert (RA2 : ro_agree rsegs m2) by (rewrite <- SEGS; exact HRO2).
  assert (P8 : p mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (NG : forall a, 0x33ff0 <= a < 0x33ff0 + 1020 -> ~ (p <= a < p + (Z.of_nat (length s) + 1))).
  { intros a Ha Hp. apply (block_not_img B API AX L2 A2 m2 md2 p _ (a - p) HM2 PIN ltac:(lia)).
    replace (p + (a - p)) with a by ring. exact (proj1 (GFACT a (proj2 (fg_iff a) Ha))). }
  assert (PG : p + (Z.of_nat (length s) + 1) <= 0x34030 \/ 0x34034 <= p).
  { destruct (Z_le_gt_dec p 0x34030).
    - destruct (Z_le_gt_dec (p + (Z.of_nat (length s) + 1)) 0x34030); [left; lia|].
      exfalso. apply (NG 0x34030); lia.
    - destruct (Z_le_gt_dec 0x34034 p); [right; lia|]. exfalso. apply (NG p); lia. }
  assert (OW : forall a, alloc_ceiling <= a < bv_unsigned (getr regs 2) \/ 0x33ff0 <= a < 0x33ff0 + 1020 ->
             0 <= a < 2 ^ 64 /\ outside [(p, p + (Z.of_nat (length s) + 1));
               (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j,
                bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j + 8)] a).
  { intros a Ha. split; [lia|]. cbn [outside]. split; [|split; [lia | exact I]].
    destruct Ha as [Ha|Ha]; [lia | exact (NG a Ha)]. }
  assert (UPW : bv_unsigned (Z_to_bv 64 (fst opn)) = fst opn).
  { pose proof (bytes_at_bound _ _ _ _ PBY) as BB. rewrite length_app in BB. cbn [length] in BB.
    apply unsigned_lit. lia. }
  assert (NSRC : bytes_at rsegs (normalize rsegs m2) (bv_unsigned (Z_to_bv 64 (fst opn))) (s ++ [Z_to_bv 8 0])).
  { rewrite UPW. apply bytes_at_normalize; [exact RA2|]. rewrite <- SEGS. exact PBY. }
  destruct (blk_cells _ _ _ _ _ _ p (Z.of_nat (length s) + 1) CH2 PIN ltac:(lia)) as [junk NBLK].
  assert (NNA : rw_cells rsegs (normalize rsegs m2) (bv_unsigned (getr regs 10) + 56 * Z.of_nat i + 4)
                  [C4 (Z_to_bv 64 (Z.of_nat (length (snd c))))]).
  { destruct HD2 as (HDa & HDb).
    assert (W2 : rw_cells rsegs m2 (dst + 56 * Z.of_nat i)
                   [C4 (Z_to_bv 64 (fst c)); C4 (Z_to_bv 64 (Z.of_nat (length (snd c))))]).
    { rewrite <- SEGS. apply rw2_intro; [exact HDa | exact HDb |]. intros t Ht.
      replace (dst + 56 * Z.of_nat i + t) with (dst + (56 * Z.of_nat i + t)) by ring. apply DW2. lia. }
    destruct (rk_app_split rsegs _ _ 4 [C4 (Z_to_bv 64 (fst c))] [C4 (Z_to_bv 64 (Z.of_nat (length (snd c))))]
                eq_refl W2) as [_ W4].
    rewrite UC. apply cells_norm; [exact RA2 | exact W4 |]. intros t Ht. cbn in Ht. left. lia. }
  destruct (dst_cells m2 (8 + 56 * Z.of_nat i + 8 * Z.of_nat j) 8 DW2 ltac:(lia) ltac:(lia) ltac:(lia)) as [jj AS2].
  assert (NAS : rw_cells rsegs (normalize rsegs m2) (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j)
                  [CB 8 jj]).
  { replace (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j)
      with (dst + (8 + 56 * Z.of_nat i + 8 * Z.of_nat j)) by lia.
    apply cells_norm; [exact RA2 | exact AS2 |]. intros t Ht. cbn in Ht. left. lia. }
  assert (NCN : rw_cells rsegs (normalize rsegs m2) 0x34030 [C4 (Z_to_bv 64 (Z.of_nat (length (r_calls R))))]).
  { apply cells_norm; [exact RA2 | |].
    - apply (rec_cells _ _ _ _ _ _ _ _ 4 CH2); [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact NCB
        | reflexivity | unfold GLOB_LO; lia | unfold GLOB_LO; change (Z.of_nat GLOB_N) with 1020; lia].
    - intros t Ht. cbn in Ht. right. apply fg_iff. lia. }
  destruct (frm_norm m2 FR2 HRO2) as [FL2 FS2].
  destruct (Nat.lt_ge_cases (S j) (length (snd c))) as [Hn|Hn].
  - destruct (nth_error (snd c) (S j)) as [s'|] eqn:Es'; [|apply nth_error_None in Es'; lia].
    destruct (nth_error Po (S j)) as [opn'|] eqn:Eo'; [|apply nth_error_None in Eo'; lia].
    pose proof (arg_cell _ _ _ _ _ _ i c Po (S j) s' opn' CH2 Hc CA Es' Eo') as ACn.
    destruct (src_slack8 _ _ _ _ _ _ i c Po (S j) s' opn' CH2 CA Es' Eo')
      as (sl' & SB' & SP' & ON0' & SE' & SEQ' & OIN' & OSZ').
    pose proof (bytes_at_bound _ _ _ _ SB') as BB'. rewrite length_app in BB'. cbn [length] in BB'.
    assert (UPW' : bv_unsigned (Z_to_bv 64 (fst opn')) = fst opn') by (apply unsigned_lit; lia).
    pose proof (bytes_at_normalize rsegs m2 _ _ RA2 SB') as NSB'.
    assert (HINp : In (p, Z.of_nat (length s) + 1) ((concat qs ++ Pn) ++ [(p, Z.of_nat (length s) + 1)]))
      by (apply in_or_app; right; left; reflexivity).
    assert (OS : forall t, 0 <= t < Z.of_nat (length (s' ++ Z_to_bv 8 0 :: sl')) ->
               0 <= fst opn' + t < 2 ^ 64 /\ outside [(p, p + (Z.of_nat (length s) + 1));
                 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j,
                  bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j + 8)] (fst opn' + t)).
    { intros t Ht. pose proof (HDJ (p, Z.of_nat (length s) + 1) opn' HINp OIN') as DJ. cbn [fst snd] in DJ.
      pose proof (ceil8_mono (fst opn' + (Z.of_nat (length s') + 1)) (fst opn' + snd opn') ltac:(lia)) as C1.
      assert (C2 : fst opn' + snd opn' <= p -> 8 * ((fst opn' + snd opn' + 7) / 8) <= p)
        by (intros Hq; apply ceil8_le; [exact Hq | exact P8]).
      split; [lia|]. cbn [outside]. split; [|split; [lia | exact I]].
      destruct DJ as [DJ|DJ]; [lia|]. specialize (C2 DJ). lia. }
    apply (run_ka R2 _ m2 md2 (QXM i (S j) (Z.of_nat (length s')) (Z_to_bv 64 (fst opn')) (AFX i j p s m2))
             Hh Hl HRO2).
    + rewrite (mkR_of_RGX R2 i j _ _ GX2), A10.
      eapply k_after_next with (str := s) (nargs := Z.of_nat (length (snd c))) (junk := junk) (jj := jj)
        (n := length (r_calls R)).
      all: try exact KO. all: try exact MCPY. all: try exact NSRC. all: try exact NBLK. all: try exact NNA.
      all: try exact NAS. all: try apply mem_inv_normalize. all: try (rewrite UPW; lia). all: try lia.
      intros m' CBm SLm NAm MUm WMm MIm. unfold st_lp. intros.
      eapply k_loop with (n := length (r_calls R)) (str := s') (slack := sl') (pw := Z_to_bv 64 (fst opn')).
      all: try exact SLEN. all: try exact KO. all: try exact MIm. all: try exact ON0'. all: try lia.
      * apply (rw_munch _ (normalize rsegs m2) m' _ _ ACn MUm). intros t Ht. cbn in Ht. apply OW. right. lia.
      * rewrite UPW'. apply (by_munch _ (normalize rsegs m2) m' _ _ NSB' MUm). exact OS.
      * intros m'' MU' WM' MI' BS'. unfold st_xm. intros. unfold QXM. do 2 eexists. split; [reflexivity|].
        split; [eapply rgx_mkR; reflexivity|].
        unfold AFX. split; [|split; [|split]].
        -- apply (rw_munch [] m' m'' _ _ CBm MU'). intros t Ht. split; [|exact I]. cbn [cells_size csize] in Ht. lia.
        -- apply (rw_munch [] m' m'' _ _ SLm MU'). intros t Ht. split; [|exact I]. cbn in Ht. lia.
        -- eapply munch_trans; [exact MUm|]. eapply munch_weaken; [|exact MU']. intros x _. exact I.
        -- eapply wmono_trans; [exact WMm | exact WM'].
    + intros ms' (can & (s0 & (R0 & mn & -> & (G1' & G10' & GX') & XX) & REL & ROS) & EQ).
      destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL) as [EC MR].
      revert EC MR ROS EQ. generalize (ms_mem can) as mf. intros mf EC MR ROS EQ. subst can.
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
      destruct (af_back _ i c j s qs Pn L2 A2 m2 md2 mn mf p Hc Es HL CH2 FR2 DW2 DN2 HD2 AG2 PNZ PIN PFR ON0 XX MR ROS)
        as (CH3 & FR3 & DW3 & DN3 & HD3 & AG3).
      rewrite <- SEGS. change (Z_to_bv 64 0x15a88) with (Z_to_bv 64 XMALLOC).
      apply (K s' opn' R' mf eq_refl eq_refl); [ | | | exact FR3 | rewrite app_assoc; exact CH3 | exact DN3 | exact HD3
        | exact AG3 | exact DW3].
      * rewrite (CF.rec_calls_free.getr_eqv R0 R' _ XR). exact G1'.
      * rewrite (CF.rec_calls_free.getr_eqv R0 R' _ XR). exact G10'.
      * exact (rgx_eqv _ _ _ _ _ _ GX' XR).
  - assert (HSj : S j = length (snd c)) by lia.
    destruct (Nat.lt_ge_cases (S i) (length (r_calls R))) as [Hs|Hs].
    + apply (run_ka R2 _ m2 md2 (QH (S i) (AFX i j p s m2)) Hh Hl HRO2).
      * rewrite (mkR_of_RGX R2 i j _ _ GX2), A10.
        eapply k_after_last with (str := s) (nargs := Z.of_nat (length (snd c))) (junk := junk) (jj := jj)
          (n := length (r_calls R)).
        all: try exact KO. all: try exact MCPY. all: try exact NSRC. all: try exact NBLK. all: try exact NNA.
        all: try exact NAS. all: try exact NCN. all: try apply mem_inv_normalize. all: try (rewrite UPW; lia).
        all: try lia.
        intros m' CBm SLm NAm NCm MUm WMm MIm.
        eapply k_tail_next with (n := length (r_calls R)). all: try exact KO. all: try lia.
        { apply (rw_munch _ (normalize rsegs m2) m' _ _ FL2 MUm). intros t Ht. unfold FRL in Ht. cbn in Ht.
          apply OW. left. lia. }
        unfold st_head. intros. unfold QH. do 2 eexists. split; [reflexivity|].
        split; [eapply rg_mkR; reflexivity|]. exact (conj CBm (conj SLm (conj MUm WMm))).
      * intros ms' (can & (s0 & (R0 & mn & -> & GR1 & XX) & REL & ROS) & EQ).
        destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL) as [EC MR].
        revert EC MR ROS EQ. generalize (ms_mem can) as mf. intros mf EC MR ROS EQ. subst can.
        destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
        destruct (af_back _ i c j s qs Pn L2 A2 m2 md2 mn mf p Hc Es HL CH2 FR2 DW2 DN2 HD2 AG2 PNZ PIN PFR ON0 XX MR
                    ROS) as (CH3 & FR3 & DW3 & DN3 & HD3 & AG3).
        rewrite <- SEGS. apply NX; [exact Hs|].
        exists R', mf, md2, L2, A2, (qs ++ [Pn ++ [(p, Z.of_nat (length s) + 1)]]). split; [reflexivity|].
        split; [exact (rg_eqv _ _ _ GR1 XR)|]. split; [exact FR3|].
        split.
        { apply (chs_end i c qs); [exact Hc | rewrite length_app; cbn [length]; lia |].
          rewrite <- HSj, app_assoc. exact CH3. }
        split; [|exact DW3].
        apply (done_snoc L2 A2 mf i qs c); [exact DN3 | exact Hc | exact HD3 | exact AG3 |].
        rewrite length_app. cbn [length]. lia.
    + apply (run_ka R2 _ m2 md2 (QRET (AFX i j p s m2)) Hh Hl HRO2).
      * rewrite (mkR_of_RGX R2 i j _ _ GX2), A10.
        eapply k_after_last with (str := s) (nargs := Z.of_nat (length (snd c))) (junk := junk) (jj := jj)
          (n := length (r_calls R)).
        all: try exact KO. all: try exact MCPY. all: try exact NSRC. all: try exact NBLK. all: try exact NNA.
        all: try exact NAS. all: try exact NCN. all: try apply mem_inv_normalize. all: try (rewrite UPW; lia).
        all: try lia.
        intros m' CBm SLm NAm NCm MUm WMm MIm.
        eapply k_tail_last with (n := length (r_calls R)). all: try exact KO. all: try lia.
        { apply (rw_munch _ (normalize rsegs m2) m' _ _ FL2 MUm). intros t Ht. unfold FRL in Ht. cbn in Ht.
          apply OW. left. lia. }
        { apply (rw_munch _ (normalize rsegs m2) m' _ _ FS2 MUm). intros t Ht. unfold FRS in Ht. cbn in Ht.
          apply OW. left. lia. }
        unfold st_ret. intros. unfold QRET. do 2 eexists. split; [reflexivity|].
        split; [eapply pres_mkR; reflexivity|]. exact (conj CBm (conj SLm (conj MUm WMm))).
      * intros ms' (can & (s0 & (R0 & mn & -> & (HP0 & H10) & XX) & REL & ROS) & EQ).
        destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL) as [EC MR].
        revert EC MR ROS EQ. generalize (ms_mem can) as mf. intros mf EC MR ROS EQ. subst can.
        destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
        destruct (af_back _ i c j s qs Pn L2 A2 m2 md2 mn mf p Hc Es HL CH2 FR2 DW2 DN2 HD2 AG2 PNZ PIN PFR ON0 XX MR
                    ROS) as (CH3 & FR3 & DW3 & DN3 & HD3 & AG3).
        assert (HSi : S i = length (r_calls R)) by lia.
        rewrite <- SEGS. apply (ret_post R' mf md2 L2 A2 (qs ++ [Pn ++ [(p, Z.of_nat (length s) + 1)]])).
        -- exact (pres_eqv _ _ HP0 XR).
        -- rewrite (CF.rec_calls_free.getr_eqv R0 R' _ XR). exact H10.
        -- rewrite <- (firstn_all (r_calls R)), <- HSi.
           apply (chs_end i c qs); [exact Hc | rewrite length_app; cbn [length]; lia |].
           rewrite <- HSj, app_assoc. exact CH3.
        -- rewrite <- HSi. apply (done_snoc L2 A2 mf i qs c); [exact DN3 | exact Hc | exact HD3 | exact AG3 |].
           rewrite length_app. cbn [length]. lia.
        -- exact DW3.
Qed.

Lemma rcc_inner : forall i c Po, nth_error (r_calls R) i = Some c ->
  call_at (ms_segs B) (blocks L A) mem (0x34038 + 56 * Z.of_nat i) c Po ->
  Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c) -> NEXT i ->
  forall k j s opn Rc mc mdc Lc Ac qs Pn, (length (snd c) - S j = k)%nat ->
  nth_error (snd c) j = Some s -> nth_error Po j = Some opn ->
  getr Rc 1 = Z_to_bv 64 0x15d20 -> getr Rc 10 = Z_to_bv 64 (Z.of_nat (length s) + 1) ->
  RGX Rc i j (Z.of_nat (length s)) (Z_to_bv 64 (fst opn)) -> FRM mc ->
  CHS (XS i j c) (concat qs ++ Pn) Lc Ac mc mdc -> DONE Lc Ac mc i qs -> HDR mc i c -> ARGS Lc Ac mc i c Pn ->
  length Pn = j -> DSTW mc ->
  SR (ms_segs B) (mkCfg (mkst Rc (Z_to_bv 64 XMALLOC) mc (seg_rom (ms_segs B))) mdc) POST.
Proof using PRE GR A0 ARR ROOM SEGS AX CTX GOWN GFACT ERRNO GOTG SLACK XM SLEN MCPY.
  clear AL8.
  intros i c Po Hc CA FL NX k.
  induction k as [|k IH]; intros j s opn Rc mc mdc Lc Ac qs Pn Hk Es Eo G1 G10 GX FR CH DN HD AG HL DW;
    (apply (xm_step i c Po j s opn (Z_to_bv 64 (fst opn)) Rc mc mdc Lc Ac qs Pn Hc CA FL Es Eo G1 G10 GX FR CH DN HD AG
              DW));
    intros L2 A2 R2 m2 md2 p GX2 A10 FR2 CH2 DN2 HD2 AG2 DW2 PNZ PAL PIN PFR PBY SEP;
    (apply (af_run i c Po j s opn L2 A2 R2 m2 md2 p qs Pn Hc CA NX Es Eo HL GX2 A10 FR2 CH2 DN2 HD2 AG2 DW2 PNZ PAL
              PIN PFR PBY SEP));
    intros s' opn' Rc' mc' Es' Eo' G1' G10' GX' FR' CH' DN' HD' AG' DW'.
  - exfalso. assert (Hl : (length (snd c) <= S j)%nat) by lia. apply nth_error_None in Hl. congruence.
  - apply (IH (S j) s' opn' Rc' mc' md2 L2 A2 qs (Pn ++ [(p, Z.of_nat (length s) + 1)])); try assumption.
    + lia.
    + rewrite length_app. cbn [length]. lia.
Qed.

Definition HX (i : nat) (cs : list cell) (mc m' : word -> option byte) : Prop :=
  rw_cells rsegs m' (bv_unsigned (getr regs 10) + 56 * Z.of_nat i) cs /\
  munch [(bv_unsigned (getr regs 10) + 56 * Z.of_nat i, bv_unsigned (getr regs 10) + 56 * Z.of_nat i + 8)]
    (normalize rsegs mc) m' /\ wmono rsegs (normalize rsegs mc) m'.

Lemma hx_back : forall xs N Lc Ac mc mdc mn mf i c qs, nth_error (r_calls R) i = Some c ->
  CHS xs N Lc Ac mc mdc -> FRM mc -> DSTW mc -> DONE Lc Ac mc i qs ->
  HX i [C4 (Z_to_bv 64 (fst c)); C4 (Z_to_bv 64 (Z.of_nat (length (snd c))))] mc mn ->
  mem_rel rsegs mf mn -> ro_same rsegs mc mf ->
  CHS xs N Lc Ac mf mdc /\ FRM mf /\ DSTW mf /\ DONE Lc Ac mf i qs /\ HDR mf i c /\ ARGS Lc Ac mf i c [].
Proof using PRE GR A0 ARR SEGS AX GOWN GFACT GOTG.
  clear AL8.
  intros xs N Lc Ac mc mdc mn mf i c qs Hc CH FR DW DN (CW & MU & WM) MR ROS.
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  pose proof (call_len i c Hc) as Hl6.
  destruct (ka_hyps ltac:(lia)) as ((_ & HSW & HDW & HDN) & UC).
  destruct (dst_facts ltac:(lia)) as (_ & D1 & D2).
  destruct (mc_misc _ _ _ _ _ _ CH) as (HRO & _).
  assert (RA : ro_agree rsegs mc) by (rewrite <- SEGS; exact HRO).
  destruct (norm_back mc mn mf _ RA MR ROS MU WM) as (MUr & WMr & _).
  pose proof (rw_cells_rel rsegs _ _ _ _ MR CW) as CWf.
  rewrite UC in MUr, CWf.
  destruct (slot_store_common xs N Lc Ac mc mdc mf (dst + 56 * Z.of_nat i) _ i c 0 Hc CH FR DW (conj CWf (conj MUr WMr))
              ltac:(lia) ltac:(lia) ltac:(lia)) as (CH' & FR' & DW' & BK & KO).
  apply rw2_bytes in CWf as (CW1 & CW2 & _). rewrite <- SEGS in CW1, CW2.
  split; [exact CH'|]. split; [exact FR'|]. split; [exact DW'|]. split.
  { apply (done_transfer Lc Ac mc); [exact DN | intros pn H; exact H | exact BK |]. intros t Ht. apply KO; lia. }
  split; [split; [exact CW1 | exact CW2]|].
  intros a s pn _ Ep. destruct a; discriminate.
Qed.

Lemma rcc_head : forall i Rc mc mdc Lc Ac qs, (i < length (r_calls R))%nat -> NEXT i -> RG Rc i -> FRM mc ->
  CHS (rcc_args (firstn i (r_calls R))) (concat qs) Lc Ac mc mdc -> DONE Lc Ac mc i qs -> DSTW mc ->
  SR (ms_segs B) (mkCfg (mkst Rc (Z_to_bv 64 0x15c94) mc (seg_rom (ms_segs B))) mdc) POST.
Proof using PRE GR A0 ARR ROOM SEGS AX CTX GOWN GFACT ERRNO GOTG SLACK XM SLEN MCPY.
  clear AL8.
  intros i Rc mc mdc Lc Ac qs Hi NX GR0 FR CH DN DW.
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
  destruct rep_facts as (H16 & NCB & RF). destruct (RF i c Hc) as (Po & CA & FL).
  pose proof CA as (CF & CL & CP & CB1 & CB2 & CND & CK).
  destruct (ka_hyps ltac:(lia)) as (KO & UC). pose proof KO as (HN0 & HSW0 & HDW0 & HDN0).
  destruct (dst_facts ltac:(lia)) as (_ & D1 & D2).
  pose proof alloc_ceiling_val as AC.
  destruct pre_facts as (_ & HCE & H63 & _).
  unfold RCC_K, XMALLOC_K, ALLOC_STACK, spZ in HCE, H63. unfold spZ in D1.
  destruct (mc_MR _ _ _ _ _ _ CH) as (HMc & _).
  destruct (mc_misc _ _ _ _ _ _ CH) as (HROc & _).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HMc) as (Hh & Hl & _).
  assert (RA : ro_agree rsegs mc) by (rewrite <- SEGS; exact HROc).
  destruct (frm_norm mc FR HROc) as [FLn FSn].
  assert (CF' : 0 <= fst c < 2 ^ 31) by (unfold REC_FN_COUNT in CF; lia).
  assert (RFc : rw_cells rsegs (normalize rsegs mc) (0x33ff0 + 56 * Z.of_nat i + 72)
                  [C4 (Z_to_bv 64 (fst c)); C4 (Z_to_bv 64 (Z.of_nat (length (snd c))))]).
  { apply cells_norm; [exact RA | |].
    - apply (rec_cells _ _ _ _ _ _ _ _ 8 CH); [cbn; tauto | | reflexivity | unfold GLOB_LO; lia
        | unfold GLOB_LO; change (Z.of_nat GLOB_N) with 1020; lia].
      cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
      + replace (0x33ff0 + 56 * Z.of_nat i + 72) with (0x34038 + 56 * Z.of_nat i + CALL_OFF_FN)
          by (unfold CALL_OFF_FN; lia). exact CB1.
      + rewrite length_le4. replace (0x33ff0 + 56 * Z.of_nat i + 72 + Z.of_nat 4)
          with (0x34038 + 56 * Z.of_nat i + CALL_OFF_NARGS) by (unfold CALL_OFF_NARGS; lia). exact CB2.
    - intros t Ht. cbn in Ht. right. apply fg_iff. lia. }
  destruct (dst_cells mc (56 * Z.of_nat i) 8 DW ltac:(lia) ltac:(lia) ltac:(lia)) as [jk SL0].
  apply (rw_cells_split_CB rsegs _ _ [] 8%nat jk [] [4; 4]%nat) in SL0; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in SL0.
  assert (SLn : exists j1 j2, rw_cells rsegs (normalize rsegs mc) (bv_unsigned (getr regs 10) + 56 * Z.of_nat i)
                  [CB 4 j1; CB 4 j2]).
  { do 2 eexists. rewrite UC. apply cells_norm; [exact RA | exact SL0 |]. intros t Ht. cbn in Ht. left. lia. }
  destruct SLn as (j1 & j2 & SLn).
  destruct (Nat.eq_dec (length (snd c)) 0) as [E0|E0].
  - pose proof E0 as E0'. apply length_zero_iff_nil in E0'.
    assert (RF0 : rw_cells rsegs (normalize rsegs mc) (0x33ff0 + 56 * Z.of_nat i + 72)
                    [C4 (Z_to_bv 64 (fst c)); C4 (Z_to_bv 64 0)]) by (rewrite E0 in RFc; exact RFc).
    assert (DONE1 : forall mn mf, HX i [C4 (Z_to_bv 64 (fst c)); C4 (Z_to_bv 64 0)] mc mn -> mem_rel rsegs mf mn ->
              ro_same rsegs mc mf ->
              FRM mf /\ CHS (rcc_args (firstn (S i) (r_calls R))) (concat (qs ++ [[]])) Lc Ac mf mdc /\
              DONE Lc Ac mf (S i) (qs ++ [[]]) /\ DSTW mf).
    { intros mn mf XX MR ROS.
      assert (XX' : HX i [C4 (Z_to_bv 64 (fst c)); C4 (Z_to_bv 64 (Z.of_nat (length (snd c))))] mc mn)
        by (rewrite E0; exact XX).
      destruct (hx_back _ _ Lc Ac mc mdc mn mf i c qs Hc CH FR DW DN XX' MR ROS)
        as (CH' & FR' & DW' & DN' & HD' & AG').
      split; [exact FR'|]. split.
      { rewrite (rcc_args_snoc _ i c Hc), E0', app_nil_r, concat_app. cbn [concat]. rewrite !app_nil_r. exact CH'. }
      split; [|exact DW'].
      apply (done_snoc Lc Ac mf i qs c); [exact DN' | exact Hc | exact HD' | exact AG' | cbn; lia]. }
    destruct (Nat.lt_ge_cases (S i) (length (r_calls R))) as [Hs|Hs].
    + apply (run_ka Rc _ mc mdc (QH (S i) (HX i [C4 (Z_to_bv 64 (fst c)); C4 (Z_to_bv 64 0)] mc)) Hh Hl HROc).
      * rewrite (mkR_of_RG Rc i GR0). eapply k_head_skip with (n := length (r_calls R)) (fn := fst c).
        all: try exact KO. all: try exact FLn. all: try exact RF0. all: try exact SLn. all: try lia.
        intros m' SL' MU WM.
        eapply k_tail_next with (n := length (r_calls R)). all: try exact KO. all: try lia.
        { apply (rw_munch _ (normalize rsegs mc) m' _ _ FLn MU). intros t Ht. unfold FRL in Ht. cbn in Ht.
          split; [lia|]. apply outside_one; lia. }
        unfold st_head. intros. unfold QH. do 2 eexists. split; [reflexivity|].
        split; [eapply rg_mkR; reflexivity|]. exact (conj SL' (conj MU WM)).
      * intros ms' (can & (s0 & (R0 & mn & -> & GR1 & XX) & REL & ROS) & EQ).
        destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL) as [EC MR].
        revert EC MR ROS EQ. generalize (ms_mem can) as mf. intros mf EC MR ROS EQ. subst can.
        destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
        destruct (DONE1 mn mf XX MR ROS) as (FR' & CH' & DN' & DW').
        rewrite <- SEGS. apply NX; [exact Hs|].
        exists R', mf, mdc, Lc, Ac, (qs ++ [[]]). split; [reflexivity|].
        split; [exact (rg_eqv _ _ _ GR1 XR)|]. split; [exact FR'|]. split; [exact CH'|]. split; [exact DN' | exact DW'].
    + apply (run_ka Rc _ mc mdc (QRET (HX i [C4 (Z_to_bv 64 (fst c)); C4 (Z_to_bv 64 0)] mc)) Hh Hl HROc).
      * rewrite (mkR_of_RG Rc i GR0). eapply k_head_skip with (n := length (r_calls R)) (fn := fst c).
        all: try exact KO. all: try exact FLn. all: try exact RF0. all: try exact SLn. all: try lia.
        intros m' SL' MU WM.
        eapply k_tail_last with (n := length (r_calls R)). all: try exact KO. all: try lia.
        { apply (rw_munch _ (normalize rsegs mc) m' _ _ FLn MU). intros t Ht. unfold FRL in Ht. cbn in Ht.
          split; [lia|]. apply outside_one; lia. }
        { apply (rw_munch _ (normalize rsegs mc) m' _ _ FSn MU). intros t Ht. unfold FRS in Ht. cbn in Ht.
          split; [lia|]. apply outside_one; lia. }
        unfold st_ret. intros. unfold QRET. do 2 eexists. split; [reflexivity|].
        split; [eapply pres_mkR; reflexivity|]. exact (conj SL' (conj MU WM)).
      * intros ms' (can & (s0 & (R0 & mn & -> & (HP0 & H10) & XX) & REL & ROS) & EQ).
        destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL) as [EC MR].
        revert EC MR ROS EQ. generalize (ms_mem can) as mf. intros mf EC MR ROS EQ. subst can.
        destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
        destruct (DONE1 mn mf XX MR ROS) as (FR' & CH' & DN' & DW').
        assert (HSi : S i = length (r_calls R)) by lia.
        rewrite <- SEGS. apply (ret_post R' mf mdc Lc Ac (qs ++ [[]])).
        -- exact (pres_eqv _ _ HP0 XR).
        -- rewrite (CF.rec_calls_free.getr_eqv R0 R' _ XR). exact H10.
        -- rewrite <- (firstn_all (r_calls R)), <- HSi. exact CH'.
        -- rewrite <- HSi. exact DN'.
        -- exact DW'.
  - destruct (nth_error (snd c) 0) as [s0|] eqn:Es0; [|apply nth_error_None in Es0; lia].
    destruct (nth_error Po 0) as [opn0|] eqn:Eo0; [|apply nth_error_None in Eo0; lia].
    pose proof (arg_cell _ _ _ _ _ _ i c Po 0 s0 opn0 CH Hc CA Es0 Eo0) as AC0.
    destruct (src_slack _ _ _ _ _ _ i c Po 0 s0 opn0 CH CA Es0 Eo0) as (slack0 & SB0 & SP0 & ON0 & SE0).
    pose proof (bytes_at_bound _ _ _ _ SB0) as BB0. rewrite length_app in BB0. cbn [length] in BB0.
    assert (UPW0 : bv_unsigned (Z_to_bv 64 (fst opn0)) = fst opn0) by (apply unsigned_lit; lia).
    pose proof (bytes_at_normalize rsegs mc _ _ RA SB0) as NSB0.
    apply (run_ka Rc _ mc mdc (QXM i 0 (Z.of_nat (length s0)) (Z_to_bv 64 (fst opn0))
             (HX i [C4 (Z_to_bv 64 (fst c)); C4 (Z_to_bv 64 (Z.of_nat (length (snd c))))] mc)) Hh Hl HROc).
    + rewrite (mkR_of_RG Rc i GR0).
      eapply k_head_call with (n := length (r_calls R)) (fn := fst c) (len := Z.of_nat (length (snd c))).
      all: try exact KO. all: try exact FLn. all: try exact RFc. all: try exact SLn. all: try lia.
      intros m' SL' MU WM. unfold st_lp. intros.
      eapply k_loop with (n := length (r_calls R)) (str := s0) (slack := slack0) (pw := Z_to_bv 64 (fst opn0)).
      all: try exact SLEN. all: try exact KO. all: try exact ON0. all: try lia.
      * apply (rw_munch _ (normalize rsegs mc) m' _ _ AC0 MU). intros t Ht. cbn in Ht. split; [lia|].
        apply outside_one; lia.
      * rewrite UPW0. apply (by_munch _ (normalize rsegs mc) m' _ _ NSB0 MU). intros t Ht. split; [lia|].
        apply outside_one; lia.
      * apply (minv_munch1 _ _ (normalize rsegs mc) m' (mem_inv_normalize rsegs mc) MU); lia.
      * intros m'' MU' WM' MI' BS'. unfold st_xm. intros. unfold QXM. do 2 eexists. split; [reflexivity|].
        split; [eapply rgx_mkR; reflexivity|].
        unfold HX. split; [|split].
        -- apply (rw_munch [] m' m'' _ _ SL' MU'). intros t Ht. split; [|exact I]. cbn in Ht. lia.
        -- eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. intros x _. exact I.
        -- eapply wmono_trans; [exact WM | exact WM'].
    + intros ms' (can & (s1 & (R0 & mn & -> & (G1' & G10' & GX') & XX) & REL & ROS) & EQ).
      destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL) as [EC MR].
      revert EC MR ROS EQ. generalize (ms_mem can) as mf. intros mf EC MR ROS EQ. subst can.
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
      destruct (hx_back _ _ Lc Ac mc mdc mn mf i c qs Hc CH FR DW DN XX MR ROS) as (CH' & FR' & DW' & DN' & HD' & AG').
      rewrite <- SEGS. change (Z_to_bv 64 0x15a88) with (Z_to_bv 64 XMALLOC).
      apply (rcc_inner i c Po Hc CA FL NX (length (snd c) - 1) 0 s0 opn0 R' mf mdc Lc Ac qs []);
        [lia | exact Es0 | exact Eo0 | | | | exact FR' | | exact DN' | exact HD' | exact AG' | reflexivity | exact DW'].
      * rewrite (CF.rec_calls_free.getr_eqv R0 R' _ XR). exact G1'.
      * rewrite (CF.rec_calls_free.getr_eqv R0 R' _ XR). exact G10'.
      * exact (rgx_eqv _ _ _ _ _ _ GX' XR).
      * unfold XS. cbn [firstn]. rewrite !app_nil_r. exact CH'.
Qed.

Lemma rcc_outer : forall k i cfg, (length (r_calls R) - i = S k)%nat -> INV i cfg -> SR (ms_segs B) cfg POST.
Proof using PRE GR A0 ARR ROOM SEGS AX CTX GOWN GFACT ERRNO GOTG SLACK XM SLEN MCPY.
  clear AL8.
  induction k as [|k IH]; intros i cfg Hk (Rc & mc & mdc & Lc & Ac & qs & -> & GR0 & FR & CH & DN & DW);
    (apply (rcc_head i Rc mc mdc Lc Ac qs ltac:(lia)); [ | exact GR0 | exact FR | exact CH | exact DN | exact DW ]).
  - intros Hs. exfalso. lia.
  - intros Hs cfg' Hinv. apply (IH (S i) cfg'); [lia | exact Hinv].
Qed.

Lemma main_sr : SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 REC_CALLS_COPY) mem (seg_rom (ms_segs B))) md) POST.
Proof using PRE RO GR A0 ARR RES ROOM SEGS AX CTX GOWN GFACT ERRNO GOTG SLACK XM SLEN MCPY AL8.
  destruct pre_facts as (HM & HCE & H63 & HAL & HRA & HWA & HTP).
  pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & HWS & _).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  destruct rep_facts as (H16 & NCB & RF).
  pose proof alloc_ceiling_val as AC.
  pose proof (mchain_init (spZ regs) RCC_K (rcc_writes dst (r_calls R)) L A regs mem md b PRE RO RES eq_refl) as CH0.
  assert (RA : ro_agree rsegs mem) by (rewrite <- SEGS; exact RO).
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (HSW : 2 ^ 20 <= bv_unsigned (getr regs 2) - 128) by (unfold spZ, RCC_K, XMALLOC_K, ALLOC_STACK in *; lia).
  assert (NC0 : rw_cells rsegs (normalize rsegs mem) 0x34030 [C4 (Z_to_bv 64 (Z.of_nat (length (r_calls R))))]).
  { apply cells_norm; [exact RA | |].
    - apply glob_cells; [cbn; tauto | | unfold GLOB_LO; lia | cbn; unfold GLOB_LO; change (Z.of_nat GLOB_N) with 1020; lia].
      cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite <- SEGS. exact NCB.
    - intros t Ht. cbn in Ht. right. apply fg_iff. lia. }
  destruct (present_rw_cells rsegs mem (bv_unsigned (getr regs 2) + -128) 128) as [junk FR0]; [lia | lia | |].
  { intros t Ht. apply writable_hi_present; [lia|]. rewrite <- SEGS. apply HWS.
    unfold spZ, RCC_K, XMALLOC_K, ALLOC_STACK in *. lia. }
  assert (FRn : rw_cells rsegs (normalize rsegs mem) (bv_unsigned (getr regs 2) + -128) [CB 128 junk]).
  { apply cells_norm; [exact RA | exact FR0 |]. intros t Ht. cbn in Ht. left. lia. }
  assert (FRAME : forall m', munch [(bv_unsigned (getr regs 2) + -128, bv_unsigned (getr regs 2))] mem m' ->
            wmono rsegs mem m' -> CHS [] [] L A m' md /\ DSTW m').
  { intros m' MU WM. split.
    - apply (mchain_own _ _ _ L A mem md b [] [] L A mem md m' _ CH0 MU); [rewrite SEGS; exact WM | | |].
      + unfold spZ, RCC_K, XMALLOC_K, ALLOC_STACK in *. lia.
      + unfold spZ in *. lia.
      + intros a Ra Hn. apply not_out1 in Hn. left. unfold spZ, RCC_K, XMALLOC_K, ALLOC_STACK in *. lia.
    - intros t Ht. destruct (ARR t Ht) as [H1 H2]. unfold spZ in H1.
      assert (Ow : outside [(bv_unsigned (getr regs 2) + -128, bv_unsigned (getr regs 2))] (dst + t))
        by (apply outside_one; lia).
      exact (proj1 (munch_writable _ _ _ _ (dst + t) MU ltac:(lia) Ow) H2). }
  unfold REC_CALLS_COPY.
  destruct (Nat.eq_dec (length (r_calls R)) 0) as [E0|E0].
  - apply (run_ka regs _ mem md (QRET (fun m' => munch [(bv_unsigned (getr regs 2) + -128, bv_unsigned (getr regs 2))]
             (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m')) Hh Hl RO).
    + rewrite mkR_getr.
      eapply (k_zero_any (getr regs 2) (getr regs 10) (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 8)
                (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) fp_regs fp_csr
                (length (r_calls R))).
      all: try exact HSW. all: try exact E0. all: try exact FRn. all: try exact NC0.
      intros m' FS' MU WM. unfold st_ret. intros. unfold QRET. do 2 eexists. split; [reflexivity|].
      split; [eapply pres_mkR; reflexivity|]. exact (conj MU WM).
    + intros ms' (can & (s0 & (R0 & mn & -> & (HP0 & H10) & (MUn & WMn)) & REL & ROS) & EQ).
      destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL) as [EC MR].
      revert EC MR ROS EQ. generalize (ms_mem can) as mf. intros mf EC MR ROS EQ. subst can.
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
      destruct (norm_back mem mn mf _ RA MR ROS MUn WMn) as (MUr & WMr & _).
      destruct (FRAME mf MUr WMr) as (CH' & DW').
      apply length_zero_iff_nil in E0.
      rewrite <- SEGS. apply (ret_post R' mf md L A []).
      * exact (pres_eqv _ _ HP0 XR).
      * rewrite (CF.rec_calls_free.getr_eqv R0 R' _ XR). exact H10.
      * rewrite E0. exact CH'.
      * split; [rewrite E0; reflexivity|]. intros i c P _ HP. destruct i; discriminate.
      * exact DW'.
  - apply (run_ka regs _ mem md (QH 0 (fun m' => FRM m' /\
             munch [(bv_unsigned (getr regs 2) + -128, bv_unsigned (getr regs 2))] (normalize rsegs mem) m' /\
             wmono rsegs (normalize rsegs mem) m')) Hh Hl RO).
    + destruct (ka_hyps ltac:(lia)) as (KO & UC).
      assert (HA8 : bv_unsigned (getr regs 10) mod 8 = 0) by (rewrite UC; apply AL8; lia).
      rewrite mkR_getr. eapply k_pro with (n := length (r_calls R)).
      all: try exact KO. all: try exact HA8. all: try exact FRn. all: try exact NC0. all: try lia.
      intros m' FL' FS' MU WM. unfold st_head. intros. unfold QH. do 2 eexists. split; [reflexivity|].
      split; [eapply rg_mkR; reflexivity|]. exact (conj (conj FL' FS') (conj MU WM)).
    + intros ms' (can & (s0 & (R0 & mn & -> & GR0 & (FRm & MUn & WMn)) & REL & ROS) & EQ).
      destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL) as [EC MR].
      revert EC MR ROS EQ. generalize (ms_mem can) as mf. intros mf EC MR ROS EQ. subst can.
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
      destruct (norm_back mem mn mf _ RA MR ROS MUn WMn) as (MUr & WMr & _).
      destruct (FRAME mf MUr WMr) as (CH' & DW').
      pose proof (frm_back mn mf MR FRm) as FRf.
      rewrite <- SEGS. apply (rcc_outer (length (r_calls R) - 1) 0); [lia|].
      exists R', mf, md, L, A, []. split; [reflexivity|]. split; [exact (rg_eqv _ _ _ GR0 XR)|].
      split; [exact FRf|]. split; [exact CH'|]. split; [|exact DW'].
      split; [reflexivity|]. intros i c P _ HP. destruct i; discriminate.
Qed.

End Run.

Theorem rec_calls_copy_holds : rec_calls_copy_contract B API.
Proof using SEGS AX CTX GOWN GFACT ERRNO GOTG SLACK XM SLEN MCPY.
  unfold rec_calls_copy_contract.
  intros L A regs mem md R O dst b PRE RO A0 GR ARR AL8 RES ROOM.
  exact (main_sr L A regs mem md R O dst b PRE RO A0 GR ARR RES ROOM AL8).
Qed.

End SR.

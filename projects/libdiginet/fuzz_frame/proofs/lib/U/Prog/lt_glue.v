(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_glue.v, with its module paths changed; 110 of its 387 lines of code are new or changed and 65 lines of the source are left out. *)
(* glue of the UBSan walk of fuzz_frame's LLVMFuzzerTestOneInput between Exec.evt segments and the SR contracts of malloc, free and check_round_trip. *)
(* The twin of lib/Prog/lt_glue.v for fuzz_frame.ubsan, in the form of libreac/fuzz_decode's
   lib/U/Prog/fd_glue.v and fd_seghelp.v (bf7779f81ed7): g_run runs an evt segment under the frame lf_fr,
   g_malloc, g_free and g_crt call malloc, free and check_round_trip through their contracts. g_crt states
   the premises of fuzz_frame's UBSan check_round_trip_contract, whose stack is U_CRT_STACK. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import check_parse_fields_c check_round_trip_c
  CheckStackU LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr.
Import ListNotations.
Open Scope Z_scope.

Lemma lf_rw_cells_frame : forall m m' A cs,
  rw_cells rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) ->
     mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (H0 & H1 & Hb)] (W0 & W1 & Hw)] HE.
  rewrite cells_bytes_length in H1 by exact Hwf.
  split; [split; [exact Hwf|] |].
  - split; [exact H0|]. split; [rewrite cells_bytes_length by exact Hwf; exact H1|].
    intros i Hi. rewrite <- (Hb i Hi). rewrite cells_bytes_length in Hi by exact Hwf.
    change (mrd rsegs m' (wa (A + Z.of_nat i)) = mrd rsegs m (wa (A + Z.of_nat i))).
    exact (proj1 (HE (A + Z.of_nat i) ltac:(lia))).
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    apply (proj1 (proj2 (HE (A + i) ltac:(lia)))). exact (Hw i Hi).
Qed.

Lemma bytes_at_frame : forall m m' A bs,
  bytes_at rsegs m A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> mbyte rsegs m' a = mbyte rsegs m a) ->
  bytes_at rsegs m' A bs.
Proof.
  intros m m' A bs (H0 & H1 & Hb) HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (Hb i Hi).
  change (mrd rsegs m' (wa (A + Z.of_nat i)) = mrd rsegs m (wa (A + Z.of_nat i))).
  exact (HE (A + Z.of_nat i) ltac:(lia)).
Qed.

Lemma blk_bytes_at : forall B m A bs, ms_segs B = rsegs -> 0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  blk_data B m A bs -> bytes_at rsegs m A bs.
Proof.
  intros B m A bs HS H0 H1 HD. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HD (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, HS. reflexivity.
Qed.

Lemma bytes_at_blk : forall B m A bs, ms_segs B = rsegs -> bytes_at rsegs m A bs -> blk_data B m A bs.
Proof.
  intros B m A bs HS (H0 & H1 & Hb) i Hi. rewrite HS.
  pose proof (Hb (Z.to_nat i) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. exact E.
Qed.

Lemma nodup_fst_in : forall {X Y : Type} (l : list (X * Y)) a b c, NoDup (map fst l) -> In (a, b) l -> In (a, c) l -> b = c.
Proof.
  intros X Y l a b c ND. apply NoDup_ListNoDup in ND. revert a b c ND.
  induction l as [|[x y] l IH]; intros a b c ND H1 H2; [destruct H1|].
  cbn [map fst] in ND. apply List.NoDup_cons_iff in ND as [Hn ND].
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - injection E1 as <- <-. injection E2 as <-. reflexivity.
  - injection E1 as <- <-. exfalso. apply Hn. apply in_map_iff. exists (x, c). auto.
  - injection E2 as <- <-. exfalso. apply Hn. apply in_map_iff. exists (x, b). auto.
  - exact (IH a b c ND H1 H2).
Qed.

Lemma app_mid_inv : forall {X : Type} (x : X) b1 b2 c1 c2,
  ~ In x b1 -> ~ In x c1 -> b1 ++ x :: b2 = c1 ++ x :: c2 -> b1 = c1 /\ b2 = c2.
Proof.
  intros X x b1. induction b1 as [|y b1 IH]; intros b2 c1 c2 H1 H2 E; destruct c1 as [|z c1]; cbn in E.
  - injection E as E. auto.
  - injection E as <- _. exfalso. apply H2. left. reflexivity.
  - injection E as -> _. exfalso. apply H1. left. reflexivity.
  - injection E as <- E. destruct (IH b2 c1 c2 ltac:(intros h; apply H1; right; exact h)
      ltac:(intros h; apply H2; right; exact h) E) as [-> ->]. auto.
Qed.

Lemma nonempty_not_twice : forall b1 b2 x n, pairwise ranges_disjoint (b1 ++ (x, n) :: b2) -> 0 < n ->
  ~ In (x, n) (b1 ++ b2).
Proof.
  intros b1 b2 x n HP Hn Hin. destruct (pairwise_app_mid _ b1 (x, n) b2 (x, n) HP Hin) as [H|H];
    unfold ranges_disjoint in H; cbn [fst snd] in H; lia.
Qed.

Lemma stk_sub : forall m lo hi lo' hi', Frame.stk rsegs m lo hi -> lo <= lo' -> hi' <= hi -> 0 <= lo' ->
  Frame.stk rsegs m lo' hi'.
Proof. intros m lo hi lo' hi' (H0 & H1 & H) H2 H3 H4. split; [lia|]. split; [lia|]. intros a Ha. apply H. lia. Qed.

Lemma disj_mid : forall b1 x b2 y, pairwise ranges_disjoint (b1 ++ x :: b2) -> In y (b1 ++ b2) ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
  intros b1 x b2 y HP Hin. destruct (pairwise_app_mid _ b1 x b2 y HP Hin) as [H|H];
    unfold ranges_disjoint in H; lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2, rw_cells segs m A cs1 ->
  rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A cs1 cs2 [[W1 B1] (R1a & R1b & R1)] [[W2 B2] (R2a & R2b & R2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))) as [H|H]; [apply R1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply R2. lia.
Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis HGG : ms_got_guard B = LLVM_GUARD_GOT.
Hypothesis HMAL : ms_malloc B = LLVM_MALLOC.
Hypothesis HFRE : ms_free B = LLVM_FREE.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis CRT : forall fx' : YK11.FPState, @check_round_trip_contract fx' rc B API.

Lemma blk_keep : forall stk Sw L A mem md LX AXX memX mdX x bs,
  lf_fr B API stk Sw L A mem md LX AXX memX mdX -> In (x, Z.of_nat (length bs)) (blocks L A) ->
  blk_data B mem x bs -> blk_data B memX x bs.
Proof.
  intros stk Sw L A mem md LX AXX memX mdX x bs (_ & _ & _ & _ & _ & _ & _ & _ & Hbyt & _) Hin HD i Hi.
  rewrite (Hbyt x _ i Hin Hi). exact (HD i Hi).
Qed.

Lemma norm_stk : forall mem lo hi, ro_agree rsegs mem -> LF_RES_TOP <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at (ms_segs B) mem a) -> Frame.stk rsegs (normalize rsegs mem) lo hi.
Proof.
  intros mem lo hi Hro Hlo Hhi H. apply lf_stk; [exact Hlo | exact Hhi |]. intros a Ha.
  assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
  unfold writable_at. rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem Hro)
    (lf_ro_addr_out B a SEGS Hni ltac:(unfold LF_RES_TOP in Hlo; lia))).
  pose proof (H a Ha) as W. rewrite SEGS in W. exact W.
Qed.

Lemma norm_blk : forall L A mem md x n, aa_MR API L A mem md -> In (x, n) (blocks L A) -> 0 < n ->
  ro_agree rsegs mem -> exists junk, rw_cells rsegs (normalize rsegs mem) x [CB (Z.to_nat n) junk].
Proof.
  intros L A mem md x n HM Hin Hn Hro. pose proof Hin as Hin'. apply blocks_In in Hin' as (q & Hq & Hqin).
  pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q n HM Hqin) as (R1 & R2). rewrite Hq in R1, R2.
  pose proof YM05.alloc_ceiling_value as Hac.
  assert (ST : Frame.stk rsegs (normalize rsegs mem) x (x + n)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (mr_blocks B _ (aa_laws API) L A mem md q n (a - x) HM Hqin ltac:(lia)) as ((v & Hv) & _).
    pose proof (ax_blocks_img AX L A mem md q n (a - x) HM Hqin ltac:(lia)) as Hni.
    rewrite Hq in Hv, Hni. replace (x + (a - x)) with a in Hv, Hni by lia.
    assert (E : normalize rsegs mem (Z_to_bv 64 a) = Some v).
    { rewrite (mem_rel_rw rsegs mem (normalize rsegs mem) (Z_to_bv 64 a) (mem_rel_normalize rsegs mem Hro)
        (lf_ro_addr_out B a SEGS Hni ltac:(lia))). exact Hv. }
    unfold wa. split.
    - unfold wview. rewrite E. discriminate.
    - exists v. unfold mrd. rewrite E. reflexivity. }
  destruct (stk_carve rsegs _ x (x + n) (Z.to_nat n) ST ltac:(rewrite Z2Nat.id by lia; lia)) as [_ [junk HR]].
  rewrite Z2Nat.id in HR by lia. replace (x + n - n) with x in HR by lia. exists junk. exact HR.
Qed.

Lemma g_pre : forall stk S L0 A0 mem0 md0 L A mem md regs K,
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - K -> spZ regs <= S -> 0 <= K ->
  YM05.alloc_ceiling + stk <= S -> spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  call_pre_k B (aa_MR API) K L A regs mem md.
Proof.
  intros stk S L0 A0 mem0 md0 L A mem md regs K
    (HM & HW & HB & HID & _ & _ & _ & _ & _ & Hstw & Herr & _) Hra Hal H1 H2 HK Hc H63 Htp.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact Hra|].
  split; [exact Hal|]. split; [lia|]. split; [exact H63|].
  split; [intros a Ha; apply Hstw; lia|]. split; [exact Htp|]. split; [exact Herr|].
  intros E. rewrite HID in E. discriminate.
Qed.

Lemma g_above : forall stk S L A regs mem md K E L' A' regs' mem' md',
  aa_MR API L A mem md ->
  call_post_k B (aa_MR API) K L A regs mem md E L' A' regs' mem' md' ->
  YM05.alloc_ceiling + stk <= S -> S - stk <= spZ regs - K -> S <= 2 ^ 64 -> 0 <= K ->
  (forall a, E a -> a < YM05.alloc_ceiling) ->
  forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a).
Proof.
  intros stk S L A regs mem md K E L' A' regs' mem' md' HM
    (HM2 & _ & _ & _ & _ & _ & _ & Hfr & _) H1 H2 H3 HK0 HE a Ha.
  pose proof YM05.alloc_ceiling_value as Hac.
  apply Hfr.
  - left. lia.
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM Ho). lia.
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
  - unfold scratch_k. intros [Hs|Hs]; [lia | pose proof (lf_errno_low B ERRNO_LOW a Hs); lia].
  - intros He. pose proof (HE a He). lia.
Qed.

Lemma g_malloc : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A n bres (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - ALLOC_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) -> YK11.getr regs 10 = Z_to_bv 64 n ->
  res_ok_slots A bres -> room_slots bres n ->
  (forall L' A' regs' mem' md' res,
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     YK11.getr regs' 10 = Z_to_bv 64 res -> 4096 <= res -> res + n <= YM05.alloc_ceiling -> res mod 16 = 0 ->
     (forall i, 0 <= i < n -> ~ in_img B (res + i)) ->
     (exists b1 b2, blocks L' A' = b1 ++ (res, n) :: b2 /\ blocks L A = b1 ++ b2) ->
     res_ok_slots A' (sb_malloc bres n) ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun _ => False) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 LLVM_MALLOC) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A n bres P FR Hc HS Hra Hal H1 H2 H63 Htp H10 Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply SR_bind.
  { replace (Z_to_bv 64 LLVM_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite HMAL; reflexivity).
    apply (MALLOC fx' L A regs mem md n bres).
    - apply call_pre_k_alloc. exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs ALLOC_STACK FR Hra Hal H1 H2
        ltac:(unfold ALLOC_STACK; lia) Hc H63 Htp).
    - rewrite SEGS. exact MI.
    - exact H10.
    - exact Hres.
    - exact Hroom. }
  intros c2 (L2 & A2 & regs2 & mem2 & md2 & res & -> & Hpost & G10 & Hres0 & Hal16 & (Hf1 & Hf2 & Hf3)
    & (b1 & b2 & Eb1 & Eb2) & Hkept & Hro2 & Hgk & Hub & Hidt & Hlen & Hres2).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold ALLOC_STACK in *; lia | lia | | | | | | exact Hidt | | ].
    - intros a Ha. exfalso. exact Ha.
    - intros a Ha. right. intros Hf. exact Hf.
    - intros a Hf Ha. exfalso. exact Hf.
    - intros a0 k0 Hin. pose proof (Hblk a0 k0 Hin) as Hin2. rewrite Eb2 in Hin2. rewrite Eb1.
      apply in_app_or in Hin2. apply in_or_app. destruct Hin2 as [Hin2|Hin2]; [left; exact Hin2 | right; right; exact Hin2].
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (fun H => H) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K L2 A2 regs2 mem2 md2 res FR2 Hrp G10 ltac:(lia) ltac:(lia) Hal16 Hf3 (ex_intro _ b1 (ex_intro _ b2 (conj Eb1 Eb2)))
    Hres2).
  - apply (g_above stk S L A regs mem md ALLOC_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM).
    + apply call_post_k_alloc. exact Hpost.
    + exact Hc.
    + exact H1.
    + exact HS.
    + unfold ALLOC_STACK; lia.
    + intros a Ha. destruct Ha.
  - exact Hkept.
Qed.

Lemma g_free : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A x n bres (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - ALLOC_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) -> YK11.getr regs 10 = Z_to_bv 64 x ->
  In (x, n) (blocks L A) -> 0 < n -> (forall a k, In (a, k) (blocks L0 A0) -> a + k <= x \/ x + n <= a) ->
  res_ok_slots A bres ->
  (forall L' A' regs' mem' md',
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     (exists b1 b2, blocks L A = b1 ++ (x, n) :: b2 /\ blocks L' A' = b1 ++ b2) ->
     res_ok_slots A' (sb_free bres n) ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun a => a = x) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 LLVM_FREE) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A x n bres P FR Hc HS Hra Hal H1 H2 H63 Htp H10 Hin Hn Hd Hres K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hin as Hin'. apply blocks_In in Hin' as (q & Hq & Hqin).
  assert (Hfreed : forall a, x <= a < x + n -> a < YM05.alloc_ceiling /\ ~ in_img B a).
  { intros a Ha.
    destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md q n (a - x) HM Hqin ltac:(lia)) as (_ & R1 & R2 & _).
    pose proof (ax_blocks_img AX L A mem md q n (a - x) HM Hqin ltac:(lia)) as Himgx.
    rewrite Hq in R1, R2, Himgx. replace (x + (a - x)) with a in Himgx by lia. split; [lia | exact Himgx]. }
  eapply SR_bind.
  { replace (Z_to_bv 64 LLVM_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite HFRE; reflexivity).
    apply (FREE fx' L A regs mem md q n bres).
    - apply call_pre_k_alloc. exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs ALLOC_STACK FR Hra Hal H1 H2
        ltac:(unfold ALLOC_STACK; lia) Hc H63 Htp).
    - rewrite SEGS. exact MI.
    - exact Hqin.
    - rewrite H10, Hq. reflexivity.
    - exact Hres. }
  intros c2 (L2 & A2 & regs2 & mem2 & md2 & -> & Hpost & (b1 & b2 & Eb1 & Eb2) & Hkept & Hro2 & Hgk & Hub & Hidt
    & Hlen & Hres2).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  rewrite Hq in Eb1, Hkept.
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold ALLOC_STACK in *; lia | lia | | | | | | exact (Hidt HID) | | ].
    - intros a Ha. right. rewrite Hq in Ha. exact (Hfreed a Ha).
    - intros a Ha. right. intros Hf. rewrite Hq in Hf. destruct (Hfreed a Hf). lia.
    - intros a Hf Ha. rewrite Hq in Hf. destruct (Hfreed a Hf). lia.
    - intros a0 k0 Hin0. pose proof (Hblk a0 k0 Hin0) as Hin2. rewrite Eb1 in Hin2. rewrite Eb2.
      apply in_app_or in Hin2. apply in_or_app.
      destruct Hin2 as [Hin2|[Hin2|Hin2]]; [left; exact Hin2 | | right; exact Hin2].
      exfalso. injection Hin2 as E1 E2. subst a0 k0. destruct (Hd _ _ Hin0); lia.
    - intros a0 k0 i Hin0 Hi. apply (Hkept a0 k0 i (Hblk a0 k0 Hin0)); [|exact Hi].
      intros E. subst a0. destruct (Hd _ _ Hin0); lia.
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K L2 A2 regs2 mem2 md2 FR2 Hrp (ex_intro _ b1 (ex_intro _ b2 (conj Eb1 Eb2))) Hres2).
  - apply (g_above stk S L A regs mem md ALLOC_STACK (fun a => ptr_addr L q <= a < ptr_addr L q + n)
      L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS ltac:(unfold ALLOC_STACK; lia)).
    intros a Ha. rewrite Hq in Ha. exact (proj1 (Hfreed a Ha)).
  - exact Hkept.
Qed.

Lemma g_crt : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A (w buf : Z) (b : list byte) bres
    (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - U_CRT_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) -> YK11.getr regs 10 = Z_to_bv 64 w ->
  fr_code b = 0 -> Z.of_nat (length b) < 2 ^ 26 ->
  0 < buf < 2 ^ 64 -> in_block L A buf (Z.of_nat (length b)) -> blk_data B mem buf b ->
  spZ regs <= w -> w mod 8 = 0 -> w + 80 <= 2 ^ 63 -> blk_data B mem w (spec_bytes buf b) ->
  frm_zero (@fp_csr fx') -> res_ok_slots A bres ->
  sb_live bres + 3 <= sb_cap bres <= CAPMAX /\ 0 <= sb_bytes bres /\ sb_bytes bres + 3 * crt_len b <= 2 ^ 40 ->
  (forall (fx'' : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx'') ->
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     blocks L' A' = blocks L A -> res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun _ => False) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A w buf b bres P FR Hc HS Hra Hal H1 H2 H63 Htp
    G10 C0 Hlen Hbuf IB BD Hw Hw8 Hw63 WD Hfrm Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply SR_bind.
  { apply (CRT fx' L A regs mem md w buf b bres SEGS).
    - exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs U_CRT_STACK FR Hra Hal H1 H2
        ltac:(unfold U_CRT_STACK, U_CRT_FRAME, ALLOC_STACK; lia) Hc H63 Htp).
    - exact G10.
    - exact C0.
    - exact Hlen.
    - exact Hbuf.
    - exact IB.
    - exact BD.
    - exact Hw.
    - exact Hw8.
    - exact Hw63.
    - exact WD.
    - rewrite SEGS. exact MI.
    - exact Hfrm.
    - exact Hres.
    - exact Hroom. }
  intros c2 (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hpost & Eb & Hkept & Hgk & Hro2 & Hres2 & Hidt).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold U_CRT_STACK, U_CRT_FRAME, ALLOC_STACK in *; lia | lia | | | | | | exact Hidt | | ].
    - intros a Ha. exfalso. exact Ha.
    - intros a Ha. right. intros Hf. exact Hf.
    - intros a Hf Ha. exfalso. exact Hf.
    - intros a0 k0 Hin. rewrite Eb. exact (Hblk a0 k0 Hin).
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (fun H => H) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp Eb Hres2).
  - apply (g_above stk S L A regs mem md U_CRT_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS
      ltac:(unfold U_CRT_STACK, U_CRT_FRAME, ALLOC_STACK; lia)).
    intros a Ha. destruct Ha.
  - exact Hkept.
Qed.

Lemma g_run : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs pc mem md L A
    (Q : machine_state -> Prop) (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m' W, ms = MState.MS R F pc' fc None m' (seg_rom rsegs) /\
     munch W (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m' /\
     (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x ->
        (S - stk <= x < S) \/ exists y k, lf_mine L0 A0 L A y k /\ y <= x < y + k)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     lf_fr B API stk S L0 A0 mem0 md0 L A m' md ->
     SR rsegs (mkCfg (@YK11.mkst (mkFP F fc) regs' pc' m' (YK11.seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (@YK11.mkst fx' regs pc mem (YK11.seg_rom rsegs)) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs pc mem md L A Q P FR Hc HS HE Hform HK.
  pose proof FR as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  apply (llvm_run_norm fx' regs pc mem md Q P Hh Hl Hro HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & F & pc' & fc & m' & W & -> & _). do 5 eexists. reflexivity.
  - intros R F pc' fc m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R2 & F2 & pc2 & fc2 & m2 & W & HE2 & MU & WM & HW).
    injection HE2 as ER EF EP EC EM. subst R2 F2 pc2 fc2 m2.
    assert (MU' : munch W mem m')
      by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU).
    assert (WM' : wmono rsegs mem m')
      by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' Hro Hsame).
    apply (HK R F pc' fc m0' HQ regs' m' Hx Hrel).
    eapply (lf_fr_evt B API SEGS AX HGG); [exact FR | exact Hc | exact HS | exact MU' | exact WM' | exact Hro' | exact HW].
Qed.

End G.

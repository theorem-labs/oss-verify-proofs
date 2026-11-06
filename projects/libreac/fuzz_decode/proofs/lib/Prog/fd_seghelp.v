From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import check_braid_c check_round_trip_c
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr fd_segments_c fd_glue.
Import ListNotations.
Open Scope Z_scope.

Lemma le4_mod : forall z, le4 (Z_to_bv 64 z) = Z_to_le_bytes 4 (z mod 2 ^ 32).
Proof.
  intros z. unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite !Z_to_le_bytes_mod by lia. reflexivity.
Qed.

Lemma mode_ro_chk : forallb (fun i => Mem.ro_addr rsegs (Z_to_bv 64 (0x103fc + Z.of_nat i))) (seq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mode_ro : forall a, 0x103fc <= a < 0x1041c -> Mem.ro_addr rsegs (Z_to_bv 64 a) = true.
Proof.
  intros a Ha. pose proof (proj1 (forallb_forall _ _) mode_ro_chk (Z.to_nat (a - 0x103fc))) as H.
  cbv beta in H. rewrite Z2Nat.id in H by lia. replace (0x103fc + (a - 0x103fc)) with a in H by lia. apply H.
  apply in_seq. lia.
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

Section H.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).

Lemma blk_keep : forall stk Sw L A mem md LX AXX memX mdX x bs,
  lf_fr B API stk Sw L A mem md LX AXX memX mdX -> In (x, Z.of_nat (length bs)) (blocks L A) ->
  blk_data B mem x bs -> blk_data B memX x bs.
Proof.
  intros stk Sw L A mem md LX AXX memX mdX x bs (_ & _ & _ & _ & _ & _ & _ & _ & Hbyt & _) Hin HD i Hi.
  rewrite (Hbyt x _ i Hin Hi). exact (HD i Hi).
Qed.


Lemma mode_img : forall a, 0x103fc <= a < 0x1041c -> in_img B a.
Proof.
  intros a Ha. pose proof (mode_ro a Ha) as R. unfold Mem.ro_addr in R. rewrite (MState.unsigned_lit a) in R by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [exact (lf_find_img B a seg SEGS E) | discriminate R].
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

Lemma mode_keep : forall S mode nch ns L A mem md LX AXX memX mdX,
  lf_fr B API (LLVM_K - FD_KEEP) (S - FD_KEEP) L A mem md LX AXX memX mdX ->
  fd_mode_ok B S mode nch ns mem -> ro_agree rsegs mem ->
  YM05.alloc_ceiling + LLVM_K <= S -> S <= 2 ^ 64 ->
  bytes_at rsegs (normalize rsegs memX) (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)).
Proof.
  intros S mode nch ns L A mem md LX AXX memX mdX FRX (Hmode & Hnch & Hns & HM4 & HM8) Hro Hc HS.
  pose proof FRX as (_ & _ & _ & _ & _ & Hhigh & _ & _ & _ & _ & _ & _ & HroX).
  pose proof YM05.alloc_ceiling_value as Hac.
  assert (Hm : (0x103f8 <= mode /\ mode + 12 <= 0x1041c) \/ mode = S - FD_KEEP).
  { unfold MODE_44K1, MODE_48K, MODE_96K in Hmode. lia. }
  assert (KEY : forall i, 0 <= i < 8 ->
     mrd rsegs (normalize rsegs memX) (Z_to_bv 64 (mode + 4 + i)) = mbyte (ms_segs B) mem (mode + 4 + i)).
  { intros i Hi. destruct Hm as [Hm | Hm].
    - pose proof (mode_ro (mode + 4 + i) ltac:(lia)) as RO.
      transitivity (seg_rom rsegs (Z_to_bv 64 (mode + 4 + i))).
      + unfold mrd, normalize. rewrite RO. reflexivity.
      + rewrite SEGS. change (mbyte rsegs mem (mode + 4 + i)) with (mrd rsegs mem (Z_to_bv 64 (mode + 4 + i))).
        symmetry. exact (Hro _ RO).
    - subst mode. unfold FD_KEEP in *.
      destruct (Hhigh (S - 116 + 4 + i)
        ltac:(unfold LLVM_K, LLVM_FRAME, CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK in Hc; lia)
        ltac:(unfold LLVM_K, LLVM_FRAME, CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK; lia)) as [E _].
      rewrite <- E. rewrite SEGS.
      rewrite <- (mrd_rel rsegs memX (normalize rsegs memX) (Z_to_bv 64 (S - 116 + 4 + i))
        (mem_rel_normalize rsegs memX HroX)).
      reflexivity. }
  assert (LZ : forall z, length (Z_to_le_bytes 4 z) = 4%nat) by (intros z; reflexivity).
  assert (L8 : length (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) = 8%nat)
    by (rewrite length_app, !length_le4; reflexivity).
  assert (Hb : 0 <= mode + 4 /\ mode + 12 <= 2 ^ 64)
    by (unfold FD_KEEP, LLVM_K, LLVM_FRAME, CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK in *; lia).
  split; [lia|]. split; [rewrite L8; lia|].
  intros i Hi. rewrite L8 in Hi.
  change (mrd rsegs (normalize rsegs memX) (Z_to_bv 64 (mode + 4 + Z.of_nat i)) =
    nth_error (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) i).
  rewrite (KEY (Z.of_nat i) ltac:(lia)).
  destruct (Nat.lt_ge_cases i 4) as [Hi4|Hi4].
  - rewrite nth_error_app1 by (rewrite length_le4; lia). rewrite le4_mod.
    rewrite (HM4 (Z.of_nat i) ltac:(rewrite LZ; lia)), Nat2Z.id. reflexivity.
  - rewrite nth_error_app2 by (rewrite length_le4; lia). rewrite length_le4, le4_mod.
    replace (mode + 4 + Z.of_nat i) with (mode + 8 + Z.of_nat (i - 4)) by lia.
    rewrite (HM8 (Z.of_nat (i - 4)) ltac:(rewrite LZ; lia)), Nat2Z.id. reflexivity.
Qed.

End H.

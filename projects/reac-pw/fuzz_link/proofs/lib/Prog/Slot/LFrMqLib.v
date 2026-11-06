(* The slot LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: the facts the mark_quietly step
   (lib/Prog/Slot/LFrMq.v) shares.
   1. the evt-level view normalize_cj m and the config's memory m: a fact over the view holds of the config's
      memory (MemNorm bytes_at_rel_cj / wr_at_rel_cj), and a fact over low or read-only bytes of the config's
      memory holds of its view (MemNorm mrd_normalize_cj);
   2. the arm's premises (LFrMqDefs.lmq_arm) moved from the arm's cut state (its registers R, the view) to
      the config (its registers, its memory);
   3. closed checks: g_said and the open-file list head are writable in every memory, g_said is image;
   4. what mark_quietly writes (mq_writes), against the image, llvm_G and the heap. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YH02 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memfile_c reac_served_mark_c mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require StdioModel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrCall LFrEn LFrRun LFrMqDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The view and the config's memory
   ========================================================================== *)

Lemma lmq_ro_seg : forall x, Mem.ro_addr rsegs x = true -> find_segment rsegs (bv_unsigned x) 1 <> None.
Proof.
  intros x H. unfold Mem.ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned x) 1); [discriminate | discriminate H].
Qed.

Lemma lmq_mrd : forall m x, ro_agree rsegs m -> (0 <= x < TASK_SIZE \/ Mem.ro_addr rsegs (wa x) = true) ->
  Mem.mrd rsegs (normalize_cj rsegs m) (wa x) = Mem.mrd rsegs m (wa x).
Proof.
  intros m x Hro Hx. apply (mrd_normalize_cj rsegs m (wa x) Hro). right.
  destruct Hx as [Hx|Hx]; [right | left; exact (lmq_ro_seg _ Hx)].
  rewrite wa_unsigned by (unfold TASK_SIZE in *; lia). lia.
Qed.

Lemma lmq_mbyte : forall m x, ro_agree rsegs m -> 0 <= x < TASK_SIZE ->
  mbyte rsegs (normalize_cj rsegs m) x = mbyte rsegs m x.
Proof. intros m x Hro Hx. unfold mbyte. exact (lmq_mrd m x Hro (or_introl Hx)). Qed.

Lemma lmq_bytes_fwd : forall m a bs, ro_agree rsegs m ->
  (forall i, (i < length bs)%nat ->
     0 <= a + Z.of_nat i < TASK_SIZE \/ Mem.ro_addr rsegs (wa (a + Z.of_nat i)) = true) ->
  bytes_at rsegs m a bs -> bytes_at rsegs (normalize_cj rsegs m) a bs.
Proof.
  intros m a bs Hro Hx (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (lmq_mrd m (a + Z.of_nat i) Hro (Hx i Hi)). exact (H i Hi).
Qed.

Lemma lmq_bytes_low : forall m a bs, ro_agree rsegs m -> a + Z.of_nat (length bs) <= TASK_SIZE ->
  bytes_at rsegs m a bs -> bytes_at rsegs (normalize_cj rsegs m) a bs.
Proof. intros m a bs Hro Hl H. exact (bytes_at_normalize_cj_low rsegs m a bs Hro Hl H). Qed.

Lemma lmq_bytes_back : forall m a bs, ro_agree rsegs m ->
  bytes_at rsegs (normalize_cj rsegs m) a bs -> bytes_at rsegs m a bs.
Proof. intros m a bs Hro H. exact (bytes_at_rel_cj rsegs m _ a bs (mem_rel_cj_normalize rsegs m Hro) H). Qed.

Lemma lmq_wr_back : forall m a n, ro_agree rsegs m ->
  wr_at rsegs (normalize_cj rsegs m) a n -> wr_at rsegs m a n.
Proof. intros m a n Hro H. exact (wr_at_rel_cj rsegs m _ a n (mem_rel_cj_normalize rsegs m Hro) H). Qed.

Lemma lmq_wr_fwd : forall m a n, ro_agree rsegs m ->
  (forall i, 0 <= i < n -> 0 <= a + i < TASK_SIZE /\ Mem.ro_addr rsegs (wa (a + i)) = false) ->
  wr_at rsegs m a n -> wr_at rsegs (normalize_cj rsegs m) a n.
Proof.
  intros m a n Hro Hx H. apply (wr_at_norm_cj rsegs m _ a n (mem_rel_cj_normalize rsegs m Hro) H).
  intros i Hi. destruct (Hx i Hi) as [H1 H2]. exact (lc_cj_keep (a + i) H1 H2).
Qed.

(* bytes equal byte by byte *)
Lemma lmq_bytes_eq : forall (m m' : word -> option byte) a bs,
  (forall i, (i < length bs)%nat -> mbyte rsegs m' (a + Z.of_nat i) = mbyte rsegs m (a + Z.of_nat i)) ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs He (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. pose proof (He i Hi) as E. unfold mbyte in E. change (Mem.mrd rsegs m' (wa (a + Z.of_nat i)) =
    Mem.mrd rsegs m (wa (a + Z.of_nat i))) in E. rewrite E. exact (H i Hi).
Qed.

Lemma lmq_u8arr_back : forall m a bs, ro_agree rsegs m ->
  u8arr rsegs (normalize_cj rsegs m) a bs -> u8arr rsegs m a bs.
Proof. intros m a bs Hro [H1 H2]. split; [exact (lmq_bytes_back m a bs Hro H1) | exact (lmq_wr_back m a _ Hro H2)]. Qed.

Lemma lmq_u8arr_fwd : forall m a bs, ro_agree rsegs m ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> 0 <= a + i < TASK_SIZE /\ Mem.ro_addr rsegs (wa (a + i)) = false) ->
  u8arr rsegs m a bs -> u8arr rsegs (normalize_cj rsegs m) a bs.
Proof.
  intros m a bs Hro Hx [H1 H2]. split.
  - apply (lmq_bytes_fwd m a bs Hro); [|exact H1]. intros i Hi. left. apply (Hx (Z.of_nat i)). lia.
  - exact (lmq_wr_fwd m a _ Hro Hx H2).
Qed.

Lemma lmq_cstr_back : forall m a s, ro_agree rsegs m -> cstr_at (normalize_cj rsegs m) a s -> cstr_at m a s.
Proof. intros m a s Hro [H1 H2]. split; [exact (lmq_bytes_back m a _ Hro H1) | exact H2]. Qed.

Lemma lmq_str_arg_back : forall m a o, ro_agree rsegs m -> str_arg (normalize_cj rsegs m) a o -> str_arg m a o.
Proof.
  intros m a [s|] Hro H; cbn [str_arg] in *; [|exact H].
  destruct H as [H1 H2]. split; [exact H1 | exact (lmq_cstr_back m a s Hro H2)].
Qed.

Lemma lmq_policy_back : forall m, ro_agree rsegs m -> policy_ro (normalize_cj rsegs m) -> policy_ro m.
Proof.
  intros m Hro (H1 & H2 & H3 & H4).
  split; [exact (lmq_cstr_back _ _ _ Hro H1)|]. split; [exact (lmq_cstr_back _ _ _ Hro H2)|].
  split; [exact (lmq_cstr_back _ _ _ Hro H3) | exact (lmq_cstr_back _ _ _ Hro H4)].
Qed.

Lemma lmq_guard_back : forall m, ro_agree rsegs m -> guard_words (normalize_cj rsegs m) -> guard_words m.
Proof.
  intros m Hro [H1 (g & H2)]. split; [exact (lmq_bytes_back _ _ _ Hro H1)|].
  exists g. exact (lmq_bytes_back _ _ _ Hro H2).
Qed.

Lemma lmq_nlk_back : forall m kbs, ro_agree rsegs m -> nlk_at (normalize_cj rsegs m) kbs -> nlk_at m kbs.
Proof. intros m kbs Hro [H1 H2]. split; [exact (lmq_u8arr_back _ _ _ Hro H1) | exact H2]. Qed.

Lemma lmq_marks_back : forall m a gbs, ro_agree rsegs m -> marks_at (normalize_cj rsegs m) a gbs -> marks_at m a gbs.
Proof. intros m a gbs Hro [H1 H2]. split; [exact (lmq_u8arr_back _ _ _ Hro H1) | exact H2]. Qed.

Lemma lmq_iftab_back : forall m kbs tab, ro_agree rsegs m ->
  iftab_at (normalize_cj rsegs m) kbs tab -> iftab_at m kbs tab.
Proof.
  intros m kbs tab Hro (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros i nm ix Hi. destruct (H3 i nm ix Hi) as (Hix & p & Hp & Hp0 & Hs & Hx).
  split; [exact Hix|]. exists p. split; [exact (lmq_bytes_back _ _ _ Hro Hp)|]. split; [exact Hp0|].
  split; [exact (lmq_cstr_back _ _ _ Hro Hs) | exact (lmq_bytes_back _ _ _ Hro Hx)].
Qed.

Lemma lmq_u64_fwd : forall m a v, ro_agree rsegs m -> 0 <= a -> a + 8 <= TASK_SIZE ->
  u64_at m a v -> u64_at (normalize_cj rsegs m) a v.
Proof. intros m a v Hro H0 H8 H. apply (lmq_bytes_low m a _ Hro); [rewrite length_le8; lia | exact H]. Qed.

Lemma lmq_u32_fwd : forall m a v, ro_agree rsegs m -> 0 <= a -> a + 4 <= TASK_SIZE ->
  u32_at m a v -> u32_at (normalize_cj rsegs m) a v.
Proof. intros m a v Hro H0 H4 H. apply (lmq_bytes_low m a _ Hro); [rewrite length_le4; lia | exact H]. Qed.

(* an if_name slot of g_nl lies low *)
Lemma lmq_slot_low : forall (tab : list (list byte * Z)) i e, Z.of_nat (length tab) <= 80 -> nth_error tab i = Some e ->
  0 <= A_G_NL + NK_IF_NAME + 8 * Z.of_nat i /\ A_G_NL + NK_IF_NAME + 8 * Z.of_nat i + 8 <= A_G_NL + NK_IF_INDEX /\
  0 <= A_G_NL + NK_IF_INDEX + 4 * Z.of_nat i /\ A_G_NL + NK_IF_INDEX + 4 * Z.of_nat i + 4 <= A_G_NL + NK_SIZE.
Proof.
  intros tab i e Hl Hi. assert (Hlt : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  unfold A_G_NL, NK_IF_NAME, NK_IF_INDEX, NK_SIZE. lia.
Qed.

(* the interface table over the return's memory, its strings where no call moves them *)
Lemma lmq_iftab_fwd : forall m kbs tab, ro_agree rsegs m ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 -> kept_str p (Z.of_nat (length n2) + 1)) ->
  iftab_at m kbs tab -> iftab_at (normalize_cj rsegs m) kbs tab.
Proof.
  intros m kbs tab Hro Hk (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros i nm ix Hi. destruct (H3 i nm ix Hi) as (Hix & p & Hp & Hp0 & Hs & Hx).
  destruct (lmq_slot_low tab i _ H2 Hi) as (L1 & L2 & L3 & L4).
  split; [exact Hix|]. exists p.
  split; [apply (lmq_u64_fwd m _ p Hro L1); [unfold A_G_NL, NK_IF_INDEX, TASK_SIZE in *; lia | exact Hp]|].
  split; [exact Hp0|].
  split.
  - destruct Hs as [Hb Hn]. split; [|exact Hn].
    pose proof Hb as (Hb0 & Hb1 & _). rewrite length_app in Hb1. cbn [length] in Hb1.
    apply (lmq_bytes_fwd m p _ Hro); [|exact Hb].
    intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    destruct (Hk i nm ix p Hi Hp ltac:(lia)) as [(G1 & G2) | G].
    + left. unfold A_G_NAMES, G_NAMES_SIZE, TASK_SIZE in *. lia.
    + right. apply G. lia.
  - apply (lmq_u32_fwd m _ ix Hro L3); [unfold A_G_NL, NK_SIZE, TASK_SIZE in *; lia | exact Hx].
Qed.

Lemma lmq_valmem_fwd : forall m a n v, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat n <= TASK_SIZE ->
  YI04.val_mem rsegs m a n v -> YI04.val_mem rsegs (normalize_cj rsegs m) a n v.
Proof.
  intros m a n v Hro H0 H1 H k Hk. rewrite (lmq_mbyte m (a + Z.of_nat k) Hro ltac:(lia)). exact (H k Hk).
Qed.

Lemma lmq_memfile_at_fwd : forall m f, ro_agree rsegs m -> 0 <= f -> f + MF_BLOCK <= TASK_SIZE ->
  memfile_at YH02.src0_msyms link_mf m f -> memfile_at YH02.src0_msyms link_mf (normalize_cj rsegs m) f.
Proof.
  intros m f Hro H0 H1 H. eapply MemFile.memfile_at_frame; [|exact H].
  intros x Hx. exact (lmq_mbyte m x Hro ltac:(unfold MF_ZEROED, MF_BLOCK in *; lia)).
Qed.

(* ==========================================================================
   2. Closed checks
   ========================================================================== *)

Lemma lmq_said_chk : zall en_chk A_G_SAID (Z.to_nat SAID_SIZE) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lmq_ofl_chk : zall en_chk StdioModel.A_OFL_HEAD 8 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lmq_said_en : forall a, A_G_SAID <= a < A_G_SAID + SAID_SIZE -> en_chk a = true.
Proof.
  intros a Ha. apply (zall_ok en_chk (Z.to_nat SAID_SIZE) A_G_SAID lmq_said_chk).
  rewrite Z2Nat.id by (unfold SAID_SIZE; lia). exact Ha.
Qed.

Lemma lmq_ofl_en : forall a, StdioModel.A_OFL_HEAD <= a < StdioModel.A_OFL_HEAD + 8 -> en_chk a = true.
Proof. intros a Ha. exact (zall_ok en_chk 8 StdioModel.A_OFL_HEAD lmq_ofl_chk a Ha). Qed.

Lemma lmq_said_wr : forall m, wr_at rsegs m A_G_SAID SAID_SIZE.
Proof.
  intros m. apply en_wr; [unfold A_G_SAID; lia | unfold A_G_SAID, SAID_SIZE; lia | exact lmq_said_en].
Qed.

Lemma lmq_ofl_wr : forall m, wr_at rsegs m StdioModel.A_OFL_HEAD 8.
Proof.
  intros m. apply en_wr; [unfold StdioModel.A_OFL_HEAD; lia | unfold StdioModel.A_OFL_HEAD; lia | exact lmq_ofl_en].
Qed.

(* g_said is image *)
Lemma lmq_chk_said : lfr_rng_img 0x74530 0x75530 = true.
Proof. vm_compute. reflexivity. Qed.

(* the FILE over the return's view *)
Lemma lmq_memfile_k_fwd : forall m f k, ro_agree rsegs m -> 4096 <= f -> f + MF_BLOCK <= TASK_SIZE ->
  (forall i, 0 <= i < MF_BLOCK -> Mem.ro_addr rsegs (wa (f + i)) = false) ->
  memfile_k m f k -> memfile_k (normalize_cj rsegs m) f k.
Proof.
  intros m f k Hro Hf0 Hf1 Hrw (H1 & H2 & H3 & H4 & H5).
  split; [exact (lmq_memfile_at_fwd m f Hro ltac:(lia) Hf1 H1)|].
  unfold MF_BLOCK in Hf1.
  split.
  { unfold mf_win, mf_fld in *.
    destruct H2 as [(Hk & A1 & A2 & A3) | (Hk & A1 & A2 & A3)]; [left | right];
      (split; [exact Hk|]);
      (split; [|split]); (apply lmq_valmem_fwd; [exact Hro | lia | lia | assumption]). }
  split.
  { apply (lmq_wr_fwd m f _ Hro); [|exact H3]. intros i Hi. split; [unfold MF_BLOCK in *; lia | exact (Hrw i Hi)]. }
  split; [exact (lmq_said_wr _) | exact H5].
Qed.

(* ==========================================================================
   3. Small facts of words and bytes
   ========================================================================== *)

Lemma lmq_le_byte0 : forall w k, le_byte 0 w k = 0.
Proof.
  intros w k. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma lmq_nth_repeat : forall {X : Type} (x : X) n i, (i < n)%nat -> nth_error (repeat x n) i = Some x.
Proof.
  intros X x n. induction n as [|n IH]; intros i Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn [repeat nth_error]. apply IH. lia.
Qed.

Lemma lmq_le4_0 : le4 (wz 0) = repeat (Z_to_bv 8 0) 4.
Proof. vm_compute. reflexivity. Qed.

Lemma lmq_val0_bytes : forall m a n, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  YI04.val_mem rsegs m a n 0 -> bytes_at rsegs m a (repeat (Z_to_bv 8 0) n).
Proof.
  intros m a n H0 H1 H. split; [exact H0|]. split; [rewrite repeat_length; exact H1|].
  intros i Hi. rewrite repeat_length in Hi. rewrite (lmq_nth_repeat _ n i Hi).
  pose proof (H i Hi) as E. rewrite lmq_le_byte0 in E. exact E.
Qed.

Lemma lmq_byte1 : forall m a b, 0 <= a < 2 ^ 64 -> mbyte rsegs m a = Some b -> bytes_at rsegs m a [b].
Proof.
  intros m a b Ha H. split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. destruct i as [|i]; [|cbn [length] in Hi; lia].
  cbn [nth_error]. replace (a + Z.of_nat 0) with a by lia. exact H.
Qed.

(* u64_at and the allocator's word_mem *)
Lemma lmq_u64_word : forall m a v, 0 <= v < 2 ^ 64 -> u64_at m a v -> word_mem rsegs m a v.
Proof.
  intros m a v Hv H. pose proof (KindBGlue.bytes_at_le8_word rsegs m a (wz v) H) as W.
  unfold wz in W. rewrite (MState.unsigned_lit v Hv) in W. exact W.
Qed.

Lemma lmq_word_u64 : forall m a v, 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 -> word_mem rsegs m a v -> u64_at m a v.
Proof. intros m a v Hv Ha Hb H. exact (KindBGlue.word_mem_le8 rsegs m a v H Hv Ha Hb). Qed.

(* ==========================================================================
   4. The arm's premises at the config
   ========================================================================== *)

(* the registers: every premise reads them through getr only *)
Lemma lmq_arm_regs : forall g hb R R' m sink tab kbs nm, Regs6ss.xregs_eqv R R' ->
  lmq_arm g hb R m sink tab kbs nm -> lmq_arm g hb R' m sink tab kbs nm.
Proof.
  intros g hb R R' m sink tab kbs nm HR.
  assert (G1 : forall r, getr R' r = getr R r) by (intros r; exact (lc_getr R R' r HR)).
  assert (G2 : forall r, YK11.getr R' r = YK11.getr R r) by (intros r; exact (lc_getr R R' r HR)).
  assert (S : spZ R' = spZ R) by (unfold spZ; rewrite G2; reflexivity).
  unfold lmq_arm, mark_errno_ok, mark_table_ok, mark_name_ok, mark_block_ok, apart_frame, errno_at, arg.
  rewrite ?G1, ?G2, ?S. exact (fun h => h).
Qed.

(* the memory: from the view to the config's memory *)
Lemma lmq_arm_back : forall g hb R m sink tab kbs nm, ro_agree rsegs m ->
  lmq_arm g hb R (normalize_cj rsegs m) sink tab kbs nm -> lmq_arm g hb R m sink tab kbs nm.
Proof.
  intros g hb R m sink tab kbs nm Hro
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  assert (HL : Z.of_nat (length tab) <= 80) by (destruct A4 as (_ & H & _); exact H).
  assert (HS : forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
    u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
    u64_at (normalize_cj rsegs m) (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
  { intros i n2 ix p Hi Hp. destruct (lmq_slot_low tab i _ HL Hi) as (L1 & L2 & _).
    apply (lmq_u64_fwd m _ p Hro L1); [unfold A_G_NL, NK_IF_INDEX, TASK_SIZE in *; lia | exact Hp]. }
  split; [exact (lmq_nlk_back m kbs Hro A1)|].
  split; [exact A2|]. split; [exact A3|].
  split; [exact (lmq_iftab_back m kbs tab Hro A4)|].
  split; [exact A5|]. split; [exact A6|].
  split; [exact (lmq_policy_back m Hro A7)|].
  split; [exact (lmq_str_arg_back m _ nm Hro A8)|].
  split; [destruct A9 as [W A9]; split; [exact (lmq_wr_back m _ 4 Hro W) | exact A9]|].
  split; [intros i n2 ix p Hi Hp; exact (A10 i n2 ix p Hi (HS i n2 ix p Hi Hp))|].
  split; [exact A11|]. split; [exact A12|].
  split; [intros i n2 ix p Hi Hp Hb; exact (A13 i n2 ix p Hi (HS i n2 ix p Hi Hp) Hb)|].
  split.
  { intros s Hs. destruct (A14 s Hs) as (B1 & B2 & B3 & B4 & B5 & (sl & B6 & B7) & B8).
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|].
    split; [exists sl; split; [exact (lmq_bytes_back m _ sl Hro B6) | exact B7] | exact B8]. }
  split.
  { intros H0. destruct (A15 H0) as (B1 & B2 & B3 & B4 & B5 & (gbs & B6 & B7)).
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|].
    exists gbs. split; [exact (lmq_marks_back m _ gbs Hro B6) | exact B7]. }
  exact (lmq_guard_back m Hro A16).
Qed.

(* ==========================================================================
   5. What mark_quietly writes
   ========================================================================== *)

(* the image part of mq_writes: g_nl up to the request ring, g_sink, g_say, g_said, the list head *)
Definition lmq_wimg (a : Z) : Prop :=
  (A_G_NL <= a < A_G_NL + NK_N_SENT + 4)
  \/ (A_G_SINK <= a < A_G_SINK + 8) \/ (A_G_SAY <= a < A_G_SAY + 8)
  \/ (A_G_SAID <= a < A_G_SAID + SAID_SIZE)
  \/ (StdioModel.A_OFL_HEAD <= a < StdioModel.A_OFL_HEAD + 8).

Lemma lmq_w_cases : forall a0 s a, mq_writes a0 s a ->
  lmq_wimg a \/ (a0 <> 0 /\ a0 <= a < a0 + MK_SIZE) \/ (s <= a < s + MF_BLOCK).
Proof.
  intros a0 s a H. unfold mq_writes, FILE_BLOCK in H. unfold lmq_wimg, MF_BLOCK.
  destruct H as [H|[H|[H|[H|[H|[H|H]]]]]].
  - left. left. exact H.
  - left. right. left. exact H.
  - left. right. right. left. exact H.
  - left. right. right. right. left. exact H.
  - left. right. right. right. right. exact H.
  - right. left. exact H.
  - right. right. exact H.
Qed.

Lemma lmq_dne : forall x y : Z, x <> y \/ ~ x <> y.
Proof. intros. lia. Qed.

Lemma lmq_w_dec : forall a0 s a, mq_writes a0 s a \/ ~ mq_writes a0 s a.
Proof.
  intros a0 s a. unfold mq_writes.
  repeat first [ apply so_dor | apply so_dand | apply so_dle | apply so_dlt | apply lmq_dne ].
Qed.

Lemma lmq_wimg_glob : forall a, lmq_wimg a -> in_globals llvm_G a.
Proof.
  intros a H. unfold lmq_wimg in H. unfold in_globals, llvm_G, frame_G.
  destruct H as [H|[H|[H|[H|H]]]].
  - exists 0x31b80, 271992. split; [cbn [In]; right; left; reflexivity|].
    unfold A_G_NL, NK_N_SENT in H. lia.
  - exists 0x74528, 8. split; [cbn [In]; do 4 right; left; reflexivity|]. unfold A_G_SINK in H. lia.
  - exists 0x75530, 8. split; [cbn [In]; do 6 right; left; reflexivity|]. unfold A_G_SAY in H. lia.
  - exists 0x74530, 4096. split; [cbn [In]; do 5 right; left; reflexivity|]. unfold A_G_SAID, SAID_SIZE in H. lia.
  - exists 0x95cc8, 8. split; [cbn [In]; do 7 right; left; reflexivity|]. unfold StdioModel.A_OFL_HEAD in H. lia.
Qed.

Lemma lmq_wimg_top : forall a, lmq_wimg a -> 0 <= a < LF_TOP.
Proof.
  intros a H. unfold lmq_wimg, A_G_NL, NK_N_SENT, A_G_SINK, A_G_SAY, A_G_SAID, SAID_SIZE,
    StdioModel.A_OFL_HEAD in H. unfold LF_TOP. lia.
Qed.

Section MQL.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

Lemma lmq_wimg_img : forall a, lmq_wimg a -> in_img B a.
Proof.
  intros a H. unfold lmq_wimg in H. destruct H as [H|[H|[H|[H|H]]]].
  - destruct (lfr_iw_facts B API FF a) as (H1 & _); [|exact H1].
    left. unfold A_G_NL, NK_N_SENT in H. lia.
  - apply (lfr_img_rng B API FF _ _ lfr_chk_h1). unfold A_G_SINK in H. lia.
  - apply (lfr_img_rng B API FF _ _ lfr_chk_h2). unfold A_G_SAY in H. lia.
  - apply (lfr_img_rng B API FF _ _ lmq_chk_said). unfold A_G_SAID, SAID_SIZE in H. lia.
  - apply (lfr_img_rng B API FF _ _ lfr_chk_h3). unfold StdioModel.A_OFL_HEAD in H. lia.
Qed.

(* the FILE block of src0_msyms (memfile_c) is the one of B: the same segments (LFF) *)
Lemma lmq_mfat_src0 : forall mem f, memfile_at B link_mf mem f -> memfile_at YH02.src0_msyms link_mf mem f.
Proof.
  intros mem f H.
  unfold memfile_at, memfile_static, memfile_flags, memfile_omode, memfile_window, memfile_cookie in *.
  rewrite (lff_segs B API FF) in H. exact H.
Qed.

Lemma lmq_mfat_B : forall mem f, memfile_at YH02.src0_msyms link_mf mem f -> memfile_at B link_mf mem f.
Proof.
  intros mem f H.
  unfold memfile_at, memfile_static, memfile_flags, memfile_omode, memfile_window, memfile_cookie in *.
  rewrite (lff_segs B API FF). exact H.
Qed.

Lemma lmq_img_src0 : forall x, ~ in_img B x -> ~ in_img YH02.src0_msyms x.
Proof. intros x H. unfold in_img in *. rewrite (lff_segs B API FF) in H. exact H. Qed.

(* the marks block and the FILE block over the return's view *)
Lemma lmq_blk_ro : forall a, ~ in_img B a -> 0 <= a < 2 ^ 64 -> Mem.ro_addr rsegs (wa a) = false.
Proof. intros a Hn Ha. exact (lfr_ro_addr_out B a (lff_segs B API FF) Hn Ha). Qed.

Lemma lmq_marks_fwd : forall m a gbs, ro_agree rsegs m ->
  (forall i, 0 <= i < MK_SIZE -> 0 <= a + i < TASK_SIZE /\ ~ in_img B (a + i)) ->
  marks_at m a gbs -> marks_at (normalize_cj rsegs m) a gbs.
Proof.
  intros m a gbs Hro Hx [H1 H2]. split; [|exact H2].
  apply (lmq_u8arr_fwd m a gbs Hro); [|exact H1].
  intros i Hi. rewrite H2 in Hi. destruct (Hx i Hi) as [X1 X2]. split; [exact X1|].
  apply lmq_blk_ro; [exact X2 | unfold TASK_SIZE in *; lia].
Qed.

Lemma lmq_nlk_fwd : forall m kbs, ro_agree rsegs m -> nlk_at m kbs -> nlk_at (normalize_cj rsegs m) kbs.
Proof.
  intros m kbs Hro [H1 H2]. split; [|exact H2].
  apply (lmq_u8arr_fwd m A_G_NL kbs Hro); [|exact H1].
  intros i Hi. rewrite H2 in Hi.
  assert (Hb : A_G_NL <= A_G_NL + i < A_G_NL + EN_BSS_LEN)
    by (unfold EN_BSS_LEN, NK_SIZE, G_NAMES_SIZE, LONG_ALIAS_SIZE in *; lia).
  split; [unfold A_G_NL, NK_SIZE, TASK_SIZE in *; lia|].
  exact (proj2 (proj2 (en_chk_ok m (A_G_NL + i) ltac:(unfold A_G_NL, NK_SIZE in *; lia) (en_bss _ Hb)))).
Qed.

End MQL.

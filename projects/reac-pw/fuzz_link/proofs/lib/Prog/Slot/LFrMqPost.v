(* The slot LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: the mark_quietly step's return, from the
   contract's Post (lib/Prog/mark_quietly_c.v) to the frame relation LFR at ra and LFrMqDefs.lmq_post.
   - lmq_file_post: the FILE after the call (the kept one, or the fresh one fmemopen allocated) is in the heap,
     below the allocator's ceiling and outside the image;
   - lmq_ret: LFR with the heap blocks lmq_hb T f hb and the kept set [(f, MF_BLOCK)] (LFrCall.lfr_call_core at
     mark_quietly's footprint mq_writes), and lmq_post over the two views. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrCall LFrEn LFrRun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LFrMqDefs LFrMqLib.
Import ListNotations.
Local Open Scope Z_scope.

Section MQR.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

Lemma lmq_file_post : forall g hb T L A mem md sink sink', LFR B API g hb T L A mem md -> lmq_sink B g hb T sink ->
  (sink <> 0 -> sink' = sink) -> (sink = 0 -> fresh_block B sink' FILE_SIZE) ->
  4096 <= sink' /\ sink' + MF_BLOCK <= YM05.alloc_ceiling /\ (forall i, 0 <= i < MF_BLOCK -> ~ in_img B (sink' + i)).
Proof.
  intros g hb T L A mem md sink sink' HF Hsink HNZ HZ.
  destruct (Z.eq_dec sink 0) as [E0|E0].
  - destruct (HZ E0) as (F1 & F2 & F3). split; [exact F1|]. split; [exact F2 | exact F3].
  - rewrite (HNZ E0). destruct Hsink as [(_ & C) | (-> & _)]; [contradiction|].
    assert (Hin : In (sink, MF_BLOCK) (blocks L A))
      by (apply (lc_T_blk B API g hb _ L A mem md _ HF); left; reflexivity).
    pose proof HF as (_ & HM & _).
    destruct (lc_blk B API FF L A mem md sink MF_BLOCK 0 HM Hin ltac:(unfold MF_BLOCK; lia)) as (_ & B1 & B2 & _).
    split; [exact B1|]. split; [exact B2|].
    intros i Hi. destruct (lc_blk B API FF L A mem md sink MF_BLOCK i HM Hin Hi) as (_ & _ & _ & _ & B5).
    exact B5.
Qed.

Lemma lmq_ret : forall (fx'' : YK11.FPState) g hb T L A regs mem md R sink tab kbs nm L' A' regs' mem' md' sink',
  LFR B API g hb T L A mem md -> spZ regs = lg_S g - SLOT_FRAME -> Regs6ss.xregs_eqv R regs ->
  lmq_sink B g hb T sink -> lmq_arm g hb R (normalize_cj rsegs mem) sink tab kbs nm ->
  YK0o.frm_zero (@YK11.fp_csr fx'') ->
  mq_post_k B API (mq_writes (bv_unsigned (getr regs 10)) sink')
    (fun a => (bv_unsigned (getr regs 10) <> 0
               /\ bv_unsigned (getr regs 10) <= a < bv_unsigned (getr regs 10) + MK_SIZE)
              \/ sink' <= a < sink' + link_mem.FILE_BLOCK)
    L A regs mem md L' A' regs' mem' md' ->
  ro_agree (ms_segs B) mem' ->
  u64_at mem' A_G_SINK sink' -> u64_at mem' A_G_SAY sink' -> u64_at mem' StdioModel.A_OFL_HEAD sink' ->
  sink' <> 0 ->
  (exists k', k' <= MARK_LINE_MAX /\ memfile_k mem' sink' k') ->
  (sink <> 0 -> sink' = sink /\ L' = L /\ A' = A /\ res_ok_slots A' (sb_hb (lg_b g) hb)) ->
  (sink = 0 ->
     fresh_block B sink' FILE_SIZE
     /\ (exists b1 b2, blocks L' A' = b1 ++ (sink', FILE_SIZE) :: b2 /\ blocks L A = b1 ++ b2)
     /\ res_ok_slots A' (sb_malloc (sb_hb (lg_b g) hb) FILE_SIZE)
     /\ (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\ st_init_done A' = true) ->
  (bv_unsigned (getr regs 10) = 0 -> getr regs' 10 = Z_to_bv 64 (- E_INVAL) /\ nlk_at mem' kbs) ->
  (bv_unsigned (getr regs 10) <> 0 -> forall gbs,
     marks_at mem (bv_unsigned (getr regs 10)) gbs ->
     let M := mark_lib tab nm (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) in
     getr regs' 10 = Z_to_bv 64 (m_rc M)
     /\ (exists gbs', marks_at mem' (bv_unsigned (getr regs 10)) gbs'
           /\ marks_wf gbs' /\ mk_names gbs' = m_marks M
           /\ mk_n gbs' = Z.of_nat (length (m_marks M)))
     /\ (exists kbs', nlk_at mem' kbs' /\ nlk_wf kbs'
           /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
           /\ nk_n_if kbs' = nk_n_if kbs /\ iftab_at mem' kbs' tab
           /\ nk_next kbs' = Z.of_nat (k_next (m_state M))
           /\ nk_sent kbs' = m_reqs M
           /\ nk_n_sent kbs' = Z.of_nat (length (m_reqs M))
           /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
           /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
           /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 2)) ->
  LFR B API g (lmq_hb T sink' hb) [(sink', MF_BLOCK)] L' A' mem' md' /\
  lmq_post B g hb T R (normalize_cj rsegs mem) sink tab kbs nm regs' (@YK11.fp_csr fx'')
    (normalize_cj rsegs mem') sink'.
Proof.
  intros fx'' g hb T L A regs mem md R sink tab kbs nm L' A' regs' mem' md' sink'
    HF Hsp HR Hsink Harm Hfz HPK HRO' HS1 HS2 HS3 Hs0 HMF HNZ HZ HA0 HA1.
  pose proof FF as (SEG & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP
    & EOFF & REP & VML & DBL & OFH & OFL & THR & CTXRO & ALLOC).
  assert (G10 : getr regs 10 = getr R 10) by exact (lc_getr R regs 10 HR).
  rewrite G10 in HPK, HA0, HA1.
  pose proof HF as (HGV & HM & HW & HBD & HID & _ & _ & _ & _ & _ & _ & _ & HRO & HRS & HP & HKT & HGI).
  destruct (lc_gv B API g HGV) as (HS & HS16 & HS47 & HM0 & Htb).
  pose proof (@lc_ceil rc) as [HC1 HC2]. unfold LF_TOP in HC1.
  pose proof HPK as (HM' & HW' & HBD' & HLE & HPA & RP & HMD & HFR & HUB & HSC).
  assert (HC : lcall_post B API MARK_QUIETLY_K L A regs mem md (mq_writes (bv_unsigned (getr R 10)) sink')
    L' A' mem' md').
  { split; [exact HM'|]. split; [exact HW'|]. split; [exact HBD'|]. split; [exact HMD|].
    split; [exact HFR | exact HSC]. }
  assert (HK0 : 0 <= MARK_QUIETLY_K <= SLOT_STACK - SLOT_FRAME) by (unfold MARK_QUIETLY_K, SLOT_STACK, SLOT_FRAME; lia).
  pose proof (lc_frame B API FF g hb T L A mem md regs MARK_QUIETLY_K _ L' A' mem' md' HF Hsp HK0 HC) as KEEP.
  destruct (lmq_file_post g hb T L A mem md sink sink' HF Hsink (fun H => proj1 (HNZ H)) (fun H => proj1 (HZ H)))
    as (F1 & F2 & F3).
  pose proof Harm as (_ & _ & _ & HIF & _ & _ & _ & _ & _ & _ & HMK & _ & HTK & _).
  assert (HROm : ro_agree rsegs mem) by (rewrite SEG in HRO; exact HRO).
  assert (HROm' : ro_agree rsegs mem') by (rewrite SEG in HRO'; exact HRO').
  (* the marks block lies in one of the slot's blocks *)
  assert (HMB : forall x, bv_unsigned (getr R 10) <> 0 ->
     bv_unsigned (getr R 10) <= x < bv_unsigned (getr R 10) + MK_SIZE ->
     exists q n, In (q, n) hb /\ 4096 <= q /\ q <= x < q + n /\ q + n <= YM05.alloc_ceiling /\ ~ in_img B x).
  { intros x H0 Hx. destruct (HMK H0) as (q & n & Hq & Q1 & Q2).
    assert (Hq' : In (q, n) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hq).
    destruct (lc_blk B API FF L A mem md q n (x - q) HM Hq' ltac:(lia)) as (_ & B1 & B2 & _ & B5).
    replace (q + (x - q)) with x in B5 by lia.
    exists q, n. split; [exact Hq|]. split; [exact B1|]. split; [lia|]. split; [exact B2 | exact B5]. }
  (* what the call writes *)
  assert (HE : forall x, mq_writes (bv_unsigned (getr R 10)) sink' x ->
     lmq_wimg x \/
     (exists q n, In (q, n) hb /\ 4096 <= q /\ q <= x < q + n /\ q + n <= YM05.alloc_ceiling /\ ~ in_img B x) \/
     (sink' <= x < sink' + MF_BLOCK)).
  { intros x Hx. destruct (lmq_w_cases _ _ x Hx) as [H|[(H0 & H)|H]];
      [left; exact H | right; left; exact (HMB x H0 H) | right; right; exact H]. }
  assert (HElow : forall x, mq_writes (bv_unsigned (getr R 10)) sink' x -> x < YM05.alloc_ceiling).
  { intros x Hx. destruct (HE x Hx) as [H|[(q & n & _ & _ & H1 & H2 & _)|H]].
    - pose proof (lmq_wimg_top x H) as Ht. unfold LF_TOP in Ht. lia.
    - lia.
    - unfold MF_BLOCK in *. lia. }
  assert (HEhi : forall a, mq_writes (bv_unsigned (getr R 10)) sink' a -> YM05.alloc_ceiling <= a ->
     lg_S g - SLOT_STACK <= a < lg_S g).
  { intros a Ha Hc. pose proof (HElow a Ha). lia. }
  assert (HEimg : forall a, mq_writes (bv_unsigned (getr R 10)) sink' a -> lf_img B a -> in_globals llvm_G a).
  { intros a Ha Hi. destruct (HE a Ha) as [H|[(q & n & _ & _ & _ & _ & H)|H]].
    - exact (lmq_wimg_glob a H).
    - exfalso. exact (H (proj1 Hi)).
    - exfalso. apply (F3 (a - sink') ltac:(lia)). replace (sink' + (a - sink')) with a by lia. exact (proj1 Hi). }
  assert (HEd : forall a, lg_S g - SLOT_STACK <= a < lg_S g ->
     mq_writes (bv_unsigned (getr R 10)) sink' a \/ ~ mq_writes (bv_unsigned (getr R 10)) sink' a)
    by (intros a _; apply lmq_w_dec).
  assert (HEw : forall a, mq_writes (bv_unsigned (getr R 10)) sink' a -> lg_S g - SLOT_STACK <= a < lg_S g ->
     writable_at (ms_segs B) mem' a).
  { intros a Ha Hw. exfalso. pose proof (HElow a Ha). unfold SLOT_STACK in *. lia. }
  (* the live blocks' bytes outside the footprint *)
  assert (HINC : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')).
  { intros q k Hq. destruct (Z.eq_dec sink 0) as [E0|E0].
    - destruct (HZ E0) as (_ & _ & _ & H & _). exact (H q k Hq).
    - destruct (HNZ E0) as (_ & _ & -> & _). exact Hq. }
  assert (HBK : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k ->
     ~ mq_writes (bv_unsigned (getr R 10)) sink' (a + i) ->
     mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i)).
  { intros a k i Hin Hi HnE. apply blocks_In in Hin as (p & <- & Hp).
    apply (HUB p k i Hp (HINC p k Hp) Hi).
    intros Hx. apply HnE. cbv beta in Hx. unfold mq_writes.
    destruct Hx as [(H0 & Hx) | Hx]; [do 5 right; left; split; [exact H0 | exact Hx] | do 6 right; exact Hx]. }
  (* the entry blocks the call may not write *)
  assert (HE0 : forall a k i, In (a, k) (blocks (lg_L g) (lg_A g)) -> ~ In (a, k) (lg_T g) -> 0 <= i < k ->
     ~ mq_writes (bv_unsigned (getr R 10)) sink' (a + i)).
  { intros a k i Hin HnT Hi Hw.
    assert (Hin' : In (a, k) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
    destruct (lc_blk B API FF L A mem md a k i HM Hin' Hi) as (_ & _ & _ & _ & Hni).
    destruct (HE (a + i) Hw) as [H|[(q & n & Hq & _ & Hx & _)|H]].
    - exact (Hni (lmq_wimg_img B API FF _ H)).
    - pose proof (lc_hb_b0 B API L A mem md hb _ (q, n) (a, k) HM HP Hq Hin) as D.
      unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
    - destruct (Z.eq_dec sink 0) as [E0|E0].
      + destruct (HZ E0) as (Hfr & (b1 & b2 & Eb' & Eb) & _).
        pose proof (lfr_fresh B API g hb L A L' A' mem' md' b1 b2 sink' FILE_SIZE HGV HP HM' Eb' Eb Hs0 Hfr)
          as (_ & _ & _ & _ & _ & D).
        destruct (D a k Hin); unfold FILE_SIZE, MF_BLOCK in *; lia.
      + destruct (HNZ E0) as (-> & _).
        destruct Hsink as [(_ & C) | (HT & _ & _ & _ & _ & _ & K6 & K7)]; [contradiction|].
        destruct (Z.eq_dec a sink) as [Ea|Ea]; [destruct (Z.eq_dec k MF_BLOCK) as [Ek|Ek]|].
        * subst a k. apply HnT. rewrite (K7 Hin). left. reflexivity.
        * destruct (K6 a k Hin ltac:(intros Eq; injection Eq as _ E2; exact (Ek E2))); unfold MF_BLOCK in *; lia.
        * destruct (K6 a k Hin ltac:(intros Eq; injection Eq as E1 _; exact (Ea E1))); unfold MF_BLOCK in *; lia. }
  assert (HID' : st_init_done A' = true).
  { destruct (Z.eq_dec sink 0) as [E0|E0].
    - exact (proj2 (proj2 (proj2 (proj2 (HZ E0))))).
    - destruct (HNZ E0) as (_ & _ & -> & _). exact HID. }
  (* the accounting at the return *)
  assert (HRS2 : res_ok_slots A' (sb_hb (lg_b g) (lmq_hb T sink' hb))).
  { destruct Hsink as [(-> & ->) | (-> & K1 & _)].
    - cbn [lmq_hb]. rewrite sb_hb_cons. destruct (HZ eq_refl) as (_ & _ & H & _). exact H.
    - cbn [lmq_hb]. destruct (HNZ ltac:(lia)) as (_ & _ & _ & H). exact H. }
  assert (HP2 : Permutation (blocks L' A') (lmq_hb T sink' hb ++ blocks (lg_L g) (lg_A g))).
  { destruct Hsink as [(-> & ->) | (-> & K1 & _)].
    - destruct (HZ eq_refl) as (_ & (b1 & b2 & Eb' & Eb) & _).
      rewrite Eb'. cbn [lmq_hb app].
      apply Permutation_trans with ((sink', FILE_SIZE) :: b1 ++ b2); [apply Permutation_sym, Permutation_middle|].
      apply perm_skip. rewrite <- Eb. exact HP.
    - cbn [lmq_hb]. destruct (HNZ ltac:(lia)) as (_ & -> & -> & _). exact HP. }
  assert (HKT2 : lkept g (lmq_hb T sink' hb) [(sink', MF_BLOCK)]).
  { destruct Hsink as [(-> & ->) | (-> & K1 & _)].
    - cbn [lmq_hb]. destruct HKT as [(H0 & H1) | (H0 & _)].
      + exfalso. exact (H0 (eq_sym H1)).
      + right. split; [exact H0|]. right. exists sink'. split; [reflexivity | left; reflexivity].
    - cbn [lmq_hb]. destruct (HNZ ltac:(lia)) as (-> & _). exact HKT. }
  assert (Hs64 : 0 <= sink' < 2 ^ 64) by (unfold MF_BLOCK in *; lia).
  assert (HGI2 : mf_gi B link_mf [(sink', MF_BLOCK)] mem').
  { right. exists sink'. split; [|split; [reflexivity|]].
    - split; [|split]; rewrite SEG.
      + exact (lmq_u64_word mem' A_G_SINK sink' Hs64 HS1).
      + exact (lmq_u64_word mem' A_G_SAY sink' Hs64 HS2).
      + rewrite OFH. exact (lmq_u64_word mem' StdioModel.A_OFL_HEAD sink' Hs64 HS3).
    - destruct HMF as (k' & _ & Hmk). exact (lmq_mfat_B B API FF mem' sink' (proj1 Hmk)). }
  destruct (lfr_call_core B API FF g hb T L A mem md regs MARK_QUIETLY_K (mq_writes (bv_unsigned (getr R 10)) sink')
    L' A' mem' md' (lmq_hb T sink' hb) [(sink', MF_BLOCK)] HF Hsp HK0 HC HEhi HEimg HEd HEw HBK HE0 HID' HRO'
    HRS2 HP2 HKT2 HGI2) as (HLF & HLC & HPM).
  split; [exact HLF|].
  (* the interface-table slots of g_nl are outside the footprint: the call leaves them *)
  assert (HSLOT : forall x, A_G_NL + NK_IF_NAME <= x < A_G_NL + NK_IF_INDEX ->
     mbyte rsegs mem x = mbyte rsegs mem' x).
  { intros x Hx0.
    assert (Hx : lfr_iw x) by (left; unfold A_G_NL, NK_IF_NAME, NK_IF_INDEX in *; lia).
    destruct (lfr_iw_facts B API FF x Hx) as (I1 & I2 & I3 & _).
    assert (Hlf : lf_img B x).
    { split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
      rewrite (lff_errno B API FF). unfold A_ERRNO, A_TP, ERRNO_TP_OFF, A_G_NL, NK_IF_INDEX in *. lia. }
    assert (HnE : ~ mq_writes (bv_unsigned (getr R 10)) sink' x).
    { intros Hw. destruct (HE x Hw) as [H|[(q & n & _ & _ & _ & _ & H)|H]].
      - unfold lmq_wimg, A_G_NL, NK_N_SENT, A_G_SINK, A_G_SAY, A_G_SAID, SAID_SIZE, StdioModel.A_OFL_HEAD,
          NK_IF_NAME, NK_IF_INDEX in H, Hx0. lia.
      - exact (H I1).
      - apply (F3 (x - sink') ltac:(unfold MF_BLOCK in *; lia)). replace (sink' + (x - sink')) with x by lia.
        exact I1. }
    rewrite <- SEG. symmetry. exact (proj1 (KEEP x (or_intror Hlf) HnE)). }
  assert (HKS : forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
      u64_at mem' (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
      kept_str p (Z.of_nat (length n2) + 1)).
  { intros i n2 ix p Hi Hp Hb. apply (HTK i n2 ix p Hi); [|exact Hb].
    assert (HL : Z.of_nat (length tab) <= 80) by (destruct HIF as (_ & H & _); exact H).
    destruct (lmq_slot_low tab i _ HL Hi) as (L1 & L2 & _).
    apply (lmq_u64_fwd mem _ p HROm L1); [unfold A_G_NL, NK_IF_INDEX, TASK_SIZE in *; lia|].
    apply (lmq_bytes_eq mem' mem); [|exact Hp].
    intros j Hj. rewrite length_le8 in Hj. apply HSLOT. lia. }
  assert (HFlow : sink' + MF_BLOCK <= TASK_SIZE) by (unfold TASK_SIZE in *; lia).
  split; [exact (lc_rp R regs regs' HR RP)|].
  split; [exact Hfz|].
  split; [exact HLC|].
  split; [exact HPM|].
  split; [apply (lmq_u64_fwd mem' _ _ HROm'); [unfold A_G_SINK; lia | unfold A_G_SINK, TASK_SIZE; lia | exact HS1]|].
  split; [apply (lmq_u64_fwd mem' _ _ HROm'); [unfold A_G_SAY; lia | unfold A_G_SAY, TASK_SIZE; lia | exact HS2]|].
  split; [apply (lmq_u64_fwd mem' _ _ HROm');
    [unfold StdioModel.A_OFL_HEAD; lia | unfold StdioModel.A_OFL_HEAD, TASK_SIZE; lia | exact HS3]|].
  split; [exact Hs0|].
  split.
  { destruct HMF as (k' & Hk' & Hmk). exists k'. split; [exact Hk'|].
    apply (lmq_memfile_k_fwd mem' sink' k' HROm' F1 HFlow); [|exact Hmk].
    intros i Hi. apply (lmq_blk_ro B API FF); [exact (F3 i Hi) | unfold MF_BLOCK in *; lia]. }
  split; [intros H; exact (proj1 (HNZ H))|].
  split.
  { intros E0. destruct (HZ E0) as (Hfr & (b1 & b2 & Eb' & Eb) & _).
    exact (lfr_fresh B API g hb L A L' A' mem' md' b1 b2 sink' FILE_SIZE HGV HP HM' Eb' Eb Hs0 Hfr). }
  split.
  { intros H0. destruct (HA0 H0) as [Hrc Hn]. split; [exact Hrc|].
    eapply lmq_nlk_fwd; [exact HROm' | exact Hn]. }
  intros H0 gbs Hg.
  pose proof (HA1 H0 gbs (lmq_marks_back mem _ gbs HROm Hg)) as H1.
  cbv zeta in H1 |- *.
  destruct H1 as (Hrc & (gbs' & M1 & M2 & M3 & M4) &
    (kbs' & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13)).
  split; [exact Hrc|].
  split.
  - exists gbs'. split; [|split; [exact M2 | split; [exact M3 | exact M4]]].
    apply (lmq_marks_fwd B API FF mem' _ gbs' HROm'); [|exact M1].
    intros i Hi.
    assert (Hx : bv_unsigned (getr R 10) <= bv_unsigned (getr R 10) + i < bv_unsigned (getr R 10) + MK_SIZE)
      by (clear - Hi; generalize (bv_unsigned (getr R 10)); intros z; lia).
    destruct (HMB _ H0 Hx) as (q & n & _ & Q0 & Q1 & Q2 & Q3).
    split; [clear - Q0 Q1 Q2 HC2; unfold TASK_SIZE; lia | exact Q3].
  - exists kbs'. split; [eapply lmq_nlk_fwd; [exact HROm' | exact N1]|].
    split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|].
    split; [exact (lmq_iftab_fwd mem' kbs' tab HROm' HKS N6)|].
    split; [exact N7|]. split; [exact N8|]. split; [exact N9|]. split; [exact N10|]. split; [exact N11|].
    split; [exact N12 | exact N13].
Qed.

End MQR.

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09 YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YL01 YL00 YL0g YI06 YI16 YI14 YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack AllocPack AllocPackRoom AllocPack3 AllocPack3Room SlotPack3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement StatementKept SlotInv SlotSteps SlotRes SlotRI3 RelayRunT RelayRunF HarnessTr KindB HarnessGlue RelayFrame RelayRep HarnessRep ListRep CheckRep source_reset_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayModel RelayKeys relay_add_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessFrame SlotMove.
Import ListNotations.
Local Open Scope Z_scope.

Lemma entry_save_run : forall
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) lo,
  stk rsegs m lo (bv_unsigned sp) -> lo + 192 <= bv_unsigned sp -> 0x100000 <= lo -> mem_inv rsegs m ->
  evt rsegs
    (fun ms => exists m' junk,
      ms = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 192)) gp tp t0 t1 t2 s0 a1 a0
        (Z_to_bv 64 (Z.shiftr (bv_unsigned a1) 26)) a2 a3 a4 a5 a6 a7
        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x140dc) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 192, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned sp - 192)
        [CB 88 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
      stk rsegs m' lo (bv_unsigned sp - 192))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO HI MI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 192%nat ST.
  unfold ENTRY. do 16 step.
  apply evt_done. do 2 eexists.
  split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. replace (bv_unsigned sp - 192) with (bv_unsigned sp + -192) by lia. exact ST.
Qed.

Lemma entry_return_run : forall
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) b
    (rra rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 : word),
  sp = Z_to_bv 64 b -> 0 <= b -> b + 192 < 2 ^ 64 ->
  rw_cells rsegs m (b + 88)
    [C8 rs11; C8 rs10; C8 rs9; C8 rs8; C8 rs7; C8 rs6; C8 rs5; C8 rs4; C8 rs3; C8 rs2; C8 rs1; C8 rs0; C8 rra] ->
  evt rsegs
    (fun ms => ms = MS (mkR rra (Z_to_bv 64 (b + 192)) gp tp t0 t1 t2 rs0 rs1 (Z_to_bv 64 0)
      a1 a2 a3 a4 a5 a6 a7 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 t3 t4 t5 t6)
      F (ret_pc rra) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14760) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b rra rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 -> HB HEND SAVED.
  do 16 step. apply evt_done. reflexivity.
Qed.

Definition entry_head_registers (b p n : Z) (gp tp : word) (R : bvmap 5 word) : Prop :=
  reg_get R 2 = Z_to_bv 64 b /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
  reg_get R 20 = Z_to_bv 64 G_RELAY_LO /\
  (0 < n ->
    reg_get R 9 = Z_to_bv 64 n /\ reg_get R 18 = Z_to_bv 64 p /\
    reg_get R 22 = Z_to_bv 64 0 /\ reg_get R 24 = Z_to_bv 64 1 /\
    reg_get R 23 = Z_to_bv 64 (b + 32) /\ reg_get R 25 = Z_to_bv 64 DIV10 /\
    reg_get R 21 = Z_to_bv 64 10 /\ reg_get R 19 = Z_to_bv 64 4 /\
    reg_get R 27 = Z_to_bv 64 (G_S + 4)).

Lemma entry_head_run : forall
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) b p n junk,
  sp = Z_to_bv 64 b -> s1 = Z_to_bv 64 n -> s2 = Z_to_bv 64 p -> s4 = Z_to_bv 64 G_RELAY_LO ->
  0 <= b -> b + 192 < 2 ^ 64 -> 0 <= n < INPUT_MAX ->
  mem_inv rsegs m -> rw_cells rsegs m (b + 8) [CB 8 junk] ->
  evt rsegs
    (fun ms => exists R m',
      ms = MS R F (Z_to_bv 64 (if 0 <? n then LOOP_BODY else LOOP_EXIT)) fc None m' (seg_rom rsegs) /\
      munch [(b + 8, b + 16)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      entry_head_registers b p n gp tp R /\
      (0 < n -> rw_cells rsegs m' (b + 8) [C8 (Z_to_bv 64 G_S)]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14118) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b p n junk -> -> -> -> HB HEND HN MI SLOT.
  unfold INPUT_MAX in HN.
  pose proof (munch_refl [(b + 8, b + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. if_cases HZ.
  - assert (EN : n = 0).
    { unfold bv_eqb in HZ. rewrite !unsigned_lit in HZ by lia. apply Z.eqb_eq in HZ. lia. }
    subst n. apply evt_done. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [unfold entry_head_registers; do 4 (split; [reflexivity|]); intros Hpos; lia|]. intros Hpos; lia.
  - assert (HN0 : 0 < n).
    { unfold bv_eqb in HZ. rewrite !unsigned_lit in HZ by lia. apply Z.eqb_neq in HZ. lia. }
    assert (NT : (0 <? n) = true) by (apply Z.ltb_lt; exact HN0).
    do 10 step.
    apply evt_done. do 2 eexists. rewrite NT.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [unfold entry_head_registers; do 4 (split; [reflexivity|]); intros _; repeat split; reflexivity|].
    intros _. exact SLOT.
Qed.

Definition entry_writes (b : Z) : list (Z * Z) :=
  [(b, b + 8); (0x21624, 0x21628); (0x318c0, 0x318c4); (0x318d8, 0x318e0);
   (0x318a4, 0x318a5); (0x318a8, 0x318a9); (0x318ac, 0x318ad); (0x318b0, 0x318b1)].

Lemma entry_init_run : forall
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) b
    (j0 jc jn jm jb jg jd je : list byte),
  sp = Z_to_bv 64 b -> 0x100000 <= b -> b + 192 < 2 ^ 64 -> mem_inv rsegs m ->
  rw_cells rsegs m b [CB 8 j0] -> rw_cells rsegs m 0x21624 [CB 4 jc] ->
  rw_cells rsegs m 0x318c0 [CB 4 jn] -> rw_cells rsegs m 0x318d8 [CB 8 jm] ->
  rw_cells rsegs m 0x318a4 [CB 1 jb] -> rw_cells rsegs m 0x318a8 [CB 1 jg] ->
  rw_cells rsegs m 0x318ac [CB 1 jd] -> rw_cells rsegs m 0x318b0 [CB 1 je] ->
  evt rsegs
    (fun ms => exists m',
      ms = MS (mkR (Z_to_bv 64 0x14118) (Z_to_bv 64 b) gp tp t0 t1 t2 s0 s1
        (Z_to_bv 64 0x310f4) (Z_to_bv 64 CLIENT_BASE) a2 a3 a4 a5 a6 a7
        a0 s3 (Z_to_bv 64 G_RELAY_LO) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OP_ADD) fc None m' (seg_rom rsegs) /\
      munch (entry_writes b) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' b [C8 (Z_to_bv 64 CLIENT_BASE)] /\
      rw_cells rsegs m' 0x21624 [C4 (Z_to_bv 64 3)] /\
      rw_cells rsegs m' 0x318c0 [C4 (Z_to_bv 64 0)] /\
      rw_cells rsegs m' 0x318d8 [C8 (Z_to_bv 64 0)] /\
      rw_cells rsegs m' 0x318a4 [C1 (Z_to_bv 8 0)] /\
      rw_cells rsegs m' 0x318a8 [C1 (Z_to_bv 8 0)] /\
      rw_cells rsegs m' 0x318ac [C1 (Z_to_bv 8 0)] /\
      rw_cells rsegs m' 0x318b0 [C1 (Z_to_bv 8 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x140e0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b j0 jc jn jm jb jg jd je -> HB HEND MI W0 WC WN WMX WB WG WD WE.
  pose proof (munch_refl (entry_writes b) m) as MU. unfold entry_writes in MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 9 step.
  do 4 (step; change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]; mem_after_store).
  step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma entry_shift_large : forall n, INPUT_MAX <= n < 2 ^ 64 ->
  0 < Z.shiftr n 26 < 2 ^ 64.
Proof.
  intros n H. rewrite Z.shiftr_div_pow2 by lia. unfold INPUT_MAX in H.
  change (2 ^ 26) with 67108864 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma entry_large_run : forall
    ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) lo n,
  stk rsegs m lo (bv_unsigned sp) -> lo + 192 <= bv_unsigned sp -> 0x100000 <= lo -> mem_inv rsegs m ->
  INPUT_MAX <= n < 2 ^ 64 ->
  evt rsegs
    (fun ms => exists m',
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0)
        (Z_to_bv 64 (Z.shiftr n 26)) a2 a3 a4 a5 a6 a7
        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 192, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n ST LO HI MI HN.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  eapply evt_cut; [eapply entry_save_run; eassumption|].
  intros ms (m' & junk & -> & MU & WM & MI' & SAVED & ST').
  rewrite unsigned_lit by (unfold INPUT_MAX in HN; lia).
  pose proof (entry_shift_large n HN) as SHIFT.
  step. if_cases HZ.
  - do 16 step.
    replace (bv_unsigned sp - 192 + 192) with (bv_unsigned sp) by lia.
    rewrite Z_to_bv_lit_self. apply evt_done. exists m'.
    split; [reflexivity|]. split; [exact MU|]. split; assumption.
  - exfalso. apply Bool.negb_false_iff in HZ. unfold bv_eqb in HZ.
    rewrite !unsigned_lit in HZ by lia. apply Z.eqb_eq in HZ. lia.
Qed.

Lemma entry_zupd_add_comm : forall xs i j d e,
  zupd (zupd xs i (nth i xs 0 + d)) j (nth j (zupd xs i (nth i xs 0 + d)) 0 + e) =
  zupd (zupd xs j (nth j xs 0 + e)) i (nth i (zupd xs j (nth j xs 0 + e)) 0 + d).
Proof.
  induction xs as [|x xs IH]; intros [|i] [|j] d e; cbn; try reflexivity.
  - f_equal. lia.
  - f_equal. apply IH.
Qed.

Lemma entry_zupd_add_cancel : forall xs i d,
  zupd (zupd xs i (nth i xs 0 + d)) i (nth i (zupd xs i (nth i xs 0 + d)) 0 - d) = xs.
Proof.
  induction xs as [|x xs IH]; intros [|i] d; cbn; try reflexivity.
  - f_equal. lia.
  - f_equal. apply IH.
Qed.

Lemma entry_malloc_free_comm : forall b n m,
  pb_malloc (pb_free b n) m = pb_free (pb_malloc b m) n.
Proof.
  intros [live bytes cap] n m. unfold pb_malloc, pb_free, lv_add, zset, znth.
  cbn [pb_live pb_bytes pb_cap]. f_equal.
  - apply entry_zupd_add_comm.
  - lia.
Qed.

Lemma entry_malloc_free_cancel : forall b n, pb_malloc (pb_free b n) n = b.
Proof.
  intros [live bytes cap] n. unfold pb_malloc, pb_free, lv_add, zset, znth.
  cbn [pb_live pb_bytes pb_cap]. f_equal.
  - replace (nth (Z.to_nat (band n)) (zupd live (Z.to_nat (band n)) (nth (Z.to_nat (band n)) live 0 + -1)) 0 + 1)
      with (nth (Z.to_nat (band n)) (zupd live (Z.to_nat (band n)) (nth (Z.to_nat (band n)) live 0 + -1)) 0 - -1) by lia.
    apply entry_zupd_add_cancel.
  - lia.
Qed.

Lemma entry_free_fold_malloc : forall (T : list (Z * Z)) b n,
  pb_malloc (fold_left (fun b t => pb_free b (snd t)) T b) n =
  fold_left (fun b t => pb_free b (snd t)) T (pb_malloc b n).
Proof.
  induction T as [|t T IH]; intros b n; cbn; [reflexivity|]. rewrite IH, entry_malloc_free_comm. reflexivity.
Qed.

Lemma entry_TDP_cancel : forall T b, TDP T T b = b.
Proof.
  induction T as [|t T IH]; intros b; [reflexivity|].
  unfold TDP in *. cbn [fold_left]. rewrite entry_free_fold_malloc, entry_malloc_free_cancel. apply IH.
Qed.

Lemma entry_large_holds : forall CS B API LS SH SK ra empty rc fx j E,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> INPUT_MAX <= ss_n E ->
  SR (ms_segs B) (slot_cfg (fx := fx) B E)
    (slot_post (rc := rc) (SH := SH) (SK := SK) B (API rc) ra j E CS).
Proof.
  intros CS B API LS SH SK ra empty rc fx j E (FF & HJ & HP & HCS) Hlarge.
  destruct HP as (PRE & RES & PACK & MIS & GI & LIVE & NI & IMG & RO & TASK & FZ).
  destruct PACK as (PE & HMC).
  destruct PRE as (PRE & LEN & DATA & SINK & FD & FS & FDC & SP47).
  destruct PRE as (HM & HW & HB & INIT & RA & ALIGN & SPLO & SPHI & WST & TP & WERR & RP & RN & INPUT & ROD).
  assert (SEG : ms_segs B = rsegs) by (unfold frame_facts in FF; tauto).
  assert (RAEV : ra mod 2 = 0) by (unfold frame_facts in FF; tauto).
  assert (OHEAD : @sk_ofl_head SH = 0x52230) by (unfold frame_facts in FF; tauto).
  assert (OLOCK : @sk_ofl_lock SK = 0x52228) by (unfold frame_facts in FF; tauto).
  assert (OTHREAD : @sk_threaded SK = 0x51e00 + 1) by (unfold frame_facts in FF; tauto).
  pose proof (@alloc_ceiling_value rc) as AC.
  pose proof (@alloc_ceiling_lt rc) as ACL.
  assert (NBOUND : INPUT_MAX <= ss_n E < 2 ^ 64).
  { destruct INPUT as [[N _]|(NP & q & Q & QE)]; [unfold INPUT_MAX in Hlarge; lia|].
    pose proof (mr_blocks_range B (aa_MR (API rc)) (aa_laws (API rc)) _ _ _ _ q (ss_n E) HM Q). lia. }
  assert (ST : stk rsegs (ss_mem E) (spZ (ss_regs E) - SLOT_STACK) (spZ (ss_regs E))).
  { split; [unfold SLOT_STACK in *; lia|]. split; [lia|]. intros a Ha.
    assert (WA : writable_at rsegs (ss_mem E) a) by (rewrite <- SEG; apply WST; exact Ha).
    split; [exact WA|]. destruct (writable_hi_present (ss_mem E) a ltac:(unfold SLOT_STACK in *; lia) WA) as [v V].
    exists v. unfold mrd, wa. rewrite V. reflexivity. }
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HM) as (HH & HL & HMAT).
  unfold slot_cfg. rewrite SEG. rewrite SEG in RO.
  eapply (kseg (ss_regs E) (Z_to_bv 64 ENTRY) (ss_mem E) (ss_md E));
    [exact wx_apart_rsegs|exact RO|exact HH|exact HL| | |].
  - unfold Regs6ss.mkR_of.
    assert (E11 : reg_get (ss_regs E) 11 = Z_to_bv 64 (ss_n E)) by exact RN. rewrite E11.
    eapply entry_large_run with (lo := spZ (ss_regs E) - SLOT_STACK).
    + apply stk_normalize; [exact ST|]. unfold SLOT_STACK in *; lia.
    + change (bv_unsigned (reg_get (ss_regs E) 2)) with (spZ (ss_regs E)). unfold SLOT_STACK in *; lia.
    + unfold SLOT_STACK in *; lia.
    + apply mem_inv_normalize.
    + exact NBOUND.
  - intros ms (m' & -> & _). do 3 eexists. reflexivity.
  - intros R pc m0 regs' mem' (m' & EQ & MU & WM & MI) GR MREL ROS.
    injection EQ as ER EP EM. subst R pc m0.
    change (bv_unsigned (reg_get (ss_regs E) 2)) with (spZ (ss_regs E)) in MU.
    destruct (rmid_norm B (API rc) SLOT_STACK (spZ (ss_regs E)) (fun _ => False) (fun _ => False)
      (ss_L E) (ss_A E) (ss_mem E) (ss_md E) m' mem' [(spZ (ss_regs E) - 192, spZ (ss_regs E))]
      SEG RO MREL ROS MU WM HM HW HB ltac:(lia)) as (RM & MUR & WMR).
    { unfold sk. intros a [Ha|Ha]; [apply WST; exact Ha|apply WERR; exact Ha]. }
    { intros a Ha HOUT. destruct (hg_not_out _ _ HOUT) as (lo & hi & [EQ|[]] & R). injection EQ as <- <-.
      left. unfold SLOT_STACK; lia. }
    { intros a HA. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HM HA).
      apply hg_out. intros lo hi [EQ|[]]. injection EQ as <- <-. left. unfold SLOT_STACK in *; lia. }
    { intros q n i HQ HI HO. destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ q n i HM HQ HI)
        as (_ & RQ & RE & _).
      exfalso. destruct (hg_not_out _ _ HO) as (lo & hi & [EQ|[]] & R). injection EQ as <- <-.
      unfold SLOT_STACK in *; lia. }
    assert (LOW : forall a, 0 <= a < @YM05.alloc_ceiling rc ->
      mbyte (ms_segs B) mem' a = mbyte (ms_segs B) (ss_mem E) a /\
      (writable_at (ms_segs B) (ss_mem E) a <-> writable_at (ms_segs B) mem' a)).
    { intros a HA. rewrite SEG. split.
      - apply (munch_mbyte rsegs _ _ _ _ MUR); [lia|]. apply hg_out. intros lo hi [EQ|[]]. injection EQ as <- <-.
        left. unfold SLOT_STACK in *; lia.
      - apply (munch_writable rsegs _ _ _ _ MUR); [lia|]. apply hg_out. intros lo hi [EQ|[]]. injection EQ as <- <-.
        left. unfold SLOT_STACK in *; lia. }
    assert (RMEM : aa_MR (API rc) (ss_L E) (ss_A E) mem' (ss_md E)) by exact (proj1 RM).
    apply SR_ret. exists fx, (ss_L E), (ss_A E), regs', mem', (ss_md E), (ss_T E).
    split.
    { rewrite SEG. f_equal. f_equal.
      change (reg_get (ss_regs E) 1) with (YK11.getr (ss_regs E) 1). rewrite RA.
      apply ret_pc_of_ok. apply ret_ok_even. rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia. }
    split; [exact FZ|]. split.
    + unfold lib_post_p3. cbv zeta.
      split; [exact RMEM|]. split; [exact HW|]. split; [exact HB|]. split; [exact INIT|].
      split; [rewrite GR; reflexivity|]. split.
      { intros r Hr. rewrite GR. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
          r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; reflexivity|]); subst r; reflexivity. }
      split.
      { exists (m_vmmaps (ss_md E)), (m_fds (ss_md E)), (m_statpins (ss_md E)).
        split; [apply os_upd_self|]. intros; reflexivity. }
      split; [intros q n HQ _; exists q; split; [exact HQ|reflexivity]|].
      split.
      { intros a HA NS. rewrite SEG. split.
        - apply (munch_mbyte rsegs _ _ _ _ MUR); [lia|]. apply hg_out. intros lo hi [EQ|[]]. injection EQ as <- <-.
          unfold lib_scratch, SLOT_STACK in NS. lia.
        - apply (munch_writable rsegs _ _ _ _ MUR); [lia|]. apply hg_out. intros lo hi [EQ|[]]. injection EQ as <- <-.
          unfold lib_scratch, SLOT_STACK in NS. lia. }
      split.
      { intros a HA _ _ _ _. apply LOW. exact (hg_img_low B SEG a HA). }
      split.
      { intros a HA. apply (proj2 (LOW a ltac:(unfold in_globals, G_reply, frame_G in HA;
          destruct HA as (lo & len & [EQ|[EQ|[]]] & HX); injection EQ as <- <-; lia))). }
      split.
      { intros q n i HQ _ _ HI. apply (proj1 (LOW (ptr_addr (ss_L E) q + i) ltac:(
          destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ q n i HM HQ HI) as (_ & H1 & H2 & _); lia))). }
      split; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RM))))))))))))|].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact FS|]. split.
      { destruct SINK as ((S1 & S2) & S3 & S4). split; [split|split; [|exact S4]].
        - eapply val_mem_frame; [|exact S1]. intros a HA. exact (proj1 (LOW a ltac:(rewrite OTHREAD in HA; cbn in HA; lia))).
        - eapply val_mem_frame; [|exact S2]. intros a HA. exact (proj1 (LOW a ltac:(rewrite OLOCK in HA; cbn in HA; lia))).
        - apply val_mem_word_mem. apply val_mem_word_mem in S3. eapply val_mem_frame; [|exact S3].
          intros a HA. exact (proj1 (LOW a ltac:(rewrite OHEAD in HA; cbn in HA; lia))). }
      split; [rewrite SEG; exact (ro_agree_same rsegs (ss_mem E) mem' RO ROS)|].
      split.
      { rewrite entry_TDP_cancel. cbn [pb_of3 pb_live pb_bytes]. rewrite <- MIS, <- HMC.
        pose proof RES as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HlM & _).
        exact (res_ok_pack3_raise (ss_A E) (ss_b E) (CS (ss_pl E)) (p3_mcap (ss_b E)) RES (proj1 (HCS (ss_pl E)))
          HlM (fun k HK => proj2 (proj1 (proj2 PE) k HK)) (fun k _ => Z.le_refl _)). }
      split.
      { intros i HI. destruct INPUT as [[NZ _]|(NP & q & HQ & QE)]; [lia|].
        apply (proj1 (LOW (ss_p E + i) ltac:(rewrite <- QE;
          destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ q (ss_n E) i HM HQ HI) as (_ & H1 & H2 & _); lia))). }
      split; [exact LIVE|]. intros t HT _. exact HT.
    + change (GI_t j (ss_T E) mem').
      apply (GI_t_local B SEG j (ss_T E) (ss_mem E) mem'); [|exact GI].
      intros a [HA|HA].
      * apply (proj1 (LOW a ltac:(unfold in_globals, G_reply, frame_G in HA;
          destruct HA as (lo & len & [EQ|[EQ|[]]] & HX); injection EQ as <- <-; lia))).
      * destruct HA as (q & n & HQ & HA). destruct LIVE as (_ & LIVE).
        pose proof (block_facts B (aa_MR (API rc)) (aa_laws (API rc)) _ _ _ _ q n (a - q) HM (LIVE _ HQ) ltac:(lia))
          as (_ & H1 & H2 & _). exact (proj1 (LOW a ltac:(lia))).
Qed.

Lemma entry_wN_bytes : forall m a v w,
  0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> 0 <= v < 2 ^ (8 * Z.of_nat w) ->
  wN_at m a v w -> bytes_at rsegs m a (Z_to_le_bytes w v).
Proof.
  intros m a v w HA HE HV H.
  replace v with (Z.shiftr v (8 * 0)) at 1 by (rewrite Z.mul_0_r, Z.shiftr_0_r; reflexivity).
  rewrite Z_to_le_bytes_zbytes.
  apply bytes_at_of_mbyte; [exact HA|rewrite length_zbytes; exact HE|].
  intros i HI. rewrite length_zbytes in HI. rewrite nth_error_zbytes by exact HI.
  rewrite H by exact HI. f_equal. unfold le_byte. rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat w)) HV).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. f_equal.
Qed.

Definition entry_frame_writes (sp : Z) : list (Z * Z) :=
  (sp - 192, sp) :: tl (entry_writes (sp - 192)).

Lemma entry_small_run : forall
    ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) lo n
    (jc jn jm jb jg jd je : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 192 <= bv_unsigned sp -> 0x100000 <= lo -> mem_inv rsegs m ->
  0 <= n < INPUT_MAX ->
  rw_cells rsegs m 0x21624 [CB 4 jc] -> rw_cells rsegs m 0x318c0 [CB 4 jn] ->
  rw_cells rsegs m 0x318d8 [CB 8 jm] -> rw_cells rsegs m 0x318a4 [CB 1 jb] ->
  rw_cells rsegs m 0x318a8 [CB 1 jg] -> rw_cells rsegs m 0x318ac [CB 1 jd] ->
  rw_cells rsegs m 0x318b0 [CB 1 je] ->
  evt rsegs
    (fun ms => exists m' junk,
      ms = MS (mkR (Z_to_bv 64 0x14118) (Z_to_bv 64 (bv_unsigned sp - 192)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n)
        (Z_to_bv 64 0x310f4) (Z_to_bv 64 CLIENT_BASE) a2 a3 a4 a5 a6 a7
        a0 s3 (Z_to_bv 64 G_RELAY_LO) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OP_ADD) fc None m' (seg_rom rsegs) /\
      munch (entry_frame_writes (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned sp - 192)
        [C8 (Z_to_bv 64 CLIENT_BASE); CB 80 junk;
         C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
      rw_cells rsegs m' 0x21624 [C4 (Z_to_bv 64 3)] /\
      rw_cells rsegs m' 0x318c0 [C4 (Z_to_bv 64 0)] /\
      rw_cells rsegs m' 0x318d8 [C8 (Z_to_bv 64 0)] /\
      rw_cells rsegs m' 0x318a4 [C1 (Z_to_bv 8 0)] /\
      rw_cells rsegs m' 0x318a8 [C1 (Z_to_bv 8 0)] /\
      rw_cells rsegs m' 0x318ac [C1 (Z_to_bv 8 0)] /\
      rw_cells rsegs m' 0x318b0 [C1 (Z_to_bv 8 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n jc jn jm jb jg jd je ST LO HI MI HN WC WN WMX WB WG WD WE.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  eapply evt_cut; [eapply entry_save_run; eassumption|].
  intros ms (m' & junk & -> & MU & WM & MI' & SAVED & ST').
  repeat match goal with
  | H : rw_cells rsegs m ?a ?cs |- _ =>
      let H' := fresh "RW" in
      pose proof (rw_cells_transport rsegs _ m m' a cs H MU WM ltac:(cbn; lia)) as H';
      clear H; rename H' into H
  end.
  assert (MU' : munch (entry_frame_writes (bv_unsigned sp)) m m').
  { eapply munch_weaken; [|exact MU]. unfold sub_fp, entry_frame_writes, entry_writes.
    intros x H. cbn [tl outside] in *. tauto. }
  clear MU. rename MU' into MU. unfold entry_frame_writes, entry_writes in MU. cbn [tl] in MU.
  rewrite unsigned_lit by (unfold INPUT_MAX in HN; lia).
  assert (SH : Z.shiftr n 26 = 0).
  { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. exact HN. }
  rewrite SH. step. if_false.
  do 9 step.
  do 4 (step; change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]; mem_after_store).
  step. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma entry_global_image : forall a, in_globals G_reply a ->
  wview rsegs (fun _ => None) (wa a) <> None /\ seg_rom rsegs (wa a) <> None.
Proof.
  intros a (lo & len & [EQ|[EQ|[]]] & HA); injection EQ as <- <-.
  - assert (C : forallb (fun i =>
        match wview rsegs (fun _ => None) (wa (0x21620 + i)), seg_rom rsegs (wa (0x21620 + i)) with
        | Some _, Some _ => true | _, _ => false end) (map Z.of_nat (seq 0 16)) = true)
      by (vm_compute; reflexivity).
    pose proof (zseq_forall _ _ C (a - 0x21620) ltac:(cbn; lia)) as H.
    change (match wview rsegs (fun _ => None) (wa (0x21620 + (a - 0x21620))),
                  seg_rom rsegs (wa (0x21620 + (a - 0x21620))) with
            | Some _, Some _ => true | _, _ => false end = true) in H.
    replace (0x21620 + (a - 0x21620)) with a in H by lia.
    destruct (wview rsegs (fun _ => None) (wa a)) as [v|] eqn:W;
      destruct (seg_rom rsegs (wa a)) as [u|] eqn:R; cbn in H; try congruence.
    split; congruence.
  - assert (C : forallb (fun i =>
        match wview rsegs (fun _ => None) (wa (0x318a0 + i)), seg_rom rsegs (wa (0x318a0 + i)) with
        | Some _, Some _ => true | _, _ => false end) (map Z.of_nat (seq 0 512)) = true)
      by (vm_compute; reflexivity).
    pose proof (zseq_forall _ _ C (a - 0x318a0) ltac:(cbn; lia)) as H.
    change (match wview rsegs (fun _ => None) (wa (0x318a0 + (a - 0x318a0))),
                  seg_rom rsegs (wa (0x318a0 + (a - 0x318a0))) with
            | Some _, Some _ => true | _, _ => false end = true) in H.
    replace (0x318a0 + (a - 0x318a0)) with a in H by lia.
    destruct (wview rsegs (fun _ => None) (wa a)) as [v|] eqn:W;
      destruct (seg_rom rsegs (wa a)) as [u|] eqn:R; cbn in H; try congruence.
    split; congruence.
Qed.

Lemma entry_global_access : forall m a, in_globals G_reply a ->
  writable_at rsegs m a /\ exists v, mbyte rsegs m a = Some v.
Proof.
  intros m a HA. destruct (entry_global_image a HA) as [W R].
  unfold writable_at, wview, mbyte, wa in *. destruct (m (Z_to_bv 64 a)) as [v|] eqn:M.
  - split; [discriminate|exists v; reflexivity].
  - split; [exact W|]. change (exists v, seg_rom rsegs (Z_to_bv 64 a) = Some v).
    destruct (seg_rom rsegs (Z_to_bv 64 a)) as [v|]; [exists v; reflexivity|contradiction].
Qed.

Lemma entry_global_cells : forall m a k,
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> in_globals G_reply (a + i)) ->
  exists junk, rw_cells rsegs m a [CB k junk].
Proof.
  intros m a k HA HE HG.
  set (junk := map (fun i => match mbyte rsegs m (a + Z.of_nat i) with Some v => v | None => Z_to_bv 8 0 end) (seq 0 k)).
  assert (L : length junk = k) by (unfold junk; rewrite length_map, length_seq; reflexivity).
  exists junk. split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_of_mbyte; [exact HA|lia|].
    intros i HI. rewrite L in HI. unfold junk. rewrite nth_error_map, nth_error_seq_lt by exact HI. cbn.
    destruct (entry_global_access m (a + Z.of_nat i) (HG (Z.of_nat i) ltac:(lia))) as (_ & v & HV). rewrite HV. reflexivity.
  - split; [exact HA|]. cbn [cells_size csize]. rewrite Nat.add_0_r. split; [exact HE|].
    intros i HI. exact (proj1 (entry_global_access m (a + i) (HG _ HI))).
Qed.

Lemma entry_block_data : forall rc B (API : AllocAPI B),
  AllocExtra B (aa_MR API) -> blocks_writable B API ->
  forall L A mem md q n,
    aa_MR API L A mem md -> In (q, n) (blocks L A) -> 0 < n ->
    fresh_block (rc := rc) B q n /\ exists bs, length bs = Z.to_nat n /\
      rw_cells (ms_segs B) mem q [CB (Z.to_nat n) bs].
Proof.
  intros rc B API AX BW L A mem md q n HM HQ HN.
  pose proof (block_facts B (aa_MR API) (aa_laws API) _ _ _ _ q n 0 HM HQ ltac:(lia)) as (_ & HB & HE & _).
  pose proof (@alloc_ceiling_lt rc) as AC.
  split.
  - split; [exact HB|]. split; [exact HE|]. intros i HI.
    unfold blocks in HQ. apply in_map_iff in HQ as ([p k] & EQ & HP). cbn in EQ. injection EQ as <- <-.
    exact (ax_blocks_img AX _ _ _ _ p k i HM HP HI).
  - destruct (present_rw_cells (ms_segs B) mem q (Z.to_nat n) ltac:(lia) ltac:(lia)) as [bs HBS].
    { intros i HI. apply (proj1 (block_facts B (aa_MR API) (aa_laws API) _ _ _ _ q n i HM HQ ltac:(lia))). }
    exists bs. split; [destruct HBS as [[HC _] _]; cbn in HC; tauto|exact HBS].
Qed.

Lemma entry_byte_cells : forall m a v k,
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> in_globals G_reply (a + i)) ->
  byte_at m a v (Z.of_nat k) -> rw_cells rsegs m a [CB k (repeat (Z_to_bv 8 v) k)].
Proof.
  intros m a v k HA HE HG HB. split.
  - split; [cbn; rewrite repeat_length; tauto|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_of_mbyte; [exact HA|rewrite repeat_length; exact HE|].
    intros i HI. rewrite repeat_length in HI. rewrite nth_error_repeat by exact HI. apply HB. lia.
  - split; [exact HA|]. cbn [cells_size csize]. rewrite Nat.add_0_r. split; [exact HE|].
    intros i HI. exact (proj1 (entry_global_access m (a + i) (HG _ HI))).
Qed.

Definition entry_relay : rentry := RE FIRST_FD 0 0 (nulbytes 4) 0 0 0 0 0 (nulbytes 4) [] [] [].

Lemma entry_relay_bytes : entry_bytes entry_relay = new_entry FIRST_FD.
Proof. reflexivity. Qed.

Lemma entry_relay_ok : forall rc B L A mem, RelayRep.entry_ok (rc := rc) B L A mem entry_relay.
Proof.
  intros rc B L A mem. unfold RelayRep.entry_ok, entry_relay, re_nheld.
  cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_hp re_keys re_junk].
  repeat split; try reflexivity; try (left; repeat split; reflexivity);
    try constructor; try tauto; try (unfold FIRST_FD; lia).
Qed.

Lemma entry_pair_ok : forall rc B L A mem q pj,
  src_at (rc := rc) B L A mem G_S (new_src FIRST_FD q pj) ->
  pair_ok (rc := rc) B L A mem 0 entry_relay (new_src FIRST_FD q pj, 0%nat).
Proof.
  intros rc B L A mem q pj HS. unfold pair_ok. cbv zeta. cbn [fst snd].
  split; [change (G_S + SRC_SIZE * Z.of_nat 0) with G_S; exact HS|].
  unfold entry_relay, new_src, empty_list, pending_stream, texts, same_set, drain_b_c.keys_texts, hs_W.
  cbn. repeat split; try constructor; try tauto; try lia.
  unfold hl_n. cbn. lia.
Qed.

Lemma entry_target_addrs : forall G OUT q pj,
  target_addrs G OUT [entry_relay] [(new_src FIRST_FD q pj, 0%nat)] = [G; OUT; q].
Proof. reflexivity. Qed.

Lemma entry_cost : forall q pj, slot_cost [entry_relay] [(new_src FIRST_FD q pj, 0%nat)] = 0.
Proof. reflexivity. Qed.

Lemma entry_gi_blocks : forall rc B (API : AllocAPI B),
  AllocExtra B (aa_MR API) -> blocks_writable B API ->
  forall L A mem md j T,
  aa_MR API L A mem md -> GI_t j T mem -> tb_live L A T ->
  exists C G NO CAP OUT tail,
    wN_at mem G_CAPSRC C 4 /\ wN_at mem G_SRC G 8 /\
    wN_at mem G_NOUT NO 8 /\ wN_at mem G_CAPOUT CAP 8 /\ wN_at mem G_OUT OUT 8 /\
    0 <= NO <= CAP /\ CAP <= TBBYTES /\ 0 <= OUT < 2 ^ 64 /\
    T = kept_blocks C G CAP OUT /\
    ((C = 0 /\ G = 0 /\ tail = []) \/
     (C = 16 /\ In (G, SRC_TABLE) (blocks L A) /\ fresh_block (rc := rc) B G SRC_TABLE /\
      Z.of_nat (length tail) = SRC_TABLE /\ rw_cells (ms_segs B) mem G [CB (Z.to_nat SRC_TABLE) tail])) /\
    output_at (rc := rc) B L A mem (Z_to_bv 64 NO) (Z_to_bv 64 CAP) (Z_to_bv 64 OUT).
Proof.
  intros rc B API AX BW L A mem md j T HM
    (_ & _ & C & G & NO & CAP & OUT & WC & WG & WNO & WCP & WO & HC & HNO & HNULL & HT) LIVE.
  destruct HNO as (HN & HCBOUND). destruct HNULL as (ONULL & GNULL).
  assert (CAP64 : 0 <= CAP < 2 ^ 64) by (unfold TBBYTES in *; lia).
  assert (NO64 : 0 <= NO < 2 ^ 64) by lia.
  assert (OUTDATA : 0 <= OUT < 2 ^ 64 /\ output_at (rc := rc) B L A mem (Z_to_bv 64 NO) (Z_to_bv 64 CAP) (Z_to_bv 64 OUT)).
  { destruct (Z.eq_dec CAP 0) as [CZ|CZ].
    - assert (OZ : OUT = 0) by (apply ONULL; exact CZ). assert (NZ : NO = 0) by lia.
      rewrite CZ, OZ, NZ. split; [lia|]. unfold output_at. cbv zeta.
      split; [exists [], []; left; repeat split; reflexivity|]. change (0 <= TBBYTES). unfold TBBYTES; lia.
    - assert (CPOS : 0 < CAP) by lia.
      assert (OB : In (OUT, CAP) (blocks L A)).
      { apply (proj2 LIVE). rewrite HT. unfold kept_blocks. apply in_or_app. right.
        rewrite (proj2 (Z.eqb_neq CAP 0) CZ). left; reflexivity. }
      destruct (entry_block_data rc B API AX BW L A mem md OUT CAP HM OB CPOS) as (OF & bytes & BL & BRW).
      pose proof OF as (OL & OE & _). pose proof (@alloc_ceiling_lt rc) as CEIL.
      split; [lia|]. unfold output_at. cbv zeta. rewrite !unsigned_lit by lia. split; [|exact HCBOUND].
      exists (firstn (Z.to_nat NO) bytes), (skipn (Z.to_nat NO) bytes). right.
      split; [exact CPOS|]. split; [lia|]. split; [exact OB|]. split; [exact OF|].
      split.
      { rewrite firstn_skipn. destruct BRW as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
      split; [rewrite length_firstn, BL; lia|]. rewrite length_skipn, BL. lia. }
  destruct OUTDATA as [ORANGE ODATA].
  assert (TAB : exists tail,
    (C = 0 /\ G = 0 /\ tail = []) \/
    (C = 16 /\ In (G, SRC_TABLE) (blocks L A) /\ fresh_block (rc := rc) B G SRC_TABLE /\
     Z.of_nat (length tail) = SRC_TABLE /\ rw_cells (ms_segs B) mem G [CB (Z.to_nat SRC_TABLE) tail])).
  { destruct HC as [CZ|CZ].
    - exists []. left. split; [exact CZ|]. split; [apply GNULL; exact CZ|reflexivity].
    - assert (GB : In (G, SRC_TABLE) (blocks L A)).
      { apply (proj2 LIVE). rewrite HT, CZ. unfold kept_blocks. cbn. left; reflexivity. }
      destruct (entry_block_data rc B API AX BW L A mem md G SRC_TABLE HM GB ltac:(change (0 < 896); lia))
        as (GF & tail & TL & RW).
      exists tail. right. split; [exact CZ|]. split; [exact GB|]. split; [exact GF|].
      split; [rewrite TL; reflexivity|exact RW]. }
  destruct TAB as [tail TAB]. exists C, G, NO, CAP, OUT, tail.
  repeat (split; [assumption|]). exact ODATA.
Qed.

Lemma entry_src_rmid : forall rc B (API : AllocAPI B),
  AllocExtra B (aa_MR API) -> blocks_writable B API ->
  forall K sp L A mem md L' A' mem' md' HA h,
  ms_segs B = rsegs -> @YM05.alloc_ceiling rc <= sp - K -> aa_MR API L A mem md ->
  rmid B API K sp (fun _ => False) (fun _ => False) L A mem md L' A' mem' md' ->
  (forall i, 0 <= i < 96 -> img_plain B (HA + i)) ->
  src_at (rc := rc) B L A mem HA h -> src_at (rc := rc) B L' A' mem' HA h.
Proof.
  intros rc B API AX BW K sp L A mem md L' A' mem' md' HA h SEG HK HM RM PL HS.
  apply src_at_iff in HS. destruct HS as (HS & HE & HH & ND). apply src_at_iff.
  split.
  - eapply (src_base_rmid B API AX BW K sp (fun _ => False) (fun _ => False));
      [exact SEG|exact HK|exact HM|exact RM|exact HS| |].
    + intros i HI. split; [apply PL; lia|tauto].
    + intros q _. split; [tauto|intros; tauto].
  - split.
    + eapply (list_at_rmid B API AX BW K sp (fun _ => False) (fun _ => False));
        [exact SEG|exact HK|exact HM|exact RM|exact HE| |].
      * intros i HI. split; [replace (HA + 64 + i) with (HA + (64 + i)) by lia; apply PL; lia|tauto].
      * intros q _. split; [tauto|intros; tauto].
    + split; [|exact ND].
      eapply (list_at_rmid B API AX BW K sp (fun _ => False) (fun _ => False));
        [exact SEG|exact HK|exact HM|exact RM|exact HH| |].
      * intros i HI. split; [replace (HA + 80 + i) with (HA + (80 + i)) by lia; apply PL; lia|tauto].
      * intros q _. split; [tauto|intros; tauto].
Qed.

Lemma entry_head_pc : forall E,
  (if 0 <? ss_n E then LOOP_BODY else LOOP_EXIT) = head_pc E 0 0.
Proof. intros E. reflexivity. Qed.

Lemma entry_head_regs_bridge : forall E R regs,
  entry_head_registers (slot_sp E) (ss_p E) (ss_n E)
    (YK11.getr (ss_regs E) 3) (YK11.getr (ss_regs E) 4) R ->
  (forall r, YK11.getr regs r = YK11.getr R r) -> head_regs E 0 0 regs.
Proof.
  intros E R regs (R2 & R3 & R4 & R20 & RB) GR.
  unfold head_regs. split; [rewrite GR; exact R2|]. split; [rewrite GR; exact R3|].
  split; [rewrite GR; exact R4|]. split; [rewrite GR; exact R20|].
  intros HB. unfold head_body, OPS_MAX in HB. cbn in HB. apply Z.ltb_lt in HB.
  specialize (RB HB). rewrite Z.sub_0_r, Z.add_0_r.
  destruct RB as (R9 & R18 & R22 & R24 & R23 & R25 & R21 & R19 & R27).
  repeat (split; [rewrite GR; assumption|]). rewrite GR. exact R27.
Qed.

Lemma entry_word8 : forall m a v,
  0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> in_globals G_reply (a + i)) ->
  wN_at m a v 8 -> rw_cells rsegs m a [C8 (Z_to_bv 64 v)].
Proof.
  intros m a v HA HE HV HG HW. split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    unfold le8, word_to_le_bytes. rewrite unsigned_lit by exact HV.
    apply entry_wN_bytes; assumption.
  - split; [exact HA|]. cbn [cells_size csize]. split; [exact HE|].
    intros i HI. exact (proj1 (entry_global_access m (a + i) (HG i HI))).
Qed.

Lemma entry_word4 : forall m a v,
  0 <= a -> a + 4 <= 2 ^ 64 -> 0 <= v < 2 ^ 32 ->
  (forall i, 0 <= i < 4 -> in_globals G_reply (a + i)) ->
  wN_at m a v 4 -> rw_cells rsegs m a [C4 (Z_to_bv 64 v)].
Proof.
  intros m a v HA HE HV HG HW. split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    unfold le4. rewrite unsigned_lit by lia. apply entry_wN_bytes; assumption.
  - split; [exact HA|]. cbn [cells_size csize]. split; [exact HE|].
    intros i HI. exact (proj1 (entry_global_access m (a + i) (HG i HI))).
Qed.

(* The first op_add's resources: from the start view RV [] [G; OUT] NC_FIX [], the run finds room, and RI holds at
   every view of the post state that covers its blocks and moves the view's nc blocks by the blocks op_add makes
   (entry_adds). *)
Definition entry_add_resources_s (F : ResFormT) (RI : res_inv) : Prop :=
  forall E L A C G OUT, RI E 0 (RV [] [G; OUT] NC_FIX []) L A -> C = 0 \/ C = 16 ->
    res_tr F (fun L' A' qs => forall q g,
                live_at L' A' (resolveF qs (Ret 0)) q PARTIAL_BYTES ->
                live_at L' A' (resolveF qs (relay_add_tbl FIRST_FD 0 C 1 (known_at L A G))) g SRC_TABLE ->
                forall G' OUT' es' hj',
                (forall x m, In (x, m) (blocks L' A') -> In (x, m) (blocks L A) \/ In x (target_addrs G' OUT' es' hj')) ->
                pend_view hj' = [[]] -> ek_view hj' = [] -> (length es' <= 4)%nat ->
                nc_move (RV [] [G; OUT] NC_FIX []) L A (view_of G' OUT' es' hj') L' A' [] (entry_adds q g C) ->
                List.NoDup (map fst (blocks L' A')) ->
                (forall p n n', In (p, n) (user_blocks A) -> In (p, n') (user_blocks A') ->
                   In (ptr_addr L p) (rv_nc (RV [] [G; OUT] NC_FIX [])) -> ~ In (ptr_addr L p) (map fst (@nil (Z * Z))) ->
                   In (ptr_addr L' p) (rv_nc (view_of G' OUT' es' hj'))) ->
                ncs (view_of G' OUT' es' hj') L' A' <= nc_wt es' hj' -> nc_wt es' hj' <= NC_FIX ->
                RI E 0 (view_of G' OUT' es' hj') L' A')
      A (op_add_tr (Some 0%nat) FIRST_FD 0 C (known_at L A G)).

Definition entry_call_regs (E : sstart) (regs : bvmap 5 word) : Prop :=
  YK11.getr regs 1 = Z_to_bv 64 0x14118 /\ YK11.getr regs 2 = Z_to_bv 64 (slot_sp E) /\
  YK11.getr regs 3 = YK11.getr (ss_regs E) 3 /\ YK11.getr regs 4 = YK11.getr (ss_regs E) 4 /\
  YK11.getr regs 9 = Z_to_bv 64 (ss_n E) /\ YK11.getr regs 18 = Z_to_bv 64 (ss_p E) /\
  YK11.getr regs 20 = Z_to_bv 64 G_RELAY_LO.

Definition entry_initialized {fx : FPState} {rc : RunCeil} B (API : AllocAPI B) E c : Prop :=
  exists regs mem junk,
    c = mkCfg (YK11.mkst regs (Z_to_bv 64 OP_ADD) mem (seg_rom (ms_segs B))) (ss_md E) /\
    rmid B API SLOT_STACK (spZ (ss_regs E)) (in_globals G_reply) (fun _ => False)
      (ss_L E) (ss_A E) (ss_mem E) (ss_md E) (ss_L E) (ss_A E) mem (ss_md E) /\
    ro_agree (ms_segs B) mem /\
    munch (entry_frame_writes (spZ (ss_regs E))) (ss_mem E) mem /\
    wmono (ms_segs B) (ss_mem E) mem /\ entry_call_regs E regs /\
    rw_cells (ms_segs B) mem (slot_sp E) ([C8 (Z_to_bv 64 CLIENT_BASE); CB 80 junk] ++ saved_cells (ss_regs E)) /\
    rw_cells (ms_segs B) mem 0x21624 [C4 (Z_to_bv 64 3)] /\
    rw_cells (ms_segs B) mem 0x318c0 [C4 (Z_to_bv 64 0)] /\
    rw_cells (ms_segs B) mem 0x318d8 [C8 (Z_to_bv 64 0)] /\
    rw_cells (ms_segs B) mem 0x318a4 [C1 (Z_to_bv 8 0)] /\
    rw_cells (ms_segs B) mem 0x318a8 [C1 (Z_to_bv 8 0)] /\
    rw_cells (ms_segs B) mem 0x318ac [C1 (Z_to_bv 8 0)] /\
    rw_cells (ms_segs B) mem 0x318b0 [C1 (Z_to_bv 8 0)].

Lemma entry_initialize : forall CS B API LS SH SK ra empty rc fx j E,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> ss_n E < INPUT_MAX ->
  SR (ms_segs B) (slot_cfg (fx := fx) B E) (entry_initialized (fx := fx) (rc := rc) B (API rc) E).
Proof.
  intros CS B API LS SH SK ra empty rc fx j E (FF & HJ & HP & HCS) Hsmall.
  destruct HP as (PRE & RES & PACK & MIS & GI & LIVE & NI & IMG & RO & TASK & FZ).
  destruct PRE as (PRE & LEN & DATA & SINK & FD & FS & FDC & SP47).
  destruct PRE as (HM & HW & HB & INIT & RA & ALIGN & SPLO & SPHI & WST & TP & WERR & RP & RN & INPUT & ROD).
  assert (SEG : ms_segs B = rsegs) by (unfold frame_facts in FF; tauto).
  assert (PL : forall a, in_globals G_reply a -> img_plain B a) by
    (unfold frame_facts, G_reply, img_plain in *; tauto).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall rc fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL rc fx). }
  assert (AX : AllocExtra B (aa_MR (API rc))) by (unfold frame_allocator in FA; tauto).
  pose proof (@alloc_ceiling_value rc) as AC. pose proof (@alloc_ceiling_lt rc) as ACL.
  assert (ST : stk rsegs (ss_mem E) (spZ (ss_regs E) - SLOT_STACK) (spZ (ss_regs E))).
  { split; [unfold SLOT_STACK in *; lia|]. split; [lia|]. intros a Ha.
    assert (WA : writable_at rsegs (ss_mem E) a) by (rewrite <- SEG; apply WST; exact Ha).
    split; [exact WA|]. destruct (writable_hi_present (ss_mem E) a ltac:(unfold SLOT_STACK in *; lia) WA) as [v V].
    exists v. unfold mrd, wa. rewrite V. reflexivity. }
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HM) as (HH & HL & HMAT).
  unfold slot_cfg. rewrite SEG. rewrite SEG in RO.
  eapply (kseg (ss_regs E) (Z_to_bv 64 ENTRY) (ss_mem E) (ss_md E));
    [exact wx_apart_rsegs|exact RO|exact HH|exact HL| | |].
  - assert (GC : forall a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
        (forall i, 0 <= i < Z.of_nat k -> in_globals G_reply (a + i)) ->
        exists junk, rw_cells rsegs (normalize rsegs (ss_mem E)) a [CB k junk]) by (intros; apply entry_global_cells; assumption).
    destruct (GC 0x21624 4%nat ltac:(lia) ltac:(lia)) as [jc WC].
    { intros i HI. exists 0x21620, 16. split; [left; reflexivity|lia]. }
    destruct (GC 0x318c0 4%nat ltac:(lia) ltac:(lia)) as [jn WN].
    { intros i HI. exists 0x318a0, 512. split; [right; left; reflexivity|lia]. }
    destruct (GC 0x318d8 8%nat ltac:(lia) ltac:(lia)) as [jm WMX].
    { intros i HI. exists 0x318a0, 512. split; [right; left; reflexivity|lia]. }
    destruct (GC 0x318a4 1%nat ltac:(lia) ltac:(lia)) as [jb WB].
    { intros i HI. exists 0x318a0, 512. split; [right; left; reflexivity|lia]. }
    destruct (GC 0x318a8 1%nat ltac:(lia) ltac:(lia)) as [jg WG].
    { intros i HI. exists 0x318a0, 512. split; [right; left; reflexivity|lia]. }
    destruct (GC 0x318ac 1%nat ltac:(lia) ltac:(lia)) as [jd WD].
    { intros i HI. exists 0x318a0, 512. split; [right; left; reflexivity|lia]. }
    destruct (GC 0x318b0 1%nat ltac:(lia) ltac:(lia)) as [je WE].
    { intros i HI. exists 0x318a0, 512. split; [right; left; reflexivity|lia]. }
    unfold Regs6ss.mkR_of. assert (E11 : reg_get (ss_regs E) 11 = Z_to_bv 64 (ss_n E)) by exact RN. rewrite E11.
    eapply entry_small_run with (lo := spZ (ss_regs E) - SLOT_STACK).
    + apply stk_normalize; [exact ST|]. unfold SLOT_STACK in *; lia.
    + change (bv_unsigned (reg_get (ss_regs E) 2)) with (spZ (ss_regs E)). unfold SLOT_STACK in *; lia.
    + unfold SLOT_STACK in *; lia.
    + apply mem_inv_normalize.
    + lia.
    + exact WC.
    + exact WN.
    + exact WMX.
    + exact WB.
    + exact WG.
    + exact WD.
    + exact WE.
  - intros ms (m' & junk & -> & _). do 3 eexists. reflexivity.
  - intros R pc m0 regs' mem' (m' & junk & EQ & MU & WM & MI & FR & WC & WN & WMX & WB & WG & WD & WE) GR MREL ROS.
    injection EQ as ER EP EM. subst R pc m0.
    change (bv_unsigned (reg_get (ss_regs E) 2)) with (spZ (ss_regs E)) in MU, FR.
    assert (WR : forall a, ~ outside (entry_frame_writes (spZ (ss_regs E))) a ->
      spZ (ss_regs E) - 192 <= a < spZ (ss_regs E) \/ in_globals G_reply a).
    { intros a HOUT. apply hg_not_out in HOUT as (lo & hi & HL' & HA).
      unfold entry_frame_writes, entry_writes in HL'. cbn [tl] in HL'.
      destruct HL' as [EQ|[EQ|[EQ|[EQ|[EQ|[EQ|[EQ|[EQ|[]]]]]]]]]; injection EQ as <- <-.
      all: first [left; exact HA |
        right; exists 0x21620, 16; split; [left; reflexivity|lia] |
        right; exists 0x318a0, 512; split; [right; left; reflexivity|lia]]. }
    destruct (rmid_norm B (API rc) SLOT_STACK (spZ (ss_regs E)) (in_globals G_reply) (fun _ => False)
      (ss_L E) (ss_A E) (ss_mem E) (ss_md E) m' mem' (entry_frame_writes (spZ (ss_regs E)))
      SEG RO MREL ROS MU WM HM HW HB ltac:(lia)) as (RM & MUR & WMR).
    { unfold sk. intros a [Ha|Ha]; [apply WST; exact Ha|apply WERR; exact Ha]. }
    { intros a HA HOUT. destruct (WR a HOUT); [left; unfold SLOT_STACK; lia|right; assumption]. }
    { intros a HA.
      assert (OD : forall W x, outside W x \/ ~ outside W x).
      { clear. induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
        destruct (IH x) as [H|H]; [|right; tauto].
        destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi); [right; lia | left; split; [lia|exact H] ..]. }
      destruct (OD (entry_frame_writes (spZ (ss_regs E))) a) as [HOUT|HOUT]; [exact HOUT|exfalso].
      destruct (WR a HOUT) as [HS|HG].
      - pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HM HA). unfold SLOT_STACK in *; lia.
      - destruct (PL a HG) as (HI & HSTATIC & HCTX & _). destruct HA as [HA|HA]; [|tauto].
        apply HCTX. exact (ax_img AX _ _ _ _ a HM HI HA). }
    { intros q n i HQ HI HOUT. exfalso. destruct (WR _ HOUT) as [HS|HG].
      - destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ q n i HM HQ HI) as (_ & H1 & H2 & _).
        unfold SLOT_STACK in *; lia.
      - exact (ax_blocks_img AX _ _ _ _ q n i HM HQ HI (proj1 (PL _ HG))). }
    apply SR_ret. exists regs', mem', junk. split; [rewrite SEG; reflexivity|].
    split; [exact RM|]. split; [rewrite SEG; exact (ro_agree_same rsegs _ _ RO ROS)|].
    split; [exact MUR|]. split; [rewrite SEG; exact WMR|]. split.
    { unfold entry_call_regs. do 5 (split; [rewrite GR; reflexivity|]).
      split; [rewrite GR; exact RP|]. rewrite GR. reflexivity. }
    rewrite SEG. split.
    { unfold slot_sp, SLOT_FRAME.
      eapply rw_cells_of_rel; [exact MREL|exact FR]. }
    repeat (split; [eapply rw_cells_of_rel; [exact MREL|eassumption]|]).
    eapply rw_cells_of_rel; [exact MREL|exact WE].
Qed.

Lemma entry_call_pre : forall CS B API LS SH SK ra empty rc fx j E regs mem,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  rmid B (API rc) SLOT_STACK (spZ (ss_regs E)) (in_globals G_reply) (fun _ => False)
    (ss_L E) (ss_A E) (ss_mem E) (ss_md E) (ss_L E) (ss_A E) mem (ss_md E) ->
  entry_call_regs E regs ->
  call_pre_k (rc := rc) B (aa_MR (API rc)) OP_ADD_K (ss_L E) (ss_A E) regs mem (ss_md E).
Proof.
  intros CS B API LS SH SK ra empty rc fx j E regs mem (_ & _ & HP & _) RM
    (R1 & R2 & R3 & R4 & R9 & R18 & R20).
  destruct HP as ((PRE & _) & _).
  destruct PRE as (HM & HW & HB & INIT & RA & ALIGN & SPLO & SPHI & WST & TP & WERR & _).
  assert (REGSP : spZ regs = slot_sp E).
  { unfold spZ. rewrite R2. apply unsigned_lit. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *.
    pose proof (@alloc_ceiling_value rc). lia. }
  assert (SCR : forall a, sk B SLOT_STACK (spZ (ss_regs E)) a -> writable_at (ms_segs B) mem a)
    by (unfold rmid in RM; tauto).
  unfold call_pre_k. split; [unfold rmid in RM; tauto|]. split; [exact HW|]. split; [exact HB|].
  split; [rewrite R1; apply ret_ok_even; vm_compute; reflexivity|].
  rewrite REGSP. split.
  { unfold slot_sp, SLOT_FRAME. Z.div_mod_to_equations. lia. }
  split; [change OP_ADD_K with 8352; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|].
  split; [unfold slot_sp, SLOT_FRAME; lia|].
  split.
  { intros a HA. apply SCR. left. change OP_ADD_K with 8352 in HA. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia. }
  split; [rewrite R4; exact TP|]. split; [intros a HA; apply SCR; right; exact HA|].
  rewrite INIT. discriminate.
Qed.

Definition entry_fixed_cells (m : word -> option byte) : Prop :=
  rw_cells rsegs m G_THREAD_UP [C1 (Z_to_bv 8 0)] /\
  rw_cells rsegs m G_WAKE0 [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
  rw_cells rsegs m G_NSRC [C4 (Z_to_bv 64 0)] /\
  rw_cells rsegs m G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 28 (nulbytes 28)] /\
  (forall i, (i < 4)%nat -> rw_cells rsegs m (G_S + SRC_SIZE * Z.of_nat i) [CB 96 (nulbytes 96)]).

Lemma entry_fixed_of_GI : forall j m, GI_reply j m -> entry_fixed_cells m.
Proof.
  intros j m (DATA & THREAD & NSRC & LOCK & SOURCES).
  assert (RD : forall a v k, 0x21620 <= a -> a + Z.of_nat k <= 0x21630 ->
    byte_at m a v (Z.of_nat k) -> rw_cells rsegs m a [CB k (repeat (Z_to_bv 8 v) k)]).
  { intros a v k HA HE HB. apply entry_byte_cells; try lia; [|exact HB].
    intros i HI. exists 0x21620, 16. split; [left; reflexivity|lia]. }
  assert (RG : forall a v k, 0x318a0 <= a -> a + Z.of_nat k <= 0x31aa0 ->
    byte_at m a v (Z.of_nat k) -> rw_cells rsegs m a [CB k (repeat (Z_to_bv 8 v) k)]).
  { intros a v k HA HE HB. apply entry_byte_cells; try lia; [|exact HB].
    intros i HI. exists 0x318a0, 512. split; [right; left; reflexivity|lia]. }
  unfold entry_fixed_cells. split.
  - eapply rw_cells_retype with (cs := [CB 1 (repeat (Z_to_bv 8 0) 1)]).
    + apply RG; [unfold G_THREAD_UP; lia|unfold G_THREAD_UP; cbn; lia|exact THREAD].
    + cbn; tauto.
    + reflexivity.
  - split.
    + eapply rw_cells_retype with (cs := [CB 8 (repeat (Z_to_bv 8 255) 8)]).
      * apply RD; [unfold G_WAKE0; lia|unfold G_WAKE0; cbn; lia|].
        intros i HI. replace (G_WAKE0 + i) with (G_DATA + (8 + i)) by (unfold G_WAKE0, G_DATA; lia).
        apply DATA. cbn in HI. lia.
      * cbn; tauto.
      * vm_compute. repeat (apply f_equal2; [apply bv_eq; reflexivity|]). reflexivity.
    + split.
      * eapply rw_cells_retype with (cs := [CB 4 (repeat (Z_to_bv 8 0) 4)]).
        -- apply RG; [unfold G_NSRC; lia|unfold G_NSRC; cbn; lia|exact NSRC].
        -- cbn; tauto.
        -- reflexivity.
      * split.
        -- eapply rw_cells_retype with (cs := [CB 40 (repeat (Z_to_bv 8 0) 40)]).
           ++ apply RG; [unfold G_LOCK; lia|unfold G_LOCK; cbn; lia|exact LOCK].
           ++ cbn; tauto.
           ++ reflexivity.
        -- intros i HI. apply RG; unfold G_S, SRC_SIZE; try lia.
           intros k HK. replace (203040 + 96 * Z.of_nat i + k) with (Statement.G_S + (96 * Z.of_nat i + k))
             by (unfold Statement.G_S; lia).
           apply SOURCES. cbn in HK. lia.
Qed.

Lemma entry_head_step : forall CS B API LS SH SK ra empty rc fx j E L A regs mem md junk,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> 0 <= ss_n E < INPUT_MAX ->
  aa_MR (API rc) L A mem md -> WF A -> bounded A -> ro_agree (ms_segs B) mem ->
  (forall a, sk B SLOT_STACK (spZ (ss_regs E)) a -> writable_at (ms_segs B) mem a) ->
  YK11.getr regs 2 = Z_to_bv 64 (slot_sp E) ->
  YK11.getr regs 3 = YK11.getr (ss_regs E) 3 -> YK11.getr regs 4 = YK11.getr (ss_regs E) 4 ->
  YK11.getr regs 9 = Z_to_bv 64 (ss_n E) -> YK11.getr regs 18 = Z_to_bv 64 (ss_p E) ->
  YK11.getr regs 20 = Z_to_bv 64 G_RELAY_LO ->
  rw_cells (ms_segs B) mem (slot_sp E + 8) [CB 8 junk] ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x14118) mem (seg_rom (ms_segs B))) md)
    (fun c => exists regs' mem',
      c = mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (head_pc E 0 0)) mem' (seg_rom (ms_segs B))) md /\
      rmid B (API rc) SLOT_STACK (spZ (ss_regs E)) (fun _ => False) (fun _ => False) L A mem md L A mem' md /\
      ro_agree (ms_segs B) mem' /\ head_regs E 0 0 regs' /\
      munch [(slot_sp E + 8, slot_sp E + 16)] mem mem' /\ wmono (ms_segs B) mem mem' /\
      (0 < ss_n E -> rw_cells (ms_segs B) mem' (slot_sp E + 8) [C8 (Z_to_bv 64 G_S)])).
Proof.
  intros CS B API LS SH SK ra empty rc fx j E L A regs mem md junk (FF & _ & HP & _)
    HN HM HW HB RO SCR R2 R3 R4 R9 R18 R20 SLOT.
  destruct HP as (((_ & _ & _ & _ & _ & _ & SPLO & SPHI & _) & _) & _).
  assert (SEG : ms_segs B = rsegs) by (unfold frame_facts in FF; tauto).
  pose proof (@alloc_ceiling_value rc) as AC. pose proof (@alloc_ceiling_lt rc) as ACL.
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HM) as (HH & HL & HMAT).
  rewrite SEG in RO, SLOT |- *.
  pose proof (rw_cells_normalize rsegs mem _ _ RO SLOT ltac:(
    intros i HI; cbn in HI; apply ro_addr_hi; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia)) as SLOT0.
  eapply (kseg regs (Z_to_bv 64 0x14118) mem md);
    [exact wx_apart_rsegs|exact RO|exact HH|exact HL| | |].
  - unfold Regs6ss.mkR_of. eapply entry_head_run with (b := slot_sp E) (p := ss_p E) (n := ss_n E).
    + exact R2.
    + exact R9.
    + exact R18.
    + exact R20.
    + unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia.
    + unfold slot_sp, SLOT_FRAME; lia.
    + exact HN.
    + apply mem_inv_normalize.
    + exact SLOT0.
  - intros ms (R & m' & -> & _). do 3 eexists. reflexivity.
  - intros R pc m0 regs' mem' (Rg & m' & EQ & MU & WM & MI & REG & SLOT') GR MREL ROS.
    injection EQ as ER EP EM. subst R pc m0.
    destruct (rmid_norm B (API rc) SLOT_STACK (spZ (ss_regs E)) (fun _ => False) (fun _ => False)
      L A mem md m' mem' [(slot_sp E + 8, slot_sp E + 16)] SEG RO MREL ROS MU WM HM HW HB ltac:(lia) SCR)
      as (RM & MUR & WMR).
    { intros a HA HOUT. destruct (hg_not_out _ _ HOUT) as (lo & hi & [EQ|[]] & HX). injection EQ as <- <-.
      left. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia. }
    { intros a HA. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HM HA).
      apply hg_out. intros lo hi [EQ|[]]. injection EQ as <- <-. left. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia. }
    { intros q n i HQ HI HOUT. destruct (hg_not_out _ _ HOUT) as (lo & hi & [EQ|[]] & HX). injection EQ as <- <-.
      destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ q n i HM HQ HI) as (_ & H1 & H2 & _).
      unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia. }
    apply SR_ret. exists regs', mem'. split; [rewrite ?SEG, <- entry_head_pc; reflexivity|].
    split; [exact RM|]. split; [rewrite ?SEG; exact (ro_agree_same rsegs _ _ RO ROS)|].
    split.
    { eapply entry_head_regs_bridge; [|exact GR].
      change (reg_get regs 3) with (YK11.getr regs 3) in REG.
      change (reg_get regs 4) with (YK11.getr regs 4) in REG. rewrite R3, R4 in REG. exact REG. }
    split; [exact MUR|]. split; [rewrite ?SEG; exact WMR|].
    intros HPOS. rewrite ?SEG. eapply rw_cells_of_rel; [exact MREL|apply SLOT'; exact HPOS].
Qed.

Definition entry_modified (C G a : Z) : Prop :=
  in_globals G_reply a \/ (C = 16 /\ G <= a < G + SRC_ENTRY).

Lemma entry_image_kept : forall CS B API LS SH SK ra empty rc fx j E C G L A mem md,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  (C = 16 -> fresh_block (rc := rc) B G SRC_TABLE) ->
  rmid B (API rc) SLOT_STACK (spZ (ss_regs E)) (entry_modified C G) (fun _ => False)
    (ss_L E) (ss_A E) (ss_mem E) (ss_md E) L A mem md ->
  image_kept (rc := rc) B E mem.
Proof.
  intros CS B API LS SH SK ra empty rc fx j E C G L A mem md (FF & _ & HP & _) GF RM.
  destruct HP as ((PRE & _) & _).
  destruct PRE as (HM & HW & HB & INIT & RA & ALIGN & SPLO & SPHI & _).
  assert (SEG : ms_segs B = rsegs) by (unfold frame_facts in FF; tauto).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall rc fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL rc fx). }
  assert (AX : AllocExtra B (aa_MR (API rc))) by (unfold frame_allocator in FA; tauto).
  pose proof RM as (HM' & HW' & HB' & LY & LEN & ADDR & KEEP & ZKEEP & OWN & VM & MUP & MB & SCR).
  assert (NOWN : forall L0 A0 m0 md0 a, aa_MR (API rc) L0 A0 m0 md0 -> img_plain B a -> ~ owned B L0 A0 a).
  { intros L0 A0 m0 md0 a HM0 (HI & HS & HC & HE) [HO|HO]; [|tauto].
    apply HC. exact (ax_img AX _ _ _ _ a HM0 HI HO). }
  assert (NIMG : forall a, in_img B a -> ~ in_globals G_reply a -> ~ entry_modified C G a).
  { intros a HI NG [HG|[HC HG]]; [tauto|]. destruct (GF HC) as (_ & _ & NX).
    apply (NX (a - G) ltac:(unfold SRC_ENTRY, SRC_TABLE; lia)). replace (G + (a - G)) with a by lia. exact HI. }
  unfold image_kept. split.
  - intros a HI HS HC HE NG. apply MUP.
    + right; exact HI.
    + apply (NOWN _ _ _ _ a HM). exact (conj HI (conj HS (conj HC HE))).
    + apply (NOWN _ _ _ _ a HM'). exact (conj HI (conj HS (conj HC HE))).
    + unfold sk. pose proof (hg_img_low B SEG a HI). lia.
    + apply NIMG; assumption.
  - split.
    + intros a HG. rewrite SEG. split; intros _; exact (proj1 (entry_global_access _ a HG)).
    + split; [|exact SCR].
      intros a HA NS. apply MUP.
      * left; exact HA.
      * intros HO. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HM HO). lia.
      * intros HO. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HM' HO). lia.
      * exact NS.
      * intros [HG|[HC HG]].
        -- destruct (entry_global_image a HG) as [W _].
           unfold in_globals, G_reply, frame_G in HG.
           destruct HG as (lo & len & [EQ|[EQ|[]]] & HX); injection EQ as <- <-;
             pose proof (@alloc_ceiling_value rc); lia.
        -- destruct (GF HC) as (_ & HE & _). unfold SRC_TABLE, SRC_ENTRY in *; lia.
Qed.

Definition entry_untouched (a : Z) : Prop :=
  0x21620 <= a < 0x21624 \/ 0x21628 <= a < 0x21630 \/ 0x318a0 <= a < 0x318a4 \/
  0x318b1 <= a < 0x318c0 \/ 0x318c4 <= a < 0x318d8 \/ 0x318e0 <= a < 0x31aa0.

Lemma entry_disjoint_pts : forall W a n,
  Forall (fun iv => fst iv < snd iv) W -> 0 < n ->
  (forall x, a <= x < a + n -> outside W x) -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW HN H; cbn; [exact I|].
  inversion HW as [|? ? HLT HW']; subst. cbn in HLT.
  split.
  - destruct (Z_le_gt_dec (a + n) lo) as [L1|L1]; [left; exact L1|].
    destruct (Z_le_gt_dec hi a) as [L2|L2]; [right; exact L2|].
    exfalso. destruct (H (Z.max a lo) ltac:(lia)) as [N _]. apply N. lia.
  - apply IH; [exact HW'|exact HN|]. intros x Hx. exact (proj2 (H x Hx)).
Qed.

Lemma entry_untouched_rw : forall m m' sp a cs,
  0x100000 <= sp - 192 ->
  munch (entry_frame_writes sp) m m' -> wmono rsegs m m' -> rw_cells rsegs m a cs ->
  0 < Z.of_nat (cells_size cs) ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> entry_untouched (a + i)) ->
  rw_cells rsegs m' a cs.
Proof.
  intros m m' sp a cs HS MU WM RW HP HT.
  eapply rw_cells_transport; [exact RW|exact MU|exact WM|].
  apply entry_disjoint_pts; [|lia|].
  { unfold entry_frame_writes, entry_writes. cbn [tl].
    repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
  intros x HX. apply hg_out. intros lo hi HIN.
  specialize (HT (x - a) ltac:(lia)). replace (a + (x - a)) with x in HT by lia.
  unfold entry_frame_writes, entry_writes in HIN. cbn [tl] in HIN.
  destruct HIN as [EQ|[EQ|[EQ|[EQ|[EQ|[EQ|[EQ|[EQ|[]]]]]]]]]; injection EQ as <- <-;
    unfold entry_untouched in HT; lia.
Qed.

Lemma entry_fixed_preserved : forall m m' sp,
  0x100000 <= sp - 192 -> munch (entry_frame_writes sp) m m' -> wmono rsegs m m' ->
  entry_fixed_cells m -> entry_fixed_cells m'.
Proof.
  intros m m' sp HS MU WM (THREAD & WAKE & NSRC & LOCK & SOURCES).
  unfold entry_fixed_cells. split.
  - eapply entry_untouched_rw; [exact HS|exact MU|exact WM|exact THREAD|cbn; lia|].
    intros k HK. cbn in HK. unfold entry_untouched, G_THREAD_UP. lia.
  - split.
    + eapply entry_untouched_rw; [exact HS|exact MU|exact WM|exact WAKE|cbn; lia|].
      intros k HK. cbn in HK. unfold entry_untouched, G_WAKE0. lia.
    + split.
      * eapply entry_untouched_rw; [exact HS|exact MU|exact WM|exact NSRC|cbn; lia|].
        intros k HK. cbn in HK. unfold entry_untouched, G_NSRC. lia.
      * split.
        -- eapply entry_untouched_rw; [exact HS|exact MU|exact WM|exact LOCK|cbn; lia|].
           intros k HK. cbn in HK. unfold entry_untouched, G_LOCK. lia.
        -- intros i HI. eapply entry_untouched_rw; [exact HS|exact MU|exact WM|apply SOURCES; exact HI|cbn; lia|].
           intros k HK. cbn in HK. unfold entry_untouched, G_S, SRC_SIZE. lia.
Qed.

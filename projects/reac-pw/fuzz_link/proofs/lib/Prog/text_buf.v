(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths and module names changed; 261 of its 292 lines of code are new or changed and 804 lines of the source are left out. *)
(* text_buf (fuzz_link.c:655-666), PLAIN build: the proof of text_buf_contract
   (lib/Prog/text_buf_c.v) on the plain image, in the SR form of the released allocator-facing
   walks (form: libreac/fuzz_pcap lib/Prog/fmemopen.v at origin/ossv/recipes 4b6f0df50aa).
   The instruction pieces are lib/Prog/text_buf_walk.v. The malloc call goes through the frame's
   malloc contract (Contract.malloc_contract); memset is a tail call, through memset_contract.
   cap = 0: no allocation, a0 = 0. cap <> 0: malloc(cap+1), whose answer is not NULL by the malloc
   contract (room_slots b (cap+1)), so the abort at +0x48 is not reached; then memset(p, 0x5a, cap+1).
   Section hypotheses: the malloc entry and the errno address of the image's allocator symbols
   (the released pin form; the errno pin keeps malloc's errno scratch off text_buf's saved
   registers), malloc_contract, memset_contract. text_buf_holds_closed instantiates memset with
   memset_holds (lib/Prog/memset.v); text_buf_holds_src0 discharges the pins at YH02.src0_msyms. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i YL01 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YH02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 MemNorm Contract KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memset_c memset hp_tb_kit text_buf_walk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require link_spec link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import text_buf_c.
Import ListNotations.
Open Scope Z_scope.

Lemma tb_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* the reading of a register through an equivalent map, stated with this file's `getr` *)
Lemma tb_getr_here : forall M R (r : bv 5), Regs6ss.xregs_eqv M R -> bv_eqb r 0 = false -> getr R r = reg_get M r.
Proof. intros M R r H NZ. unfold getr. rewrite NZ. symmetry. apply H. exact NZ. Qed.

Section F.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC_PC : ms_malloc B = 0x17514.
Hypothesis TP_PIN : ms_tp B = 0x75608.
Hypothesis ERRNO_PIN : ms_errno_off B = -164.
Hypothesis MALLOC : malloc_contract B API.

Section M.
Hypothesis MEMSET : memset_contract.

Theorem text_buf_holds : text_buf_contract B API.
Proof.
  unfold text_buf_contract.
  intros L A regs mem md b cap SEGS PRE RO A0 CAP RES ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof MALLOC as MAL. unfold malloc_contract in MAL. rewrite SEGS, MALLOC_PC in MAL.
  assert (IL : img_low B).
  { eapply img_low_of_check with (C := 2 ^ 21); [unfold img_check; rewrite SEGS; vm_compute; reflexivity | lia]. }
  assert (ERR : errno_addr B = 0x75564) by (unfold errno_addr; rewrite TP_PIN, ERRNO_PIN; reflexivity).
  unfold TEXT_BUF_K in *. change (16 + ALLOC_STACK) with 8208 in *.
  pose proof PRE as PRE0.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  rewrite SEGS in RO.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8208) (bv_unsigned sp)).
  { pose proof (kb_stk B API IL 8208 L A regs mem md PRE0 ltac:(lia)) as X. rewrite SEGS in X. exact X. }
  assert (RN0 : mem_rel rsegs mem (normalize rsegs mem)) by (apply mem_rel_normalize; exact RO).
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (kb_ret_pc _ HRA).
  assert (OUT1 : forall x, ~ (bv_unsigned sp - 16 <= x < bv_unsigned sp) ->
            Frame.outside [(bv_unsigned sp - 16, bv_unsigned sp)] x) by (intros x Hx; cbn; split; [exact Hx | exact I]).
  rewrite SEGS.
  destruct (Z.eq_dec cap 0) as [C0|C0].
  - (* cap = 0: no allocation, the answer is NULL *)
    subst cap.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 0) by exact A0.
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite tb_canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold TEXT_BUF.
      apply (evt_normalize rsegs); [exact tb_wx | exact RO |].
      eapply text_buf_zero with (lo := bv_unsigned sp - 8208);
        [ exact R10 | apply tb_stk_normalize; [exact ST | lia] | lia | apply mem_inv_normalize ]. }
    intros ms1 (can1 & (s1 & Q1 & REL1 & ROS1) & EQ1).
    destruct Q1 as (sp1 & m1n & -> & SP1 & MU1n & WM1n & MI1n & ST1n).
    destruct (tb_ms_rel_MS _ _ _ _ _ _ _ _ _ REL1) as [CAN1 HR1].
    remember (ms_mem can1) as m1 eqn:Em1. subst can1. clear Em1.
    pose proof (munch_rel rsegs _ _ _ _ _ RN0 HR1 ROS1 MU1n) as MU1.
    pose proof (wmono_rel rsegs _ _ _ _ RN0 HR1 ROS1 WM1n) as WM1.
    pose proof (ro_agree_same rsegs _ _ RO ROS1) as RO1.
    destruct (tb_eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (SPE : sp1 = sp) by (apply bv_eq; exact SP1). subst sp1.
    assert (X1' : Regs6ss.xregs_eqv (Regs6ss.mkR_of regs) R1) by exact X1.
    assert (G1 : forall r, getr R1 r = getr regs r).
    { intros r. rewrite (kb_getr_eqv _ _ X1' r). apply kb_getr_eqv. exact (Regs6ss.mkR_of_eqv regs). }
    rewrite RP.
    apply SR_ret.
    exists L, A, R1, m1, md.
    split; [reflexivity|].
    split.
    { apply (kb_post B API).
      - change (spZ regs) with (bv_unsigned sp).
        eapply (kb_mid_A B API IL) with (W := [(bv_unsigned sp - 16, bv_unsigned sp)]);
          [ exact HMR | exact HWF | exact HBD | | exact MU1 | rewrite SEGS; exact WM1 | | ].
        + intros a [Ha|Ha]; [apply HWS; lia | apply HERR; exact Ha].
        + intros x _ Hs _. apply OUT1. lia.
        + intros x Hx _. apply OUT1. lia.
      - intros r Hr. exact (G1 (Z_to_bv 5 r)). }
    split; [exact RO1|].
    split.
    { intros _. split; [rewrite G1; exact A0|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | exact RES]. }
    intros C. exfalso. apply C. reflexivity.
  - (* cap <> 0: malloc(cap + 1), then the tail call memset(p, 0x5a, cap + 1) *)
    assert (R10 : bv_unsigned (reg_get regs 10) = cap).
    { pose proof (f_equal bv_unsigned A0) as E. rewrite unsigned_lit in E by lia. exact E. }
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite tb_canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold TEXT_BUF.
      apply (evt_normalize rsegs); [exact tb_wx | exact RO |].
      eapply text_buf_pro with (lo := bv_unsigned sp - 8208);
        [ exact R10 | lia | apply tb_stk_normalize; [exact ST | lia] | lia | apply mem_inv_normalize ]. }
    intros ms1 (can1 & (s1 & Q1 & REL1 & ROS1) & EQ1).
    destruct Q1 as (sp1 & s01 & a01 & m1n & -> & SP1 & ES0 & EA0 & FR1n & MU1n & WM1n & MI1n & ST1n).
    destruct (tb_ms_rel_MS _ _ _ _ _ _ _ _ _ REL1) as [CAN1 HR1].
    remember (ms_mem can1) as m1 eqn:Em1. subst can1. clear Em1.
    pose proof (munch_rel rsegs _ _ _ _ _ RN0 HR1 ROS1 MU1n) as MU1.
    pose proof (wmono_rel rsegs _ _ _ _ RN0 HR1 ROS1 WM1n) as WM1.
    pose proof (ro_agree_same rsegs _ _ RO ROS1) as RO1.
    pose proof (tb_rw_cells_of_rel rsegs _ _ _ _ HR1 FR1n) as FR1.
    destruct (tb_eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x14fcc) by (rewrite (tb_getr_here _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_2 : getr R1 2 = sp1) by (rewrite (tb_getr_here _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (tb_getr_here _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_8 : getr R1 8 = Z_to_bv 64 (cap + 1)) by (rewrite (tb_getr_here _ _ 8 X1 eq_refl); simp_regs; exact ES0).
    assert (E1_10 : getr R1 10 = Z_to_bv 64 (cap + 1)) by (rewrite (tb_getr_here _ _ 10 X1 eq_refl); simp_regs; exact EA0).
    assert (SPZ1 : spZ R1 = bv_unsigned sp - 16) by (unfold spZ; rewrite <- SP1; f_equal; exact E1_2).
    assert (MID1 : kb_mid B API 8208 (bv_unsigned sp) L A mem md (fun _ => False) L A m1 md).
    { eapply (kb_mid_A B API IL) with (W := [(bv_unsigned sp - 16, bv_unsigned sp)]);
        [ exact HMR | exact HWF | exact HBD | | exact MU1 | rewrite SEGS; exact WM1 | | ].
      - intros a [Ha|Ha]; [apply HWS; lia | apply HERR; exact Ha].
      - intros x _ Hs _. apply OUT1. lia.
      - intros x Hx _. apply OUT1. lia. }
    assert (CP1 : call_pre B (aa_MR API) L A R1 m1 md).
    { apply call_pre_k_alloc.
      eapply (kb_pre_A B API) with (K := 8208) (f := 16) (W := [(bv_unsigned sp - 16, bv_unsigned sp)]);
        [ exact PRE0 | lia | change ALLOC_STACK with 8192; lia | change ALLOC_STACK with 8192; lia
        | rewrite SPZ1; reflexivity | | exact E1_4 | | exact MU1 | rewrite SEGS; exact WM1 | | ].
      - rewrite SPZ1. replace (bv_unsigned sp - 16) with (bv_unsigned sp + (-1) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      - lazymatch goal with |- YK0s.ret_ok ?x => replace x with (Z_to_bv 64 0x14fcc) by (symmetry; exact E1_1) end.
        apply bv_eq. vm_compute. reflexivity.
      - intros x _ Hx. change (spZ regs) with (bv_unsigned sp) in Hx. apply OUT1. lia.
      - intros x Hx _. apply OUT1. lia. }
    eapply SR_bind.
    { eapply (MAL L A R1 m1 md (cap + 1) b); [exact CP1 | exact RO1 | exact E1_10 | exact RES | exact ROOM]. }
    intros c2 RET.
    destruct RET as (L' & A' & R2 & m2 & md2 & h & -> & POST & A0' & NZ & AL & FRESH & BLK & KEPT & RO2 & GK & UBK
      & INIT & RLEN & RES').
    try rewrite SEGS in RO2.
    destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ POST) as [MIDm HPRES].
    pose proof POST as (HMR' & HWF' & HBD' & HLE & HSTAB & _ & HVM & HFRAME & HBLKS & HSCR).
    destruct (mr_model _ _ LAWS _ _ _ _ HMR') as (Hh2 & Hl2 & Hmat2).
    destruct BLK as (b1 & b2 & BLK1 & BLK2).
    pose proof FRESH as (FR_lo & FR_hi & FR_img).
    rewrite SPZ1 in MIDm.
    assert (MID2 : kb_mid B API 8208 (bv_unsigned sp) L A mem md (fun a => False \/ False) L' A' m2 md2).
    { eapply (kb_mid_seqAX B API); [exact MID1 | exact MIDm | change ALLOC_STACK with 8192; lia | lia | lia | lia |].
      intros a _ _ F. exact F. }
    assert (NOWN : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
    { intros a Ha. split; intros Ho;
        [pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ HMR Ho) | pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ HMR' Ho)]; lia. }
    assert (HI2 : forall a, bv_unsigned sp - 16 <= a < 2 ^ 64 ->
       mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
       (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
    { intros a Ha. destruct (NOWN a ltac:(lia)) as [N1 N2].
      apply HFRAME; [left; lia | exact N1 | exact N2 | | intros F; exact F].
      unfold scratch_k. rewrite SPZ1, ERR. change ALLOC_STACK with 8192. intros [H|H]; lia. }
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 16) [C8 (reg_get regs 8); C8 (reg_get regs 1)]).
    { apply (tb_rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
      destruct (HI2 (bv_unsigned sp - 16 + i) ltac:(lia)) as [E W]. split; [exact E | apply W]. }
    assert (ST2 : stk rsegs m2 (bv_unsigned sp - 8208) (bv_unsigned sp - 16)).
    { split; [lia|]. split; [lia|]. intros a Ha.
      assert (W : writable_at rsegs m2 a).
      { rewrite <- SEGS. apply HSCR. unfold scratch_k. rewrite SPZ1. change ALLOC_STACK with 8192. left. lia. }
      split; [exact W|].
      destruct (tb_writable_hi_present m2 a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
    assert (INH : In (h, cap + 1) (blocks L' A')) by (rewrite BLK1; apply in_or_app; right; left; reflexivity).
    destruct (tb_present_rw_cells rsegs m2 h (Z.to_nat (cap + 1))) as [junk DST]; [lia | lia | |].
    { intros i Hi. exact (proj1 (tb_block_facts B _ LAWS _ _ _ _ _ _ i HMR' INH ltac:(lia))). }
    assert (E2_2 : reg_get R2 2 = sp1) by exact (eq_trans (HPRES 2 ltac:(unfold callee_saved; lia)) E1_2).
    assert (E2_8 : reg_get R2 8 = Z_to_bv 64 (cap + 1)) by exact (eq_trans (HPRES 8 ltac:(unfold callee_saved; lia)) E1_8).
    assert (E2_10 : reg_get R2 10 = Z_to_bv 64 h) by exact A0'.
    lazymatch goal with |- SR _ (mkCfg (?MK R2 ?pc m2 ?ro) _) _ =>
      replace pc with (Z_to_bv 64 0x14fcc) by (symmetry; exact E1_1) end.
    eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
    { rewrite tb_canon_mkst. unfold Regs6ss.mkR_of. rewrite SEGS, E2_2.
      apply (evt_normalize rsegs); [exact tb_wx | exact RO2 |].
      eapply (text_buf_tail MEMSET) with (lo := bv_unsigned sp - 8208) (h := h) (cap := cap) (junk := junk);
        [ exact E2_10 | lia | exact E2_8 | lia
        | apply tb_rw_cells_normalize; [exact RO2 | exact DST | ]
        | rewrite SP1; apply tb_rw_cells_normalize; [exact RO2 | exact FR2 | ]
        | rewrite SP1; apply tb_stk_normalize; [exact ST2 | lia]
        | rewrite SP1; lia | rewrite SP1; lia | lia | apply mem_inv_normalize ].
      - intros i Hi. cbn [cells_size csize] in Hi. apply (tb_ro_addr_out B SEGS); [lia | apply FR_img; lia].
      - intros i Hi. cbn in Hi. apply tb_ro_addr_hi. lia. }
    intros ms3 (can3 & (s3 & Q3 & REL3 & ROS3) & EQ3).
    destruct Q3 as (sp3 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3n
      & -> & SP3 & MU3n & WM3n & MI3n & ST3n & BUF3n).
    destruct (tb_ms_rel_MS _ _ _ _ _ _ _ _ _ REL3) as [CAN3 HR3].
    remember (ms_mem can3) as m3 eqn:Em3. subst can3. clear Em3.
    assert (RN2 : mem_rel rsegs m2 (normalize rsegs m2)) by (apply mem_rel_normalize; exact RO2).
    pose proof (munch_rel rsegs _ _ _ _ _ RN2 HR3 ROS3 MU3n) as MU3.
    pose proof (wmono_rel rsegs _ _ _ _ RN2 HR3 ROS3 WM3n) as WM3.
    pose proof (ro_agree_same rsegs _ _ RO2 ROS3) as RO3.
    pose proof (tb_rw_cells_of_rel rsegs _ _ _ _ HR3 BUF3n) as BUF3.
    destruct (tb_eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    rewrite SP1 in MU3, ST3n.
    assert (SPE : sp3 = sp) by (apply bv_eq; rewrite SP3, SP1; ring). subst sp3.
    assert (PRES3 : forall x, m2 x <> None -> m3 x <> None).
    { intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx.
      destruct (kb_outside_dec [(bv_unsigned sp - 16, bv_unsigned sp - 16 + 16); (h, h + cap + 1)] (bv_unsigned x))
        as [Ho|Ho].
      - rewrite (MU3 x Ho). exact Hx.
      - rewrite <- (Z_to_bv_bv_unsigned x).
        assert (Hin : (bv_unsigned sp - 16 <= bv_unsigned x < bv_unsigned sp) \/ (h <= bv_unsigned x < h + cap + 1)).
        { cbn [Frame.outside] in Ho. lia. }
        destruct Hin as [Hs|Hb].
        + destruct ST3n as (_ & _ & ST3f).
          destruct (ST3f (bv_unsigned x) ltac:(lia)) as [Wv _].
          destruct (tb_writable_hi_present _ (bv_unsigned x) ltac:(lia) Wv) as [bb Eb].
          rewrite (mem_rel_rw rsegs m3 m3n (Z_to_bv 64 (bv_unsigned x)) HR3
                     (tb_ro_addr_hi (bv_unsigned x) ltac:(lia))) in Eb.
          rewrite Eb. discriminate.
        + pose proof BUF3 as (_ & (_ & _ & Hw)).
          specialize (Hw (bv_unsigned x - h) ltac:(cbn [cells_size csize]; lia)).
          replace (h + (bv_unsigned x - h)) with (bv_unsigned x) in Hw by ring.
          assert (NI : ~ in_img B (bv_unsigned x)).
          { replace (bv_unsigned x) with (h + (bv_unsigned x - h)) by ring. apply FR_img. lia. }
          destruct (tb_present_of_writable_out B SEGS m3 (bv_unsigned x) ltac:(lia) NI Hw) as [bb Eb].
          rewrite Eb. discriminate. }
    assert (MID3 : kb_mid B API 8208 (bv_unsigned sp) L A mem md
                     (fun a => (False \/ False) \/ (h <= a < h + cap + 1)) L' A' m3 md2).
    { eapply (kb_mid_tail B API IL) with (W := [(bv_unsigned sp - 16, bv_unsigned sp - 16 + 16); (h, h + cap + 1)]);
        [ exact MID2 | exact MU3 | rewrite SEGS; exact WM3 | exact PRES3 | | | ].
      - intros x Hx Hs Hw. cbv beta in Hw. cbn [Frame.outside]. split; [lia|]. split; [lia | exact I].
      - intros x Hx Ho. cbn [Frame.outside]. split; [lia|]. split; [|exact I].
        intros Hin. apply (proj2 (proj2 (proj2 (tb_block_facts B _ LAWS _ _ _ _ _ _ (x - h) HMR' INH ltac:(lia))))).
        replace (h + (x - h)) with x by ring. exact Ho.
      - intros p n i Hin Hin' Hi.
        destruct (mr_blocks _ _ LAWS L A mem md p n i HMR Hin Hi) as (_ & Hlo & Hhi & _).
        assert (INA : In (ptr_addr L p, n) (b1 ++ b2)).
        { rewrite <- BLK2. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hin). }
        pose proof (tb_blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR' BLK1 INA) as Dj.
        cbn [Frame.outside]. split; [lia|]. split; [lia | exact I]. }
    assert (PRES : regs_preserved regs R3).
    { eapply (tb_preserved_chain (fun r => (r =? 2) || (r =? 8)) regs R1 R2 R3 _ _ X1 HPRES X3).
      - intros r Hr O. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O | split; reflexivity]|]).
        subst r. split; reflexivity.
      - intros r Hr O. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O | reflexivity]|]).
        subst r. discriminate O. }
    assert (E3_10 : getr R3 10 = Z_to_bv 64 h) by (rewrite (tb_getr_here _ _ 10 X3 eq_refl); simp_regs; reflexivity).
    assert (UH : bv_unsigned (Z_to_bv 64 h) = h) by (apply unsigned_lit; lia).
    rewrite RP.
    apply SR_ret.
    exists L', A', R3, m3, md2.
    split; [reflexivity|].
    split.
    { apply (kb_post B API); [|exact PRES].
      eapply (kb_mid_E B API); [exact MID3|].
      intros a [[F|F]|Ha]; [destruct F | destruct F | cbv beta].
      lazymatch goal with |- context [bv_unsigned (?G R3 ?l)] =>
        assert (EG : G R3 l = Z_to_bv 64 h) by exact E3_10; rewrite EG end.
      rewrite UH. lia. }
    split; [exact RO3|].
    split; [intros C; exfalso; exact (C0 C)|].
    intros _.
    lazymatch goal with |- ?G R3 ?l <> _ /\ _ =>
      assert (EG : G R3 l = Z_to_bv 64 h) by exact E3_10; rewrite EG end.
    rewrite !UH.
    split.
    { intros E. apply (f_equal bv_unsigned) in E. rewrite UH in E.
      change (bv_unsigned (Z_to_bv 64 0)) with 0 in E. lia. }
    split; [exact FRESH|].
    split; [exists b1, b2; split; [exact BLK1 | exact BLK2]|].
    split; [exact RES'|].
    split; [exact UBK|].
    split; [exact INIT|].
    unfold link_mem.tbuf_at.
    apply tb_tbuf_split; [lia|].
    exact BUF3.
Qed.

End M.

Theorem text_buf_holds_closed : text_buf_contract B API.
Proof. exact (text_buf_holds memset_holds). Qed.

End F.

(* at the frame's allocator symbols of the plain image (Reusable/YH02.v src0_msyms: malloc at
   0x17514, tp 0x75608, errno offset -164) the three pins hold by computation *)
Theorem text_buf_holds_src0 {fx : YK11.FPState} {rc : YM05.RunCeil} (API : AllocAPI YH02.src0_msyms) :
  malloc_contract YH02.src0_msyms API -> text_buf_contract YH02.src0_msyms API.
Proof. intros H. exact (text_buf_holds_closed YH02.src0_msyms API eq_refl eq_refl eq_refl H). Qed.

About text_buf_holds.
About text_buf_holds_closed.
About text_buf_holds_src0.
Print Assumptions text_buf_holds.
Print Assumptions text_buf_holds_closed.
Print Assumptions text_buf_holds_src0.

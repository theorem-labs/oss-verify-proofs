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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths and module names changed; 385 of its 418 lines of code are new or changed and 802 lines of the source are left out. *)
(* text_of (fuzz_link.c:126-136), plain image, entry 0x15aa8: its contract text_of_contract
   (lib/Prog/text_of_c.v) over the frame's allocator interface.
   The run is cut at the one allocator call: lib/Prog/text_of_pro.v walks the entry up to `ret` (table
   arm) or up to `jal malloc` (copy arm), lib/Prog/text_of_tail.v walks malloc's return up to `ret`;
   both over a memory without read-only entries (MemNorm.normalize). malloc is called through the
   frame's malloc_contract. The callee contracts (malloc, memchr, memcpy) are Section hypotheses;
   text_of_closed instantiates memchr and memcpy with the walks lib/Prog/memchr.v and
   lib/Prog/memcpy.v. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
  YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 Contract OutForm KindBGlue AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memchr_c memcpy_c memchr memcpy hp_tb_kit
  text_of_lem text_of_pro text_of_tail text_of_c.
Import ListNotations.
Open Scope Z_scope.

Lemma tf_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tf_cells8 : forall segs m a x, rw_cells segs m a [C8 x] -> bytes_at segs m a (le8 x).
Proof. intros segs m a x [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Section F.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALLOC_PC : ms_malloc B = 0x17514.
Hypothesis ERRC : errno_addr B + 4 <= alloc_ceiling.
Hypothesis MALLOC : malloc_contract B API.
Hypothesis MEMCHR : memchr_contract.
Hypothesis MEMCPY : memcpy_contract.

(* kb_pre_A, with the allocator already set up instead of the writes kept below sp: the auxv
   words call_pre names lie above sp, where the cursor and *own may lie *)
Lemma tf_pre : forall K f K1 L A regs mem md regs1 mem1 W,
  call_pre_k B (aa_MR API) K L A regs mem md -> 0 <= f -> 0 <= K1 -> f + K1 <= K ->
  spZ regs1 = spZ regs - f -> spZ regs1 mod 16 = 0 ->
  getr regs1 4 = getr regs 4 -> YK0s.ret_ok (getr regs1 1) ->
  Frame.munch W mem mem1 -> Frame.wmono (ms_segs B) mem mem1 ->
  st_init_done A = true ->
  (forall x, 0 <= x < alloc_ceiling -> (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
     Frame.outside W x) ->
  call_pre_k B (aa_MR API) K1 L A regs1 mem1 md.
Proof.
  intros K f K1 L A regs mem md regs1 mem1 W (HM & HWF & HB & Hra & Hal & Hlo & Hhi & HW & Htp & Herr & Haux)
    Hf HK1 HfK Hsp Hal1 Htp1 Hra1 Hm Hw INIT Hown.
  split; [exact (kb_MR_A B API L A mem mem1 md W HM Hm Hown)|].
  split; [exact HWF|]. split; [exact HB|]. split; [exact Hra1|]. split; [exact Hal1|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; unfold writable_at; apply Hw; exact (HW a ltac:(lia))|].
  split; [rewrite Htp1; exact Htp|].
  split; [intros a Ha; unfold writable_at; apply Hw; exact (Herr a Ha)|].
  intros Hd. rewrite INIT in Hd. discriminate Hd.
Qed.

Lemma tf_mono_some : forall m m' W, Frame.munch W m m' -> Frame.wmono rsegs m m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Frame.outside W a -> writable_at rsegs m' a -> present m' a) ->
  forall x, m x <> None -> m' x <> None.
Proof.
  intros m m' W Hm Hw HP x Hx.
  pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx.
  destruct (kb_outside_dec W (bv_unsigned x)) as [O|O].
  - rewrite (Hm x O). exact Hx.
  - assert (Wx : writable_at rsegs m' (bv_unsigned x)).
    { unfold writable_at. rewrite Z_to_bv_bv_unsigned. apply Hw.
      destruct (m x) as [bb|] eqn:E; [|contradiction]. unfold wview. rewrite E. discriminate. }
    destruct (HP (bv_unsigned x) Rx O Wx) as [bb E]. rewrite Z_to_bv_bv_unsigned in E. rewrite E. discriminate.
Qed.

Theorem text_of_holds : text_of_contract B API.
Proof.
  unfold text_of_contract.
  intros L A regs mem md b c0 c1 _ PRE RO CUR (w & OWN) A0NZ A1NZ CA0 CA1 RES ROOM INIT
    (inp & INP & LEN & DI0 & DI1) BLKI D01 AF0 AF1 GIMG DT0 DT1.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof MALLOC as MAL. unfold malloc_contract in MAL. rewrite SEGS, MALLOC_PC in MAL.
  assert (IL : img_low B).
  { eapply img_low_of_check with (C := 0x97000); [unfold img_check; rewrite SEGS; vm_compute; reflexivity | lia]. }
  unfold TEXT_OF_K, apart_frame, A_TEXTS, TEXTS_N in *.
  change ALLOC_STACK with 8192 in *.
  pose proof PRE as PRE0.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  pose proof (kb_stk B API IL (48 + 8192) L A regs mem md PRE0 ltac:(lia)) as ST. rewrite SEGS in ST.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (bv_unsigned_in_range 64 c0) as RC0. unfold bv_modulus in RC0.
  pose proof (bv_unsigned_in_range 64 c1) as RC1. unfold bv_modulus in RC1.
  pose proof (rw_cells_bound _ _ _ _ CUR) as BC. cbn [cells_size csize] in BC.
  pose proof (rw_cells_bound _ _ _ _ OWN) as BO. cbn [cells_size csize] in BO.
  pose proof (bytes_at_bound _ _ _ _ INP) as BI.
  assert (G10 : PropExec.getr regs 10 = reg_get regs 10) by reflexivity.
  assert (G11 : PropExec.getr regs 11 = reg_get regs 11) by reflexivity.
  remember (bv_unsigned (PropExec.getr regs 10)) as A0 eqn:EA0 in *.
  remember (bv_unsigned (PropExec.getr regs 11)) as A1 eqn:EA1 in *.
  remember (bv_unsigned c0) as C0 eqn:EC0 in *.
  remember (bv_unsigned c1) as N eqn:EN in *.
  assert (R10 : reg_get regs 10 = Z_to_bv 64 A0) by (rewrite EA0, G10; symmetry; apply Z_to_bv_bv_unsigned).
  assert (R11 : reg_get regs 11 = Z_to_bv 64 A1) by (rewrite EA1, G11; symmetry; apply Z_to_bv_bv_unsigned).
  assert (EC0' : c0 = Z_to_bv 64 C0) by (rewrite EC0; symmetry; apply Z_to_bv_bv_unsigned).
  assert (EN' : c1 = Z_to_bv 64 N) by (rewrite EN; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite EC0', EN' in CUR.
  (* the input lies in a live user block, below the frame *)
  assert (HIN : N <> 0 -> 0 < C0 /\ C0 + N <= bv_unsigned sp + -48).
  { intros HN. destruct (BLKI HN) as (q & k & Hq & Q1 & Q2).
    destruct (mr_blocks_range _ _ LAWS _ _ _ _ _ _ HMR Hq) as [Q3 Q4]. lia. }
  assert (RN0 : mem_rel rsegs mem (normalize rsegs mem)) by (apply mem_rel_normalize; rewrite <- SEGS; exact RO).
  rewrite SEGS in RO.
  assert (TXT : bytes_at rsegs (normalize rsegs mem) 133104 TL_TB).
  { apply tl_bytes_at_rom; [lia | rewrite tl_TB_len; lia | | exact tl_texts_img].
    intros i Hi. rewrite tl_TB_len in Hi.
    rewrite <- (mrd_rel rsegs mem (normalize rsegs mem) _ RN0).
    assert (Hg : in_globals [(133104, 8 * 11)] (133104 + Z.of_nat i))
      by (exists 133104, (8 * 11); split; [left; reflexivity | lia]).
    pose proof (GIMG _ Hg) as G. rewrite SEGS in G. exact G. }
  set (W := [(bv_unsigned sp + -48, bv_unsigned sp); (A0, A0 + 16); (A1, A1 + 8)]).
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite tb_canon_mkst. unfold Regs6ss.mkR_of. fold sp. rewrite R10, R11. unfold TEXT_OF.
    apply (evt_normalize rsegs); [exact tf_wx | exact RO |].
    eapply pro_entry with (A0 := A0) (A1 := A1) (C0 := C0) (N := N) (inp := inp) (w := w)
      (lo := bv_unsigned sp - (48 + 8192)) (HMC := MEMCHR).
    - unfold geo. repeat split; lia.
    - exact HIN.
    - apply tb_stk_normalize; [exact ST | lia].
    - lia.
    - apply tb_rw_cells_normalize; [exact RO | exact CUR |].
      intros i Hi. cbn in Hi. apply tb_ro_addr_hi. lia.
    - apply tb_rw_cells_normalize; [exact RO | exact OWN |].
      intros i Hi. cbn in Hi. apply tb_ro_addr_hi. lia.
    - apply bytes_at_normalize; [exact RO | exact INP].
    - exact TXT.
    - apply mem_inv_normalize. }
  intros ms1 (can1 & (s1' & Q1 & REL1 & ROS1) & EQ1).
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (kb_ret_pc _ HRA).
  destruct Q1 as [TAB | CALL].
  (* ===== the table arm: no allocation ===== *)
  - destruct TAB as (j & sp' & x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31
      & m1n & v1 & v2 & adv & -> & SPE & HJ & MU1n & WM1n & MI1n & CUR1n & V1 & V2 & HADV & OWN1n).
    destruct (tb_ms_rel_MS _ _ _ _ _ _ _ _ _ REL1) as [CAN1 HR1].
    remember (ms_mem can1) as m1 eqn:Em1. subst can1. clear Em1.
    pose proof (munch_rel rsegs _ _ _ _ _ RN0 HR1 ROS1 MU1n) as MU1.
    pose proof (wmono_rel rsegs _ _ _ _ RN0 HR1 ROS1 WM1n) as WM1.
    pose proof (ro_agree_same rsegs _ _ RO ROS1) as RO1.
    pose proof (tb_rw_cells_of_rel rsegs _ _ _ _ HR1 CUR1n) as CUR1.
    pose proof (tb_rw_cells_of_rel rsegs _ _ _ _ HR1 OWN1n) as OWN1.
    destruct (tb_eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    destruct (tl_text_facts m1 j RO1 HJ) as (TC & TL & TLO & THI).
    unfold A_RO_LO, A_RO_END in *.
    assert (MID : kb_mid B API (48 + 8192) (bv_unsigned sp) L A mem md
                    (fun a => (0 <= a < 0 + 0) \/ (A0 <= a < A0 + 16) \/ (A1 <= a < A1 + 8)) L A m1 md).
    { eapply (kb_mid_A B API IL) with (W := W);
        [ exact HMR | exact HWF | exact HBD | | exact MU1 | rewrite SEGS; exact WM1 | | ].
      - intros a [Ha|Ha]; [apply HWS; lia | apply HERR; exact Ha].
      - intros x Hx Hs He. unfold W. cbn [Frame.outside].
        split; [lia|]. split; [intro; apply He; right; left; lia|]. split; [intro; apply He; right; right; lia | exact I].
      - intros x Hx _. unfold W. cbn [Frame.outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    assert (PRES : regs_preserved regs R1).
    { intros r Hr. unfold callee_saved in Hr.
      assert (NZ : bv_eqb (Z_to_bv 5 r) 0 = false).
      { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
        change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia. }
      rewrite (tb_getr_of_eqv _ _ _ X1 NZ). unfold getr. rewrite NZ.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct C as [C|C]; [subst r; first [reflexivity | (apply bv_eq; exact SPE)]|]).
      subst r. reflexivity. }
    rewrite RP. apply SR_ret.
    exists L, A, R1, m1, md, 0, (tl_ptr j), (tl_str j), 0.
    split; [reflexivity|].
    split; [apply (kb_post B API); [exact MID | exact PRES]|].
    split; [exact RO1|].
    split; [exact (tb_getr_of_eqv _ _ 10 X1 eq_refl)|].
    split; [lia|].
    split; [exact TC|]. split; [exact TL|].
    split; [apply tf_cells8; exact OWN1|].
    split.
    { exists adv. split; [lia|].
      replace v1 with (Z_to_bv 64 (C0 + adv)) in CUR1 by (apply bv_eq; rewrite unsigned_lit by lia; lia).
      replace v2 with (Z_to_bv 64 (N - adv)) in CUR1 by (apply bv_eq; rewrite unsigned_lit by lia; lia).
      exact CUR1. }
    split; [intros _; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [exact RES | lia]|].
    intros C. exfalso. apply C. reflexivity.
  (* ===== the copy arm: malloc (n + 1), then the copy ===== *)
  - destruct CALL as (d & take & n & x5 & x6 & x7 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18
      & x28 & x29 & x30 & x31 & m1n & junk & v1 & v2 & -> & H9 & H10 & H18 & HD1 & HT0 & HDT & HT320 & HN
      & FR1n & MU1n & WM1n & MI1n & CUR1n & V1 & V2 & OWN1n & INP1n).
    destruct (tb_ms_rel_MS _ _ _ _ _ _ _ _ _ REL1) as [CAN1 HR1].
    remember (ms_mem can1) as m1 eqn:Em1. subst can1. clear Em1.
    pose proof (munch_rel rsegs _ _ _ _ _ RN0 HR1 ROS1 MU1n) as MU1.
    pose proof (wmono_rel rsegs _ _ _ _ RN0 HR1 ROS1 WM1n) as WM1.
    pose proof (ro_agree_same rsegs _ _ RO ROS1) as RO1.
    pose proof (tb_rw_cells_of_rel rsegs _ _ _ _ HR1 FR1n) as FR1.
    pose proof (tb_rw_cells_of_rel rsegs _ _ _ _ HR1 CUR1n) as CUR1.
    pose proof (tb_rw_cells_of_rel rsegs _ _ _ _ HR1 OWN1n) as OWN1.
    destruct (tb_eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (NNZ : N <> 0) by lia.
    destruct (HIN NNZ) as [HC0 HCF].
    destruct (BLKI NNZ) as (q & k & Hq & Q1 & Q2).
    set (buf := skipn (Z.to_nat d) inp) in *.
    assert (BL : Z.of_nat (length buf) = N - d) by (unfold buf; rewrite length_skipn; lia).
    destruct (tl_strnlen take buf ltac:(lia)) as [SNB SNZ]. rewrite <- HN in SNB, SNZ.
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x15bf8) by (rewrite (tb_getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp + -48))
      by (rewrite (tb_getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (tb_getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_10 : getr R1 10 = x10) by (rewrite (tb_getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
    assert (SPZ1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
    set (E1 := fun a => (A0 <= a < A0 + 16) \/ (A1 <= a < A1 + 8)).
    assert (MID1 : kb_mid B API (48 + 8192) (bv_unsigned sp) L A mem md E1 L A m1 md).
    { eapply (kb_mid_A B API IL) with (W := W);
        [ exact HMR | exact HWF | exact HBD | | exact MU1 | rewrite SEGS; exact WM1 | | ].
      - intros a [Ha|Ha]; [apply HWS; lia | apply HERR; exact Ha].
      - intros x Hx Hs He. unfold W, E1 in *. cbn [Frame.outside].
        split; [lia|]. split; [intro; apply He; left; lia|]. split; [intro; apply He; right; lia | exact I].
      - intros x Hx _. unfold W. cbn [Frame.outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    assert (CP1 : call_pre B (aa_MR API) L A R1 m1 md).
    { apply call_pre_k_alloc.
      eapply (tf_pre (48 + 8192) 48 8192 L A regs mem md R1 m1 W);
        [ exact PRE0 | lia | lia | lia | rewrite SPZ1; reflexivity | | rewrite E1_4; reflexivity | | exact MU1
        | rewrite SEGS; exact WM1 | exact INIT | ].
      - rewrite SPZ1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
      - intros x Hx _. unfold W. cbn [Frame.outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    assert (ROOMn : room_slots b (n + 1)).
    { destruct ROOM as (R0 & R1' & R2). split; [lia|]. split; [exact R1'|].
      apply (CAPOK_mono (sb_cap b) (sb_cap b) (sb_bytes b + 320) (sb_bytes b + (n + 1)) 320 (n + 1));
        [lia | lia | lia | exact R2]. }
    eapply SR_bind.
    { eapply (MAL L A R1 m1 md (n + 1) b);
        [ exact CP1 | exact RO1 | | exact RES | exact ROOMn ].
      rewrite E1_10. apply bv_eq. rewrite H10, unsigned_lit by lia. reflexivity. }
    intros c2 RET.
    destruct RET as (L' & A' & R2 & m2 & md2 & h & -> & POST & A0' & NZ & AL & FRESH & BLK & KEPT & RO2 & GK & UBK
      & INIT' & RLEN & RES').
    rewrite SEGS in RO2.
    destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ POST) as [MIDm HPRES].
    pose proof POST as (HMR' & HWF' & HBD' & HLE & HSTAB & _ & HVM & HFRAME & HBLKS & HSCR).
    destruct (mr_model _ _ LAWS _ _ _ _ HMR') as (Hh2 & Hl2 & Hmat2).
    destruct BLK as (b1 & b2 & BLK1 & BLK2).
    pose proof FRESH as (FR_lo & FR_hi & FR_img).
    rewrite SPZ1 in MIDm.
    assert (MID2 : kb_mid B API (48 + 8192) (bv_unsigned sp) L A mem md (fun a => E1 a \/ False) L' A' m2 md2).
    { eapply (kb_mid_seqAX B API); [exact MID1 | exact MIDm | lia | lia | lia | lia |].
      intros a _ _ F. exact F. }
    pose proof MID2 as (_ & _ & _ & _ & _ & _ & MF2 & MB2 & _).
    assert (NOWN : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
    { intros a Ha. split; intros Ho;
        [pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ HMR Ho) | pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ HMR' Ho)]; lia. }
    (* what malloc keeps: everything at or above alloc_ceiling outside its own frame, and the old blocks *)
    assert (HI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 48 - 8192 <= a < bv_unsigned sp - 48) ->
       mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
       (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
    { intros a Ha Hs. destruct (NOWN a ltac:(lia)) as [N1 N2].
      apply HFRAME; [left; lia | exact N1 | exact N2 | | intros F; exact F].
      unfold scratch_k. rewrite SPZ1. intros [H|H]; lia. }
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -48)
                    [CB 8 junk; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                     C8 (reg_get regs 1)]).
    { apply (tb_rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
      destruct (HI2 (bv_unsigned sp + -48 + i) ltac:(lia) ltac:(lia)) as [E W']. split; [exact E | apply W']. }
    assert (CUR2 : rw_cells rsegs m2 A0 [C8 v1; C8 v2]).
    { apply (tb_rw_cells_transfer rsegs m1); [exact CUR1|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
      destruct (HI2 (A0 + i) ltac:(lia) ltac:(lia)) as [E W']. split; [exact E | apply W']. }
    assert (OWN2 : rw_cells rsegs m2 A1 [C8 (Z_to_bv 64 0)]).
    { apply (tb_rw_cells_transfer rsegs m1); [exact OWN1|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
      destruct (HI2 (A1 + i) ltac:(lia) ltac:(lia)) as [E W']. split; [exact E | apply W']. }
    assert (INP2 : bytes_at rsegs m2 C0 inp).
    { apply (tb_bytes_at_transfer rsegs mem); [exact INP|]. intros i Hi. rewrite <- SEGS.
      replace (C0 + i) with (ptr_addr L q + (C0 + i - ptr_addr L q)) by lia.
      exact (MB2 q k (C0 + i - ptr_addr L q) Hq (UBK _ _ Hq) ltac:(lia)). }
    assert (INH : In (h, n + 1) (blocks L' A')) by (rewrite BLK1; apply in_or_app; right; left; reflexivity).
    destruct (tb_present_rw_cells rsegs m2 h (Z.to_nat n)) as [j1 DST]; [lia | lia | |].
    { intros i Hi. exact (proj1 (tb_block_facts B _ LAWS _ _ _ _ _ _ i HMR' INH ltac:(lia))). }
    destruct (tb_present_rw_cells rsegs m2 (h + n) 1%nat) as [j2 DLB0]; [lia | lia | |].
    { intros i Hi. replace (h + n + i) with (h + (n + i)) by ring.
      exact (proj1 (tb_block_facts B _ LAWS _ _ _ _ _ _ (n + i) HMR' INH ltac:(lia))). }
    assert (J2L : length j2 = 1%nat) by (destruct DLB0 as [[[HL _] _] _]; exact HL).
    destruct j2 as [|jb [|jx jr]]; [discriminate J2L | | discriminate J2L].
    assert (DLB : rw_cells rsegs m2 (h + n) [C1 jb])
      by (apply (tb_rw_cells_recell rsegs m2 (h + n) _ _ DLB0); [cbn; tauto | reflexivity]).
    assert (HBD2 : ptr_addr L q + k <= h \/ h + (n + 1) <= ptr_addr L q).
    { assert (Hq' : In (ptr_addr L q, k) (b1 ++ b2)).
      { rewrite <- BLK2. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (q, k) Hq). }
      exact (tb_blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR' BLK1 Hq'). }
    assert (HNI : forall i, 0 <= i < n + 1 -> ~ in_img B (h + i)) by exact FR_img.
    assert (E2_ : forall r, callee_saved r -> getr R2 (Z_to_bv 5 r) = getr R1 (Z_to_bv 5 r)) by exact HPRES.
    assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp + -48)) by exact (eq_trans (E2_ 2 ltac:(unfold callee_saved; lia)) E1_2).
    assert (E2_8 : reg_get R2 8 = Z_to_bv 64 A1)
      by exact (eq_trans (E2_ 8 ltac:(unfold callee_saved; lia)) (tb_getr_of_eqv _ _ 8 X1 eq_refl)).
    assert (E2_9a : reg_get R2 9 = x9)
      by exact (eq_trans (E2_ 9 ltac:(unfold callee_saved; lia)) (tb_getr_of_eqv _ _ 9 X1 eq_refl)).
    assert (E2_9 : reg_get R2 9 = Z_to_bv 64 (C0 + d))
      by (rewrite E2_9a; apply bv_eq; rewrite H9, unsigned_lit by lia; reflexivity).
    assert (E2_10 : reg_get R2 10 = Z_to_bv 64 h) by exact A0'.
    assert (E2_18a : reg_get R2 18 = x18)
      by exact (eq_trans (E2_ 18 ltac:(unfold callee_saved; lia)) (tb_getr_of_eqv _ _ 18 X1 eq_refl)).
    assert (E2_18 : reg_get R2 18 = Z_to_bv 64 n)
      by (rewrite E2_18a; apply bv_eq; rewrite H18, unsigned_lit by lia; reflexivity).
    assert (TKL : Z.of_nat (length (firstn (Z.to_nat n) buf)) = n) by (rewrite length_firstn; lia).
    assert (SRC : bytes_at rsegs m2 (C0 + d) (firstn (Z.to_nat n) buf)).
    { apply tl_bytes_at_firstn. unfold buf. replace (C0 + d) with (C0 + Z.of_nat (Z.to_nat d)) by lia.
      apply tl_bytes_at_skipn; [exact INP2 | lia]. }
    rewrite E1_1, SEGS.
    eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
    { rewrite tb_canon_mkst. unfold Regs6ss.mkR_of. rewrite E2_8, E2_9, E2_10, E2_18.
      apply (evt_normalize rsegs); [exact tf_wx | exact RO2 |].
      eapply tail_walk with (h := h) (hn := h + n) (P := C0 + d) (n := n) (A0 := A0) (A1 := A1)
        (tk := firstn (Z.to_nat n) buf) (j1 := j1) (jb := jb) (HMCP := MEMCPY).
      - lia.
      - reflexivity.
      - exact TKL.
      - lia.
      - rewrite E2_2, unsigned_lit by lia. lia.
      - apply bytes_at_normalize; [exact RO2 | exact SRC].
      - apply tb_rw_cells_normalize; [exact RO2 | exact DST |].
        intros i Hi. cbn in Hi. apply (tb_ro_addr_out B SEGS); [lia | apply HNI; lia].
      - apply tb_rw_cells_normalize; [exact RO2 | exact DLB |].
        intros i Hi. cbn in Hi. apply (tb_ro_addr_out B SEGS); [lia |]. replace (h + n + i) with (h + (n + i)) by ring.
        apply HNI; lia.
      - rewrite E2_2, unsigned_lit by lia. apply tb_rw_cells_normalize; [exact RO2 | exact FR2 |].
        intros i Hi. cbn in Hi. apply tb_ro_addr_hi. lia.
      - apply tb_rw_cells_normalize; [exact RO2 | exact OWN2 |].
        intros i Hi. cbn in Hi. apply tb_ro_addr_hi. lia.
      - apply tb_rw_cells_normalize; [exact RO2 | exact CUR2 |].
        intros i Hi. cbn in Hi. apply tb_ro_addr_hi. lia.
      - lia.
      - lia.
      - lia.
      - rewrite E2_2, unsigned_lit by lia. lia.
      - rewrite E2_2, unsigned_lit by lia. lia.
      - rewrite E2_2, unsigned_lit by lia. lia.
      - lia.
      - apply mem_inv_normalize. }
    intros ms3 (can3 & (s3' & Q3 & REL3 & ROS3) & EQ3).
    destruct Q3 as (sp3 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3n
      & -> & SPE3 & MU3n & WM3n & MI3n & STR3n & OWN3n & CUR3n).
    destruct (tb_ms_rel_MS _ _ _ _ _ _ _ _ _ REL3) as [CAN3 HR3].
    remember (ms_mem can3) as m3 eqn:Em3. subst can3. clear Em3.
    assert (RN2 : mem_rel rsegs m2 (normalize rsegs m2)) by (apply mem_rel_normalize; exact RO2).
    pose proof (munch_rel rsegs _ _ _ _ _ RN2 HR3 ROS3 MU3n) as MU3.
    pose proof (wmono_rel rsegs _ _ _ _ RN2 HR3 ROS3 WM3n) as WM3.
    pose proof (ro_agree_same rsegs _ _ RO2 ROS3) as RO3.
    pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ HR3) STR3n) as STR3.
    pose proof (tb_rw_cells_of_rel rsegs _ _ _ _ HR3 OWN3n) as OWN3.
    pose proof (tb_rw_cells_of_rel rsegs _ _ _ _ HR3 CUR3n) as CUR3.
    destruct (tb_eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    rewrite E2_2, unsigned_lit in SPE3 by lia.
    assert (SP3 : sp3 = sp) by (apply bv_eq; rewrite SPE3; lia).
    subst sp3.
    assert (PRES3 : regs_preserved regs R3).
    { eapply (tb_preserved_chain (fun r => (r =? 2) || (r =? 8) || (r =? 9) || (r =? 18) || (r =? 19))
        regs R1 R2 R3 _ _ X1 HPRES X3).
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
    set (E2 := fun a => (h <= a < h + (n + 1)) \/ (A1 <= a < A1 + 8)).
    assert (MID3 : kb_mid B API (48 + 8192) (bv_unsigned sp) L A mem md (fun a => (E1 a \/ False) \/ E2 a) L' A' m3 md2).
    { eapply (kb_mid_tail B API IL) with (W := [(h, h + n + 1); (A1, A1 + 8)]);
        [ exact MID2 | exact MU3 | rewrite SEGS; exact WM3 | | | | ].
      - apply (tf_mono_some m2 m3 _ MU3 WM3). intros a Ha O Wa. cbn [Frame.outside] in O.
        destruct (Z_lt_le_dec a (h + n + 1)) as [Lt|Ge].
        + apply (tb_present_of_writable_out B SEGS m3 a Ha); [|exact Wa].
          intro Hi. destruct (Z_le_gt_dec h a) as [Le|Gt]; [apply (HNI (a - h)); [lia | replace (h + (a - h)) with a by ring; exact Hi]|].
          apply O. split; [lia|]. split; [lia | exact I].
        + apply tb_writable_hi_present; [|exact Wa]. split; [|lia].
          destruct (Z_lt_le_dec a A1) as [Lt|Ge2]; [exfalso; apply O; split; [lia|]; split; [lia | exact I]|].
          lia.
      - intros x Hx Hs He. unfold E2 in He. cbn [Frame.outside].
        split; [intro; apply He; left; lia|]. split; [intro; apply He; right; lia | exact I].
      - intros x Hx Ho. cbn [Frame.outside]. split; [|split; [lia | exact I]].
        intros Hin. apply (proj2 (proj2 (proj2 (tb_block_facts B _ LAWS _ _ _ _ _ _ (x - h) HMR' INH ltac:(lia))))).
        replace (h + (x - h)) with x by ring. exact Ho.
      - intros p nb i Hin Hin' Hi.
        destruct (mr_blocks B _ LAWS L A mem md p nb i HMR Hin Hi) as (_ & Hlo & Hhi & _).
        assert (INA : In (ptr_addr L p, nb) (b1 ++ b2)).
        { rewrite <- BLK2. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (p, nb) Hin). }
        pose proof (tb_blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR' BLK1 INA) as Dj.
        cbn [Frame.outside]. split; [lia|]. split; [lia | exact I]. }
    rewrite RP. apply SR_ret.
    exists L', A', R3, m3, md2, h, h, (firstn (Z.to_nat n) buf), (n + 1).
    split; [reflexivity|].
    split.
    { apply (kb_post B API); [|exact PRES3].
      eapply (kb_mid_E B API); [exact MID3|]. unfold E1, E2. intros a [[Ha|[]]|Ha]; lia. }
    split; [exact RO3|].
    split; [exact (tb_getr_of_eqv _ _ 10 X3 eq_refl)|].
    split; [lia|].
    split; [split; [exact STR3 | exact SNZ]|].
    split; [lia|].
    split; [apply tf_cells8; exact OWN3|].
    split.
    { exists (d + take). split; [lia|].
      replace v1 with (Z_to_bv 64 (C0 + (d + take))) in CUR3 by (apply bv_eq; rewrite unsigned_lit by lia; lia).
      replace v2 with (Z_to_bv 64 (N - (d + take))) in CUR3 by (apply bv_eq; rewrite unsigned_lit by lia; lia).
      exact CUR3. }
    split; [intros C; lia|].
    intros _. split; [reflexivity|].
    split; [lia|]. split; [exact FRESH|]. split; [lia|].
    split; [exists b1, b2; split; [exact BLK1 | exact BLK2]|].
    split; [exact RES'|].
    split; [exact UBK|].
    exact INIT'.
Qed.

End F.

(* memchr and memcpy instantiated by their walks *)
Theorem text_of_closed : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x17514 -> errno_addr B + 4 <= alloc_ceiling ->
  malloc_contract B API -> text_of_contract B API.
Proof.
  intros fx rc B API HS HM HE HMal.
  eapply text_of_holds; first [eassumption | exact memchr_holds | exact memcpy_holds].
Qed.

About text_of_holds.
About text_of_closed.
Print Assumptions text_of_holds.
Print Assumptions text_of_closed.

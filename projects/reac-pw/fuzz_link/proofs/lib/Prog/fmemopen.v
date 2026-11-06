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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths, module names, addresses and numbers changed; 361 of its 410 lines of code are new or changed and 786 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 Contract KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import StdioModel KindB strchr_c memset_c __ofl_add_c
  fmemopen_pro fmemopen_tail fmemopen_mf fmemopen_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require memfile_c memfile_place link_mem link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require strchr memset __ofl_add __ofl_lock __ofl_unlock __lock __unlock.
Import ListNotations.
Open Scope Z_scope.

(* fmemopen(g_said, 4096, "w") on link's plain image (0x192a0, 464 bytes; the code is byte-identical to pcap's
   0x15fb4, compared byte for byte). The walk is pcap's (fmemopen_pro to malloc, then
   fmemopen_tail), re-aimed at mode "w": strchr(mode, '+') = 0 and strchr("rwa", 'w') <> 0 (+0x2c / +0x44), buf
   <> 0 (+0x4c / +0xe4), flags = F_NORD (+0x11c, +0x128), no c.len store (+0x140 is skipped: 'w' is not 'r'), no
   store to the buffer (+0x164 is skipped: no '+'). a Theorem Labs lane's obligation (a): stdio_ok's byte __libc + 1 is 0 at
   the call; the walk reads it at +0x18c (fmemopen_tail, RDT, from stdio_ok's first conjunct), +0x1a0 does not
   branch, and +0x1a8 stores lock = -1 (the C4 at +140 of mfw_cells). The post is MemFile.v's FILE (fmemopen_mf).
   pcap's top (fmemopen_holds, mode "rb", a heap buffer) is here fmemopen_w_proof. *)

Lemma wx_rsegs : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Section F.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALLOC_PC : ms_malloc B = 0x17514.
Hypothesis TP_PIN : ms_tp B = 0x75608.
Hypothesis ERRNO_PIN : ms_errno_off B = -164.
Hypothesis CTX_PIN : ms_ctx B = 0x95910.
Hypothesis LOCK_PIN : ms_lock B = 0x95908.
Hypothesis LIBC_PIN : ms_libc B = 0x95898.
Hypothesis GOT_PIN : ms_got_guard B = 0x208d8.
Hypothesis GUARD_PIN : ms_guard B = 0x95878.
Hypothesis DEBRUIJN_PIN : ms_debruijn B = 0x10778.
Hypothesis SIZE_CLASSES_PIN : ms_size_classes B = 0x10798.
Hypothesis SMALL_CNT_PIN : ms_small_cnt B = 0x107f8.
Hypothesis MED_CNT_PIN : ms_med_cnt B = 0x10813.
Hypothesis VMLOCK_PIN : ms_vmlock B = None.
Hypothesis DBLEN_PIN : ms_debruijn_len B = 32.
Hypothesis MALLOC : malloc_contract B API.
Hypothesis NOLOCKS : libc_no_locks B API.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis STRCHR : strchr_contract.
Hypothesis MEMSET : memset_contract.
Hypothesis OFLADD : __ofl_add_contract.

Lemma img_rng : forall lo hi,
  existsb (fun s => (bv_unsigned (fst s) <=? lo) && (hi <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved rsegs) = true ->
  forall a, lo <= a < hi -> in_img B a.
Proof.
  intros lo hi H a Ha. apply existsb_exists in H as (s & Hs & E).
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  unfold in_img. rewrite SEGS. split; [intros N; rewrite N in Hs; exact Hs|].
  exists s. split; [exact Hs | lia].
Qed.

Lemma img_glob : forall a, 0x95878 <= a < 0x95cd0 -> in_img B a.
Proof. intros a Ha. apply (img_rng 0x95878 0x95cd0); [vm_compute; reflexivity | exact Ha]. Qed.

Lemma img_mode : forall a, 0x10564 <= a < 0x10566 -> in_img B a.
Proof. intros a Ha. apply (img_rng 0x10564 0x10566); [vm_compute; reflexivity | exact Ha]. Qed.

Lemma disj_img : forall q n lo hi, 0 < n -> lo < hi ->
  (forall i, 0 <= i < n -> ~ in_img B (q + i)) -> (forall a, lo <= a < hi -> in_img B a) ->
  q + n <= lo \/ hi <= q.
Proof.
  intros q n lo hi Hn Hlh Hq Hr.
  destruct (Z_le_gt_dec (q + n) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec hi q) as [D'|D']; [right; exact D'|]. exfalso.
  apply (Hq (Z.max q lo - q)); [lia|].
  replace (q + (Z.max q lo - q)) with (Z.max q lo) by lia. apply Hr. lia.
Qed.

Lemma glob_free : forall L A mem md a, aa_MR API L A mem md -> (a = 0x95899 \/ 0x95cc0 <= a < 0x95cd0) ->
  ~ owned B L A a.
Proof.
  intros L A mem md a HM Ha [Ho|Ho].
  - pose proof (ax_img AX L A mem md a HM (img_glob a ltac:(lia)) Ho) as C.
    rewrite CTX_PIN in C. unfold CTX_SIZE in C. lia.
  - unfold static_owned in Ho.
    rewrite LOCK_PIN, LIBC_PIN, GOT_PIN, GUARD_PIN, DEBRUIJN_PIN, SIZE_CLASSES_PIN, SMALL_CNT_PIN, MED_CNT_PIN in Ho.
    unfold vml_lo, vml_len in Ho. rewrite VMLOCK_PIN, DBLEN_PIN in Ho. change (Z.max 32 32) with 32 in Ho.
    lia.
Qed.

(* g_said (link_mem.A_G_SAID, 4096 bytes of .bss): an image range the allocator does not own *)
Lemma img_said : forall a, 0x74530 <= a < 0x75530 -> in_img B a.
Proof. intros a Ha. apply (img_rng 0x74530 0x75530); [vm_compute; reflexivity | exact Ha]. Qed.

Lemma said_free : forall L A mem md a, aa_MR API L A mem md -> 0x74530 <= a < 0x75530 -> ~ owned B L A a.
Proof.
  intros L A mem md a HM Ha [Ho|Ho].
  - pose proof (ax_img AX L A mem md a HM (img_said a Ha) Ho) as C.
    rewrite CTX_PIN in C. unfold CTX_SIZE in C. lia.
  - unfold static_owned in Ho.
    rewrite LOCK_PIN, LIBC_PIN, GOT_PIN, GUARD_PIN, DEBRUIJN_PIN, SIZE_CLASSES_PIN, SMALL_CNT_PIN, MED_CNT_PIN in Ho.
    unfold vml_lo, vml_len in Ho. rewrite VMLOCK_PIN, DBLEN_PIN in Ho. change (Z.max 32 32) with 32 in Ho.
    lia.
Qed.

Lemma mid_tail : img_low B -> forall K sp L A mem md E1 L' A' mem1 md' mem' W (E2 : Z -> Prop),
  kb_mid B API K sp L A mem md E1 L' A' mem1 md' ->
  Frame.munch W mem1 mem' -> Frame.wmono (ms_segs B) mem1 mem' ->
  (forall q n i, In (q, n) (user_blocks A') -> 0 <= i < n -> present mem' (ptr_addr L' q + i)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (sp - K <= x < sp) -> ~ E2 x -> Frame.outside W x) ->
  (forall x, 0 <= x < alloc_ceiling -> owned B L' A' x -> Frame.outside W x) ->
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> 0 <= i < n ->
     Frame.outside W (ptr_addr L p + i)) ->
  kb_mid B API K sp L A mem md (fun a => E1 a \/ E2 a) L' A' mem' md'.
Proof.
  intros [HI _] K sp L A mem md E1 L' A' mem1 md' mem' W E2 (M1 & W1 & B1 & Y1 & P1 & D1 & F1 & K1 & S1)
    Hm Hw Hp HE HO HB.
  pose proof alloc_ceiling_val as Hc.
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M1) as (Hh & Hl & Hmat).
  split.
  { apply (mr_frame _ _ (aa_laws API) L' A' mem1 mem' md' md' M1).
    - intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho).
      apply (munch_mbyte (ms_segs B) W); [exact Hm | lia | apply HO; [lia | exact Ho]].
    - intros a Ho Hpr. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho).
      apply (munch_present W mem1); [exact Hm | lia | apply HO; [lia | exact Ho] | exact Hpr].
    - exact Hp.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact W1|]. split; [exact B1|]. split; [exact Y1|]. split; [exact P1|]. split; [exact D1|].
  split.
  { intros a Ha Ho Ho' Hs He.
    assert (Hr : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | apply HI in Ha; lia]).
    destruct (F1 a Ha Ho Ho' ltac:(tauto) ltac:(tauto)) as [E1a E1w].
    assert (Hout : Frame.outside W a) by (apply HE; [exact Hr | tauto | tauto]).
    split.
    - rewrite (munch_mbyte (ms_segs B) W mem1 mem' a Hm Hr Hout). exact E1a.
    - rewrite E1w. exact (munch_writable (ms_segs B) W mem1 mem' a Hm Hr Hout). }
  split.
  { intros p n i Hin Hin' Hi.
    destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n M1 Hin') as [R1 R2].
    rewrite (P1 p n Hin Hin') in R1, R2.
    rewrite (munch_mbyte (ms_segs B) W mem1 mem' (ptr_addr L p + i) Hm ltac:(lia) (HB p n i Hin Hin' Hi)).
    exact (K1 p n i Hin Hin' Hi). }
  intros a Ha. unfold writable_at. apply Hw. exact (S1 a Ha).
Qed.

Theorem fmemopen_w_proof : fmemopen_w_contract B API.
Proof.
  unfold fmemopen_w_contract.
  intros L A regs mem md b0 _ PRE A0 A1 A2 WRS SOK OE GOK RO RES ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof MALLOC as MAL. unfold malloc_contract in MAL. rewrite SEGS, MALLOC_PC in MAL.
  assert (IL : img_low B).
  { eapply img_low_of_check with (C := 0x97000); [unfold img_check; rewrite SEGS; vm_compute; reflexivity | lia]. }
  assert (ERR : errno_addr B = 0x75564) by (unfold errno_addr; rewrite TP_PIN, ERRNO_PIN; reflexivity).
  unfold memfile_c.FMEMOPEN_K in *.
  pose proof PRE as PRE0.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  rewrite SEGS in RO.
  assert (R10 : reg_get regs 10 = Z_to_bv 64 link_mem.A_G_SAID) by exact A0.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8240) (bv_unsigned sp)).
  { pose proof (kb_stk B API IL 8240 L A regs mem md PRE0 ltac:(lia)) as X. rewrite SEGS in X. exact X. }
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold memfile_c.FMEMOPEN.
    apply (evt_normalize rsegs); [exact wx_rsegs | exact RO |].
    eapply (fmemopen_pro STRCHR) with (lo := bv_unsigned sp - 8240);
      [ apply stk_normalize; [exact ST | lia] | lia | lia | exact A2 | | apply mem_inv_normalize ].
    rewrite R10. unfold link_mem.A_G_SAID. rewrite unsigned_lit by lia. lia. }
  intros ms1 (can1 & (s1 & Q1 & REL1 & ROS1) & EQ1).
  unfold fmemopen_pro_post in Q1.
  destruct Q1 as (sp1 & t0 & t1 & t2 & a0' & a1' & a2' & a3 & a4 & a5 & a6 & a7 & s4' & t3 & t4 & t5 & t6 & m1n
    & -> & SP1 & EA0 & ES4 & FR1n & MU1n & WM1n & MI1n & ST1n).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL1) as [CAN1 HR1].
  remember (ms_mem can1) as m1 eqn:Em1. subst can1. clear Em1.
  assert (RN0 : mem_rel rsegs mem (normalize rsegs mem)) by (apply mem_rel_normalize; exact RO).
  pose proof (munch_rel rsegs _ _ _ _ _ RN0 HR1 ROS1 MU1n) as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ RN0 HR1 ROS1 WM1n) as WM1.
  pose proof (ro_agree_same rsegs _ _ RO ROS1) as RO1.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ HR1 FR1n) as FR1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x1933c) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = sp1) by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_9 : getr R1 9 = reg_get regs 10) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 1304) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; exact EA0).
  assert (E1_18 : getr R1 18 = reg_get regs 11) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_19 : getr R1 19 = reg_get regs 12) by (rewrite (getr_of_eqv _ _ 19 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_20 : getr R1 20 = Z_to_bv 64 0) by (rewrite (getr_of_eqv _ _ 20 X1 eq_refl); simp_regs; exact ES4).
  assert (SPZ1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E1_2; exact SP1).
  assert (OUT1 : forall x, ~ (bv_unsigned sp - 80 <= x < bv_unsigned sp) ->
            Frame.outside [(bv_unsigned sp - 80, bv_unsigned sp)] x) by (intros x Hx; cbn; split; [exact Hx | exact I]).
  assert (MID1 : kb_mid B API 8240 (bv_unsigned sp) L A mem md (fun _ => False) L A m1 md).
  { eapply (kb_mid_A B API IL) with (W := [(bv_unsigned sp - 80, bv_unsigned sp)]);
      [ exact HMR | exact HWF | exact HBD | | exact MU1 | rewrite SEGS; exact WM1 | | ].
    - intros a [Ha|Ha]; [apply HWS; lia | apply HERR; exact Ha].
    - intros x _ Hs _. apply OUT1. lia.
    - intros x Hx _. apply OUT1. lia. }
  assert (CP1 : call_pre B (aa_MR API) L A R1 m1 md).
  { apply call_pre_k_alloc.
    eapply (kb_pre_A B API) with (K := 8240) (f := 48) (W := [(bv_unsigned sp - 80, bv_unsigned sp)]);
      [ exact PRE0 | lia | change ALLOC_STACK with 8192; lia | change ALLOC_STACK with 8192; lia
      | unfold spZ; rewrite E1_2; exact SP1 | | rewrite E1_4; reflexivity | | exact MU1 | rewrite SEGS; exact WM1 | | ].
    - rewrite SPZ1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
    - intros x _ Hx. change (spZ regs) with (bv_unsigned sp) in Hx. apply OUT1. lia.
    - intros x Hx _. apply OUT1. lia. }
  eapply SR_bind.
  { eapply (MAL L A R1 m1 md 1304 b0); [exact CP1 | exact RO1 | exact E1_10 | exact RES | exact ROOM]. }
  intros c2 RET.
  destruct RET as (L' & A' & R2 & m2 & md2 & h & -> & POST & A0' & NZ & AL & FRESH & BLK & KEPT & RO2 & GK & UBK
    & INIT & RLEN & RES').
  rewrite SEGS in RO2.
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ POST) as [MIDm HPRES].
  pose proof POST as (HMR' & HWF' & HBD' & HLE & HSTAB & _ & HVM & HFRAME & HBLKS & HSCR).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR') as (Hh2 & Hl2 & Hmat2).
  destruct BLK as (b1 & b2 & BLK1 & BLK2).
  pose proof FRESH as (FR_lo & FR_hi & FR_img).
  rewrite SPZ1 in MIDm.
  assert (MID2 : kb_mid B API 8240 (bv_unsigned sp) L A mem md (fun a => False \/ False) L' A' m2 md2).
  { eapply (kb_mid_seqAX B API); [exact MID1 | exact MIDm | change ALLOC_STACK with 8192; lia | lia | lia | lia |].
    intros a _ _ F. exact F. }
  pose proof MID2 as (_ & _ & _ & _ & _ & _ & MF2 & MB2 & _).
  assert (NOWN : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
  { intros a Ha. split; intros Ho;
      [destruct (owned_low B _ LAWS _ _ _ _ _ HMR Ho) | destruct (owned_low B _ LAWS _ _ _ _ _ HMR' Ho)]; lia. }
  assert (HI2 : forall a, bv_unsigned sp - 48 <= a < 2 ^ 64 ->
     mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
     (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha. destruct (NOWN a ltac:(lia)) as [N1 N2].
    apply HFRAME; [left; lia | exact N1 | exact N2 | | intros F; exact F].
    unfold scratch_k. rewrite SPZ1, ERR. change ALLOC_STACK with 8192. intros [H|H]; lia. }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 48)
                  [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                   C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
    destruct (HI2 (bv_unsigned sp - 48 + i) ltac:(lia)) as [E W]. split; [exact E | apply W]. }
  assert (ST2 : stk rsegs m2 (bv_unsigned sp - 8240) (bv_unsigned sp - 48)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs m2 a).
    { rewrite <- SEGS. apply HSCR. unfold scratch_k. rewrite SPZ1. change ALLOC_STACK with 8192. left. lia. }
    split; [exact W|].
    destruct (writable_hi_present m2 a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  assert (INH : In (h, 1304) (blocks L' A')) by (rewrite BLK1; apply in_or_app; right; left; reflexivity).
  destruct (present_rw_cells rsegs m2 h 1304%nat) as [junk DST]; [lia | lia | |].
  { intros i Hi. exact (proj1 (block_facts B _ LAWS _ _ _ _ _ _ i HMR' INH Hi)). }
  assert (HSEP : h + 1304 <= A_LIBC \/ A_OFL_HEAD + 8 <= h).
  { pose proof (disj_img h 1304 0x95898 0x95cd0 ltac:(lia) ltac:(lia) FR_img (fun a Ha => img_glob a ltac:(lia))) as D.
    unfold A_LIBC, A_OFL_HEAD. lia. }
  assert (HMODE : h + 1304 <= 0x10564 \/ 0x10566 <= h)
    by exact (disj_img h 1304 0x10564 0x10566 ltac:(lia) ltac:(lia) FR_img img_mode).
  assert (GK2 : forall a, a = 0x95899 \/ 0x95cc0 <= a < 0x95cd0 ->
    mbyte (ms_segs B) m2 a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha.
    apply MF2; [right; apply img_glob; lia | exact (glob_free _ _ _ _ a HMR Ha) | exact (glob_free _ _ _ _ a HMR' Ha)
               | | intros HF; destruct HF as [F|F]; exact F].
    rewrite ERR. intros [H|H]; lia. }
  assert (GKb : forall a, a = 0x95899 \/ 0x95cc0 <= a < 0x95cd0 -> mbyte (ms_segs B) m2 a = mbyte (ms_segs B) mem a)
    by (intros a Ha; exact (proj1 (GK2 a Ha))).
  (* g_said stays writable across malloc: an image range malloc does not own, outside its scratch *)
  assert (WRS2 : wr_at rsegs m2 link_mem.A_G_SAID link_spec.SAID_SIZE).
  { destruct WRS as (W0 & W1 & W2). split; [exact W0|]. split; [exact W1|]. intros i Hi.
    unfold link_mem.A_G_SAID, link_spec.SAID_SIZE in *.
    destruct (MF2 (0x74530 + i)) as [_ Ew];
      [ right; apply img_said; lia | exact (said_free _ _ _ _ (0x74530 + i) HMR ltac:(lia))
      | exact (said_free _ _ _ _ (0x74530 + i) HMR' ltac:(lia)) | rewrite ERR; intros [H|H]; lia
      | intros HF; destruct HF as [F|F]; exact F | ].
    unfold writable_at in Ew. rewrite SEGS in Ew. apply Ew. exact (W2 i Hi). }
  assert (SOK2 : stdio_ok m2).
  { destruct SOK as (S1 & S2 & S3). unfold stdio_ok, A_LIBC, A_OFL_LOCK in *.
    split; [|split].
    - apply (bytes_at_transfer rsegs mem); [exact S1|]. intros i Hi. cbn in Hi. rewrite <- SEGS. apply GKb. lia.
    - pose proof (NOLOCKS _ _ _ _ HMR') as NL. rewrite LIBC_PIN, SEGS in NL.
      apply bytes_at_of_mbyte; [lia | cbn; lia |]. intros i Hi.
      destruct i as [|i]; [|cbn in Hi; lia]. cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact NL.
    - apply (bytes_at_transfer rsegs mem); [exact S3|]. intros i Hi. rewrite length_le4 in Hi.
      rewrite <- SEGS. apply GKb. lia. }
  assert (OE2 : ofl_empty m2).
  { unfold ofl_empty, A_OFL_HEAD in *. apply (rw_cells_transfer rsegs mem); [exact OE|]. intros i Hi. cbn in Hi.
    rewrite <- SEGS. destruct (GK2 (0x95cc8 + i) ltac:(lia)) as [E W]. split; [exact E | apply W]. }
  assert (SOK2n : stdio_ok (normalize rsegs m2)).
  { destruct SOK2 as (S1 & S2 & S3). split; [|split]; apply bytes_at_normalize; assumption. }
  assert (OE2n : ofl_empty (normalize rsegs m2)).
  { unfold ofl_empty in *. apply rw_cells_normalize; [exact RO2 | exact OE2 |].
    intros i Hi. cbn in Hi. unfold A_OFL_HEAD.
    assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity. }
  assert (E2_2 : reg_get R2 2 = sp1) by exact (eq_trans (HPRES 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_9 : reg_get R2 9 = Z_to_bv 64 link_mem.A_G_SAID)
    by exact (eq_trans (eq_trans (HPRES 9 ltac:(unfold callee_saved; lia)) E1_9) A0).
  assert (E2_10 : reg_get R2 10 = Z_to_bv 64 h) by exact A0'.
  assert (E2_18 : reg_get R2 18 = Z_to_bv 64 link_spec.SAID_SIZE)
    by exact (eq_trans (eq_trans (HPRES 18 ltac:(unfold callee_saved; lia)) E1_18) A1).
  assert (E2_19 : reg_get R2 19 = Z_to_bv 64 0x10564)
    by exact (eq_trans (eq_trans (HPRES 19 ltac:(unfold callee_saved; lia)) E1_19) A2).
  assert (E2_20 : reg_get R2 20 = Z_to_bv 64 0) by exact (eq_trans (HPRES 20 ltac:(unfold callee_saved; lia)) E1_20).
  rewrite E1_1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite SEGS, E2_2.
    apply (evt_normalize rsegs); [exact wx_rsegs | exact RO2 |].
    eapply (fmemopen_tail MEMSET OFLADD) with (lo := bv_unsigned sp - 8240) (h := h) (b := link_mem.A_G_SAID)
      (n := link_spec.SAID_SIZE) (junk := junk);
      [ exact E2_10 | lia | exact AL | exact E2_9 | exact E2_18 | exact E2_19 | exact E2_20
      | unfold link_mem.A_G_SAID; lia
      | apply rw_cells_normalize; [exact RO2 | exact DST | ]
      | rewrite SP1; apply rw_cells_normalize; [exact RO2 | exact FR2 | ]
      | rewrite SP1; apply stk_normalize; [exact ST2 | lia]
      | rewrite SP1; lia | lia | rewrite SP1; lia | lia | exact HSEP | exact HMODE
      | exact SOK2n | exact OE2n | apply mem_inv_normalize ].
    - intros i Hi. cbn in Hi. apply (ro_addr_out B SEGS); [lia | apply FR_img; lia].
    - intros i Hi. cbn in Hi. apply ro_addr_hi. lia. }
  intros ms3 (can3 & (s3 & Q3 & REL3 & ROS3) & EQ3).
  destruct Q3 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3n
    & -> & MU3n & WM3n & MI3n & ST3n & (ung & bufb & LUNG & LBUF & MFC3n) & OFL3n & SOK3n).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL3) as [CAN3 HR3].
  remember (ms_mem can3) as m3 eqn:Em3. subst can3. clear Em3.
  assert (RN2 : mem_rel rsegs m2 (normalize rsegs m2)) by (apply mem_rel_normalize; exact RO2).
  pose proof (munch_rel rsegs _ _ _ _ _ RN2 HR3 ROS3 MU3n) as MU3.
  pose proof (wmono_rel rsegs _ _ _ _ RN2 HR3 ROS3 WM3n) as WM3.
  pose proof (ro_agree_same rsegs _ _ RO2 ROS3) as RO3.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ HR3 MFC3n) as MFC3.
  unfold ofl_one in OFL3n. pose proof (rw_cells_of_rel rsegs _ _ _ _ HR3 OFL3n) as OFL3.
  assert (SOK3 : stdio_ok m3).
  { destruct SOK3n as (S1 & S2 & S3).
    split; [|split]; apply (proj2 (bytes_at_rel rsegs _ _ _ _ HR3)); assumption. }
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  rewrite SP1 in MU3, X3.
  assert (SPB : Z_to_bv 64 (bv_unsigned sp - 48 + 48) = sp).
  { replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) by ring. apply Z_to_bv_bv_unsigned. }
  rewrite SPB in X3.
  assert (PRES3 : forall q n i, In (q, n) (user_blocks A') -> 0 <= i < n -> present m3 (ptr_addr L' q + i)).
  { intros q n i Hq Hi.
    destruct (mr_blocks B _ LAWS _ _ _ _ q n i HMR' Hq Hi) as (Hp & Hlo & Hhi & _).
    apply (present_of_writable_out B SEGS m3); [lia | exact (ax_blocks_img AX _ _ _ _ _ _ _ HMR' Hq Hi) |].
    unfold writable_at. apply WM3. destruct Hp as [bb E]. unfold wview. rewrite E. discriminate. }
  assert (MID3 : kb_mid B API 8240 (bv_unsigned sp) L A mem md (fmemopen_w_writes h) L' A' m3 md2).
  { eapply (kb_mid_E B API).
    - eapply (mid_tail IL) with (E2 := fmemopen_w_writes h);
        [ exact MID2 | exact MU3 | rewrite SEGS; exact WM3 | exact PRES3 | | | ].
      + intros x Hx Hs Hw. unfold fmemopen_w_writes, MemFile.MF_BLOCK in Hw. unfold A_OFL_HEAD in *. cbn.
        split; [lia|]. split; [lia|]. split; [lia | exact I].
      + intros x Hx Ho. unfold A_OFL_HEAD. cbn. split; [lia|]. split.
        { intros Hin. apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (x - h) HMR' INH ltac:(lia))))).
          replace (h + (x - h)) with x by ring. exact Ho. }
        split; [|exact I]. intros Hin. exact (glob_free _ _ _ _ x HMR' ltac:(lia) Ho).
      + intros p n i Hin Hin' Hi.
        destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (_ & Hlo & Hhi & _).
        assert (INA : In (ptr_addr L p, n) (b1 ++ b2)).
        { rewrite <- BLK2. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hin). }
        pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR' BLK1 INA) as Dj.
        pose proof (ax_blocks_img AX L A mem md p n i HMR Hin Hi) as NI.
        unfold A_OFL_HEAD. cbn [Frame.outside]. split; [lia|]. split; [lia|]. split; [|exact I].
        intros Hin2. apply NI. apply img_glob. lia.
    - intros a HE. destruct HE as [HE|HE]; [destruct HE as [F|F]; destruct F | exact HE]. }
  assert (PRES : regs_preserved regs R3).
  { eapply (preserved_chain (fun r => (r =? 2) || (r =? 8) || (r =? 9) || (r =? 18) || (r =? 19) || (r =? 20))
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
  assert (GOK3 : guard_ok m3).
  { pose proof MID3 as (HMR3 & _). destruct (ax_statics AX L' A' m3 md2 HMR3) as (GW1 & (g & Hg & GW2) & _).
    rewrite GOT_PIN, GUARD_PIN, SEGS in GW1. rewrite GUARD_PIN, SEGS in GW2.
    split.
    - unfold A_GOT_GUARD, A_GUARD, wz. apply (word_mem_le8 rsegs); [exact GW1 | lia | lia | lia].
    - exists (Z_to_bv 64 g). unfold A_GUARD. apply (word_mem_le8 rsegs); [exact GW2 | lia | lia | lia]. }
  assert (KEPT3 : blocks_kept B L A mem m3 (fun _ => False)).
  { intros a k i Hin _ Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
    cbn [fst snd] in E. injection E as <- <-.
    pose proof MID3 as (_ & _ & _ & _ & _ & _ & _ & MB3 & _).
    exact (MB3 p k' i Hp (UBK _ _ Hp) Hi). }
  assert (WRS3 : wr_at rsegs m3 link_mem.A_G_SAID link_spec.SAID_SIZE).
  { destruct WRS2 as (W0 & W1 & W2). split; [exact W0|]. split; [exact W1|]. intros i Hi. apply WM3. exact (W2 i Hi). }
  (* the block lies outside the image's address range: malloc's fresh_block, through memfile_place *)
  assert (PLACE : memfile_c.mf_place_ok h).
  { apply memfile_place.mf_place_of_fresh; [exact FR_lo|].
    intros i Hi Himg. apply (FR_img i ltac:(unfold MemFile.MF_BLOCK in Hi; lia)).
    unfold in_img in *. rewrite SEGS. exact Himg. }
  destruct (mfw_props m3 h ung bufb MFC3 ltac:(lia) ltac:(unfold MemFile.MF_BLOCK; lia) AL)
    as (MAT & WIN & DYN & WRH).
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite RP.
  apply SR_ret.
  exists L', A', R3, m3, md2, h.
  split; [reflexivity|].
  split; [apply (kb_post B API); [exact MID3 | exact PRES]|].
  split; [rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity|].
  split; [exact NZ|]. split; [exact AL|]. split; [exact FRESH|].
  split; [exists b1, b2; split; [exact BLK1 | exact BLK2]|].
  split; [exact KEPT3|].
  split; [exact UBK|]. split; [exact INIT|]. split; [exact RLEN|]. split; [exact RES'|].
  split.
  { unfold memfile_c.memfile_k. split; [exact MAT|]. split; [exact WIN|]. split; [exact WRH|].
    split; [exact WRS3 | exact PLACE]. }
  split; [exact DYN|]. split; [exact OFL3|]. split; [exact SOK3|]. split; [exact GOK3|]. exact RO3.
Qed.

End F.

(* The same with the leaf contracts discharged by the walks on this tree: strchr, memset, and __ofl_add over
   __ofl_lock / __ofl_unlock (__lock / __unlock). What stays: the frame's pins, malloc's contract, libc_no_locks
   and AllocExtra. *)
Theorem fmemopen_w_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) :
  ms_segs B = rsegs -> ms_malloc B = 0x17514 -> ms_tp B = 0x75608 -> ms_errno_off B = -164 ->
  ms_ctx B = 0x95910 -> ms_lock B = 0x95908 -> ms_libc B = 0x95898 -> ms_got_guard B = 0x208d8 ->
  ms_guard B = 0x95878 -> ms_debruijn B = 0x10778 -> ms_size_classes B = 0x10798 -> ms_small_cnt B = 0x107f8 ->
  ms_med_cnt B = 0x10813 -> ms_vmlock B = None -> ms_debruijn_len B = 32 ->
  malloc_contract B API -> libc_no_locks B API -> AllocExtra B (aa_MR API) ->
  fmemopen_w_contract B API.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HM HN HX.
  exact (fmemopen_w_proof B API H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HM HN HX
    strchr.strchr_holds memset.memset_holds
    (__ofl_add.__ofl_add_holds (__ofl_lock.__ofl_lock_holds __lock.__lock_holds)
       (__ofl_unlock.__ofl_unlock_holds __unlock.__unlock_holds))).
Qed.

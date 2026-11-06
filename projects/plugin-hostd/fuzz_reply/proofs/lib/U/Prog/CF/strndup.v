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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths, module names, addresses and numbers changed; 236 of its 443 lines of code are new or changed and 628 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import strnlen_c memcpy_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition ndup_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S n : Z) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x1deac) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 S)
                  (Z_to_bv 64 (strnlen_res n buf)) (Z_to_bv 64 (strnlen_res n buf + 1)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1608c) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp - 32)%Z [C8 s2; C8 s1; C8 s0; C8 ra]
    /\ bytes_at rsegs m' S buf.

Lemma ndup_run1 : strnlen_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (S n lo : Z) (buf : list byte),
  bytes_at rsegs m S buf -> memchr_ok S 0 n buf -> (0 < S < 2 ^ 64)%Z -> (0 <= n < 2 ^ 64)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 64 <= bv_unsigned sp)%Z ->
  (S + Z.of_nat (length buf) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= S)%Z ->
  mem_inv rsegs m ->
  evt rsegs (ndup_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S n buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1de84) fc None m (seg_rom rsegs)).
Proof.
  intros SNL ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S n lo buf BS MCH SR NR ST LO DISJ MI.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 7 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (SNL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S n lo buf);
      rewrite ?unsigned_lit by lia; first [eassumption | lia]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold strnlen_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call rsegs mm ]
  end.
  cbv delta [mkR].
  do 3 step.
  apply evt_done. unfold ndup_mid.
  do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Definition ndup_end (ra0 sp0 gp tp s00 s01 s02 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7
                  s02 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom rsegs)
    /\ munch [(d, d + Z.of_nat (length src) + 1)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' d [CB (length src) src]
    /\ rw_cells rsegs m' (d + Z.of_nat (length src))%Z [C1 (Z_to_bv 8 0)].

Lemma ndup_run2 : memcpy_contract ->
  forall ra gp tp t0 t1 t2 s2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 : word) (S d : Z) (src junk j1 : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [C8 s02; C8 s01; C8 s00; C8 ra0] ->
  bytes_at rsegs m S src ->
  rw_cells rsegs m d [CB (length src) junk] ->
  rw_cells rsegs m (d + Z.of_nat (length src))%Z [CB 1 j1] ->
  (S + Z.of_nat (length src) <= d \/ d + Z.of_nat (length src) <= S)%Z ->
  (0 < d)%Z -> (d + Z.of_nat (length src) + 1 <= bv_unsigned sp0 - 32)%Z ->
  (0 <= S < 2 ^ 64)%Z -> (32 <= bv_unsigned sp0)%Z ->
  mem_inv rsegs m ->
  evt rsegs (ndup_end ra0 sp0 gp tp s00 s01 s02 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d src m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length src)))
             (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1deac) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra gp tp t0 t1 t2 s2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 S d src junk j1 FR SRC DST DZ SEP DP DB SR SPR MI.
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (US : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (UD : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 (Z.of_nat (length src))) = Z.of_nat (length src)) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(d, d + Z.of_nat (length src) + 1)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. if_false. do 4 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ src junk);
      [ rewrite US; exact SRC | rewrite UN, Nat2Z.id; reflexivity | rewrite UD, UN, Nat2Z.id; exact DST
      | rewrite US, UD, UN; lia | exact MI ]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold memcpy_post in PO; rewrite ?US, ?UD, ?UN, ?Nat2Z.id in PO; revert ms' PO;
      post_call rsegs mm ]
  end.
  cbv delta [mkR].
  do 2 step.
  remember (d + Z.of_nat (length src))%Z as e eqn:Ee.
  step.
  change (le1 (Z_to_bv 64 0)) with (le1 (zxb (Z_to_bv 8 0))).
  mem_after_store.
  do 6 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  subst e.
  apply evt_done. unfold ndup_end.
  do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma strnlen_res_bounds : forall S n buf, memchr_ok S 0 n buf -> (0 <= n)%Z ->
  (0 <= strnlen_res n buf <= Z.of_nat (length buf) /\ strnlen_res n buf <= n)%Z.
Proof.
  intros S n buf M N. unfold memchr_ok in M. unfold strnlen_res. revert M.
  destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:F; intros M.
  - destruct (find_byte_Some _ _ _ F) as (Hl & _). rewrite length_firstn in Hl. lia.
  - lia.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import strndup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Local Open Scope Z_scope.

Section NDup.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALLOC_PC : ms_malloc B = 0x1608c.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Variable RF : ResForm.
Hypothesis MALLOC : malloc_contract_r B API RF.
Hypothesis SNLEN : strnlen_contract.
Hypothesis MEMCPY : memcpy_contract.

Theorem strndup_holds_r : strndup_contract_r B API RF.
Proof using SEGS MALLOC_PC ERRNO_LOW MALLOC SNLEN MEMCPY.
  unfold strndup_contract_r.
  intros L A regs mem md s n buf b PRE A0 A1 NR SRC MCH S0 DISJ HOME LEN RES ROOM RO.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof MALLOC as MAL. unfold malloc_contract_r in MAL. rewrite SEGS, MALLOC_PC in MAL.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold STRNDUP_STACK in *. change ALLOC_STACK with 8192 in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (strnlen_res_bounds s n buf MCH ltac:(lia)) as LB.
  set (l := strnlen_res n buf) in *.
  set (src := firstn (Z.to_nat l) buf).
  assert (LSRC : Z.of_nat (length src) = l) by (unfold src; rewrite length_firstn; lia).
  rewrite SEGS in RO, HWS, HERR, SRC.
  assert (BS : bytes_at rsegs mem s buf) by (apply bytes_at_of_mbyte; [lia | lia | exact SRC]).
  assert (ST : stk rsegs mem (bv_unsigned sp - 8224) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 s) by exact A0. rewrite R10.
    assert (R11 : reg_get regs 11 = Z_to_bv 64 n) by exact A1. rewrite R11.
    unfold STRNDUP.
    apply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO |].
    eapply (ndup_run1 SNLEN); [apply bytes_at_normalize; [exact RO | exact BS] | exact MCH | lia | lia
      | apply stk_normalize; [exact ST | lia] | lia | lia | apply mem_inv_normalize]. }
  intros ms1 (can1 & (s1 & Q1 & REL1 & ROS1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1'
    & -> & MU1' & WM1' & MI1' & FR1' & BS1n).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL1) as [CAN1 HR1].
  remember (ms_mem can1) as m1 eqn:Em1. subst can1. clear Em1.
  assert (RN0 : mem_rel rsegs mem (normalize rsegs mem)) by (apply mem_rel_normalize; exact RO).
  pose proof (munch_rel rsegs _ _ _ _ _ RN0 HR1 ROS1 MU1') as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ RN0 HR1 ROS1 WM1') as WM1.
  pose proof (ro_agree_same rsegs _ _ RO ROS1) as RO1.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ HR1 FR1') as FR1.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ HR1) BS1n) as BS1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x1deac) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 s) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 l) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 (l + 1)) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 64 <= a < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 64, bv_unsigned sp)] a) by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
  assert (MR1 : aa_MR API L A m1 md).
  { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - intros p k i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p k i HMR Hin Hi) as (Hp & H4 & Hc & _).
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  eapply SR_bind.
  { eapply (MAL L A R1 m1 md (l + 1) b); [ | exact RO1 | exact E1_10 | exact RES | exact ROOM].
    split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
    split; [rewrite E1_1; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite SP1; replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring;
            rewrite Z.mod_add by lia; exact HAL|].
    split; [rewrite SP1; change ALLOC_STACK with 8192; lia|].
    split; [rewrite SP1; lia|].
    split; [intros a Ha; rewrite SP1 in Ha; change ALLOC_STACK with 8192 in Ha; rewrite SEGS; apply WM1; apply HWS; lia|].
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
    lia. }
  intros c2 RET.
  destruct RET as (L' & A' & R2 & m2 & md2 & d & -> & POST & A0' & NZ & AL & FRESH & BLK & KEPT & RO2 & GK & UBK & INIT & RLEN
    & RES').
  rewrite SEGS in RO2.
  destruct POST as (HMR' & HWF' & HBD' & HLE & HSTAB & HPRES & HVM & HFRAME & HBLKS & HSCR).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR') as (Hh2 & Hl2 & Hmat2).
  destruct BLK as (b1 & b2 & BLK1 & BLK2).
  pose proof FRESH as (FR_lo & FR_hi & FR_img).
  unfold str_home in HOME. rewrite SEGS in HOME.
  assert (INB : In (d, l + 1) (blocks L' A')) by (rewrite BLK1; apply in_or_app; right; left; reflexivity).
  assert (NOWN : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
  { intros a Ha. split; intros Ho;
      [destruct (owned_low B _ LAWS _ _ _ _ _ HMR Ho) | destruct (owned_low B _ LAWS _ _ _ _ _ HMR' Ho)]; lia. }
  assert (HI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8224 <= a < bv_unsigned sp - 32) ->
     mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
     (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha Hs. destruct (NOWN a (proj1 Ha)) as [N1 N2].
    apply HFRAME; [left; exact Ha | exact N1 | exact N2 | | intros F; exact F].
    unfold scratch_k. rewrite SP1. change ALLOC_STACK with 8192. intros [H|H]; lia. }
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by exact (eq_trans (HPRES 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_8 : reg_get R2 8 = Z_to_bv 64 s) by exact (eq_trans (HPRES 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (E2_9 : reg_get R2 9 = Z_to_bv 64 l) by exact (eq_trans (HPRES 9 ltac:(unfold callee_saved; lia)) E1_9).
  assert (E2_10 : reg_get R2 10 = Z_to_bv 64 d) by exact A0'.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    rewrite <- SEGS. destruct (HI2 (bv_unsigned sp - 32 + i) ltac:(lia) ltac:(lia)) as [E W].
    split; [exact E | apply W]. }
  assert (BS1' : bytes_at rsegs m1 s src).
  { unfold src. rewrite <- (firstn_skipn (Z.to_nat l) buf) in BS1. apply bytes_at_app in BS1. exact (proj1 BS1). }
  assert (KEEP : forall i, 0 <= i < l -> mbyte rsegs m2 (s + i) = mbyte rsegs m1 (s + i)).
  { intros i Hi. destruct HOME as [(H1 & H2) | [(q & k & Hq & H1 & H2) | (H1 & H2 & H3)]].
    - rewrite <- SEGS. exact (proj1 (HI2 (s + i) ltac:(lia) ltac:(lia))).
    - pose proof (KEPT q k (s + i - q) Hq (fun F => F) ltac:(lia)) as E.
      replace (q + (s + i - q)) with (s + i) in E by ring. rewrite <- SEGS. exact E.
    - rewrite (mbyte_ro_agree _ _ _ RO2 (H3 i Hi)), (mbyte_ro_agree _ _ _ RO1 (H3 i Hi)). reflexivity. }
  assert (SRC2 : bytes_at rsegs m2 s src).
  { apply (bytes_at_transfer rsegs m1); [exact BS1'|]. intros i Hi. apply KEEP. lia. }
  destruct (present_rw_cells rsegs m2 d (length src)) as [junk2 DST2]; [lia | lia | |].
  { intros i Hi. exact (proj1 (block_facts B _ LAWS _ _ _ _ _ _ i HMR' INB ltac:(lia))). }
  destruct (present_rw_cells rsegs m2 (d + Z.of_nat (length src)) 1) as [j1 DZ2]; [lia | lia | |].
  { intros i Hi. cbn in Hi. replace (d + Z.of_nat (length src) + i) with (d + (l + i)) by lia.
    exact (proj1 (block_facts B _ LAWS _ _ _ _ _ _ (l + i) HMR' INB ltac:(lia))). }
  assert (SEP2 : s + l <= d \/ d + l <= s).
  { destruct HOME as [(H1 & H2) | [(q & k & Hq & H1 & H2) | (H1 & H2 & H3)]].
    - right. lia.
    - rewrite BLK2 in Hq. pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR' BLK1 Hq) as Dj. lia.
    - destruct (Z_le_gt_dec (s + l) d) as [D|D]; [left; exact D|].
      destruct (Z_le_gt_dec (d + l) s) as [D'|D']; [right; exact D'|]. exfalso.
      apply (FR_img (Z.max s d - d) ltac:(lia)).
      replace (d + (Z.max s d - d)) with (s + (Z.max s d - s)) by lia.
      apply (ro_in_img B SEGS); [lia | exact (H3 (Z.max s d - s) ltac:(lia))]. }
  rewrite E1_1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2_2, E2_8, E2_9, E2_10, SEGS.
    replace (Z_to_bv 64 l) with (Z_to_bv 64 (Z.of_nat (length src))) by (rewrite LSRC; reflexivity).
    apply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO2 |].
    eapply (ndup_run2 MEMCPY) with (sp0 := sp);
      [ apply rw_cells_normalize; [exact RO2 | exact FR2 | intros i Hi; cbn in Hi; apply ro_addr_hi; lia]
      | apply bytes_at_normalize; [exact RO2 | exact SRC2]
      | apply rw_cells_normalize; [exact RO2 | exact DST2 |]
      | apply rw_cells_normalize; [exact RO2 | exact DZ2 |]
      | rewrite LSRC; exact SEP2 | lia | lia | lia | lia | apply mem_inv_normalize ].
    - intros i Hi. cbn [cells_size csize] in Hi. rewrite Nat.add_0_r, LSRC in Hi.
      apply (ro_addr_out B SEGS); [lia | apply FR_img; lia].
    - intros i Hi. cbn in Hi. rewrite LSRC.
      replace (d + l + i) with (d + (l + i)) by ring.
      apply (ro_addr_out B SEGS); [lia | apply FR_img; lia]. }
  intros ms3 (can3 & (s3 & Q3 & REL3 & ROS3) & EQ3). unfold ndup_end in Q3.
  destruct Q3 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3'
    & -> & MU3' & WM3' & MI3' & DST3' & DZ3').
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL3) as [CAN3 HR3].
  remember (ms_mem can3) as m3 eqn:Em3. subst can3. clear Em3.
  assert (RN2 : mem_rel rsegs m2 (normalize rsegs m2)) by (apply mem_rel_normalize; exact RO2).
  pose proof (munch_rel rsegs _ _ _ _ _ RN2 HR3 ROS3 MU3') as MU3.
  pose proof (wmono_rel rsegs _ _ _ _ RN2 HR3 ROS3 WM3') as WM3.
  pose proof (ro_agree_same rsegs _ _ RO2 ROS3) as RO3.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ HR3 DST3') as DST3.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ HR3 DZ3') as DZ3.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  rewrite LSRC in MU3, DZ3.
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite RP.
  assert (OUT3 : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + l + 1) -> outside [(d, d + l + 1)] a)
    by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
  assert (WNB : forall i, 0 <= i < l + 1 -> writable_at rsegs m3 (d + i)).
  { intros i Hi. destruct (Z_lt_ge_dec i l) as [D|D].
    - pose proof DST3 as [_ (_ & _ & W)]. apply W. cbn [cells_size csize]. lia.
    - pose proof DZ3 as [_ (_ & _ & W)]. replace (d + i) with (d + l + 0) by lia. apply W. cbn. lia. }
  assert (BNB : forall i, (i <= Z.to_nat l)%nat ->
            mbyte rsegs m3 (d + Z.of_nat i) = nth_error (src ++ [Z_to_bv 8 0]) i).
  { intros i Hi. destruct (Nat.lt_ge_cases i (length src)) as [D|D].
    - pose proof DST3 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      rewrite nth_error_app1 by exact D. exact (mbyte_of_bytes_at _ _ _ _ _ Hb D).
    - assert (Ei : i = length src) by lia. subst i.
      pose proof DZ3 as [[_ Hb] _]. cbn [cells_bytes cbytes app] in Hb.
      rewrite nth_error_app2, Nat.sub_diag by lia. rewrite LSRC.
      pose proof (mbyte_of_bytes_at _ _ _ _ 0 Hb ltac:(cbn; lia)) as E. cbn [Z.of_nat] in E. rewrite Z.add_0_r in E. exact E. }
  assert (MR3 : aa_MR API L' A' m3 md2).
  { eapply (mr_frame B _ LAWS L' A' m2 m3 md2 md2 HMR').
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR' Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU3 | lia | apply OUT3; [lia|]]. intros Hin.
      apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (a - d) HMR' INB ltac:(lia))))).
      replace (d + (a - d)) with a by ring. exact Ho.
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR' Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU3 | lia | apply OUT3; [lia|] | exact Hp]. intros Hin.
      apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (a - d) HMR' INB ltac:(lia))))).
      replace (d + (a - d)) with a by ring. exact Ho.
    - intros p k i Hin Hi. destruct (mr_blocks B _ LAWS L' A' m2 md2 p k i HMR' Hin Hi) as (Hp & H4 & Hc & _).
      destruct (Z_le_gt_dec d (ptr_addr L' p + i)) as [D1|D1];
        [destruct (Z_lt_ge_dec (ptr_addr L' p + i) (d + (l + 1))) as [D2|D2]|].
      + apply (present_of_writable_out B SEGS m3 (ptr_addr L' p + i) ltac:(lia)).
        * replace (ptr_addr L' p + i) with (d + (ptr_addr L' p + i - d)) by ring. apply FR_img. lia.
        * replace (ptr_addr L' p + i) with (d + (ptr_addr L' p + i - d)) by ring. apply WNB. lia.
      + eapply munch_present; [exact MU3 | lia | apply OUT3; lia | exact Hp].
      + eapply munch_present; [exact MU3 | lia | apply OUT3; lia | exact Hp].
    - reflexivity.
    - exact Hh2.
    - exact Hl2.
    - exact Hmat2. }
  apply SR_ret.
  exists L', A', R3, m3, md2, d.
  split; [reflexivity|].
  split.
  { split; [exact MR3|]. split; [exact HWF'|]. split; [exact HBD'|]. split; [exact HLE|]. split; [exact HSTAB|].
    split.
    { eapply (preserved_chain (fun r => (r =? 2) || (r =? 8) || (r =? 9) || (r =? 18)) regs R1 R2 R3 _ _ X1 HPRES X3).
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
    split; [exact HVM|].
    split.
    { intros a HA NO1 NO2 NS NE. cbn beta in NE.
      assert (AR : 0 <= a < 2 ^ 64) by (destruct HA as [HA|HA]; [lia | pose proof (in_img_low B SEGS a HA); lia]).
      assert (NSP : ~ (bv_unsigned sp - 8224 <= a < bv_unsigned sp)).
      { intro H. apply NS. left. unfold spZ. change (getr regs 2) with sp. lia. }
      assert (NER : ~ (errno_addr B <= a < errno_addr B + 4)) by (intro H; apply NS; right; exact H).
      pose proof (munch_mbyte (ms_segs B) _ _ _ a MU1 AR (OUT1 a AR ltac:(lia))) as E01.
      pose proof (munch_writable (ms_segs B) _ _ _ a MU1 AR (OUT1 a AR ltac:(lia))) as W01.
      assert (H12 : mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
                    (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
      { apply HFRAME; [exact HA | exact NO1 | exact NO2 | | intros F; exact F].
        unfold scratch_k. rewrite SP1. change ALLOC_STACK with 8192. intros [H|H]; [lia | exact (NER H)]. }
      pose proof (munch_mbyte (ms_segs B) _ _ _ a MU3 AR (OUT3 a AR ltac:(lia))) as E23.
      pose proof (munch_writable (ms_segs B) _ _ _ a MU3 AR (OUT3 a AR ltac:(lia))) as W23.
      split; [rewrite E23, (proj1 H12), E01; reflexivity | rewrite W01, (proj2 H12), W23; tauto]. }
    split.
    { intros p k i Hin Hin' Hi.
      destruct (mr_blocks B _ LAWS L A mem md p k i HMR Hin Hi) as (_ & Hlo & Hhi & _).
      assert (INA : In (ptr_addr L p, k) (b1 ++ b2)).
      { rewrite <- BLK2. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hin). }
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR' BLK1 INA) as Dj.
      rewrite (munch_mbyte _ _ _ _ (ptr_addr L p + i) MU3 ltac:(lia) (OUT3 (ptr_addr L p + i) ltac:(lia) ltac:(lia))).
      rewrite (HBLKS p k i Hin Hin' Hi).
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    intros a Ha. unfold scratch_k, spZ in Ha. change (getr regs 2) with sp in Ha.
    rewrite SEGS. apply WM3. rewrite <- SEGS.
    destruct Ha as [Ha|Ha].
    - destruct (Z_lt_ge_dec a (bv_unsigned sp - 32)) as [D|D].
      + apply HSCR. unfold scratch_k. rewrite SP1. change ALLOC_STACK with 8192. left. lia.
      + destruct (NOWN a ltac:(lia)) as [N1 N2].
        apply (proj1 (proj2 (HFRAME a ltac:(left; lia) N1 N2 ltac:(unfold scratch_k; rewrite SP1;
                 change ALLOC_STACK with 8192; intros [H|H]; lia) (fun F => F)))).
        rewrite SEGS. apply WM1. apply HWS. lia.
    - apply HSCR. right. exact Ha. }
  split; [rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity|].
  split; [exact NZ|]. split; [exact AL|]. split; [exact FRESH|].
  split; [exists b1, b2; split; [exact BLK1 | exact BLK2]|].
  split.
  { intros q k i Hq _ Hi.
    destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hq Hi) as (_ & Hlo & Hhi & _).
    assert (Hq' : In (q, k) (b1 ++ b2)) by (rewrite <- BLK2; exact Hq).
    pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR' BLK1 Hq') as Dj.
    rewrite (munch_mbyte _ _ _ _ (q + i) MU3 ltac:(lia) (OUT3 (q + i) ltac:(lia) ltac:(lia))).
    rewrite (KEPT q k i Hq (fun F => F) Hi).
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split; [exact BNB|].
  split; [exact RO3|].
  split.
  { intros i Hi.
    assert (OWN : forall L0 A0, owned B L0 A0 (ms_got_guard B + i)) by (intros; right; unfold static_owned; lia).
    destruct (owned_low B _ LAWS _ _ _ _ _ HMR (OWN L A)) as [G1 G2].
    assert (NB : ~ (d <= ms_got_guard B + i < d + l + 1)).
    { intros Hin. apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (ms_got_guard B + i - d) HMR' INB ltac:(lia))))).
      replace (d + (ms_got_guard B + i - d)) with (ms_got_guard B + i) by ring. apply OWN. }
    rewrite (munch_mbyte _ _ _ _ (ms_got_guard B + i) MU3 ltac:(lia) (OUT3 (ms_got_guard B + i) ltac:(lia) NB)).
    rewrite (GK i Hi).
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split; [exact UBK|]. split; [exact INIT|]. split; [exact RLEN|]. exact RES'.
Qed.

End NDup.

(* The instance at the frame's sbound form. *)
Theorem strndup_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B)
    (SEGS : ms_segs B = rsegs) (MALLOC_PC : ms_malloc B = 0x1608c) (ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling)
    (MALLOC : malloc_contract_r B API sb_form) (SNLEN : strnlen_contract) (MEMCPY : memcpy_contract) :
  strndup_contract B API.
Proof. exact (strndup_holds_r B API SEGS MALLOC_PC ERRNO_LOW sb_form MALLOC SNLEN MEMCPY). Qed.

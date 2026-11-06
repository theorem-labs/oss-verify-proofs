From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strlen_c memcpy_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition dup_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR (Z_to_bv 64 0x20f8c) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 S)
                  (Z_to_bv 64 (Z.of_nat (length str) + 1)) (Z_to_bv 64 (Z.of_nat (length str) + 1)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x18c10) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp - 32)%Z [CB 8 junk; C8 s1; C8 s0; C8 ra]
    /\ bytes_at rsegs m' S (str ++ Z_to_bv 8 0 :: slack).

Lemma dup_run1 : strlen_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (S lo : Z) (str slack : list byte),
  bytes_at rsegs m S (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= S)%Z ->
  mem_inv rsegs m ->
  evt rsegs (dup_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20f68) fc None m (seg_rom rsegs)).
Proof.
  intros SLEN ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S lo str slack BS NONUL PAD ST LO DISJ MI.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB. rewrite length_app in SB, DISJ. cbn [length] in SB, DISJ.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (US : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 6 step.
  call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str slack).
  1-4: rewrite ?US; first [eassumption | lia].
  cbv delta [mkR].
  do 3 step.
  apply evt_done. unfold dup_mid.
  do 16 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma dup_run2 : memcpy_contract ->
  forall ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 : word) (S d : Z) (src junk junk2 : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [CB 8 junk; C8 s01; C8 s00; C8 ra0] ->
  bytes_at rsegs m S src ->
  rw_cells rsegs m d [CB (length src) junk2] ->
  (S + Z.of_nat (length src) <= d \/ d + Z.of_nat (length src) <= S)%Z ->
  (0 < d < 2 ^ 64)%Z -> (0 <= S < 2 ^ 64)%Z -> (32 <= bv_unsigned sp0)%Z ->
  mem_inv rsegs m ->
  evt rsegs (memcpy_post ra0 sp0 gp tp s00 s01 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (Z_to_bv 64 d) (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length src))) src m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length src)))
             (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20f8c) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 S d src junk junk2 FR SRC DST SEP DR SR SPR MI.
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (US : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (UD : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 (Z.of_nat (length src))) = Z.of_nat (length src)) by (apply unsigned_lit; lia).
  step. if_false. do 7 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  eapply (MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ src junk2).
  - rewrite US. exact SRC.
  - rewrite UN, Nat2Z.id. reflexivity.
  - rewrite UD, UN, Nat2Z.id. exact DST.
  - rewrite US, UD, UN. lia.
  - exact MI.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB strdup_c.
Local Open Scope Z_scope.

Section Dup.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALLOC_PC : ms_malloc B = 0x18c10.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis MALLOC : malloc_contract B API.
Hypothesis SLEN : strlen_contract.
Hypothesis MEMCPY : memcpy_contract.

Theorem strdup_holds : strdup_contract B API.
Proof using SEGS MALLOC_PC ERRNO_LOW MALLOC SLEN MEMCPY.
  unfold strdup_contract.
  intros L A regs mem md s str slack b PRE A0 SRC NONUL PAD S0 DISJ HOME LEN RES ROOM RO.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof MALLOC as MAL. unfold malloc_contract in MAL. rewrite SEGS, MALLOC_PC in MAL.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold STRDUP_STACK in *. change ALLOC_STACK with 8192 in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  set (l := Z.of_nat (length str)) in *.
  assert (LALL : Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) = l + 1 + Z.of_nat (length slack))
    by (rewrite length_app; cbn [length]; lia).
  assert (LSRC : Z.of_nat (length (str ++ [Z_to_bv 8 0])) = l + 1) by (rewrite length_app; cbn [length]; lia).
  rewrite LALL in DISJ.
  rewrite SEGS in RO, HWS, HERR, SRC.
  assert (BS : bytes_at rsegs mem s (str ++ Z_to_bv 8 0 :: slack)).
  { apply bytes_at_of_mbyte; [lia | rewrite LALL; lia | exact SRC]. }
  assert (ST : stk rsegs mem (bv_unsigned sp - 8224) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 s) by exact A0. rewrite R10.
    unfold STRDUP.
    apply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO |].
    eapply (dup_run1 SLEN); [apply bytes_at_normalize; [exact RO | exact BS] | exact NONUL | exact PAD
      | apply stk_normalize; [exact ST | lia] | lia | rewrite LALL; lia | apply mem_inv_normalize]. }
  intros ms1 (can1 & (s1 & Q1 & REL1 & ROS1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' & junk
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
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x20f8c) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 s) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 (l + 1)) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 (l + 1)) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 32 <= a < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 32, bv_unsigned sp)] a) by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
  assert (MR1 : aa_MR API L A m1 md).
  { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (Hp & H4 & Hc & _).
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
  assert (E2_9 : reg_get R2 9 = Z_to_bv 64 (l + 1))
    by exact (eq_trans (HPRES 9 ltac:(unfold callee_saved; lia)) E1_9).
  assert (E2_10 : reg_get R2 10 = Z_to_bv 64 d) by exact A0'.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32)
                  [CB 8 junk; C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    rewrite <- SEGS. destruct (HI2 (bv_unsigned sp - 32 + i) ltac:(lia) ltac:(lia)) as [E W].
    split; [exact E | apply W]. }
  assert (BS1' : bytes_at rsegs m1 s (str ++ [Z_to_bv 8 0])).
  { replace (str ++ Z_to_bv 8 0 :: slack) with ((str ++ [Z_to_bv 8 0]) ++ slack) in BS1
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BS1. exact (proj1 BS1). }
  assert (KEEP : forall i, 0 <= i < l + 1 -> mbyte rsegs m2 (s + i) = mbyte rsegs m1 (s + i)).
  { intros i Hi. destruct HOME as [(H1 & H2) | [(q & k & Hq & H1 & H2) | (H1 & H2 & H3)]].
    - rewrite <- SEGS. exact (proj1 (HI2 (s + i) ltac:(lia) ltac:(lia))).
    - pose proof (KEPT q k (s + i - q) Hq (fun F => F) ltac:(lia)) as E.
      replace (q + (s + i - q)) with (s + i) in E by ring. rewrite <- SEGS. exact E.
    - rewrite (mbyte_ro_agree _ _ _ RO2 (H3 i Hi)), (mbyte_ro_agree _ _ _ RO1 (H3 i Hi)). reflexivity. }
  assert (SRC2 : bytes_at rsegs m2 s (str ++ [Z_to_bv 8 0])).
  { apply (bytes_at_transfer rsegs m1); [exact BS1'|]. intros i Hi. apply KEEP. lia. }
  destruct (present_rw_cells rsegs m2 d (length (str ++ [Z_to_bv 8 0]))) as [junk2 DST2];
    [lia | rewrite LSRC; lia | |].
  { intros i Hi. rewrite LSRC in Hi. exact (proj1 (block_facts B _ LAWS _ _ _ _ _ _ i HMR' INB Hi)). }
  assert (SEP2 : s + (l + 1) <= d \/ d + (l + 1) <= s).
  { destruct HOME as [(H1 & H2) | [(q & k & Hq & H1 & H2) | (H1 & H2 & H3)]].
    - right. lia.
    - rewrite BLK2 in Hq. pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR' BLK1 Hq) as Dj. lia.
    - destruct (Z_le_gt_dec (s + (l + 1)) d) as [D|D]; [left; exact D|].
      destruct (Z_le_gt_dec (d + (l + 1)) s) as [D'|D']; [right; exact D'|]. exfalso.
      apply (FR_img (Z.max s d - d) ltac:(lia)).
      replace (d + (Z.max s d - d)) with (s + (Z.max s d - s)) by lia.
      apply (ro_in_img B SEGS); [lia | exact (H3 (Z.max s d - s) ltac:(lia))]. }
  rewrite E1_1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2_2, E2_8, E2_9, E2_10, SEGS.
    replace (Z_to_bv 64 (l + 1)) with (Z_to_bv 64 (Z.of_nat (length (str ++ [Z_to_bv 8 0]))))
      by (rewrite LSRC; reflexivity).
    apply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO2 |].
    eapply (dup_run2 MEMCPY) with (sp0 := sp);
      [ apply rw_cells_normalize; [exact RO2 | exact FR2 | intros i Hi; cbn in Hi; apply ro_addr_hi; lia]
      | apply bytes_at_normalize; [exact RO2 | exact SRC2]
      | apply rw_cells_normalize; [exact RO2 | exact DST2 |]
      | rewrite LSRC; exact SEP2 | lia | lia | lia | apply mem_inv_normalize ].
    intros i Hi. cbn [cells_size csize] in Hi. rewrite Nat.add_0_r, LSRC in Hi.
    apply (ro_addr_out B SEGS); [lia | apply FR_img; lia]. }
  intros ms3 (can3 & (s3 & Q3 & REL3 & ROS3) & EQ3). unfold memcpy_post in Q3.
  destruct Q3 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3'
    & -> & MU3' & WM3' & MI3' & DST3' & SRC3').
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL3) as [CAN3 HR3].
  remember (ms_mem can3) as m3 eqn:Em3. subst can3. clear Em3.
  assert (RN2 : mem_rel rsegs m2 (normalize rsegs m2)) by (apply mem_rel_normalize; exact RO2).
  pose proof (munch_rel rsegs _ _ _ _ _ RN2 HR3 ROS3 MU3') as MU3.
  pose proof (wmono_rel rsegs _ _ _ _ RN2 HR3 ROS3 WM3') as WM3.
  pose proof (ro_agree_same rsegs _ _ RO2 ROS3) as RO3.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ HR3 DST3') as DST3.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  rewrite !unsigned_lit in MU3, DST3 by lia. rewrite LSRC in MU3. rewrite Nat2Z.id in DST3.
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite RP.
  assert (OUT3 : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + (l + 1)) -> outside [(d, d + (l + 1))] a)
    by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
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
    - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L' A' m2 md2 p n i HMR' Hin Hi) as (Hp & H4 & Hc & _).
      destruct (Z_le_gt_dec d (ptr_addr L' p + i)) as [D1|D1];
        [destruct (Z_lt_ge_dec (ptr_addr L' p + i) (d + (l + 1))) as [D2|D2]|].
      + apply (present_of_writable_out B SEGS m3 (ptr_addr L' p + i) ltac:(lia)).
        * replace (ptr_addr L' p + i) with (d + (ptr_addr L' p + i - d)) by ring. apply FR_img. lia.
        * pose proof DST3 as [_ (_ & _ & W)].
          assert (Hb : 0 <= ptr_addr L' p + i - d < Z.of_nat (cells_size [CB (length (str ++ [Z_to_bv 8 0])) (str ++ [Z_to_bv 8 0])]))
            by (cbn [cells_size csize]; rewrite Nat.add_0_r, LSRC; lia).
          specialize (W (ptr_addr L' p + i - d) Hb).
          replace (d + (ptr_addr L' p + i - d)) with (ptr_addr L' p + i) in W by ring. exact W.
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
    { eapply (preserved_chain (fun r => (r =? 2) || (r =? 8) || (r =? 9)) regs R1 R2 R3 _ _ X1 HPRES X3).
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
    { intros p n i Hin Hin' Hi.
      destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (_ & Hlo & Hhi & _).
      assert (INA : In (ptr_addr L p, n) (b1 ++ b2)).
      { rewrite <- BLK2. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hin). }
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR' BLK1 INA) as Dj.
      rewrite (munch_mbyte _ _ _ _ (ptr_addr L p + i) MU3 ltac:(lia) (OUT3 (ptr_addr L p + i) ltac:(lia) ltac:(lia))).
      rewrite (HBLKS p n i Hin Hin' Hi).
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
  split.
  { intros i Hi. pose proof DST3 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
    apply (mbyte_of_bytes_at _ _ _ _ _ Hb). rewrite length_app. cbn [length]. lia. }
  split; [exact RO3|].
  split.
  { intros i Hi.
    assert (OWN : forall L0 A0, owned B L0 A0 (ms_got_guard B + i)) by (intros; right; unfold static_owned; lia).
    destruct (owned_low B _ LAWS _ _ _ _ _ HMR (OWN L A)) as [G1 G2].
    assert (NB : ~ (d <= ms_got_guard B + i < d + (l + 1))).
    { intros Hin. apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (ms_got_guard B + i - d) HMR' INB ltac:(lia))))).
      replace (d + (ms_got_guard B + i - d)) with (ms_got_guard B + i) by ring. apply OWN. }
    rewrite (munch_mbyte _ _ _ _ (ms_got_guard B + i) MU3 ltac:(lia) (OUT3 (ms_got_guard B + i) ltac:(lia) NB)).
    rewrite (GK i Hi).
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split; [exact UBK|]. split; [exact INIT|]. split; [exact RLEN|]. exact RES'.
Qed.

End Dup.

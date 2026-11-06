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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module names, addresses and numbers changed; 593 of its 651 lines of code are new or changed and 777 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/sup_remove.v, with its module paths, module names, addresses and numbers changed; 165 of its 244 lines of code are new or changed and 572 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma sra_head :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 16 <= bv_unsigned sp)%Z -> (0x40000 <= lo)%Z ->
  evt rsegs (fun ms' => exists m' junk,
       ms' = MS (mkR (Z_to_bv 64 0x16718) (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 3)
                     a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 16)%Z [CB 8 junk; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16708) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 16%nat junk [] [8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 4 step.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma sra_tail :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 : word) (junk : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 16) [CB 8 junk; C8 ra0] ->
  (0x40000 <= bv_unsigned sp0 - 16)%Z ->
  evt rsegs (fun ms' =>
       ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0x10417) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16310) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16718) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 junk FR LO.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 6 step.
  try replace (Z_to_bv 64 (bv_unsigned sp0 - 16 + 16)) with sp0
    by (replace (bv_unsigned sp0 - 16 + 16)%Z with (bv_unsigned sp0) by lia; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB RecSeq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecStep RecGlue RecAnsB RecTail RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import record_c answer_c sup_remove_all_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Local Open Scope Z_scope.

Lemma sra_mod_host_shape : forall m, ro_agree rsegs m -> ans_shape rsegs m 0x10417 REC_MOD_HOST_SHAPE.
Proof.
  intros m RA.
  assert (RO : forall i, 0 <= i <= 6 -> ro_addr rsegs (Z_to_bv 64 (0x10417 + i)) = true).
  { intros i Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
    repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity. }
  split.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    unfold wa. rewrite (RA _ (RO (Z.of_nat i) ltac:(lia))).
    assert (C : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat \/ i = 4%nat \/ i = 5%nat \/ i = 6%nat) by lia.
    repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity.
  - split; [apply no0_nz; vm_compute; reflexivity|]. split; [cbn; unfold LMAX; lia|].
    split; [apply fits_shape_set; left; reflexivity|]. intros i Hi. apply RO. cbn in Hi. lia.
Qed.

Lemma sra_code_record : forall R fn As, r_code (rec_record R fn As) = r_code R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma sra_stub_len : forall R fn As x chg, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_answer (rec_record R fn As) (fn, As) x chg)) <= Nat.max (length x) 16)%nat.
Proof.
  intros R fn As x chg H. rewrite rec_answer_text. destruct (r_refuse (rec_record R fn As) =? 0).
  - pose proof (inst_length x). lia.
  - rewrite sra_code_record. pose proof (resp_length (r_code R) H). lia.
Qed.

Ltac sra_saved :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr ?; unfold callee_saved in Hr;
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
              r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  clear Hr;
  repeat (destruct C as [C|C]; [subst r; first [lia | reflexivity]|]);
  subst r; first [lia | reflexivity].

Section SRA.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis REC : record_contract B API.
Hypothesis ANS : answer_contract B API.

Theorem sup_remove_all_holds : sup_remove_all_contract B API.
Proof using SEGS ERRNO_LOW GOWN AX CTX SLACK REC ANS.
  unfold sup_remove_all_contract.
  intros L A regs mem md R O b PRE GR RA FRM F18 RES ROOM.
  pose proof alloc_ceiling_val as AC.
  assert (IL : img_low B)
    by (apply (img_low_of_check B (2 ^ 21)); [unfold img_check; rewrite SEGS; vm_compute; reflexivity | lia]).
  assert (KV : RECORD_K = 8336) by reflexivity.
  assert (AK : ANSWER_K <= SUP_REMOVE_ALL_K) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof PRE as (PRK & HTS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (kb_md B API _ _ _ _ HMR) as [Hh Hl].
  pose proof (kb_stk B API IL _ _ _ _ _ _ PRK ltac:(unfold SUP_REMOVE_ALL_K; lia)) as ST. rewrite SEGS in ST.
  rewrite SEGS in GR, RA, F18.
  pose proof (rec_rep_calls_le rsegs G_REC REC_SC L A mem R O GR) as C1.
  pose proof GR as (Q0 & (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HCODE & _) & _) & _).
  pose proof (sinv_init B API SUP_REMOVE_ALL_K L A regs mem md R O b PRK ltac:(unfold SUP_REMOVE_ALL_K; lia)
                GR RA F18 RES) as SI0.
  change (sup_remove_all_m R)
    with (rec_answer (rec_record R REC_REMOVE_ALL []) (REC_REMOVE_ALL, []) REC_MOD_HOST_SHAPE true) in ROOM.
  unfold sup_remove_all_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  assert (LT : (length (snd (rec_answer (rec_record R REC_REMOVE_ALL []) (REC_REMOVE_ALL, []) REC_MOD_HOST_SHAPE true))
                 <= 16)%nat).
  { pose proof (sra_stub_len R REC_REMOVE_ALL [] REC_MOD_HOST_SHAPE true HCODE) as H.
    assert (LX : length REC_MOD_HOST_SHAPE = 6%nat) by reflexivity. rewrite LX in H. exact H. }
  set (sp := getr regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SUP_REMOVE_ALL_K in HCEIL.
  eapply (kb_run B regs (Z_to_bv 64 SUP_REMOVE_ALL) mem md
    (fun R1 pc' m' => exists junk,
       pc' = Z_to_bv 64 0x1612c /\
       munch [(bv_unsigned sp - 16, bv_unsigned sp)] mem m' /\ wmono rsegs mem m' /\
       rw_cells rsegs m' (bv_unsigned sp - 16) [CB 8 junk; C8 (getr regs 1)] /\
       getr R1 1 = Z_to_bv 64 0x16718 /\ getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 16) /\
       getr R1 10 = Z_to_bv 64 3 /\
       (forall r, callee_saved r -> r <> 2 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)))
    _ Hh Hl).
  { unfold rmk. fold sp. rewrite SEGS. eapply evt_cut.
    - eapply (sra_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fp_regs fp_csr mem
                (bv_unsigned sp - SUP_REMOVE_ALL_K));
        [exact ST | unfold SUP_REMOVE_ALL_K; lia | unfold SUP_REMOVE_ALL_K; lia].
    - intros ms' (m' & junk & -> & MU & WM & FR). apply evt_done.
      do 3 eexists. split; [reflexivity|]. exists junk.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact FR|].
      do 3 (split; [reflexivity|]). sra_saved. }
  intros R1 pc1 m1 regs1 (junk & -> & MU1 & WM1 & FR1 & E1_1 & E1_2 & E1_10 & E1_S) HG1.
  rewrite <- HG1 in E1_1, E1_2, E1_10.
  assert (E1S : forall r, callee_saved r -> r <> 2 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r H1 H2. rewrite HG1. exact (E1_S r H1 H2). }
  clear E1_S.
  assert (SP1 : spZ regs1 = bv_unsigned sp - 16) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (HW1 : forall a, 0 <= a < 2 ^ 64 -> ~ outside [(bv_unsigned sp - 16, bv_unsigned sp)] a ->
            bv_unsigned sp - SUP_REMOVE_ALL_K <= a < bv_unsigned sp).
  { intros a Ra Hm. cbn in Hm. unfold SUP_REMOVE_ALL_K. lia. }
  pose proof (sinv_stack B API SEGS GOWN AX SUP_REMOVE_ALL_K (bv_unsigned sp) L A mem md O L A mem md R O b m1 _
                SI0 MU1 WM1 HW1) as SI1.
  rewrite SEGS.
  apply (sinv_record B API SEGS ERRNO_LOW AX REC SUP_REMOVE_ALL_K (bv_unsigned sp) L A mem md O L A m1 md R O b regs1
           REC_REMOVE_ALL _ SI1);
    [ rewrite E1_1; apply bv_eq; vm_compute; reflexivity
    | rewrite SP1; replace (bv_unsigned sp - 16) with (bv_unsigned sp + (-1) * 16) by ring;
      rewrite Z.mod_add by lia; exact HAL
    | rewrite SP1, KV; unfold SUP_REMOVE_ALL_K; lia
    | rewrite SP1; lia
    | exact (eq_trans (E1S 4 ltac:(unfold callee_saved; lia) ltac:(lia)) HTP)
    | exact E1_10
    | unfold REC_FN_COUNT, REC_REMOVE_ALL; lia
    | ].
  intros L1 A1 regs2 m2 md2 O1 SI2 BLE2 PR R10 FK.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 16) [CB 8 junk; C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct (FK (bv_unsigned sp - 16 + i) ltac:(rewrite SP1; lia)) as [E W].
    split; [exact E | apply W]. }
  pose proof SI2 as (RJ2 & GR3 & ON2 & B12 & B22 & RA3 & F183 & RS3).
  pose proof RJ2 as (PM & _).
  assert (E2_2 : getr regs2 2 = Z_to_bv 64 (bv_unsigned sp - 16))
    by exact (eq_trans (PR 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2S : forall r, callee_saved r -> r <> 2 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r H1 H2. rewrite (PR r H1). exact (E1S r H1 H2). }
  destruct (kb_md B API _ _ _ _ PM) as [Hh2 Hl2].
  rewrite E1_1. rewrite <- SEGS.
  eapply (kb_run B regs2 (Z_to_bv 64 0x16718) m2 md2
    (fun R3 pc' m' =>
       pc' = Z_to_bv 64 0x16310 /\ m' = m2 /\
       getr R3 1 = getr regs 1 /\ getr R3 2 = sp /\ getr R3 10 = getr regs2 10 /\
       getr R3 11 = Z_to_bv 64 0x10417 /\ getr R3 12 = Z_to_bv 64 1 /\ regs_preserved regs R3)
    _ Hh2 Hl2).
  { unfold rmk. rewrite SEGS. rewrite E2_2. eapply evt_cut.
    - eapply (sra_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fp_regs fp_csr m2
                sp (getr regs 1) junk); [exact FR2 | lia].
    - intros ms' ->. apply evt_done.
      do 3 eexists. split; [reflexivity|].
      do 7 (split; [reflexivity|]).
      intros r Hr. pose proof Hr as Hr0. unfold callee_saved in Hr.
      assert (C : r = 2 \/ r <> 2) by lia.
      destruct C as [->|H2]; [reflexivity|].
      rewrite <- (E2S r Hr0 H2).
      assert (C : r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                  r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      clear Hr Hr0 H2.
      repeat (destruct C as [C|C]; [subst r; reflexivity|]). subst r. reflexivity. }
  intros R3 pc3 m3 regs3 (-> & -> & E3_1 & E3_2 & E3_10 & E3_11 & E3_12 & P3) HG3.
  rewrite <- HG3 in E3_1, E3_2, E3_10, E3_11, E3_12.
  assert (RP3 : regs_preserved regs regs3) by exact (kb_preserved_getr regs R3 regs3 P3 HG3).
  assert (BLEb : sb_le (sb_shift b A A1) b) by (rewrite sb_shift_refl in BLE2; exact BLE2).
  eapply SR_mono.
  { apply (answer_tail B API SEGS AX CTX ERRNO_LOW ANS SLACK SUP_REMOVE_ALL_K L A regs mem md O L1 A1 regs3 m2 md2
             (rec_record R REC_REMOVE_ALL []) O1 b b (sb_shift b A A1) (rec_slot R) 0x10417
             (REC_REMOVE_ALL, []) REC_MOD_HOST_SHAPE true PRE AK RJ2 E3_1
             ltac:(unfold spZ; rewrite E3_2; reflexivity) RP3).
    - rewrite E3_10. exact R10.
    - exact E3_11.
    - rewrite E3_12. reflexivity.
    - rewrite SEGS. exact GR3.
    - intros _. rewrite SEGS. exact (sra_mod_host_shape m2 RA3).
    - intros _ _. exact (ans_entry_record R REC_REMOVE_ALL [] C1).
    - exact FRM.
    - rewrite SEGS. exact F183.
    - rewrite SEGS. exact RA3.
    - exact RS3.
    - reflexivity.
    - exact BLEb.
    - apply (room_slots_mono _ _ _ 17 (sb_malloc_mono _ _ _ (sb_malloc_mono _ _ _ BLEb))); [lia | exact ROOM].
    - exact ON2.
    - exact B12.
    - exact B22. }
  intros c' TR. unfold sup_remove_all_ret.
  destruct TR as (fx' & L' & A' & regs' & mem' & md' & O' & q & TR).
  exists fx', L', A', regs', mem', md', (fst (sup_remove_all_m R)), O', (snd (sup_remove_all_m R)), q.
  split; [apply surjective_pairing | exact TR].
Qed.

End SRA.

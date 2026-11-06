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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths, module names and addresses changed; 492 of its 548 lines of code are new or changed and 779 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/sup_pin_accept.v, with its module names, addresses and numbers changed; 285 of its 656 lines of code are new or changed and 177 lines of the source are left out. *)
From Stdlib Require Import String ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import rec_shape_of_c.
Import ListNotations.
Open Scope Z_scope.

Definition slw_rom_chk (a : Z) (bs : list byte) : bool :=
  forallb (fun i => ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) &&
     match seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)), nth_error bs i with
     | Some b, Some c => Z.eqb (bv_unsigned b) (bv_unsigned c)
     | _, _ => false
     end) (seq 0 (length bs)).

Lemma slw_rom_chk_bytes : forall m a bs, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  slw_rom_chk a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs RA H0 H1 C. split; [lia|]. split; [lia|]. intros i Hi.
  unfold slw_rom_chk in C.
  pose proof (proj1 (forallb_forall _ _) C i ltac:(apply in_seq; lia)) as Ci. cbv beta in Ci.
  apply andb_prop in Ci as [Cr Cv].
  unfold wa. rewrite (RA _ Cr).
  destruct (seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [|discriminate].
  destruct (nth_error bs i) as [c|]; [|discriminate].
  apply Z.eqb_eq in Cv. f_equal. apply bv_eq. exact Cv.
Qed.

Lemma slw_ro_agree_of_inv : forall m, mem_inv rsegs m -> ro_agree rsegs m.
Proof.
  intros m MI x Hx. unfold mrd. destruct (m x) as [b|] eqn:E; [|reflexivity].
  rewrite (MI _ _ E) in Hx. discriminate.
Qed.

Lemma slw_pre :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16d48) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 a1 a0
                     (Z_to_bv 64 15) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16d24) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 9 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma slw_mid1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16d54) sp gp tp t0 t1 t2 s0 s1 a0 s1 a2 a3 a4 a5 a6 a7
                                    a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16d48) fc None m (seg_rom rsegs)).
Proof.
  intros. do 3 step. apply evt_done. reflexivity.
Qed.

Lemma slw_mid2 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16d60) sp gp tp t0 t1 t2 s0 s1 s2 s0 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16d54) fc None m (seg_rom rsegs)).
Proof.
  intros. do 3 step. apply evt_done. reflexivity.
Qed.

Lemma slw_tail :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s10' s20 : word),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [C8 s20; C8 s10'; C8 s00; C8 ra0] -> 32 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s10' s2 a0 (Z_to_bv 64 1) a3 a4 a5 a6 a7
                                    s20 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x16310) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16d70) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s10' s20 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 9 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma slw_verb : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x104ed (str_bytes "lv2_worker_set"%string).
Proof.
  intros m MI. apply slw_rom_chk_bytes; [exact (slw_ro_agree_of_inv m MI) | lia | cbn; lia | vm_compute; reflexivity].
Qed.

Lemma slw_shape : shape_find shape_rows (str_bytes "lv2_worker_set"%string) = 0x10417.
Proof. vm_compute. reflexivity. Qed.

Lemma slw_after : rec_shape_of_contract ->
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sp0 ra0 s00 s10' s20 : word),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [C8 s20; C8 s10'; C8 s00; C8 ra0] ->
  stk rsegs m lo (bv_unsigned sp0 - 32) -> lo + 96 <= bv_unsigned sp0 -> 0x343f0 <= lo ->
  bytes_at rsegs m G_SHAPES g_shapes_bytes -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m' (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s00 s10' s2 (Z_to_bv 64 0x10417) (Z_to_bv 64 1)
                     a3' a4' a5' a6' a7' s20 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16310) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp0 - 96, bv_unsigned sp0 - 32)] m m' /\ wmono rsegs m m')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16d60) fc None m (seg_rom rsegs)).
Proof.
  intros RSO ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo sp0 ra0 s00 s10' s20 FR ST LO LO2 GS MI.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP.
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 32)) = bv_unsigned sp0 - 32) by (apply unsigned_lit; lia).
  do 4 step.
  eapply evt_cut.
  { eapply RSO with (lo := lo) (v := str_bytes "lv2_worker_set"%string).
    - exact MI.
    - rewrite SPU. exact ST.
    - rewrite SPU. unfold REC_SHAPE_OF_FRAME. lia.
    - exact GS.
    - left. rewrite SPU. unfold REC_SHAPE_OF_FRAME, G_SHAPES. lia.
    - rewrite unsigned_lit by lia. reflexivity.
    - intros _. rewrite unsigned_lit by lia. split; [exact (slw_verb m MI)|].
      left. rewrite SPU. unfold REC_SHAPE_OF_FRAME. rewrite ?unsigned_lit by lia. lia. }
  intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
    & MI2 & ST2).
  rewrite SPU in MU2. unfold REC_SHAPE_OF_FRAME in MU2.
  rewrite (ret_pc_even 0x16d70) by lia. rewrite slw_shape.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp0 - 32) [C8 s20; C8 s10'; C8 s00; C8 ra0]).
  { apply (rw_cells_transport rsegs _ m m2 _ _ FR MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  eapply evt_cut; [eapply slw_tail; [exact FR2 | lia] |].
  intros ms3 ->. apply evt_done.
  exists m2, t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6'.
  split; [reflexivity|].
  split; [|exact WM2].
  replace (bv_unsigned sp0 - 96) with (bv_unsigned sp0 - 32 - 64) by ring. exact MU2.
Qed.

From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecSeq RecStep RecGlue RecTail RecAnsB RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import answer_c record_c arg_s_c xmalloc_c sup_lv2_worker_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Local Open Scope Z_scope.

Definition slw_kx (xs : list Z) (R R' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> ~ In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

Lemma slw_kx_trans : forall xs R1 R2 R3, slw_kx xs R1 R2 -> slw_kx xs R2 R3 -> slw_kx xs R1 R3.
Proof. intros xs R1 R2 R3 H1 H2 r Hr N. rewrite (H2 r Hr N). exact (H1 r Hr N). Qed.

Lemma slw_kx_of_pres : forall xs R R', regs_preserved R R' -> slw_kx xs R R'.
Proof. intros xs R R' H r Hr _. exact (H r Hr). Qed.

Lemma slw_kx_pres : forall xs R R', slw_kx xs R R' ->
  (forall r, In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) -> regs_preserved R R'.
Proof.
  intros xs R R' K E r Hr. destruct (in_dec Z.eq_dec r xs) as [H|H]; [exact (E r H) | exact (K r Hr H)].
Qed.

Ltac slw_one X :=
  first [ exfalso; match goal with N : ~ In _ _ |- _ => apply N end; cbn [In]; lia
        | match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
          simp_regs; first [reflexivity | unfold getr; reflexivity] ].

Ltac slw_tac X :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in let Nrr := fresh "Nrr" in
  intros rr Hrr Nrr; unfold callee_saved in Hrr;
  assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr;
  repeat (destruct CC as [CC|CC]; [subst rr; slw_one X|]);
  subst rr; slw_one X.

Lemma slw_mod_host_shape : forall m, ro_agree rsegs m -> CF.answer_c.ans_shape rsegs m 0x10417 REC_MOD_HOST_SHAPE.
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

Lemma slw_code_record : forall R fn As, r_code (rec_record R fn As) = r_code R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma slw_stub_len : forall R fn As x chg, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_answer (rec_record R fn As) (fn, As) x chg)) <= Nat.max (length x) 16)%nat.
Proof.
  intros R fn As x chg H. rewrite rec_answer_text. destruct (r_refuse (rec_record R fn As) =? 0).
  - pose proof (inst_length x). lia.
  - rewrite slw_code_record. pose proof (resp_length (r_code R) H). lia.
Qed.

Lemma slw_room1 : forall b b1 n1 n2 t, sb_le b1 b -> 0 <= n1 <= LMAX + 1 -> 0 <= n2 -> 0 <= t ->
  room_ag (sb_mallocs b [n1; n2; t; t]) (LMAX + 1) -> room_ag (sb_malloc b1 n1) n1.
Proof.
  intros b b1 n1 n2 t BLE Hn1 Hn2 Ht ROOM. unfold sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  eapply room_slots_mono; [| | exact ROOM]; [|lia].
  apply (sb_le_trans _ (sb_malloc b n1)); [apply sb_malloc_mono; exact BLE|].
  apply (sb_le_trans _ (sb_malloc (sb_malloc b n1) n2)); [apply sb_le_malloc; lia|].
  apply (sb_le_trans _ (sb_malloc (sb_malloc (sb_malloc b n1) n2) t)); apply sb_le_malloc; lia.
Qed.

Lemma slw_room2 : forall b b2 n1 n2 t, sb_le b2 (sb_malloc b n1) -> 0 <= n2 <= LMAX + 1 -> 0 <= t ->
  room_ag (sb_mallocs b [n1; n2; t; t]) (LMAX + 1) -> room_ag (sb_malloc b2 n2) n2.
Proof.
  intros b b2 n1 n2 t BLE Hn2 Ht ROOM. unfold sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  eapply room_slots_mono; [| | exact ROOM]; [|lia].
  apply (sb_le_trans _ (sb_malloc (sb_malloc b n1) n2)); [apply sb_malloc_mono; exact BLE|].
  apply (sb_le_trans _ (sb_malloc (sb_malloc (sb_malloc b n1) n2) t)); apply sb_le_malloc; lia.
Qed.

Lemma slw_sarg_len : forall B L A O S K mem p v, str_arg B L A O S K mem p v -> Z.of_nat (length (sarg v)) <= LMAX.
Proof.
  intros B0 L A O S K mem p [x|] H; cbn [str_arg sarg] in H |- *.
  - destruct H as (_ & _ & LX & _). exact LX.
  - vm_compute. congruence.
Qed.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RFREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis REC : record_contract B API.
Hypothesis ARGS : arg_s_contract B API.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis ANS : answer_contract B API.

Lemma slw_shapes_kept : forall K L A regs mem md E excl L' A' regs' mem' md',
  call_pre_k B (aa_MR API) K L A regs mem md ->
  call_post_rec B (aa_MR API) K L A regs mem md E excl L' A' regs' mem' md' ->
  (forall a, G_SHAPES <= a < G_SHAPES + 448 -> ~ E a) ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes ->
  bytes_at rsegs mem' G_SHAPES g_shapes_bytes.
Proof using SEGS RIMG RFREE.
  intros K L A regs mem md E excl L' A' regs' mem' md' PRE POST HE BS.
  pose proof alloc_ceiling_val as AC.
  destruct PRE as (HM & _ & _ & _ & _ & HCE & _).
  destruct POST as (PM & _ & _ & _ & _ & _ & _ & PF & _).
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  apply (bytes_at_transfer rsegs mem); [exact BS|]. intros i Hi. rewrite GL in Hi.
  assert (RL : in_globals frame_RELRO (G_SHAPES + i)).
  { exists 0x226b0, 1680. split; [left; reflexivity | unfold G_SHAPES; lia]. }
  destruct (RIMG _ RL) as (I1 & _ & _ & I4).
  pose proof (in_img_low B SEGS _ I1) as IL.
  rewrite <- SEGS.
  assert (NS : ~ scratch_k B K regs (G_SHAPES + i))
    by (unfold scratch_k; intros [H|H]; [lia | exact (I4 H)]).
  exact (proj1 (PF _ (or_intror I1) (RFREE _ _ _ _ _ HM RL) (RFREE _ _ _ _ _ PM RL) NS
                 (HE (G_SHAPES + i) ltac:(lia)))).
Qed.

Lemma slw_rjr_shapes : forall K S O L A mem md Lc Ac mc mdc,
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes ->
  bytes_at rsegs mc G_SHAPES g_shapes_bytes.
Proof using SEGS RIMG.
  intros K S O L A mem md Lc Ac mc mdc RJ BS. pose proof alloc_ceiling_val as AC.
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  destruct RJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  apply (bytes_at_transfer rsegs mem); [exact BS|]. intros i Hi. rewrite GL in Hi.
  assert (RL : in_globals frame_RELRO (G_SHAPES + i)).
  { exists 0x226b0, 1680. split; [left; reflexivity | unfold G_SHAPES; lia]. }
  destruct (RIMG _ RL) as (I1 & I2 & I3 & I4).
  pose proof (in_img_low B SEGS _ I1) as IL.
  assert (NS : ~ (S - K <= G_SHAPES + i < S)) by lia.
  assert (NR : ~ rec_area (G_SHAPES + i))
    by (unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES; lia).
  rewrite <- SEGS. exact (proj1 (HF _ (or_intror (conj I1 (conj I2 I3))) NS I4 NR)).
Qed.

Lemma slw_head : forall L A regs mem md R O b (P : config -> Prop),
  call_pre_t B API 12384 L A regs mem md ->
  g_rec_rep rsegs L A mem R O -> ro_agree rsegs mem -> f18_words rsegs mem -> res_ok_slots A b ->
  (forall L1 A1 regs1 m1 md1 O1,
     sinv B API 12384 (spZ regs) L A mem md O L1 A1 m1 md1 (rec_record R REC_LV2_WORKER_SET []) O1 b ->
     sb_le (sb_shift b A A1) b ->
     getr regs1 2 = Z_to_bv 64 (spZ regs - 32) ->
     getr regs1 8 = getr regs 11 -> getr regs1 9 = getr regs 10 ->
     getr regs1 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
     slw_kx [2; 8; 9; 18] regs regs1 ->
     rw_cells rsegs m1 (spZ regs - 32) [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
     SR rsegs (mkCfg (mkst regs1 (Z_to_bv 64 0x16d48) m1 (seg_rom rsegs)) md1) P) ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 SUP_LV2_WORKER_SET) mem (seg_rom rsegs)) md) P.
Proof using SEGS AX ERRNO_LOW REC GOWN.
  intros L A regs mem md R O b P PRE GR RA F18 RES KONT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  rewrite SEGS in HWS.
  pose proof (sinv_init B API 12384 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 12384) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    eapply slw_pre; [exact ST | lia]. }
  intros ms1 (can1 & (m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16d48) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = getr regs 11) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_9 : getr R1 9 = getr regs 10) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 15) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (K01 : slw_kx [2; 8; 9; 18] regs R1) by slw_tac X1.
  assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  apply (sinv_record B API SEGS ERRNO_LOW AX REC 12384 (bv_unsigned sp) L A mem md O L A m1 md R O b R1 REC_LV2_WORKER_SET
           P SI1).
  - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP1. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
    rewrite Z.mod_add by lia. exact HAL.
  - rewrite SP1. unfold RECORD_K, ALLOC_STACK. lia.
  - rewrite SP1. lia.
  - rewrite E1_4. exact HTP.
  - exact E1_10.
  - unfold REC_FN_COUNT, REC_LV2_WORKER_SET. lia.
  - intros L1 A1 regs1 m2 md1 O1 SI2 BLE2 RP2 R10 FK2.
    rewrite E1_1.
    apply (KONT L1 A1 regs1 m2 md1 O1 SI2).
    + rewrite sb_shift_refl in BLE2. exact BLE2.
    + exact (eq_trans (RP2 2 ltac:(unfold callee_saved; lia)) E1_2).
    + exact (eq_trans (RP2 8 ltac:(unfold callee_saved; lia)) E1_8).
    + exact (eq_trans (RP2 9 ltac:(unfold callee_saved; lia)) E1_9).
    + exact R10.
    + exact (slw_kx_trans _ _ _ _ K01 (slw_kx_of_pres _ _ _ RP2)).
    + apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
      destruct (FK2 (bv_unsigned sp - 32 + i) ltac:(rewrite SP1; lia)) as [K1 K2].
      split; [exact K1 | exact (proj1 K2)].
Qed.

Lemma slw_arg1 : forall L A regs mem md pu uri R O b L1 A1 regs1 m1 md1 O1 (P : config -> Prop),
  call_pre_t B API 12384 L A regs mem md -> getr regs 10 = Z_to_bv 64 pu ->
  str_arg B L A O (spZ regs) 12384 mem pu uri -> ro_agree rsegs mem ->
  room_ag (sb_malloc (sb_shift b A A1) (Z.of_nat (length (sarg uri)) + 1)) (Z.of_nat (length (sarg uri)) + 1) ->
  sinv B API 12384 (spZ regs) L A mem md O L1 A1 m1 md1 (rec_record R REC_LV2_WORKER_SET []) O1 b ->
  getr regs1 2 = Z_to_bv 64 (spZ regs - 32) ->
  getr regs1 8 = getr regs 11 -> getr regs1 9 = getr regs 10 ->
  getr regs1 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  slw_kx [2; 8; 9; 18] regs regs1 ->
  rw_cells rsegs m1 (spZ regs - 32) [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  (forall L2 A2 regs2 m2 md2 p,
     sinv B API 12384 (spZ regs) L A mem md O L2 A2 m2 md2 (rec_record R REC_LV2_WORKER_SET [sarg uri])
       (O1 ++ [(p, Z.of_nat (length (sarg uri)) + 1)]) b ->
     sb_shift b A A2 = sb_malloc (sb_shift b A A1) (Z.of_nat (length (sarg uri)) + 1) ->
     getr regs2 2 = Z_to_bv 64 (spZ regs - 32) -> getr regs2 8 = getr regs 11 ->
     getr regs2 18 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
     slw_kx [2; 8; 9; 18] regs regs2 ->
     rw_cells rsegs m2 (spZ regs - 32) [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
     SR rsegs (mkCfg (mkst regs2 (Z_to_bv 64 0x16d54) m2 (seg_rom rsegs)) md2) P) ->
  SR rsegs (mkCfg (mkst regs1 (Z_to_bv 64 0x16d48) m1 (seg_rom rsegs)) md1) P.
Proof using SEGS AX ERRNO_LOW GFACT GOWN ARGS SLACK.
  intros L A regs mem md pu uri R O b L1 A1 regs1 m1 md1 O1 P PRE A0 SA RA ROOM SI1 E2 E8 E9 E10 K1 FR KONT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  pose proof SI1 as (RJ1 & _). pose proof RJ1 as (HM1 & _).
  destruct (mr_model B _ LAWS L1 A1 m1 md1 HM1) as (Hh1 & Hl1 & _).
  set (sp := reg_get regs 2) in *. change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  eapply evt_SR_canon; [ | exact Hh1 | exact Hl1 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. eapply slw_mid1. }
  intros ms2 (can2 & -> & EQ2).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
  assert (F1 : getr R2 1 = Z_to_bv 64 0x16d54) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity).
  assert (F2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs; exact E2).
  assert (F4 : getr R2 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X2 eq_refl); simp_regs.
    exact (K1 4 ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)). }
  assert (F8 : getr R2 8 = getr regs 11) by (rewrite (getr_of_eqv _ _ 8 X2 eq_refl); simp_regs; exact E8).
  assert (F18 : getr R2 18 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 18 X2 eq_refl); simp_regs; exact E10).
  assert (F10 : getr R2 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs; exact E10).
  assert (F11 : getr R2 11 = Z_to_bv 64 pu)
    by (rewrite (getr_of_eqv _ _ 11 X2 eq_refl); simp_regs; exact (eq_trans E9 A0)).
  assert (K12 : slw_kx [2; 8; 9; 18] regs1 R2) by slw_tac X2.
  assert (SP2 : spZ R2 = bv_unsigned sp - 32) by (unfold spZ; rewrite F2; apply unsigned_lit; lia).
  apply (sinv_arg_s B API SEGS ERRNO_LOW GFACT GOWN AX ARGS 12384 (bv_unsigned sp) L A mem md O L1 A1 m1 md1 R
           REC_LV2_WORKER_SET O1 b R2 pu uri P SI1).
  - rewrite F1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP2. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
    rewrite Z.mod_add by lia. exact HAL.
  - rewrite SP2. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
  - rewrite SP2. lia.
  - rewrite F4. exact HTP.
  - exact F10.
  - exact F11.
  - rewrite SP2.
    apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L1 A1 m1 md1 _ O1 b pu uri
             (bv_unsigned sp - 32) SI1 RA); [unfold ARG_S_K, XMALLOC_K, ALLOC_STACK; lia | lia | exact SA].
  - exact ROOM.
  - intros L2 A2 regs2 m2 md2 p SI3 SH3 INI3 RP3 FK3.
    rewrite F1.
    apply (KONT L2 A2 regs2 m2 md2 p SI3 SH3).
    + exact (eq_trans (RP3 2 ltac:(unfold callee_saved; lia)) F2).
    + exact (eq_trans (RP3 8 ltac:(unfold callee_saved; lia)) F8).
    + exact (eq_trans (RP3 18 ltac:(unfold callee_saved; lia)) F18).
    + exact (slw_kx_trans _ _ _ _ K1 (slw_kx_trans _ _ _ _ K12 (slw_kx_of_pres _ _ _ RP3))).
    + apply (rw_cells_transfer rsegs m1); [exact FR|]. intros i Hi. cbn in Hi.
      destruct (FK3 (bv_unsigned sp - 32 + i) ltac:(rewrite SP2; lia)) as [K1' K2'].
      split; [exact K1' | exact (proj1 K2')].
Qed.

Lemma slw_arg2 : forall L A regs mem md pw uri worker R O b L2 A2 regs2 m2 md2 O2 (P : config -> Prop),
  call_pre_t B API 12384 L A regs mem md -> getr regs 11 = Z_to_bv 64 pw ->
  str_arg B L A O (spZ regs) 12384 mem pw worker -> ro_agree rsegs mem ->
  room_ag (sb_malloc (sb_shift b A A2) (Z.of_nat (length (sarg worker)) + 1)) (Z.of_nat (length (sarg worker)) + 1) ->
  sinv B API 12384 (spZ regs) L A mem md O L2 A2 m2 md2 (rec_record R REC_LV2_WORKER_SET [sarg uri]) O2 b ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 32) -> getr regs2 8 = getr regs 11 ->
  getr regs2 18 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  slw_kx [2; 8; 9; 18] regs regs2 ->
  rw_cells rsegs m2 (spZ regs - 32) [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  (forall L3 A3 regs3 m3 md3 p,
     sinv B API 12384 (spZ regs) L A mem md O L3 A3 m3 md3 (rec_record R REC_LV2_WORKER_SET [sarg uri; sarg worker])
       (O2 ++ [(p, Z.of_nat (length (sarg worker)) + 1)]) b ->
     sb_shift b A A3 = sb_malloc (sb_shift b A A2) (Z.of_nat (length (sarg worker)) + 1) ->
     getr regs3 2 = Z_to_bv 64 (spZ regs - 32) ->
     getr regs3 18 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
     slw_kx [2; 8; 9; 18] regs regs3 ->
     rw_cells rsegs m3 (spZ regs - 32) [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
     SR rsegs (mkCfg (mkst regs3 (Z_to_bv 64 0x16d60) m3 (seg_rom rsegs)) md3) P) ->
  SR rsegs (mkCfg (mkst regs2 (Z_to_bv 64 0x16d54) m2 (seg_rom rsegs)) md2) P.
Proof using SEGS AX ERRNO_LOW GFACT GOWN ARGS SLACK.
  intros L A regs mem md pw uri worker R O b L2 A2 regs2 m2 md2 O2 P PRE A1 SA RA ROOM SI2 E2 E8 E18 K2 FR KONT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  pose proof SI2 as (RJ2 & _). pose proof RJ2 as (HM2 & _).
  destruct (mr_model B _ LAWS L2 A2 m2 md2 HM2) as (Hh2 & Hl2 & _).
  set (sp := reg_get regs 2) in *. change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. eapply slw_mid2. }
  intros ms3 (can3 & -> & EQ3).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  assert (F1 : getr R3 1 = Z_to_bv 64 0x16d60) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (F2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; exact E2).
  assert (F4 : getr R3 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs.
    exact (K2 4 ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)). }
  assert (F18 : getr R3 18 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 18 X3 eq_refl); simp_regs; exact E18).
  assert (F10 : getr R3 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; exact E18).
  assert (F11 : getr R3 11 = Z_to_bv 64 pw)
    by (rewrite (getr_of_eqv _ _ 11 X3 eq_refl); simp_regs; exact (eq_trans E8 A1)).
  assert (K23 : slw_kx [2; 8; 9; 18] regs2 R3) by slw_tac X3.
  assert (SP3 : spZ R3 = bv_unsigned sp - 32) by (unfold spZ; rewrite F2; apply unsigned_lit; lia).
  apply (sinv_arg_sn B API SEGS ERRNO_LOW GFACT GOWN AX ARGS 12384 (bv_unsigned sp) L A mem md O L2 A2 m2 md2 R
           REC_LV2_WORKER_SET [sarg uri] O2 b R3 pw worker P SI2).
  - cbn [length]. lia.
  - rewrite F1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP3. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
    rewrite Z.mod_add by lia. exact HAL.
  - rewrite SP3. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
  - rewrite SP3. lia.
  - rewrite F4. exact HTP.
  - exact F10.
  - exact F11.
  - rewrite SP3.
    apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L2 A2 m2 md2 _ O2 b pw worker
             (bv_unsigned sp - 32) SI2 RA); [unfold ARG_S_K, XMALLOC_K, ALLOC_STACK; lia | lia | exact SA].
  - exact ROOM.
  - intros L3 A3 regs3 m3 md3 p SI3 SH3 INI3 RP3 FK3.
    rewrite F1.
    apply (KONT L3 A3 regs3 m3 md3 p SI3 SH3).
    + exact (eq_trans (RP3 2 ltac:(unfold callee_saved; lia)) F2).
    + exact (eq_trans (RP3 18 ltac:(unfold callee_saved; lia)) F18).
    + exact (slw_kx_trans _ _ _ _ K2 (slw_kx_trans _ _ _ _ K23 (slw_kx_of_pres _ _ _ RP3))).
    + apply (rw_cells_transfer rsegs m2); [exact FR|]. intros i Hi. cbn in Hi.
      destruct (FK3 (bv_unsigned sp - 32 + i) ltac:(rewrite SP3; lia)) as [K1' K2'].
      split; [exact K1' | exact (proj1 K2')].
Qed.

Lemma slw_rest : forall L A regs mem md uri worker R O b L3 A3 regs3 m3 md3 O3,
  call_pre_t B API 12384 L A regs mem md ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes -> frm_zero fp_csr ->
  room_ag (sb_mallocs b (sup_lv2_worker_set_sizes uri worker (snd (sup_lv2_worker_set_m R uri worker)))) (LMAX + 1) ->
  sinv B API 12384 (spZ regs) L A mem md O L3 A3 m3 md3 (rec_record R REC_LV2_WORKER_SET [sarg uri; sarg worker]) O3 b ->
  sb_le (sb_shift b A A3)
    (sb_malloc (sb_malloc b (Z.of_nat (length (sarg uri)) + 1)) (Z.of_nat (length (sarg worker)) + 1)) ->
  (length (r_calls R) <= 16)%nat -> -2^31 <= r_code R < 2^31 ->
  getr regs3 2 = Z_to_bv 64 (spZ regs - 32) -> getr regs3 18 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  slw_kx [2; 8; 9; 18] regs regs3 ->
  rw_cells rsegs m3 (spZ regs - 32) [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  SR rsegs (mkCfg (mkst regs3 (Z_to_bv 64 0x16d60) m3 (seg_rom rsegs)) md3)
    (sup_lv2_worker_set_ret B API L A regs mem md uri worker R O b).
Proof using SEGS AX CTX ERRNO_LOW ANS SLACK GOWN RSO RIMG RFREE.
  intros L A regs mem md uri worker R O b L3 A3 regs3 m3 md3 O3 PRE GS FRM ROOM SI3 BLE3 HN HCODE E2 E18 K3 FR.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  change (snd (sup_lv2_worker_set_m R uri worker)) with
    (snd (rec_answer (rec_record R REC_LV2_WORKER_SET [sarg uri; sarg worker]) (REC_LV2_WORKER_SET, [sarg uri; sarg worker])
      (daemon_shape "lv2_worker_set"%string) true)) in ROOM.
  unfold sup_lv2_worker_set_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  assert (LT : (length (snd (rec_answer (rec_record R REC_LV2_WORKER_SET [sarg uri; sarg worker])
                  (REC_LV2_WORKER_SET, [sarg uri; sarg worker]) (daemon_shape "lv2_worker_set"%string) true)) <= 16)%nat).
  { pose proof (slw_stub_len R REC_LV2_WORKER_SET [sarg uri; sarg worker] (daemon_shape "lv2_worker_set"%string) true HCODE)
      as H.
    assert (LX : length (daemon_shape "lv2_worker_set"%string) = 6%nat) by (vm_compute; reflexivity).
    rewrite LX in H. exact H. }
  set (e := rec_entry G_REC REC_SC R) in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof SI3 as (RJ3 & _ & _ & _ & _ & RA3 & _).
  pose proof RJ3 as (HM3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC3 & _).
  destruct (mr_model B _ LAWS L3 A3 m3 md3 HM3) as (Hh3 & Hl3 & _).
  assert (FRn : rw_cells rsegs (normalize rsegs m3) (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply rw_cells_norm_hi; [exact RA3 | lia | exact FR]. }
  assert (STn : stk rsegs (normalize rsegs m3) (bv_unsigned sp - 12384) (bv_unsigned sp - 32)).
  { apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC3. left. lia. }
  pose proof (bytes_at_normalize rsegs m3 _ _ RA3
                (slw_rjr_shapes 12384 (bv_unsigned sp) O L A mem md L3 A3 m3 md3 RJ3 GS)) as GSn.
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (Q2 : reg_get regs3 2 = Z_to_bv 64 (bv_unsigned sp - 32)) by exact E2.
    rewrite Q2.
    eapply (evt_normalize rsegs); [exact WX | exact RA3 |].
    eapply (slw_after RSO); [exact FRn | exact STn | lia | lia | exact GSn | apply mem_inv_normalize]. }
  intros ms4 (can4 & (s4n & Q4 & REL4 & RO4) & EQ4).
  destruct Q4 as (m4n & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU4n & WM4n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL4) as [EC4 MR4r].
  revert EC4 MR4r RO4 EQ4. generalize (ms_mem can4) as m4. intros m4 EC4 MR4r RO4 EQ4. subst can4.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR4r RO4 MU4n) as MU4.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR4r RO4 WM4n) as WM4.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4).
  pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L3 A3 m3 md3 _ _ b m4 _ SI3 MU4 WM4
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI4.
  assert (E4_1 : getr R4 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_2 : getr R4 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_10 : getr R4 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X4 eq_refl); simp_regs; exact E18).
  assert (E4_11 : getr R4 11 = Z_to_bv 64 0x10417)
    by (rewrite (getr_of_eqv _ _ 11 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_12 : getr R4 12 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 12 X4 eq_refl); simp_regs; reflexivity).
  assert (K34 : slw_kx [2; 8; 9; 18] regs3 R4) by slw_tac X4.
  assert (RP4 : regs_preserved regs R4).
  { apply (slw_kx_pres [2; 8; 9; 18]).
    - exact (slw_kx_trans _ regs regs3 R4 K3 K34).
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
        match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X4 eq_refl) end;
        simp_regs; first [reflexivity | unfold getr; reflexivity]. }
  assert (SP4 : spZ R4 = spZ regs) by (unfold spZ; rewrite E4_2; reflexivity).
  assert (AK : ANSWER_K <= 12384) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof SI4 as (RJ4 & GR4 & ON4 & B14 & B24 & RA4 & F184 & RS4).
  assert (SHP : CF.answer_c.ans_shape rsegs m4 0x10417 (daemon_shape "lv2_worker_set"%string)).
  { replace (daemon_shape "lv2_worker_set"%string) with REC_MOD_HOST_SHAPE by (vm_compute; reflexivity).
    exact (slw_mod_host_shape m4 RA4). }
  assert (ROOM3 : room_ag
            (sb_malloc (sb_malloc (sb_shift b A A3)
               (Z.of_nat (length (snd (rec_answer (rec_record R REC_LV2_WORKER_SET [sarg uri; sarg worker])
                  (REC_LV2_WORKER_SET, [sarg uri; sarg worker]) (daemon_shape "lv2_worker_set"%string) true))) + 1))
               (Z.of_nat (length (snd (rec_answer (rec_record R REC_LV2_WORKER_SET [sarg uri; sarg worker])
                  (REC_LV2_WORKER_SET, [sarg uri; sarg worker]) (daemon_shape "lv2_worker_set"%string) true))) + 1))
            (Z.of_nat (length (snd (rec_answer (rec_record R REC_LV2_WORKER_SET [sarg uri; sarg worker])
               (REC_LV2_WORKER_SET, [sarg uri; sarg worker]) (daemon_shape "lv2_worker_set"%string) true))) + 1)).
  { eapply room_slots_mono; [| | exact ROOM].
    - apply sb_malloc_mono, sb_malloc_mono. exact BLE3.
    - unfold LMAX. lia. }
  rewrite <- SEGS in GR4, RA4, F184, SHP.
  pose proof (answer_tail B API SEGS AX CTX ERRNO_LOW ANS SLACK 12384 L A regs mem md O L3 A3 R4 m4 md3
                (rec_record R REC_LV2_WORKER_SET [sarg uri; sarg worker]) O3 b
                (sb_malloc (sb_malloc b (Z.of_nat (length (sarg uri)) + 1)) (Z.of_nat (length (sarg worker)) + 1))
                (sb_shift b A A3) e 0x10417
                (REC_LV2_WORKER_SET, [sarg uri; sarg worker]) (daemon_shape "lv2_worker_set"%string) true PRE AK RJ4 E4_1 SP4
                RP4 E4_10 E4_11 ltac:(rewrite E4_12; reflexivity) GR4 (fun _ => SHP)
                (fun _ _ => ans_entry_record R REC_LV2_WORKER_SET [sarg uri; sarg worker] HN)
                FRM F184 RA4 RS4 eq_refl BLE3 ROOM3 ON4 B14 B24) as TR0.
  rewrite SEGS in TR0.
  eapply SR_mono; [exact TR0|].
  intros c' TR.
  destruct TR as (fx'' & L' & A' & regs' & mem' & md' & O' & q & -> & FK' & POST' & A10' & GR' & ON' & BL' & IN' & FB'
    & NQ' & BY' & OK' & AP' & RA' & F18' & INI' & REG' & BLE' & RES').
  exists fx'', L', A', regs', mem', md', (fst (sup_lv2_worker_set_m R uri worker)), O',
    (snd (sup_lv2_worker_set_m R uri worker)), q.
  split; [apply surjective_pairing|]. split; [reflexivity|]. split; [exact FK'|].
  split; [exact POST'|].
  do 10 (split; [assumption|]).
  split.
  { rewrite SEGS. apply (slw_shapes_kept _ L A regs mem md _ _ L' A' regs' mem' md' PRK POST'); [|exact GS].
    intros a Ha Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES in *. lia. }
  repeat (split; [assumption|]). exact RES'.
Qed.

Theorem sup_lv2_worker_set_holds : sup_lv2_worker_set_contract B API.
Proof using SEGS ERRNO_LOW GFACT GOWN RIMG RFREE AX CTX SLACK REC ARGS RSO ANS.
  unfold sup_lv2_worker_set_contract.
  intros L A regs mem md pu pw uri worker R O b PRE GA0 GA1 SAU SAW GS GR RA FRM F18 RES ROOM.
  unfold SUP_LV2_WORKER_SET_K in PRE, SAU, SAW.
  rewrite SEGS in GS, GR, RA, F18 |- *.
  pose proof (rec_rep_calls_le _ _ _ _ _ _ _ _ GR) as HN.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & _ & _ & _ & HX & _).
  pose proof HX as (_ & _ & _ & _ & _ & _ & HCODE & _).
  pose proof (slw_sarg_len B L A O (spZ regs) 12384 mem pu uri SAU) as LU.
  pose proof (slw_sarg_len B L A O (spZ regs) 12384 mem pw worker SAW) as LW.
  pose proof ROOM as ROOMs.
  unfold sup_lv2_worker_set_sizes in ROOMs.
  apply (slw_head L A regs mem md R O b _ PRE GR RA F18 RES).
  intros L1 A1 regs1 m1 md1 O1 SI1 BLE1 E2 E8 E9 E10 K1 FR.
  assert (ROOMA : room_ag (sb_malloc (sb_shift b A A1) (Z.of_nat (length (sarg uri)) + 1))
                    (Z.of_nat (length (sarg uri)) + 1)).
  { apply (slw_room1 b _ _ (Z.of_nat (length (sarg worker)) + 1)
             (Z.of_nat (length (snd (sup_lv2_worker_set_m R uri worker))) + 1) BLE1);
      [unfold LMAX in *; lia | lia | lia | exact ROOMs]. }
  apply (slw_arg1 L A regs mem md pu uri R O b L1 A1 regs1 m1 md1 O1 _ PRE GA0 SAU RA ROOMA SI1 E2 E8 E9 E10 K1 FR).
  intros L2 A2 regs2 m2 md2 p1 SI2 SH2 H2 H8 H18 K2 FR2.
  assert (BLE2 : sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length (sarg uri)) + 1))).
  { rewrite SH2. apply sb_malloc_mono. exact BLE1. }
  assert (ROOMB : room_ag (sb_malloc (sb_shift b A A2) (Z.of_nat (length (sarg worker)) + 1))
                    (Z.of_nat (length (sarg worker)) + 1)).
  { apply (slw_room2 b _ (Z.of_nat (length (sarg uri)) + 1) _
             (Z.of_nat (length (snd (sup_lv2_worker_set_m R uri worker))) + 1) BLE2);
      [unfold LMAX in *; lia | lia | exact ROOMs]. }
  apply (slw_arg2 L A regs mem md pw uri worker R O b L2 A2 regs2 m2 md2 _ _ PRE GA1 SAW RA ROOMB SI2 H2 H8 H18 K2
           FR2).
  intros L3 A3 regs3 m3 md3 p2 SI3 SH3 G2 G18 K3 FR3.
  apply (slw_rest L A regs mem md uri worker R O b L3 A3 regs3 m3 md3 _ PRE GS FRM ROOM SI3); try assumption.
  rewrite SH3. apply sb_malloc_mono. exact BLE2.
Qed.

End P.

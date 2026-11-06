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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths, module names and addresses changed; 503 of its 565 lines of code are new or changed and 773 lines of the source are left out. *)
From Stdlib Require Import String ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import rec_shape_of_c.
Import ListNotations.
Open Scope Z_scope.

Definition sqc_rom_chk (a : Z) (bs : list byte) : bool :=
  forallb (fun i => ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) &&
     match seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)), nth_error bs i with
     | Some b, Some c => Z.eqb (bv_unsigned b) (bv_unsigned c)
     | _, _ => false
     end) (seq 0 (length bs)).

Lemma sqc_rom_chk_bytes : forall m a bs, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  sqc_rom_chk a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs RA H0 H1 C. split; [lia|]. split; [lia|]. intros i Hi.
  unfold sqc_rom_chk in C.
  pose proof (proj1 (forallb_forall _ _) C i ltac:(apply in_seq; lia)) as Ci. cbv beta in Ci.
  apply andb_prop in Ci as [Cr Cv].
  unfold wa. rewrite (RA _ Cr).
  destruct (seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [|discriminate].
  destruct (nth_error bs i) as [c|]; [|discriminate].
  apply Z.eqb_eq in Cv. f_equal. apply bv_eq. exact Cv.
Qed.

Lemma sqc_ro_agree_of_inv : forall m, mem_inv rsegs m -> ro_agree rsegs m.
Proof.
  intros m MI x Hx. unfold mrd. destruct (m x) as [b|] eqn:E; [|reflexivity].
  rewrite (MI _ _ E) in Hx. discriminate.
Qed.

Lemma sqc_pre :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x343f0 <= lo ->
  evt rsegs (fun ms' => exists j0 m',
       ms' = MS (mkR (Z_to_bv 64 0x16b94) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 a0 s1
                     (Z_to_bv 64 11) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [CB 8 j0; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16b78) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 7 step.
  apply evt_done.
  do 2 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma sqc_mid :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16ba0) sp gp tp t0 t1 t2 s0 a0 a0 s0 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16b94) fc None m (seg_rom rsegs)).
Proof.
  intros. do 3 step. apply evt_done. reflexivity.
Qed.

Lemma sqc_tail :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s10' : word) (j0 : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [CB 8 j0; C8 s10'; C8 s00; C8 ra0] -> 32 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s10' s1 a0 (Z_to_bv 64 1) a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x16310) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16bb0) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s10' j0 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 8 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma sqc_verb : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10792 (str_bytes "quarantine_clear"%string).
Proof.
  intros m MI. apply sqc_rom_chk_bytes; [exact (sqc_ro_agree_of_inv m MI) | lia | cbn; lia | vm_compute; reflexivity].
Qed.

Lemma sqc_shape : shape_find shape_rows (str_bytes "quarantine_clear"%string) = 0x10417.
Proof. vm_compute. reflexivity. Qed.

Lemma sqc_after : rec_shape_of_contract ->
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sp0 ra0 s00 s10' : word) (j0 : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [CB 8 j0; C8 s10'; C8 s00; C8 ra0] ->
  stk rsegs m lo (bv_unsigned sp0 - 32) -> lo + 96 <= bv_unsigned sp0 -> 0x343f0 <= lo ->
  bytes_at rsegs m G_SHAPES g_shapes_bytes -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m' (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s00 s10' s1 (Z_to_bv 64 0x10417) (Z_to_bv 64 1)
                     a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16310) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp0 - 96, bv_unsigned sp0 - 32)] m m' /\ wmono rsegs m m')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16ba0) fc None m (seg_rom rsegs)).
Proof.
  intros RSO ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo sp0 ra0 s00 s10' j0 FR ST LO LO2 GS MI.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP.
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 32)) = bv_unsigned sp0 - 32) by (apply unsigned_lit; lia).
  do 4 step.
  eapply evt_cut.
  { eapply RSO with (lo := lo) (v := str_bytes "quarantine_clear"%string).
    - exact MI.
    - rewrite SPU. exact ST.
    - rewrite SPU. unfold REC_SHAPE_OF_FRAME. lia.
    - exact GS.
    - left. rewrite SPU. unfold REC_SHAPE_OF_FRAME, G_SHAPES. lia.
    - rewrite unsigned_lit by lia. reflexivity.
    - intros _. rewrite unsigned_lit by lia. split; [exact (sqc_verb m MI)|].
      left. rewrite SPU. unfold REC_SHAPE_OF_FRAME. rewrite ?unsigned_lit by lia. lia. }
  intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
    & MI2 & ST2).
  rewrite SPU in MU2. unfold REC_SHAPE_OF_FRAME in MU2.
  rewrite (ret_pc_even 0x16bb0) by lia. rewrite sqc_shape.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp0 - 32) [CB 8 j0; C8 s10'; C8 s00; C8 ra0]).
  { apply (rw_cells_transport rsegs _ m m2 _ _ FR MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  eapply evt_cut; [eapply sqc_tail; [exact FR2 | lia] |].
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import answer_c record_c arg_s_c xmalloc_c sup_quarantine_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Local Open Scope Z_scope.

Lemma sqc_mod_host_shape : forall m, ro_agree rsegs m -> CF.answer_c.ans_shape rsegs m 0x10417 REC_MOD_HOST_SHAPE.
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

Lemma sqc_code_record : forall R fn As, r_code (rec_record R fn As) = r_code R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma sqc_stub_len : forall R fn As x chg, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_answer (rec_record R fn As) (fn, As) x chg)) <= Nat.max (length x) 16)%nat.
Proof.
  intros R fn As x chg H. rewrite rec_answer_text. destruct (r_refuse (rec_record R fn As) =? 0).
  - pose proof (inst_length x). lia.
  - rewrite sqc_code_record. pose proof (resp_length (r_code R) H). lia.
Qed.

Lemma sqc_getr_nz : forall r, callee_saved r -> bv_eqb (Z_to_bv 5 r) 0 = false.
Proof.
  intros r Hr. assert (Hk : 0 < r < 32) by (unfold callee_saved in Hr; lia).
  unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia.
Qed.

Lemma sqc_pres : forall regs R3 M3,
  Regs6ss.xregs_eqv M3 R3 ->
  (forall r, callee_saved r -> reg_get M3 (Z_to_bv 5 r) = reg_get regs (Z_to_bv 5 r)) ->
  regs_preserved regs R3.
Proof.
  intros regs R3 M3 X3 K r Hr.
  pose proof (sqc_getr_nz r Hr) as NZ.
  rewrite (getr_of_eqv _ _ _ X3 NZ). unfold getr. rewrite NZ. exact (K r Hr).
Qed.

Lemma sqc_room_arg : forall b b1 n t, sb_le b1 b -> 0 <= n <= LMAX + 1 -> 0 <= t ->
  room_ag (sb_mallocs b [n; t; t]) (LMAX + 1) -> room_ag (sb_malloc b1 n) n.
Proof.
  intros b b1 n t BLE Hn Ht ROOM. unfold sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  eapply room_slots_mono; [| | exact ROOM]; [|lia].
  eapply sb_le_trans; [apply sb_malloc_mono; exact BLE|].
  eapply sb_le_trans; apply sb_le_malloc; lia.
Qed.

Lemma sqc_room_ans : forall b b2 n t, sb_le b2 (sb_malloc b n) -> 0 <= t <= LMAX + 1 ->
  room_ag (sb_mallocs b [n; t; t]) (LMAX + 1) -> room_ag (sb_malloc (sb_malloc b2 t) t) t.
Proof.
  intros b b2 n t BLE Ht ROOM. unfold sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  eapply room_slots_mono; [| | exact ROOM]; [|lia].
  apply sb_malloc_mono, sb_malloc_mono. exact BLE.
Qed.

Section H.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RFREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.

Lemma sqc_shapes_kept : forall K L A regs mem md E excl L' A' regs' mem' md',
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

Lemma sqc_rjr_shapes : forall K S O L A mem md Lc Ac mc mdc,
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

End H.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis REC : record_contract B API.
Hypothesis ANSF : forall fx0 : YK11.FPState, answer_contract (fx := fx0) B API.

Lemma sqc_answer : forall K L A regs mem md O Lc Ac regs1 mc mdc Rc Oc bc bpre c sh e x chg,
  call_pre_t B API K L A regs mem md -> ANSWER_K <= K ->
  sinv B API K (spZ regs) L A mem md O Lc Ac mc mdc Rc Oc bc ->
  getr regs1 1 = getr regs 1 -> spZ regs1 = spZ regs -> regs_preserved regs regs1 ->
  getr regs1 10 = Z_to_bv 64 c -> getr regs1 11 = Z_to_bv 64 sh -> chg = negb (bv_unsigned (getr regs1 12) =? 0) ->
  (r_refuse Rc = 0 -> ans_shape rsegs mc sh x) ->
  (r_refuse Rc = 0 -> chg = true -> ans_entry Rc c e) ->
  frm_zero fp_csr -> sb_le (sb_shift bc A Ac) bpre ->
  room_ag (sb_malloc (sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (snd (rec_answer Rc e x chg))) + 1))
                (Z.of_nat (length (snd (rec_answer Rc e x chg))) + 1))
             (Z.of_nat (length (snd (rec_answer Rc e x chg))) + 1) ->
  SR rsegs (mkCfg (mkst regs1 (Z_to_bv 64 ANSWER) mc (seg_rom rsegs)) mdc)
    (tail_ret B API K L A regs mem md O Rc e x chg bc bpre).
Proof using SEGS AX CTX ERRNO_LOW ANSF SLACK.
  intros K L A regs mem md O Lc Ac regs1 mc mdc Rc Oc bc bpre c sh e x chg PRE KA SI RA1 SP1 RP1 A10 A11 ACH SH EN FRM
    BLE ROOM.
  destruct SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  rewrite <- SEGS in GR, RA, F18, SH |- *.
  exact (answer_tail B API SEGS AX CTX ERRNO_LOW (ANSF fx) SLACK K L A regs mem md O Lc Ac regs1 mc mdc Rc Oc bc bpre
           (sb_shift bc A Ac) c sh e x chg
           PRE KA RJ RA1 SP1 RP1 A10 A11 ACH GR SH EN FRM F18 RA RS eq_refl BLE ROOM ON B1 B2).
Qed.

Lemma sqc_head : forall L A regs mem md R O b (P : config -> Prop),
  call_pre_t B API 12384 L A regs mem md ->
  g_rec_rep rsegs L A mem R O -> ro_agree rsegs mem -> f18_words rsegs mem -> res_ok_slots A b ->
  (forall L1 A1 regs1 m1 md1 O1 (j0 : list byte),
     sinv B API 12384 (spZ regs) L A mem md O L1 A1 m1 md1 (rec_record R REC_QUARANTINE_CLEAR []) O1 b ->
     sb_le (sb_shift b A A1) b ->
     getr regs1 2 = Z_to_bv 64 (spZ regs - 32) -> getr regs1 4 = getr regs 4 ->
     getr regs1 8 = getr regs 10 -> getr regs1 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
     (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
     rw_cells rsegs m1 (spZ regs - 32) [CB 8 j0; C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
     SR rsegs (mkCfg (mkst regs1 (Z_to_bv 64 0x16b94) m1 (seg_rom rsegs)) md1) P) ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 SUP_QUARANTINE_CLEAR) mem (seg_rom rsegs)) md) P.
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
    eapply sqc_pre; [exact ST | lia | lia]. }
  intros ms1 (can1 & (j0 & m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16b94) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = getr regs 10) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 11) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  apply (sinv_record B API SEGS ERRNO_LOW AX REC 12384 (bv_unsigned sp) L A mem md O L A m1 md R O b R1 REC_QUARANTINE_CLEAR P SI1).
  - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP1. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
    rewrite Z.mod_add by lia. exact HAL.
  - rewrite SP1. unfold RECORD_K, ALLOC_STACK. lia.
  - rewrite SP1. lia.
  - rewrite E1_4. exact HTP.
  - exact E1_10.
  - unfold REC_FN_COUNT, REC_QUARANTINE_CLEAR. lia.
  - intros L1 A1 regs1 m2 md1 O1 SI2 BLE2 RP2 R10 FK2.
    rewrite E1_1.
    apply (KONT L1 A1 regs1 m2 md1 O1 j0 SI2).
    + rewrite sb_shift_refl in BLE2. exact BLE2.
    + exact (eq_trans (RP2 2 ltac:(unfold callee_saved; lia)) E1_2).
    + exact (eq_trans (RP2 4 ltac:(unfold callee_saved; lia)) E1_4).
    + exact (eq_trans (RP2 8 ltac:(unfold callee_saved; lia)) E1_8).
    + exact R10.
    + intros r Hr N2 N8 N9. rewrite (RP2 r Hr). pose proof (sqc_getr_nz r Hr) as NZ.
      rewrite (getr_of_eqv _ _ _ X1 NZ). unfold callee_saved in Hr.
      assert (CC : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/
                   r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct CC as [CC|CC]; [subst r; simp_regs; reflexivity|]). subst r; simp_regs; reflexivity.
    + apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
      destruct (FK2 (bv_unsigned sp - 32 + i) ltac:(rewrite SP1; lia)) as [K1 K2].
      split; [exact K1 | exact (proj1 K2)].
Qed.

Hypothesis ARGS : arg_s_contract B API.

Lemma sqc_arg : forall L A regs mem md pw which R O b L1 A1 regs1 m1 md1 O1 (j0 : list byte) (P : config -> Prop),
  call_pre_t B API 12384 L A regs mem md -> getr regs 10 = Z_to_bv 64 pw ->
  str_arg B L A O (spZ regs) 12384 mem pw which -> ro_agree rsegs mem ->
  room_ag (sb_malloc (sb_shift b A A1) (Z.of_nat (length (sarg which)) + 1)) (Z.of_nat (length (sarg which)) + 1) ->
  sinv B API 12384 (spZ regs) L A mem md O L1 A1 m1 md1 (rec_record R REC_QUARANTINE_CLEAR []) O1 b ->
  getr regs1 2 = Z_to_bv 64 (spZ regs - 32) -> getr regs1 4 = getr regs 4 ->
  getr regs1 8 = getr regs 10 -> getr regs1 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  rw_cells rsegs m1 (spZ regs - 32) [CB 8 j0; C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  (forall L2 A2 regs2 m2 md2 p,
     sinv B API 12384 (spZ regs) L A mem md O L2 A2 m2 md2 (rec_record R REC_QUARANTINE_CLEAR [sarg which])
       (O1 ++ [(p, Z.of_nat (length (sarg which)) + 1)]) b ->
     sb_shift b A A2 = sb_malloc (sb_shift b A A1) (Z.of_nat (length (sarg which)) + 1) ->
     getr regs2 2 = Z_to_bv 64 (spZ regs - 32) -> getr regs2 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
     (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
     rw_cells rsegs m2 (spZ regs - 32) [CB 8 j0; C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
     SR rsegs (mkCfg (mkst regs2 (Z_to_bv 64 0x16ba0) m2 (seg_rom rsegs)) md2) P) ->
  SR rsegs (mkCfg (mkst regs1 (Z_to_bv 64 0x16b94) m1 (seg_rom rsegs)) md1) P.
Proof using SEGS AX ERRNO_LOW GFACT GOWN ARGS SLACK.
  intros L A regs mem md pw which R O b L1 A1 regs1 m1 md1 O1 j0 P PRE A0 SA RA ROOM SI1 E2 E4 E8 E10 KR FR KONT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  pose proof SI1 as (RJ1 & _). pose proof RJ1 as (HM1 & _).
  destruct (mr_model B _ LAWS L1 A1 m1 md1 HM1) as (Hh1 & Hl1 & _).
  set (sp := reg_get regs 2) in *. change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  eapply evt_SR_canon; [ | exact Hh1 | exact Hl1 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. eapply sqc_mid. }
  intros ms2 (can2 & -> & EQ2).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
  assert (F1 : getr R2 1 = Z_to_bv 64 0x16ba0) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity).
  assert (F2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs; exact E2).
  assert (F4 : getr R2 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X2 eq_refl); simp_regs; exact E4).
  assert (F9 : getr R2 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 9 X2 eq_refl); simp_regs; exact E10).
  assert (F10 : getr R2 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs; exact E10).
  assert (F11 : getr R2 11 = Z_to_bv 64 pw)
    by (rewrite (getr_of_eqv _ _ 11 X2 eq_refl); simp_regs; exact (eq_trans E8 A0)).
  assert (SP2 : spZ R2 = bv_unsigned sp - 32) by (unfold spZ; rewrite F2; apply unsigned_lit; lia).
  apply (sinv_arg_s B API SEGS ERRNO_LOW GFACT GOWN AX ARGS 12384 (bv_unsigned sp) L A mem md O L1 A1 m1 md1 R REC_QUARANTINE_CLEAR
           O1 b R2 pw which P SI1).
  - rewrite F1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP2. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
    rewrite Z.mod_add by lia. exact HAL.
  - rewrite SP2. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
  - rewrite SP2. lia.
  - rewrite F4. exact HTP.
  - exact F10.
  - exact F11.
  - rewrite SP2.
    apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L1 A1 m1 md1 _ O1 b pw which
             (bv_unsigned sp - 32) SI1 RA); [unfold ARG_S_K, XMALLOC_K, ALLOC_STACK; lia | lia | exact SA].
  - exact ROOM.
  - intros L2 A2 regs2 m2 md2 p SI3 SH3 INI3 RP3 FK3.
    rewrite F1.
    apply (KONT L2 A2 regs2 m2 md2 p SI3 SH3).
    + exact (eq_trans (RP3 2 ltac:(unfold callee_saved; lia)) F2).
    + exact (eq_trans (RP3 9 ltac:(unfold callee_saved; lia)) F9).
    + intros r Hr N2 N8 N9. rewrite (RP3 r Hr). pose proof (sqc_getr_nz r Hr) as NZ.
      rewrite (getr_of_eqv _ _ _ X2 NZ). rewrite <- (KR r Hr N2 N8 N9). unfold callee_saved in Hr.
      assert (CC : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/
                   r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct CC as [CC|CC]; [subst r; simp_regs; reflexivity|]). subst r; simp_regs; reflexivity.
    + apply (rw_cells_transfer rsegs m1); [exact FR|]. intros i Hi. cbn in Hi.
      destruct (FK3 (bv_unsigned sp - 32 + i) ltac:(rewrite SP2; lia)) as [K1 K2].
      split; [exact K1 | exact (proj1 K2)].
Qed.

Hypothesis RSO : rec_shape_of_contract.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RFREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.

Lemma sqc_rest : forall L A regs mem md which R O b A1 L2 A2 regs2 m2 md2 O1 p (j0 : list byte),
  call_pre_t B API 12384 L A regs mem md ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes -> frm_zero fp_csr ->
  -2^31 <= r_code R < 2^31 -> (length (r_calls R) <= 16)%nat ->
  room_ag (sb_mallocs b (sup_quarantine_clear_sizes which (snd (sup_quarantine_clear_m R which)))) (LMAX + 1) ->
  sb_le (sb_shift b A A1) b ->
  sinv B API 12384 (spZ regs) L A mem md O L2 A2 m2 md2 (rec_record R REC_QUARANTINE_CLEAR [sarg which])
    (O1 ++ [(p, Z.of_nat (length (sarg which)) + 1)]) b ->
  sb_shift b A A2 = sb_malloc (sb_shift b A A1) (Z.of_nat (length (sarg which)) + 1) ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 32) -> getr regs2 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  rw_cells rsegs m2 (spZ regs - 32) [CB 8 j0; C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  SR rsegs (mkCfg (mkst regs2 (Z_to_bv 64 0x16ba0) m2 (seg_rom rsegs)) md2)
    (sup_quarantine_clear_ret B API L A regs mem md which R O b).
Proof using SEGS AX CTX ERRNO_LOW ANSF SLACK GOWN RSO RIMG RFREE.
  intros L A regs mem md which R O b A1 L2 A2 regs2 m2 md2 O1 p j0 PRE GS FRM HCODE C1 ROOM BLE1 SI2 SH2 E2 E9
    KR FR.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  pose proof SI2 as (RJ2 & _ & _ & _ & _ & RA2 & _).
  pose proof RJ2 as (HM2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC2 & _).
  destruct (mr_model B _ LAWS L2 A2 m2 md2 HM2) as (Hh2 & Hl2 & _).
  set (sp := reg_get regs 2) in *. change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (FRn : rw_cells rsegs (normalize rsegs m2) (bv_unsigned sp - 32)
                  [CB 8 j0; C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)])
    by (apply rw_cells_norm_hi; [exact RA2 | lia | exact FR]).
  assert (STn : stk rsegs (normalize rsegs m2) (bv_unsigned sp - 12384) (bv_unsigned sp - 32)).
  { apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC2. left. lia. }
  pose proof (bytes_at_normalize rsegs m2 _ _ RA2
                (sqc_rjr_shapes B API SEGS RIMG 12384 (bv_unsigned sp) O L A mem md L2 A2 m2 md2 RJ2 GS)) as GSn.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (Q2 : reg_get regs2 2 = Z_to_bv 64 (bv_unsigned sp - 32)) by exact E2.
    rewrite Q2.
    eapply (evt_normalize rsegs); [exact WX | exact RA2 |].
    eapply (sqc_after RSO); [exact FRn | exact STn | lia | lia | exact GSn | apply mem_inv_normalize]. }
  intros ms3 (can3 & (s3n & Q3 & REL3 & RO3) & EQ3).
  destruct Q3 as (m3n & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU3n & WM3n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL3) as [EC3 MR3r].
  revert EC3 MR3r RO3 EQ3. generalize (ms_mem can3) as m3. intros m3 EC3 MR3r RO3 EQ3. subst can3.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR3r RO3 MU3n) as MU3.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR3r RO3 WM3n) as WM3.
  clear MU3n WM3n MR3r.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L2 A2 m2 md2 _ _ b m3 _ SI2 MU3 WM3
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI3.
  assert (E3_1 : getr R3 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; exact E9).
  assert (E3_11 : getr R3 11 = Z_to_bv 64 0x10417)
    by (rewrite (getr_of_eqv _ _ 11 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_12 : getr R3 12 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 12 X3 eq_refl); simp_regs; reflexivity).
  assert (RP3 : regs_preserved regs R3).
  { intros r Hr. pose proof (sqc_getr_nz r Hr) as NZ. rewrite (getr_of_eqv _ _ _ X3 NZ).
    pose proof Hr as Hr0. unfold callee_saved in Hr.
    assert (CC : r = 2 \/ r = 8 \/ r = 9 \/ (r <> 2 /\ r <> 8 /\ r <> 9)) by lia.
    destruct CC as [->|[->|[->|(N2 & N8 & N9)]]]; [simp_regs; reflexivity | simp_regs; reflexivity
      | simp_regs; reflexivity |].
    rewrite <- (KR r Hr0 N2 N8 N9).
    assert (CC : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/
                 r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr Hr0 N2 N8 N9 NZ.
    repeat (destruct CC as [CC|CC]; [subst r; simp_regs; reflexivity|]). subst r; simp_regs; reflexivity. }
  assert (LT : (length (snd (rec_answer (rec_record R REC_QUARANTINE_CLEAR [sarg which]) (REC_QUARANTINE_CLEAR, [sarg which])
                 (daemon_shape "quarantine_clear") true)) <= 16)%nat).
  { pose proof (sqc_stub_len R REC_QUARANTINE_CLEAR [sarg which] (daemon_shape "quarantine_clear") true HCODE) as H.
    assert (LX : length (daemon_shape "quarantine_clear") = 6%nat) by (vm_compute; reflexivity).
    rewrite LX in H. exact H. }
  change (sup_quarantine_clear_m R which) with (rec_answer (rec_record R REC_QUARANTINE_CLEAR [sarg which]) (REC_QUARANTINE_CLEAR, [sarg which])
           (daemon_shape "quarantine_clear") true) in ROOM.
  assert (BLE2 : sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length (sarg which)) + 1)))
    by (rewrite SH2; apply sb_malloc_mono; exact BLE1).
  assert (AK : ANSWER_K <= 12384) by (apply Z.leb_le; vm_compute; reflexivity).
  eapply SR_mono.
  { apply (sqc_answer 12384 L A regs mem md O L2 A2 R3 m3 md2 (rec_record R REC_QUARANTINE_CLEAR [sarg which])
             (O1 ++ [(p, Z.of_nat (length (sarg which)) + 1)]) b (sb_malloc b (Z.of_nat (length (sarg which)) + 1))
             (rec_entry G_REC REC_SC R) 0x10417 (REC_QUARANTINE_CLEAR, [sarg which]) (daemon_shape "quarantine_clear") true
             PRE AK SI3 E3_1 ltac:(unfold spZ; rewrite E3_2; reflexivity) RP3 E3_10 E3_11
             ltac:(rewrite E3_12; reflexivity)).
    - intros _. replace (daemon_shape "quarantine_clear") with REC_MOD_HOST_SHAPE by (vm_compute; reflexivity).
      apply sqc_mod_host_shape. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 SI3)))))).
    - intros _ _. exact (ans_entry_record R REC_QUARANTINE_CLEAR [sarg which] C1).
    - exact FRM.
    - exact BLE2.
    - eapply sqc_room_ans; [exact BLE2 | unfold LMAX; lia | exact ROOM]. }
  intros c' TR.
  destruct TR as (fx'' & L' & A' & regs' & mem' & md' & O' & q & -> & FK' & POST' & A10' & GR' & ON' & BL' & IN' & FB'
    & NQ' & BY' & OK' & AP' & RA' & F18' & INI' & REG' & BLE' & RES').
  exists fx'', L', A', regs', mem', md', (fst (sup_quarantine_clear_m R which)), O', (snd (sup_quarantine_clear_m R which)), q.
  split; [apply surjective_pairing|]. split; [reflexivity|]. split; [exact FK'|].
  split; [exact POST'|].
  do 10 (split; [assumption|]).
  split.
  { rewrite SEGS. apply (sqc_shapes_kept B API SEGS RIMG RFREE 12384 L A regs mem md _ _ L' A' regs' mem' md' PRK POST');
      [|exact GS]. intros a Ha Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES in *. lia. }
  repeat (split; [assumption|]). exact RES'.
Qed.

Theorem sup_quarantine_clear_holds : sup_quarantine_clear_contract B API.
Proof using SEGS ERRNO_LOW GFACT GOWN AX CTX SLACK REC ANSF ARGS RSO RIMG RFREE.
  unfold sup_quarantine_clear_contract.
  intros L A regs mem md pw which R O b PRE A0 SA GS GR RA FRM F18 RES ROOM.
  rewrite SEGS in GS, GR, RA, F18 |- *.
  pose proof (rec_rep_calls_le rsegs G_REC REC_SC L A mem R O GR) as C1.
  pose proof GR as (Q0 & (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HCODE & _) & _) & _).
  assert (LN : Z.of_nat (length (sarg which)) <= LMAX).
  { destruct which as [x|]; [destruct SA as (_ & _ & HL & _); exact HL | apply Z.leb_le; vm_compute; reflexivity]. }
  apply (sqc_head L A regs mem md R O b _ PRE GR RA F18 RES).
  intros L1 A1 regs1 m1 md1 O1 j0 SI1 BLE1 E2 E4 E8 E10 KR FR.
  assert (ROOMA : room_ag (sb_malloc (sb_shift b A A1) (Z.of_nat (length (sarg which)) + 1))
                    (Z.of_nat (length (sarg which)) + 1)).
  { apply (sqc_room_arg b _ _ (Z.of_nat (length (snd (sup_quarantine_clear_m R which))) + 1));
      [exact BLE1 | lia | lia | exact ROOM]. }
  apply (sqc_arg L A regs mem md pw which R O b L1 A1 regs1 m1 md1 O1 j0 _ PRE A0 SA RA ROOMA SI1 E2 E4 E8 E10 KR FR).
  intros L2 A2 regs2 m2 md2 p SI2 SH2 F2 F9 KR2 FR2.
  exact (sqc_rest L A regs mem md which R O b A1 L2 A2 regs2 m2 md2 O1 p j0 PRE GS FRM HCODE C1 ROOM BLE1 SI2 SH2
           F2 F9 KR2 FR2).
Qed.

End P.

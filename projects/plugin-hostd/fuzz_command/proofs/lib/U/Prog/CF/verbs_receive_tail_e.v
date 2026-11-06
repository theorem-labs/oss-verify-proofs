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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v; 1022 of its 1119 lines of code are new or changed and 738 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/chain_words.v, with its module paths and module names changed; 183 of its 219 lines of code are new or changed and 1083 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/verbs_receive_br.v; 145 of its 184 lines of code are new or changed and 180 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_call.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_br.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecKindB reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_tail0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Lemma tle_k : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (jk : list byte)
    (w1 w8 w9 w18 w19 w20 w21 w22 w23 w24 : word),
  bv_unsigned sp + 608 < 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned sp + 520)
    [CB 8 jk; C8 w24; C8 w23; C8 w22; C8 w21; C8 w20; C8 w19; C8 w18; C8 w9; C8 w8; C8 w1] ->
  evt rsegs (fun ms' => ms' = MS (mkR w1 (Z_to_bv 64 (bv_unsigned sp + 608)) gp tp t0 t1 t2 w8 w9 a0 a1 a2 a3 a4 a5 a6 a7
                                   w18 w19 w20 w21 w22 w23 w24 s9 s10 s11 t3 t4 t5 t6)
                              F (ret_pc w1) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17b20) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m jk w1 w8 w9 w18 w19 w20 w21 w22 w23 w24 H608 FR.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  do 12 zstep. apply evt_done. reflexivity.
Qed.

Lemma tle_le_at : forall (B : malloc_syms) m m' a bs, le_at B m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  le_at B m' a bs.
Proof. unfold le_at, blk_data. intros B m m' a bs H E i Hi. rewrite (E i Hi). exact (H i Hi). Qed.

Definition tle_R (rg rg0 : bvmap 5 word) : bvmap 5 word :=
  mkR (getr rg0 1) (Z_to_bv 64 (bv_unsigned (reg_get rg 2) + 608)) (reg_get rg 3) (reg_get rg 4)
      (reg_get rg 5) (reg_get rg 6) (reg_get rg 7) (getr rg0 8) (getr rg0 9) (reg_get rg 10) (reg_get rg 11)
      (reg_get rg 12) (reg_get rg 13) (reg_get rg 14) (reg_get rg 15) (reg_get rg 16) (reg_get rg 17)
      (getr rg0 18) (getr rg0 19) (getr rg0 20) (getr rg0 21) (getr rg0 22) (getr rg0 23) (getr rg0 24)
      (reg_get rg 25) (reg_get rg 26) (reg_get rg 27) (reg_get rg 28) (reg_get rg 29) (reg_get rg 30) (reg_get rg 31).

Section TE.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Local Notation D := (s_D S).
Local Notation VS f := (@vr_state f _ B API S).
Local Notation TS f := (@tl_state f _ B API S).

Lemma tl_epi : forall rg mem1 md1 L1 A1 R1 O1 k1 qv jk c x (quit : bool),
  TS fx rg 0x17b20 mem1 md1 L1 A1 R1 O1 k1 qv [] jk c ->
  vr_run (s_R S) D = (R1, x, quit) -> qv = (if quit then 1 else s_q0 S) ->
  SR rsegs c (vr_post B API S).
Proof using HF HS.
  intros rg mem1 md1 L1 A1 R1 O1 k1 qv jk c x quit HST HRUN HQV. subst qv.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof HST as (_ & FPK & VR & T & FR & GQ & _).
  pose proof VR as (V2 & V3 & V4 & V8 & V9 & V25 & V26 & V27).
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  pose proof (ok_pre B API S HS) as (HM0 & HW0 & _ & RA0 & _).
  pose proof (t_ro _ _ _ _ _ _ _ _ _ _ _ T) as RO1. rewrite SEGS in RO1.
  assert (SP2 : bv_unsigned (reg_get rg 2) = s_spf S).
  { change (reg_get rg 2) with (getr rg 2). rewrite V2. apply unsigned_lit. unfold s_spf, VR_K in *. lia. }
  assert (CELLS : rw_cells rsegs (normalize rsegs mem1) (bv_unsigned (reg_get rg 2) + 520)
    [CB 8 jk; C8 (getr (s_regs S) 24); C8 (getr (s_regs S) 23); C8 (getr (s_regs S) 22); C8 (getr (s_regs S) 21);
     C8 (getr (s_regs S) 20); C8 (getr (s_regs S) 19); C8 (getr (s_regs S) 18); C8 (getr (s_regs S) 9);
     C8 (getr (s_regs S) 8); C8 (getr (s_regs S) 1)]).
  { rewrite SP2. destruct FR as (FR1 & _). apply rw_cells_normalize; [exact RO1 | exact FR1 |].
    intros i Hi. cbn in Hi. apply ro_addr_hi. unfold s_spf, VR_K in *. lia. }
  assert (EV : evt rsegs (fun ms' => ms' = MS (tle_R rg (s_regs S)) fp_regs (ret_pc (getr (s_regs S) 1)) fp_csr None
                                        (normalize rsegs mem1) (seg_rom rsegs))
                 (MS (Regs6ss.mkR_of rg) fp_regs (Z_to_bv 64 0x17b20) fp_csr None (normalize rsegs mem1) (seg_rom rsegs))).
  { unfold Regs6ss.mkR_of, tle_R. eapply tle_k; [|exact CELLS]. rewrite SP2. unfold s_spf, VR_K in *. lia. }
  apply (tl_bridge B API HF S HS rg 0x17b20 mem1 md1 L1 A1 R1 O1 k1 _ [] jk c []
    (fun ms' => ms' = MS (tle_R rg (s_regs S)) fp_regs (ret_pc (getr (s_regs S) 1)) fp_csr None
                     (normalize rsegs mem1) (seg_rom rsegs)) (vr_post B API S) HST).
  - intros y _ _ _. exact I.
  - eapply evt_mono; [exact EV|]. intros ms' E. split; [exact E|].
    exists (tle_R rg (s_regs S)), (ret_pc (getr (s_regs S) 1)), (normalize rsegs mem1).
    split; [exact E|]. split; [apply munch_refl | apply wmono_refl].
  - intros R' pc' m' mem2 rg' HQ X _ MU _ T2 _.
    injection HQ; intros; subst.
    pose proof (t_rel _ _ _ _ _ _ _ _ _ _ _ T2) as REL2.
    pose proof REL2 as (HM2 & _ & _ & _ & HR2 & _ & HF2 & HK2 & _).
    pose proof (t_old _ _ _ _ _ _ _ _ _ _ _ T2) as OLD.
    pose proof (OLD _ (ok_db B API S HS) (ok_dno B API S HS)) as (DB1 & DNO1).
    assert (NIN : ~ In (s_data S) (map fst (s_O S))).
    { apply (addr_notin B API (s_L S) (s_A S) (s_mem S) (s_md S) (s_R S) (s_O S) (s_data S) (Z.max (s_n S) 1) HM0
               (ok_rec B API S HS) (ok_db B API S HS)); [lia | exact (ok_dno B API S HS)]. }
    assert (PR : regs_preserved (s_regs S) rg').
    { intros r Hr. cs_cases r Hr;
        match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv (tle_R rg (s_regs S)) rg' k X eq_refl) end;
        [ | exact V3 | exact V4 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | reflexivity | reflexivity | reflexivity | exact V25 | exact V26 | exact V27 ].
      transitivity (Z_to_bv 64 (bv_unsigned (reg_get rg 2) + 608)); [reflexivity|].
      rewrite SP2. unfold s_spf. replace (spZ (s_regs S) - 608 + 608) with (spZ (s_regs S)) by ring.
      unfold spZ. apply Z_to_bv_bv_unsigned. }
    assert (MK : forall i, 0 <= i < 24 ->
      mbyte (ms_segs B) mem2 (s_msg S + i) = mbyte (ms_segs B) (s_mem S) (s_msg S + i)).
    { intros i Hi. destruct (ok_mout B API S HS i Hi) as (NO0 & NSC).
      pose proof (ok_spm B API S HS) as SPM. pose proof (ok_m63 B API S HS) as M63.
      change (bv_unsigned (getr (s_regs S) 2)) with (spZ (s_regs S)) in SPM.
      refine (proj1 (HF2 (s_msg S + i) _ NO0 _ NSC (ok_mnw B API S HS i Hi))).
      - left. unfold VR_K in SPC. lia.
      - intros Ho. destruct (owned_low B _ (aa_laws API) _ _ _ _ _ HM2 Ho) as [_ Hlt]. unfold VR_K in SPC. lia. }
    assert (GQ2 : le_at B mem2 G_QUIT (Mem.le4 (Z_to_bv 64 (if quit then 1 else s_q0 S)))).
    { apply (tle_le_at B mem1).
      - apply CF.reply.bytes_le_at. rewrite SEGS. exact GQ.
      - intros i Hi. rewrite Mem.length_le4 in Hi. rewrite SEGS.
        apply (munch_mbyte rsegs [] mem1 mem2 _ MU); [unfold G_QUIT; lia | exact I]. }
    assert (DATA2 : le_at B mem2 (s_data S) D).
    { apply (tle_le_at B (s_mem S)); [exact (ok_D B API S HS)|]. intros i Hi.
      pose proof (ok_nD B API S HS) as ND.
      apply (HK2 (s_data S) (Z.max (s_n S) 1) i (ok_db B API S HS) NIN). lia. }
    assert (KEPT : blocks_kept B (s_L S) (s_A S) (s_mem S) mem2 (owned_by (s_O S))).
    { intros a k i Hin Hno Hi. apply (HK2 a k i Hin); [|exact Hi]. intros Ha. apply Hno.
      apply in_map_iff in Ha as ([a' k'] & E & Hin'). cbn [fst] in E. subst a'. unfold owned_by. exists k'. exact Hin'. }
    assert (TAB : exists can', vr_tables B mem2 can').
    { destruct (st_f18 B API HF _ _ _ _ HM2) as (_ & cn & SSP1 & SSP2).
      destruct (ok_tab B API S HS) as (IV & INF & _ & _).
      exists cn. split; [|split; [|split; [exact SSP1 | exact SSP2]]].
      - apply (tle_le_at B (s_mem S)); [exact IV|]. intros i Hi.
        assert (LIV : length (concat (map (fun p => Mem.le8 (Z_to_bv 64 p)) iv_ptrs_b)) = 144%nat)
          by (vm_compute; reflexivity).
        rewrite LIV in Hi.
        apply (st_relro B API HF S HS _ _ _ _ _ REL2). exists 0x226b0, 1680. split; [left; reflexivity|].
        unfold IV_TABLE_B. lia.
      - apply (tle_le_at B (s_mem S)); [exact INF|]. intros i Hi.
        assert (LIN : length info_bytes = 160%nat) by (vm_compute; reflexivity).
        rewrite LIN in Hi.
        apply (st_relro B API HF S HS _ _ _ _ _ REL2). exists 0x226b0, 1680. split; [left; reflexivity|].
        unfold INFO_TABLE. lia. }
    assert (SHP : Mem.bytes_at (ms_segs B) mem2 rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes).
    { apply (bytes_at_transfer _ (s_mem S)); [exact (ok_shp B API S HS)|]. intros i Hi.
      apply (st_relro B API HF S HS _ _ _ _ _ REL2). exists 0x226b0, 1680. split; [left; reflexivity|].
      rewrite rec_shape_of.g_shapes_length in Hi. unfold rec_shape_of_c.G_SHAPES. lia. }
    rewrite (ret_pc_of_ok _ RA0). apply SR_ret. unfold vr_post.
    exists fx, L1, A1, rg', mem2, md1, O1, (sb_n (s_b S) k1).
    split; [rewrite SEGS; reflexivity|].
    split; [exact FPK|].
    split; [apply (rel_final B API); [exact HW0 | exact REL2 | exact PR]|].
    split; [exact (t_ro _ _ _ _ _ _ _ _ _ _ _ T2)|].
    split; [rewrite HRUN; split; [exact (t_rec _ _ _ _ _ _ _ _ _ _ _ T2) | exact GQ2]|].
    split; [exact DB1|]. split; [exact DATA2|]. split; [exact DNO1|].
    split; [intros pn H1 H2; exact (proj1 (OLD pn H1 H2))|].
    split; [intros pn H1 H2; exact (proj2 (OLD pn H1 H2))|].
    split; [intros _; exact (t_init _ _ _ _ _ _ _ _ _ _ _ T2)|].
    split; [exact HR2|].
    split.
    { apply (tle_le_at B (s_mem S)); [exact (ok_fd B API S HS)|]. intros i Hi. rewrite Mem.length_le4 in Hi.
      apply MK. lia. }
    split.
    { apply (tle_le_at B (s_mem S)); [exact (ok_mdat B API S HS)|]. intros i Hi. rewrite Mem.length_le8 in Hi.
      replace (s_msg S + 8 + i) with (s_msg S + (8 + i)) by ring. apply MK. lia. }
    split.
    { apply (tle_le_at B (s_mem S)); [exact (ok_mn B API S HS)|]. intros i Hi. rewrite Mem.length_le8 in Hi.
      replace (s_msg S + 16 + i) with (s_msg S + (16 + i)) by ring. apply MK. lia. }
    split.
    { intros pn Hpn. destruct (t_sub _ _ _ _ _ _ _ _ _ _ _ T2 pn Hpn) as [H|[H|H]];
        [left; exact H | right; exact H | destruct H]. }
    split; [exact KEPT|].
    split; [exact TAB|].
    split; [exact SHP|].
    split; [exact (proj1 (t_res _ _ _ _ _ _ _ _ _ _ _ T2)) | reflexivity].
Qed.

End TE.
